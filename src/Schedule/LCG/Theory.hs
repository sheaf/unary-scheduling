{-# LANGUAGE CPP                 #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions    #-}

-- | The /theory/ side of the DPLL(T) loop for unary scheduling.
--
-- A 'Theory' bundles the SAT core ("SAT.Solver"), the precedence-atom
-- registry ("Schedule.LCG.Atoms"), the unary-scheduling propagators
-- ("Schedule.Propagators"), and the shared schedule trail.
module Schedule.LCG.Theory
  ( -- * Theory state
    Theory(..)
  , newTheory
    -- * SAT-decision-level synchronisation
  , pushLevel
  , popToLevel
    -- * One round of theory propagation
  , theoryPropagate
    -- * Inspection
  , numPrecedenceDecisions
  )
  where

-- base
import Control.Monad
  ( replicateM_
#ifdef DEBUG
  , when
#endif
  )
import Control.Monad.ST
  ( ST )
import Data.Bits
  ( shiftR )

-- containers
import Data.IntMap.Strict
  ( IntMap )
import qualified Data.IntMap.Strict as IntMap
  ( toList )
import Data.IntSet
  ( IntSet )
import qualified Data.IntSet as IntSet
  ( empty, fromList, insert, singleton, toList )

-- mtl
import Control.Monad.Trans.Class
  ( lift )
import Control.Monad.Trans.Except
  ( ExceptT, runExceptT, throwE )
import Control.Monad.Trans.Reader
  ( runReaderT )
import Control.Monad.Trans.State.Strict
  ( runStateT )

-- primitive
import Control.Monad.Primitive
  ( PrimMonad(PrimState) )
import Data.Primitive.MutVar
  ( MutVar, newMutVar, readMutVar, writeMutVar, modifyMutVar' )

-- text
import Data.Text
  ( Text )

-- memory-arena
import qualified Memory.Growable as Growable
import Memory.Growable
  ( Growable )

-- vector
import qualified Data.Vector as Boxed.Vector
  ( length )
import qualified Data.Vector.Primitive.Mutable as Primitive
  ( MVector )

-- unary-scheduling
import SAT.Base
  ( Lit, LBool(..)
  , negateLit, litVar, varIndex
  )
import SAT.Clause
  ( Reason(..), LazyReason(..), forceLazyReason )
import qualified SAT.Solver as SAT
import Schedule.Constraint
  ( Constraints(..) )
import Schedule.LCG.Atoms
  ( PrecedenceAtoms, mkPrecedenceAtoms, precLit
  , litPrecedence, isPrecedenceVar
  , numTasks
  )
import Schedule.Monad
  ( ScheduleMonad, TaskUpdates(..) )
import Schedule.Monitor
  ( Monitoring(..), MonitorMode(..), Monitor )
import Schedule.Ordering
  ( EdgeOrigin(..), CycleInfo
  , addIncidentEdgesTransitively
#ifdef DEBUG
  , Order(LessThan, GreaterThan, Unknown, Equal), readOrdering
#endif
  )
import Schedule.Propagators
  ( Propagator, propagationLoop, seedAllOf, seedMatrixWatchers )
import Schedule.Task
  ( MutableTaskInfos, TaskInfos(..) )
import Schedule.Trail
  ( Trail, newTrail, currentMark, undoTo, orderingCellWriter )
import Schedule.Interval
  ( Measurable )

-------------------------------------------------------------------------------
-- Theory state.

-- | The DPLL(T) theory state for unary scheduling.
--
-- The @mode@ parameter selects the instrumentation level ('Schedule.Monitor');
-- at @mode ~ 'Schedule.Monitor.MonitoringOff'@ the monitor and all its hooks are erased.
data Theory mode s task t = Theory
  { -- | The CDCL core driving search.
    solver         :: !( SAT.Solver s )
  , -- | The bijection between task pairs and SAT variables.
    atoms          :: !PrecedenceAtoms
  , -- | The borrowed shared scheduler state (in-place mutated).
    tasks          :: !( MutableTaskInfos s task t )
  , -- | The schedule trail for in-place undo.
    schedTrail     :: !( Trail s task t )
  , -- | Scheduling propagators run on each theory round.
    propagators    :: ![ Propagator task t ]
  , -- | Maximum propagator-round iterations per theory step.
    maxPropRounds  :: !Int
  , -- | Next SAT trail position to channel into the scheduler.
    --
    -- @[0, theoryHead)@ have already been processed; @[theoryHead, trailSize)@
    -- still need to be channeled.
    theoryHead     :: !( MutVar s SAT.TrailPos )
  , -- | Per SAT decision level, the schedule-trail mark in effect at the
    -- start of that level. Indexed by the level minus one (level @k + 1@
    -- starts at @levelMarks[k]@).
    levelMarks     :: !( Growable Primitive.MVector s Int )
  , -- | Driver for the propagator seed on the next 'runPropagators' call.
    --
    -- 'Nothing' marks the very first call: every propagator subscription
    -- is seeded with the full task set ('seedAllOf').
    dirtySeed      :: !( MutVar s ( Maybe IntSet ) )
  , -- | Cumulative count of theory propagations: literals the theory has
    -- promoted onto the SAT trail (both derived transitive edges and
    -- propagator-emitted precedences). For instrumentation.
    theoryPropCount :: !( MutVar s Int )
  , -- | Optional instrumentation. Erased entirely when @mode ~ 'MonitoringOff'@.
    monitor         :: !( Monitor mode s )
  }

{-# INLINABLE newTheory #-}
{-# SPECIALISE newTheory @MonitoringOff #-}

-- | Allocate a fresh 'Theory' for the given scheduler state and
-- propagators.
newTheory
  :: forall mode s task t
  .  MonitorMode mode
  => MutableTaskInfos s task t
  -> [ Propagator task t ]
  -> Int                          -- ^ propagator-round cap per theory step
  -> ST s ( Theory mode s task t )
newTheory tis props rounds = do
  s     <- SAT.newSolver
  let nT  = Boxed.Vector.length ( taskNames tis )
      !nA = ( nT * ( nT - 1 ) ) `shiftR` 1
  ps    <-
    if nA == 0
    then pure ( mkPrecedenceAtoms nT 0 )
    else do
      v0 <- SAT.newVar s
      replicateM_ ( nA - 1 ) ( SAT.newVar s )
      pure ( mkPrecedenceAtoms nT ( varIndex v0 ) )
  trail <- newTrail
  th    <- newMutVar 0
  lms   <- Growable.new 16
  ds    <- newMutVar Nothing
  tpc   <- newMutVar 0
  mon   <- newMonitor @mode
  pure Theory
    { solver          = s
    , atoms           = ps
    , tasks           = tis
    , schedTrail      = trail
    , propagators     = props
    , maxPropRounds   = rounds
    , theoryHead      = th
    , levelMarks      = lms
    , dirtySeed       = ds
    , theoryPropCount = tpc
    , monitor         = mon
    }

-------------------------------------------------------------------------------
-- SAT-decision-level synchronisation.

-- | Snapshot the current schedule-trail mark to associate it with a fresh
-- SAT decision level. Must be called immediately after 'SAT.pushNewLevel'.
--
-- The semantics mirror 'SAT.Solver.trailLim': @levelMarks[k]@ holds the
-- schedule-trail mark captured at the start of level @k + 1@ (i.e. just
-- before the level-@(k+1)@ decision is asserted), so undoing back to that
-- mark restores the trail to the state right after level @k@'s effects.
pushLevel :: Theory mode s task t -> ST s ()
pushLevel t = do
  m <- currentMark ( schedTrail t )
  Growable.push ( levelMarks t ) m

-- | Roll the schedule trail back to the mark associated with the given
-- SAT decision level. Must be called immediately after 'SAT.cancelUntil'.
--
-- Precondition: @lvl@ is strictly less than the current SAT level
-- (i.e. we are actually backjumping). This matches how
-- 'SAT.Solver.cancelUntil' itself indexes 'SAT.Solver.trailLim'.
popToLevel :: Theory mode s task t -> SAT.DecisionLevel -> ST s ()
popToLevel t ( SAT.DecisionLevel lvl ) = do
#ifdef DEBUG
  n <- Growable.length ( levelMarks t )
  when ( lvl < 0 || lvl >= n ) $
    error $ "Schedule.LCG.Theory.popToLevel: out-of-range lvl=" <> show lvl
         <> " levelMarks.length=" <> show n
#endif
  -- 'levelMarks[lvl]' is the mark captured at the start of level @lvl + 1@,
  -- which is the mark we want to restore to in order to be back at level
  -- @lvl@ with its effects intact.
  m <- Growable.read ( levelMarks t ) lvl
  Growable.truncate ( levelMarks t ) lvl
  undoTo ( schedTrail t ) ( tasks t ) m
  -- Rewind the theory head: any trail positions above the new top are gone.
  newSize <- SAT.trailSize ( solver t )
  writeMutVar ( theoryHead t ) newSize

-- | Number of precedence literals currently on the SAT trail.
--
-- Used only for debugging/instrumentation.
numPrecedenceDecisions :: Theory mode s task t -> ST s Int
numPrecedenceDecisions t = do
  SAT.TrailPos sz <- SAT.trailSize ( solver t )
  let
    loop !i !acc
      | i >= sz   = pure acc
      | otherwise = do
          lit <- SAT.trailAt ( solver t ) ( SAT.TrailPos i )
          if isPrecedenceVar ( atoms t ) ( litVar lit )
          then loop ( i + 1 ) ( acc + 1 )
          else loop ( i + 1 ) acc
  loop 0 0

-------------------------------------------------------------------------------
-- One round of theory propagation.

{-# INLINABLE theoryPropagate #-}
{-# SPECIALISE theoryPropagate @MonitoringOff #-}

-- | Channel new SAT trail literals into the scheduler's ordering matrix,
-- run the unary-scheduling propagators to a fixpoint, and promote the
-- emitted precedence inferences back to the SAT trail.
--
-- Returns 'Nothing' on success (any newly enqueued literals will be
-- visible to the next 'SAT.propagate' call) and 'Just c' on conflict.
theoryPropagate
  :: forall mode s task t
  .  ( Num t, Measurable t, Bounded t
     , Show t, Show task
     , MonitorMode mode
     )
  => Theory mode s task t
  -> ST s ( Maybe SAT.Conflict )
theoryPropagate t = do
  channelOutcome <- channelPending t
  case channelOutcome of
    Just c  -> pure ( Just c )
    Nothing -> runPropagators t

-------------------------------------------------------------------------------
-- (1) Channel SAT trail literals into the ordering matrix.

{-# INLINABLE channelPending #-}
{-# SPECIALISE channelPending @MonitoringOff #-}

-- | Drain @[theoryHead, trailSize)@ into the matrix. Each channeled lit
-- may push more theory propagations onto the SAT trail (transitive-closure
-- derivations), which the loop then consumes in turn.
--
-- Returns the first conflict encountered (if any).
channelPending
  :: forall mode s task t
  .  ( Num t, Measurable t, Bounded t
     , MonitorMode mode
     )
  => Theory mode s task t
  -> ST s ( Maybe SAT.Conflict )
channelPending t = do
#ifdef DEBUG
  checkMatrixTrailInvariant t "channelPending (start)"
#endif
  loop
  where
    loop :: ST s ( Maybe SAT.Conflict )
    loop = do
      ok <- SAT.isOk ( solver t )
      if not ok
      then pure Nothing  -- solver already marked UNSAT; outer loop will bail.
      else do
        h@( SAT.TrailPos hi ) <- readMutVar ( theoryHead t )
        SAT.TrailPos sz       <- SAT.trailSize ( solver t )
        if hi >= sz
        then pure Nothing
        else do
          lit <- SAT.trailAt ( solver t ) h
          writeMutVar ( theoryHead t ) ( SAT.TrailPos ( hi + 1 ) )
          case litPrecedence ( atoms t ) lit of
            Nothing                       -> loop
            Just ( predTask, succTask ) -> do
              mbConf <- channelLit t predTask succTask
              case mbConf of
                Just c  -> pure ( Just c )
                Nothing -> loop

#ifdef DEBUG
-- | Diagnostic invariant: every 'LessThan' or 'GreaterThan' cell in the
-- ordering matrix must correspond to an assigned precedence literal on the
-- SAT trail.
checkMatrixTrailInvariant
  :: forall mode s task t
  .  Theory mode s task t
  -> String
  -> ST s ()
checkMatrixTrailInvariant t ctx = iterPairs 0 1
  where
    ps     = atoms t
    nTasks = numTasks ps
    mat    = orderings ( tasks t )
    bad :: Int -> Int -> Order -> LBool -> String -> ST s ()
    bad i j o val expected = do
      dump <- SAT.dumpSolverState ( solver t )
      error $ "Schedule.LCG.Theory.checkMatrixTrailInvariant [" <> ctx <> "]: "
           <> "mat[" <> show i <> "," <> show j <> "] = " <> show o
           <> " but lit " <> show ( precLit ps i j ) <> " is " <> show val
           <> " (expected " <> expected <> ")\n" <> dump
    checkPair :: Int -> Int -> ST s ()
    checkPair i j = do
      o   <- readOrdering mat i j
      val <- SAT.litValue ( solver t ) ( precLit ps i j )
      case o of
        Unknown     -> pure ()
        LessThan    -> case val of LTrue  -> pure (); _ -> bad i j o val "LTrue"
        GreaterThan -> case val of LFalse -> pure (); _ -> bad i j o val "LFalse"
        Equal       -> bad i j o val "<matrix cycle>"
    iterPairs :: Int -> Int -> ST s ()
    iterPairs i j
      | i >= nTasks - 1 = pure ()
      | j >= nTasks     = iterPairs ( i + 1 ) ( i + 2 )
      | otherwise       = do
          checkPair i j
          iterPairs i ( j + 1 )
#endif

{-# INLINABLE channelLit #-}
{-# SPECIALISE channelLit @MonitoringOff #-}

-- | Channel a single SAT precedence assignment into the ordering matrix.
--
-- TODO: in the LCG path the ordering matrix has two writers — propagator
-- precedences are written non-transitively by 'applyConstraints' during the
-- propagation loop, then the same precedence is re-written transitively here
-- once its SAT literal is drained. The first write is redundant; the matrix
-- should have a single owner (ideally channeling).
channelLit
  :: forall mode s task t
  .  ( Num t, Measurable t, Bounded t
     , MonitorMode mode
     )
  => Theory mode s task t
  -> Int -> Int
  -> ST s ( Maybe SAT.Conflict )
channelLit t predTask succTask = do
  let tis = tasks t
  tickChannelCall ( monitor t )
#ifdef DEBUG
  let ps = atoms t
      d = numTasks ps
  when ( predTask < 0 || predTask >= d || succTask < 0 || succTask >= d ) $
    error $ "Schedule.LCG.Theory.channelLit: decoded pair=("
         <> show predTask <> "," <> show succTask <> ") out of range; dim="
         <> show d
  when ( predTask == succTask ) $
    error "Schedule.LCG.Theory.channelLit: decoded pair has equal indices"
#endif
  result <- runExceptT $
    addIncidentEdgesTransitively
      ( orderingCellWriter ( schedTrail t ) tis )
      onNewEdge
      LiftedCycle
      ( orderings tis )
      succTask
      ( IntSet.singleton predTask )
      mempty
  case result of
    Right ()                      -> pure Nothing
    Left ( LiftedCycle _info )    ->
      -- TODO: construct a clausal explanation from the cycle.
      snapshotConflict t Nothing
    Left ( LiftedConflict c )     -> pure ( Just c )
  where
    onNewEdge
      :: EdgeOrigin
      -> Int -> Int
      -> ExceptT ChannelOutcome ( ST s ) ()
    onNewEdge origin a b = do
      lift ( markDirtyPair t a b )
      case origin of
        SeedEdge -> pure ()
        DerivedEdge u -> do
          lift ( tickDerivedEdges ( monitor t ) 1 )
          -- Derived edge @a → b@ via the witness vertex @u@.
          -- The reason clause has exactly three literals:
          --   ¬p(a → u) ∨ ¬p(u → b) ∨ p(a → b)
          let derived  = precLit ( atoms t ) a b
              antePred = precLit ( atoms t ) a u
              anteSucc = precLit ( atoms t ) u b
              reason   =
                LazyReason $
                  pure
                    [ negateLit antePred
                    , negateLit anteSucc
                    , derived
                    ]
          mbConf <- lift ( assertTheoryLit t derived reason )
          case mbConf of
            Nothing -> pure ()
            Just c  -> throwE ( LiftedConflict c )

-- | Add a pair of task indices to the running dirty set so that the next
-- 'runPropagators' call wakes only the matrix-watching propagators on
-- the relevant tasks. While 'dirtySeed' is still 'Nothing' (before the
-- first 'runPropagators' call) we leave it alone: that first call will
-- seed every propagator subscription with the full task set anyway.
markDirtyPair :: Theory mode s task t -> Int -> Int -> ST s ()
markDirtyPair t a b =
  modifyMutVar' ( dirtySeed t ) $ \ case
    Nothing    -> Nothing
    Just dirty -> Just ( IntSet.insert a ( IntSet.insert b dirty ) )

-- | Outcome of a single channeling step, lifted through 'ExceptT'.
data ChannelOutcome
  = -- | The closure detected a cycle in the matrix.
    LiftedCycle !CycleInfo
  | -- | The 'onNewEdge' callback discovered a contradiction with the
    -- current SAT assignment.
    LiftedConflict !SAT.Conflict

-------------------------------------------------------------------------------
-- (2) Run the unary-scheduling propagators.

{-# INLINABLE runPropagators #-}
{-# SPECIALISE runPropagators @MonitoringOff #-}

-- | Run 'propagationLoop' over the theory's state, then walk the emitted
-- precedence inferences and promote each to a theory-propagated SAT
-- literal.
runPropagators
  :: forall mode s task t
  .  ( Num t, Measurable t, Bounded t
     , Show t, Show task
     , MonitorMode mode
     )
  => Theory mode s task t
  -> ST s ( Maybe SAT.Conflict )
runPropagators t = do
#ifdef DEBUG
  checkMatrixTrailInvariant t "runPropagators (start)"
#endif
  -- Pick the seed for this round: on the very first call we kick every
  -- subscription with the full task set; afterwards only the
  -- matrix-watching propagators wake, over the tasks 'channelLit' has
  -- marked dirty.
  mbDirty <- readMutVar ( dirtySeed t )
  let seed = case mbDirty of
        Nothing    -> seedAllOf ( propagators t )
                        ( IntSet.fromList [ 0 .. numTasks ( atoms t ) - 1 ] )
        Just dirty -> seedMatrixWatchers dirty
  writeMutVar ( dirtySeed t ) ( Just IntSet.empty )
  ( eRes, finalUpdates ) <- runSchedule ( tasks t )
    ( propagationLoop ( monitor t ) ( maxPropRounds t ) ( schedTrail t ) ( propagators t ) seed )
  -- TODO: 'propagationLoop' doesn't properly report 'GiveUp', which means we
  -- currently conflate "fixpoint, consistent" with "gave up early".
  -- That's a glaring, incompleteness/soundness hazard.
  case eRes of
    Left _err ->
      -- A propagator threw (e.g. overload, cycle, etc).
      -- Materialise a coarse snapshot conflict.
      -- TODO: use proper explanations.
      snapshotConflict t Nothing
    Right () -> do
      r <- assertEmittedPrecedences t ( precedences ( taskConstraints finalUpdates ) )
#ifdef DEBUG
      case r of
        -- All precedences asserted: invariant must hold again.
        Nothing -> checkMatrixTrailInvariant t "runPropagators (end, no conflict)"
        Just _  -> pure ()
#endif
      pure r

-- | Unwrap one round of the 'ScheduleMonad' against the theory's mutable
-- state, returning both the success/failure and the accumulated
-- 'TaskUpdates'.
runSchedule
  :: forall s task t a
  .  Measurable t
  => MutableTaskInfos s task t
  -> ScheduleMonad s task t a
  -> ST s ( Either Text a, TaskUpdates t )
runSchedule tis action =
  runStateT ( runExceptT ( runReaderT action tis ) ) mempty

-- | Walk the propagator-emitted precedence inferences and assert each as
-- a theory propagation on the SAT trail.
assertEmittedPrecedences
  :: forall mode s task t
  .  Theory mode s task t
  -> IntMap ( IntSet, IntSet )
  -> ST s ( Maybe SAT.Conflict )
assertEmittedPrecedences t precsMap = goPairs ( unpackPairs precsMap )
  where
    -- A precedence map entry @k ↦ (preds, succs)@ unpacks to one pair
    -- @(p, k)@ per @p ∈ preds@ and one pair @(k, s)@ per @s ∈ succs@.
    unpackPairs :: IntMap ( IntSet, IntSet ) -> [ ( Int, Int ) ]
    unpackPairs m =
         [ ( p, k ) | ( k, ( preds, _     ) ) <- IntMap.toList m, p <- IntSet.toList preds ]
      ++ [ ( k, s ) | ( k, ( _,     succs ) ) <- IntMap.toList m, s <- IntSet.toList succs ]

    goPairs :: [ ( Int, Int ) ] -> ST s ( Maybe SAT.Conflict )
    goPairs [] = pure Nothing
    goPairs ( ( a, b ) : rest ) = do
      ok <- SAT.isOk ( solver t )
      if not ok then pure Nothing  -- solver marked UNSAT; outer loop will bail.
      else do
#ifdef DEBUG
        let !d = numTasks ( atoms t )
        when ( a < 0 || a >= d || b < 0 || b >= d ) $
          error $ "Schedule.LCG.Theory.assertEmittedPrecedences: pair=("
               <> show a <> "," <> show b <> ") out of range; dim=" <> show d
        when ( a == b ) $
          error "Schedule.LCG.Theory.assertEmittedPrecedences: self-precedence"
#endif
        let lit = precLit ( atoms t ) a b
        reason <- snapshotReason t lit
        mbConf <- assertTheoryLit t lit reason
        case mbConf of
          Just c  -> pure ( Just c )
          Nothing -> goPairs rest

-------------------------------------------------------------------------------
-- Theory propagation primitive.

-- | Try to assert a theory-inferred literal on the SAT trail.
--
-- Returns 'Nothing' on success (or when the literal was already true) and
-- 'Just c' on contradiction with the current assignment.
assertTheoryLit
  :: forall mode s task t
  .  Theory mode s task t
  -> Lit
  -> LazyReason s
  -> ST s ( Maybe SAT.Conflict )
assertTheoryLit t lit reason = do
  val <- SAT.litValue ( solver t ) lit
  case val of
    LTrue  -> pure Nothing
    LUndef -> do
      lvl <- SAT.currentLevel ( solver t )
      if lvl == SAT.GroundLevel
      then
        -- A ground-level theory propagation is an unconditional fact.
        -- 1-UIP analysis never resolves against ground-level literals, so it
        -- needs no reason clause.
        SAT.enqueueUndef ( solver t ) lit RFact
      else do
        -- TODO: the lazy-reason table is never reclaimed on backjump, so
        -- closures from undone propagations linger, each retaining the
        -- captured 'Theory'/trail bound. Reclaim it in lockstep with the
        -- trail (cf. 'levelMarks').
        lref <- SAT.recordLazyReason ( solver t ) reason
        SAT.enqueueUndef ( solver t ) lit ( RLazy lref )
      modifyMutVar' ( theoryPropCount t ) ( + 1 )
      pure Nothing
    LFalse ->
      -- The theory inferred 'lit' but SAT has already assigned it false.
      -- Force the reason and install it as a conflict clause for 1-UIP.
      forceLazyReason reason >>= literalsAsConflict ( solver t )

-------------------------------------------------------------------------------
-- Snapshot reasons and conflict assembly.

-- The theory infers literals with two flavours of supporting clauses:
--
--   * a precise three-literal /derived-edge/ reason emitted directly by
--     'channelLit' (transitive-closure step), and
--   * a coarse /trail snapshot/ reason emitted by 'assertEmittedPrecedences'
--     (every precedence currently true above ground level supports the new
--     inference).

-- | Walk @trail[0, bound)@ and collect the negation of every precedence
-- literal at a decision level strictly above ground, optionally appending
-- @appendLast@ (which 1-UIP will resolve on after all the supporting
-- literals).
--
-- @bound@ is the exclusive upper trail position. Passing the current
-- 'SAT.trailSize' captures the snapshot of what is on the trail right
-- now; passing a smaller bound (captured at an earlier moment) reproduces
-- the trail snapshot as it stood then, ignoring any later additions.
snapshotBody
  :: forall mode s task t m
  .  ( PrimMonad m, PrimState m ~ s )
  => Theory mode s task t
  -> SAT.TrailPos     -- ^ exclusive upper bound on the trail walk
  -> Maybe Lit        -- ^ optional appended literal
  -> m [ Lit ]
snapshotBody t ( SAT.TrailPos bound ) mbAppend = loop 0 []
  where
    appended = case mbAppend of
      Nothing -> []
      Just l  -> [ l ]
    loop !i !acc
      | i >= bound = pure ( reverse acc ++ appended )
      | otherwise  = do
          let pos = SAT.TrailPos i
          lit <- SAT.trailAt ( solver t ) pos
          if isPrecedenceVar ( atoms t ) ( litVar lit )
          then do
            lvl <- SAT.levelOfAssignedVar ( solver t ) ( litVar lit )
            if lvl <= SAT.GroundLevel
            then loop ( i + 1 ) acc
            else loop ( i + 1 ) ( negateLit lit : acc )
          else loop ( i + 1 ) acc

-- | Build a 'LazyReason' that, when forced, returns the trail snapshot as
-- it stood at the moment of this call.
--
-- TODO: the resulting clause is coarse — every level-@>0@ precedence
-- literal on the trail appears in it. Per-propagator antecedent subsets
-- would shrink it.
snapshotReason
  :: forall mode s task t
  .  Theory mode s task t
  -> Lit          -- ^ propagated literal, appended to the clause body
  -> ST s ( LazyReason s )
snapshotReason t propLit = do
  -- Capture the current trail bound so that the deferred walk sees exactly
  -- the literals that were on the trail at the moment of propagation.
  bound <- SAT.trailSize ( solver t )
  pure ( LazyReason ( snapshotBody t bound ( Just propLit ) ) )

{-# INLINABLE snapshotConflict #-}
{-# SPECIALISE snapshotConflict @MonitoringOff #-}

-- | Capture a snapshot of the current trail (optionally appending
-- @propLit@) and materialise it eagerly as a 'SAT.Conflict' via
-- 'literalsAsConflict'.
--
-- Used at conflict-discovery time, where the clause is consumed
-- immediately by 1-UIP analysis (there is no laziness to gain).
snapshotConflict
  :: forall mode s task t
  .  MonitorMode mode
  => Theory mode s task t
  -> Maybe Lit
  -> ST s ( Maybe SAT.Conflict )
snapshotConflict t mbPropLit = do
  bound <- SAT.trailSize ( solver t )
  body  <- snapshotBody t bound mbPropLit
  tickTheoryConflict ( monitor t )
  recordReasonLen ( monitor t ) ( length body )
  literalsAsConflict ( solver t ) body

-- | Materialise a list of literals as a SAT 'Conflict' value.
literalsAsConflict
  :: SAT.Solver s
  -> [ Lit ]
  -> ST s ( Maybe SAT.Conflict )
literalsAsConflict s = \ case
  []       -> SAT.markFalse s *> pure Nothing
  -- TODO: a unit conflict is encoded as 'ConflictBinary x x' (a fake 2-lit
  -- clause); this only works because 'analyse' dedups via the 'seen' marker.
  -- A dedicated unit-conflict representation would be less of a trap.
  [ x ]    -> pure ( Just ( SAT.ConflictBinary x x ) )
  [ a, b ] -> pure ( Just ( SAT.ConflictBinary a b ) )
  longer   -> Just . SAT.ConflictClause <$> SAT.recordTheoryClause s longer
