{-# LANGUAGE CPP                 #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions    #-}

-- | The /theory/ side of the DPLL(T) loop for unary scheduling.
--
-- A 'Theory' bundles the SAT core ("SAT.Solver"), the atom registries
-- ("Schedule.LCG.Atoms"), the unary-scheduling propagators
-- ("Schedule.Propagators"), and the shared schedule trail.
--
-- The encoding reifies two families of SAT atoms (see "Schedule.LCG.Atoms"):
--
--   * /precedence atoms/ @p(i ≺ j)@ (used as decision variables).
--   * /bound atoms/ @[start_i ≤ k]@.
--
-- Both families carry /no/ structural clauses: antisymmetry is free (literal
-- negation), and transitivity, monotonicity and domain consistency are
-- enforced lazily by the theory (transitive-closure derivations, channelling,
-- and the propagators), generating reason clauses on demand.
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
import Data.Foldable
  ( for_ )
import Data.Maybe
  ( catMaybes )

-- containers
import Data.IntMap.Strict
  ( IntMap )
import qualified Data.IntMap.Strict as IntMap
  ( toList, lookup )
import Data.IntSet
  ( IntSet )
import qualified Data.IntSet as IntSet
  ( empty, fromList, insert, singleton, toList )

-- acts
import Data.Act
  ( Act((•)) )

-- groups
import Data.Group
  ( invert )

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

-- memory-arena
import qualified Memory.Growable as Growable
import Memory.Growable
  ( Growable )

-- vector
import qualified Data.Vector as Boxed.Vector
  ( length )
import qualified Data.Vector.Mutable as Boxed.MVector
  ( unsafeRead )
import qualified Data.Vector.Primitive.Mutable as Primitive
  ( MVector )

-- unary-scheduling
import SAT.Base
  ( Lit, LBool(..)
  , Polarity(Positive, Negative)
  , negateLit, litVar, varIndex
  )
import SAT.Clause
  ( Reason(..), LazyReason(..), forceLazyReason )
import qualified SAT.Solver as SAT
import Schedule.Constraint
  ( Constraints(..), Infeasible(..)
  , constrainToAfter, constrainToBefore
  )
import Schedule.Interval
  ( Intervals(..), Measurable
  , estLowerToStartUpper, startUpperToEstLower
  )
import Schedule.LCG.Atoms
  ( PrecedenceAtoms, mkPrecedenceAtoms, precLit
  , isPrecedenceVar, numTasks
  , BoundAtoms, newBoundAtoms, internLowerBound, internUpperBound
  , BoundThreshold(..), AtomMeaning(..), litMeaning
  )
import Schedule.Monad
  ( ScheduleMonad, TaskUpdates(..) )
import Schedule.Monitor
  ( Monitoring(..), MonitorMode(..), Monitor )
import Schedule.Ordering
  ( EdgeOrigin(..), CycleInfo
  , addIncidentEdgesTransitively
  , Order(..), readOrdering
  )
import Schedule.Propagators
  ( Propagator, propagationLoop, seedAllOf )
import Schedule.Task
  ( MutableTaskInfos, TaskInfos(..), Task(..)
  , est, lct, lst
  )
import Schedule.Trail
  ( Trail, newTrail, currentMark, undoTo, orderingCellWriter )

-------------------------------------------------------------------------------
-- Theory state.

-- | The DPLL(T) theory state for unary scheduling.
--
-- The @mode@ parameter selects the instrumentation level ('Schedule.Monitor');
-- at @mode ~ 'Schedule.Monitor.MonitoringOff'@ the monitor and all its hooks are erased.
data Theory mode s task t = Theory
  { -- | The CDCL core driving search.
    solver         :: !( SAT.Solver s )
  , -- | The bijection between task pairs and SAT decision variables.
    atoms          :: !PrecedenceAtoms
  , -- | The lazily-grown registry of start-time bound atoms (auxiliary,
    -- non-decision variables).
    boundAtoms     :: !( BoundAtoms s t )
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
    -- promoted onto the SAT trail (derived transitive edges, propagator
    -- precedences, and channelled-out bound tightenings). For instrumentation.
    theoryPropCount :: !( MutVar s Int )
  , -- | Optional instrumentation. Erased entirely when @mode ~ 'MonitoringOff'@.
    monitor         :: !( Monitor mode s )
  }

{-# INLINABLE newTheory #-}
{-# SPECIALISE newTheory @MonitoringOff #-}

-- | Allocate a fresh 'Theory' for the given scheduler state and
-- propagators, and seed each task's initial start-time bounds as ground-level
-- bound atoms (so the theory's local clausal reasons always have those bounds
-- available on the trail).
newTheory
  :: forall mode s task t
  .  ( Num t, Measurable t, Bounded t
     , MonitorMode mode
     )
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
  -- Bound atoms occupy variable indices above the fixed precedence block.
  ba    <- newBoundAtoms nA
  trail <- newTrail
  th    <- newMutVar 0
  lms   <- Growable.new 16
  ds    <- newMutVar Nothing
  tpc   <- newMutVar 0
  mon   <- newMonitor @mode
  let t = Theory
        { solver          = s
        , atoms           = ps
        , boundAtoms      = ba
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
  seedInitialBounds t nT
  pure t

-- | Assert each (non-empty) task's initial earliest-start and latest-start
-- bounds as ground-level bound facts. Maintaining \"every task's current
-- bound is an asserted bound atom\" lets the theory's local reasons cite those
-- atoms freely.
seedInitialBounds
  :: forall mode s task t
  .  ( Num t, Measurable t, Bounded t )
  => Theory mode s task t -> Int -> ST s ()
seedInitialBounds t nT =
  for_ [ 0 .. nT - 1 ] \ i -> do
    task <- readTask t i
    if null ( intervals ( taskAvailability task ) )
    then pure ()  -- a degenerate empty instance; surfaced by the first propagation
    else do
      estL <- currentEstLit t i
      lctL <- currentLctLit t i
      SAT.enqueueUndef ( solver t ) estL RFact
      SAT.enqueueUndef ( solver t ) lctL RFact

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

-- | Channel new SAT trail literals into the scheduler (precedences into the
-- ordering matrix, bound literals into the task domains), run the
-- unary-scheduling propagators to a fixpoint, and promote the emitted
-- inferences (precedences and bound tightenings) back to the SAT trail.
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
-- (1) Channel SAT trail literals into the scheduler.

{-# INLINABLE channelPending #-}
{-# SPECIALISE channelPending @MonitoringOff #-}

-- | Drain @[theoryHead, trailSize)@ into the scheduler. A precedence literal
-- is added to the ordering matrix (which may derive further transitive
-- precedences, pushed back onto the SAT trail); a bound literal tightens its
-- task's domain. Both may surface a conflict.
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
          meaning <- litMeaning ( atoms t ) ( boundAtoms t ) lit
          case meaning of
            Nothing                       -> loop
            Just ( MeansPrecedence p s )  -> do
              mbConf <- channelLit t p s
              case mbConf of
                Just c  -> pure ( Just c )
                Nothing -> loop
            Just ( MeansBound task thr pol ) -> do
              mbConf <- channelBound t task thr pol
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
      -- A matrix cycle: explained coarsely by the active precedence snapshot.
      -- TODO: reconstruct the cycle's precedence chain for a tight reason.
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

-- | Channel a single SAT bound assignment into the task's domain.
--
-- Each combination of bound kind and literal polarity tightens one side of the
-- task's start window (raising the earliest start or lowering the latest
-- completion, the latter via the @start + duration@ shift). If the tightening
-- empties the domain — a bound literal the SAT core forced against the
-- domain — surface a conflict.
channelBound
  :: forall mode s task t
  .  ( Num t, Measurable t, Bounded t
     , MonitorMode mode
     )
  => Theory mode s task t
  -> Int -> BoundThreshold t -> Polarity
  -> ST s ( Maybe SAT.Conflict )
channelBound t task thr pol = do
  let tis = tasks t
  before <- readTask t task
  let dur = taskDuration before
  _ <- case ( thr, pol ) of
    -- @start ≥ e@.
    ( LowerThreshold e, Positive ) ->
      constrainToAfter  ( schedTrail t ) tis task e
    -- @start < e@ ⟹ completion < e + duration.
    ( LowerThreshold e, Negative ) ->
      constrainToBefore ( schedTrail t ) tis task ( invert dur • estLowerToStartUpper e )
    -- @start ≤ l@ ⟹ completion ≤ l + duration.
    ( UpperThreshold l, Positive ) ->
      constrainToBefore ( schedTrail t ) tis task ( invert dur • l )
    -- @start > l@ ⟹ earliest start raised past l.
    ( UpperThreshold l, Negative ) ->
      constrainToAfter  ( schedTrail t ) tis task ( startUpperToEstLower l )
  after <- readTask t task
  if null ( intervals ( taskAvailability after ) )
  then
    -- The forced bound contradicts the domain. Explain with the (full,
    -- bound-inclusive) trail snapshot; the crossing bounds are not localised
    -- here. TODO: cite the two crossing bound atoms instead.
    snapshotConflict t Nothing
  else do
    markDirtyTask t task
    pure Nothing

-- | Add a pair of task indices to the running dirty set so that the next
-- 'runPropagators' call wakes the propagators on the relevant tasks. While
-- 'dirtySeed' is still 'Nothing' (before the first 'runPropagators' call) we
-- leave it alone: that first call seeds every propagator with the full task
-- set anyway.
markDirtyPair :: Theory mode s task t -> Int -> Int -> ST s ()
markDirtyPair t a b =
  modifyMutVar' ( dirtySeed t ) $ \ case
    Nothing    -> Nothing
    Just dirty -> Just ( IntSet.insert a ( IntSet.insert b dirty ) )

-- | Like 'markDirtyPair', for a single task (a domain change channelled in).
markDirtyTask :: Theory mode s task t -> Int -> ST s ()
markDirtyTask t i =
  modifyMutVar' ( dirtySeed t ) $ \ case
    Nothing    -> Nothing
    Just dirty -> Just ( IntSet.insert i dirty )

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

-- | Run 'propagationLoop' to a fixpoint, then promote its inferences to the
-- SAT trail: detected precedences become precedence literals and est\/lct
-- tightenings become bound literals, each carrying a local clausal reason.
-- Finally, surface any infeasibility the propagators reported.
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
  -- Pick the seed: on the very first call, wake every subscription with the
  -- full task set; afterwards wake the propagators over the tasks that
  -- channeling has marked dirty (precedence edges and bound tightenings).
  mbDirty <- readMutVar ( dirtySeed t )
  let seed = case mbDirty of
        Nothing    -> seedAllOf ( propagators t )
                        ( IntSet.fromList [ 0 .. numTasks ( atoms t ) - 1 ] )
        Just dirty -> seedAllOf ( propagators t ) dirty
  writeMutVar ( dirtySeed t ) ( Just IntSet.empty )
  ( eRes, finalUpdates ) <- runSchedule ( tasks t )
    ( propagationLoop ( monitor t ) ( maxPropRounds t ) ( schedTrail t ) ( propagators t ) seed )
  -- TODO: 'propagationLoop' doesn't properly report 'GiveUp', which means we
  -- currently conflate "fixpoint, consistent" with "gave up early".
  let cts = taskConstraints finalUpdates
  -- The accumulated 'TaskUpdates' is preserved even when a propagator threw
  -- (the state sits below 'ExceptT'), so we can always channel out the bounds
  -- and precedences derived so far before turning the infeasibility into a
  -- local clausal conflict.
  mbConf1 <- assertEmittedPrecedences t ( precedences cts )
  case mbConf1 of
    Just c  -> pure ( Just c )
    Nothing -> do
      mbConf2 <- channelOutBounds t ( tightenedBounds finalUpdates ) ( boundReasons cts )
      case mbConf2 of
        Just c  -> pure ( Just c )
        Nothing -> case eRes of
          Right () -> do
#ifdef DEBUG
            checkMatrixTrailInvariant t "runPropagators (end, no conflict)"
#endif
            pure Nothing
          Left infeasible -> buildInfeasibleConflict t infeasible

-- | Unwrap one round of the 'ScheduleMonad' against the theory's mutable
-- state, returning both the success/failure and the accumulated
-- 'TaskUpdates' (which is retained even on a 'Left', as the state monad sits
-- below the error monad).
runSchedule
  :: forall s task t a
  .  Measurable t
  => MutableTaskInfos s task t
  -> ScheduleMonad s task t a
  -> ST s ( Either Infeasible a, TaskUpdates t )
runSchedule tis action =
  runStateT ( runExceptT ( runReaderT action tis ) ) mempty

-------------------------------------------------------------------------------
-- (2a) Promote detected precedences to the SAT trail.

-- | Assert each propagator-detected precedence as a theory propagation. The
-- precedence @p ≺ i@ is an energetic consequence of the responsible subset's
-- bounds, so its reason cites those tasks' current bound atoms.
assertEmittedPrecedences
  :: forall mode s task t
  .  ( Num t, Measurable t, Bounded t, MonitorMode mode )
  => Theory mode s task t
  -> IntMap ( IntSet, IntSet )
  -> ST s ( Maybe SAT.Conflict )
assertEmittedPrecedences t precsMap = goEntries ( IntMap.toList precsMap )
  where
    goEntries :: [ ( Int, ( IntSet, IntSet ) ) ] -> ST s ( Maybe SAT.Conflict )
    goEntries [] = pure Nothing
    goEntries ( ( i, ( preds, succs ) ) : rest ) = do
      let predList = IntSet.toList preds
          succList = IntSet.toList succs
          -- @p ≺ i@ for each predecessor, justified by the co-detected
          -- predecessors and @i@; dually @i ≺ s@ for each successor.
          edges = [ ( p, i, i : predList ) | p <- predList ]
               ++ [ ( i, s, i : succList ) | s <- succList ]
      mb <- goEdges edges
      case mb of
        Just c  -> pure ( Just c )
        Nothing -> goEntries rest

    goEdges :: [ ( Int, Int, [ Int ] ) ] -> ST s ( Maybe SAT.Conflict )
    goEdges [] = pure Nothing
    goEdges ( ( a, b, why ) : rest ) = do
      mb <- assertOnePrecedence t a b why
      case mb of
        Just c  -> pure ( Just c )
        Nothing -> goEdges rest

-- | Assert @a ≺ b@ with a reason built from the bound atoms of @reasonTasks@.
assertOnePrecedence
  :: forall mode s task t
  .  ( Num t, Measurable t, Bounded t, MonitorMode mode )
  => Theory mode s task t
  -> Int -> Int
  -> [ Int ]   -- ^ tasks whose bounds justify the precedence
  -> ST s ( Maybe SAT.Conflict )
assertOnePrecedence t a b reasonTasks = do
  ok <- SAT.isOk ( solver t )
  if not ok then pure Nothing
  else do
#ifdef DEBUG
    let !d = numTasks ( atoms t )
    when ( a < 0 || a >= d || b < 0 || b >= d ) $
      error $ "Schedule.LCG.Theory.assertOnePrecedence: pair=("
           <> show a <> "," <> show b <> ") out of range; dim=" <> show d
    when ( a == b ) $
      error "Schedule.LCG.Theory.assertOnePrecedence: self-precedence"
#endif
    let lit = precLit ( atoms t ) a b
    reason <- boundReasonOrSnapshot t lit reasonTasks []
    assertBatch t lit reason

-------------------------------------------------------------------------------
-- (2b) Channel est/lct tightenings out as bound literals.

-- | For each task whose earliest start \/ latest completion moved this pass,
-- assert the matching bound literal with a local clausal reason. Tasks whose
-- domain emptied are skipped (handled by the infeasibility conflict).
channelOutBounds
  :: forall mode s task t
  .  ( Num t, Measurable t, Bounded t, MonitorMode mode )
  => Theory mode s task t
  -> IntMap ( Bool, Bool )       -- ^ per task, @(est moved, lct moved)@
  -> IntMap ( IntSet, IntSet )   -- ^ per task, responsible subset @(est side, lct side)@
  -> ST s ( Maybe SAT.Conflict )
channelOutBounds t deltas brs = goTasks ( IntMap.toList deltas )
  where
    goTasks :: [ ( Int, ( Bool, Bool ) ) ] -> ST s ( Maybe SAT.Conflict )
    goTasks [] = pure Nothing
    goTasks ( ( i, ( estMoved, lctMoved ) ) : rest ) = do
      ok <- SAT.isOk ( solver t )
      if not ok then pure Nothing
      else do
        task <- readTask t i
        if null ( intervals ( taskAvailability task ) )
        then goTasks rest  -- empty domain: surfaced by the infeasibility conflict
        else do
          let ( estWhy, lctWhy ) = maybe ( IntSet.empty, IntSet.empty )
                                         id ( IntMap.lookup i brs )
          mb1 <- if estMoved then assertEstBound t i estWhy else pure Nothing
          case mb1 of
            Just c  -> pure ( Just c )
            Nothing -> do
              mb2 <- if lctMoved then assertLctBound t i lctWhy else pure Nothing
              case mb2 of
                Just c  -> pure ( Just c )
                Nothing -> goTasks rest

-- | Assert task @i@'s lower bound @start_i ≥ est_i@ (the negative bound atom),
-- reasoned from the responsible subset.
assertEstBound
  :: forall mode s task t
  .  ( Num t, Measurable t, Bounded t, MonitorMode mode )
  => Theory mode s task t -> Int -> IntSet -> ST s ( Maybe SAT.Conflict )
assertEstBound t i why = do
  lit    <- currentEstLit t i
  reason <- boundPropReason t lit i ( IntSet.toList why )
  assertBatch t lit reason

-- | Assert task @i@'s upper bound @start_i ≤ lst_i@ (the positive bound atom),
-- reasoned from the responsible subset.
assertLctBound
  :: forall mode s task t
  .  ( Num t, Measurable t, Bounded t, MonitorMode mode )
  => Theory mode s task t -> Int -> IntSet -> ST s ( Maybe SAT.Conflict )
assertLctBound t i why = do
  lit    <- currentLctLit t i
  reason <- boundPropReason t lit i ( IntSet.toList why )
  assertBatch t lit reason

-- | The local clausal reason for a bound tightening on task @i@: the
-- responsible subset's current bound atoms, plus any precedence literals
-- between @i@ and the subset that the matrix currently holds (which makes the
-- precedence-matrix inferences sound and is a harmless, true antecedent for
-- the energetic ones).
boundPropReason
  :: forall mode s task t
  .  ( Num t, Measurable t, Bounded t )
  => Theory mode s task t
  -> Lit       -- ^ the propagated bound literal
  -> Int       -- ^ the constrained task
  -> [ Int ]   -- ^ the responsible subset
  -> ST s ( LazyReason s )
boundPropReason t propLit i subset = do
  precLits <- catMaybes <$> traverse ( precEdgeLit t i ) subset
  boundReasonOrSnapshot t propLit subset precLits

-- | Build a local clausal reason for a theory propagation: cite the
-- @subset@'s current bound atoms together with @extra@ (already-true
-- literals, e.g. precedence edges). Falls back to a coarse snapshot reason
-- when any subset bound atom is /not/ currently asserted — which happens when
-- a task's actual @est@\/@lct@ landed on an interior hole or was channelled in
-- from a learnt clause, so its exact bound is not a reified, on-trail atom.
-- Citing an unasserted literal would be unsound (and would crash 1-UIP), so we
-- take the always-valid full snapshot instead.
boundReasonOrSnapshot
  :: forall mode s task t
  .  ( Num t, Measurable t, Bounded t )
  => Theory mode s task t
  -> Lit       -- ^ the propagated literal
  -> [ Int ]   -- ^ subset whose bound atoms are cited
  -> [ Lit ]   -- ^ extra antecedents already known true (e.g. precedence edges)
  -> ST s ( LazyReason s )
boundReasonOrSnapshot t propLit subset extra = do
  mbBounds <- checkedBoundLits t subset
  case mbBounds of
    Nothing     -> snapshotReason t propLit
    Just bounds -> pure ( LazyReason ( pure ( propLit : map negateLit ( bounds ++ extra ) ) ) )

-- | The precedence literal between @i@ and @p@ that the matrix currently
-- holds (true on the trail), or 'Nothing' if they are unordered.
precEdgeLit
  :: forall mode s task t
  .  Theory mode s task t -> Int -> Int -> ST s ( Maybe Lit )
precEdgeLit t i p = do
  o <- readOrdering ( orderings ( tasks t ) ) p i
  pure $ case o of
    LessThan    -> Just ( precLit ( atoms t ) p i )  -- p ≺ i
    GreaterThan -> Just ( precLit ( atoms t ) i p )  -- i ≺ p
    _           -> Nothing

-------------------------------------------------------------------------------
-- Bound-atom literals.

-- | Read a task's current availability record.
readTask :: Theory mode s task t -> Int -> ST s ( Task task t )
readTask t i = Boxed.MVector.unsafeRead ( taskAvails ( tasks t ) ) i

-- | The literal asserting task @i@'s current lower bound @start_i ≥ est_i@
-- (the positive literal of its lower-bound atom). Interns the atom if needed.
currentEstLit
  :: ( Measurable t, Bounded t )
  => Theory mode s task t -> Int -> ST s Lit
currentEstLit t i = do
  task <- readTask t i
  fst <$> internLowerBound ( boundAtoms t ) ( SAT.newAuxVar ( solver t ) ) i ( est task )

-- | The literal asserting task @i@'s current upper bound @start_i ≤ lst_i@
-- (the positive literal of its upper-bound atom). Interns the atom if needed.
currentLctLit
  :: ( Num t, Measurable t, Bounded t )
  => Theory mode s task t -> Int -> ST s Lit
currentLctLit t i = do
  task <- readTask t i
  fst <$> internUpperBound ( boundAtoms t ) ( SAT.newAuxVar ( solver t ) ) i ( lst task )

-- | The current lower- and upper-bound literals of every task in the list
-- (two per task), but only if every one is currently /true/ on the trail —
-- i.e. each task's actual @est@\/@lct@ is a reified, asserted bound atom.
--
-- Returns 'Nothing' as soon as some task's bound atom is unasserted (an
-- interior-hole or channelled-in bound that was not promoted to an atom), so
-- the caller can fall back to a coarse but always-valid reason rather than
-- cite a literal that is not on the trail.
checkedBoundLits
  :: ( Num t, Measurable t, Bounded t )
  => Theory mode s task t -> [ Int ] -> ST s ( Maybe [ Lit ] )
checkedBoundLits t = go []
  where
    go acc [] = pure ( Just ( reverse acc ) )
    go acc ( i : is ) = do
      e  <- currentEstLit t i
      ev <- SAT.litValue ( solver t ) e
      l  <- currentLctLit t i
      lv <- SAT.litValue ( solver t ) l
      if ev == LTrue && lv == LTrue
      then go ( l : e : acc ) is
      else pure Nothing

-------------------------------------------------------------------------------
-- Theory propagation primitives.

-- | Enqueue a theory-inferred literal known to be currently unassigned,
-- attaching its reason (as a ground fact at the ground level, or a lazy
-- reason otherwise).
enqueuePropagated
  :: forall mode s task t
  .  Theory mode s task t -> Lit -> LazyReason s -> ST s ()
enqueuePropagated t lit reason = do
  lvl <- SAT.currentLevel ( solver t )
  if lvl == SAT.GroundLevel
  then
    -- A ground-level theory propagation is an unconditional fact; 1-UIP never
    -- resolves against ground-level literals, so it needs no reason clause.
    SAT.enqueueUndef ( solver t ) lit RFact
  else do
    -- TODO: the lazy-reason table is never reclaimed on backjump.
    lref <- SAT.recordLazyReason ( solver t ) reason
    SAT.enqueueUndef ( solver t ) lit ( RLazy lref )
  modifyMutVar' ( theoryPropCount t ) ( + 1 )

-- | Try to assert a theory-inferred literal whose reason is /self-contained/
-- (every cited literal is already on the trail), forcing the reason into a
-- conflict if the literal is already false. Used for transitive-closure
-- derived edges.
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
    LUndef -> enqueuePropagated t lit reason *> pure Nothing
    LFalse -> forceLazyReason reason >>= literalsAsConflict ( solver t )

-- | Like 'assertTheoryLit', but for the end-of-pass batch (bound tightenings
-- and detected precedences) whose lazy reasons may cite literals asserted
-- /later/ in the same batch. Those reasons are sound once forced during 1-UIP
-- (the whole batch is then on the trail), but an /immediate/ conflict here
-- could force a reason prematurely, so the rare immediate case falls back to
-- the coarse precedence snapshot.
assertBatch
  :: forall mode s task t
  .  MonitorMode mode
  => Theory mode s task t
  -> Lit
  -> LazyReason s
  -> ST s ( Maybe SAT.Conflict )
assertBatch t lit reason = do
  val <- SAT.litValue ( solver t ) lit
  case val of
    LTrue  -> pure Nothing
    LUndef -> enqueuePropagated t lit reason *> pure Nothing
    LFalse -> snapshotConflict t ( Just lit )

-------------------------------------------------------------------------------
-- Conflict assembly.

-- | Turn a propagator-reported infeasibility into a SAT conflict.
--
-- An overload is explained tightly by the culprit subset's bound atoms (all
-- on the trail after channelling out). An emptied domain or a matrix cycle
-- falls back to the coarse active-precedence snapshot.
buildInfeasibleConflict
  :: forall mode s task t
  .  ( Num t, Measurable t, Bounded t, MonitorMode mode )
  => Theory mode s task t -> Infeasible -> ST s ( Maybe SAT.Conflict )
buildInfeasibleConflict t = \ case
  Overloaded culprit _ -> do
    mbLits <- checkedBoundLits t ( IntSet.toList culprit )
    case mbLits of
      Just lits -> do
        tickTheoryConflict ( monitor t )
        recordReasonLen ( monitor t ) ( length lits )
        literalsAsConflict ( solver t ) ( map negateLit lits )
      -- A culprit's actual bound is not a reified, on-trail atom: fall back.
      Nothing   -> snapshotConflict t Nothing
  EmptyDomain   _ _ -> snapshotConflict t Nothing
  CycleDetected _ _ -> snapshotConflict t Nothing

-------------------------------------------------------------------------------
-- Coarse snapshot reasons (fallback for cycles, emptied domains, rare
-- immediate batch conflicts, and tight reasons whose bounds are not reified).
--
-- A coarse reason is the negation of every atom — precedence /and/ bound —
-- true above the ground level. It is sound because the scheduling derivations
-- are monotone in the set of true atoms (they read present edges / tightened
-- domains, never the absence of one), so the whole current assignment is a
-- valid superset antecedent. Bound atoms must be included: once a bound can be
-- channelled in from a learnt clause, the domains are no longer a pure function
-- of the precedence atoms, so a precedence-only snapshot would be unsound. The
-- snapshot is blunt; tight per-inference reasons are emitted directly above.

-- | Walk @trail[0, bound)@ and collect the negation of every literal at a
-- decision level strictly above ground, optionally appending @appendLast@
-- (which 1-UIP resolves on after the supporting literals).
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
          lit <- SAT.trailAt ( solver t ) ( SAT.TrailPos i )
          lvl <- SAT.levelOfAssignedVar ( solver t ) ( litVar lit )
          if lvl <= SAT.GroundLevel
          then loop ( i + 1 ) acc
          else loop ( i + 1 ) ( negateLit lit : acc )

-- | Build a 'LazyReason' that, when forced, returns the snapshot of the trail
-- as it stood at the moment of this call (appending @propLit@, on which 1-UIP
-- resolves). The trail prefix is stable until a backjump crosses it, which
-- cannot happen before 1-UIP forces the reason, so the deferred walk is sound.
snapshotReason
  :: forall mode s task t
  .  Theory mode s task t
  -> Lit          -- ^ the propagated literal, appended to the clause body
  -> ST s ( LazyReason s )
snapshotReason t propLit = do
  bound <- SAT.trailSize ( solver t )
  pure ( LazyReason ( snapshotBody t bound ( Just propLit ) ) )

{-# INLINABLE snapshotConflict #-}
{-# SPECIALISE snapshotConflict @MonitoringOff #-}

-- | Capture a snapshot of the active trail (optionally appending @propLit@)
-- and materialise it eagerly as a 'SAT.Conflict'.
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
  [ x ]    -> pure ( Just ( SAT.ConflictBinary x x ) )
  [ a, b ] -> pure ( Just ( SAT.ConflictBinary a b ) )
  longer   -> Just . SAT.ConflictClause <$> SAT.recordTheoryClause s longer
