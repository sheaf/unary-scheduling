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
-- Two families of SAT atoms (with structure lazily enforced by the theory):
--
--   * /Precedence atoms/ @p(i ≺ j)@, one per unordered task pair. These are the
--     primary decision variables. Antisymmetry is free (literal negation);
--     transitivity is enforced by transitive-closure derivations when an edge is
--     channelled into the ordering matrix.
--
--   * /Bound atoms/ @[start_i ≤ k]@ on a single latest-start axis (see
--     "Schedule.LCG.Atoms"), lazily reified and used in two complementary ways:
--
--       (1) /Learning + pruning./ Each propagator bound tightening is channelled
--           /out/ to the matching bound atom with a tight, local clausal reason.
--
--       (2) /Day-assignment decisions./ For each task whose availability has
--           interior gaps (a multi-day song that cannot straddle a day boundary),
--           a /decision/ bound atom is seeded at every gap boundary. Allows
--           for some meaningful structural branching.
--
--     Binary monotonicity lemmata (@[start ≤ a] ⟹ [start ≤ b]@ for @a ≤ b@)
--     keep a task's bound atoms mutually consistent, so a decided or
--     channelled-in bound propagates along the axis.
module Schedule.LCG.Theory
  ( -- * Theory state
    Theory(..)
  , newTheory
    -- * SAT-decision-level synchronisation
  , pushLevel
  , popToLevel
    -- * One round of theory propagation
  , theoryPropagate
    -- * Structural decision heuristic
  , theoryDecide
    -- * Conflict-ordering search
  , noteDecision
  , recordConflict
    -- * Inspection
  , numPrecedenceDecisions
#ifdef DEBUG
    -- * Debug audits
  , debugAuditPropagationFixpoint
#endif
  )
  where

-- base
import Control.Monad
  ( foldM, replicateM_, when )
import Control.Monad.ST
  ( ST )
import Data.Bits
  ( shiftR )
import Data.Coerce
  ( coerce )
import Data.Foldable
  ( for_, toList )
import Data.Maybe
  ( catMaybes, isJust )
import Data.Traversable
  ( for )

-- containers
import Data.IntMap.Strict
  ( IntMap )
import qualified Data.IntMap.Strict as IntMap
  ( toList, lookup, insert
#ifdef DEBUG
  , keysSet, filter
#endif
  )
import Data.IntSet
  ( IntSet )
import qualified Data.IntSet as IntSet
  ( empty, fromList, insert, singleton, toList, null, member )

-- acts
import Data.Act
  ( Torsor((-->)) )

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

-- text
import Data.Text
  ( Text )

-- vector
import qualified Data.Vector as Boxed.Vector
  ( Vector, length, (!), generateM )
import qualified Data.Vector.Mutable as Boxed.MVector
  ( unsafeRead )
import qualified Data.Vector.Primitive.Mutable as Primitive
  ( MVector )

-- unary-scheduling
import SAT.Base
  ( Var(..), Lit, LBool(..)
  , Polarity(Positive, Negative)
  , negateLit, litVar, varIndex
  )
import SAT.Clause
  ( Reason(..), LazyReason(..), forceLazyReason )
import qualified SAT.Solver as SAT
import Schedule.Constraint
  ( Constraints(..), Infeasible(..)
  , BoundMove(..)
  , constrainToAfter, constrainToBefore
  )
import Schedule.Interval
  ( Endpoint(endpoint), Intervals(..), Interval(..), Measurable(..), end
  , flipClusivity, cutBefore, cutAfter, remove
  , estLowerToStartUpper, startUpperToEstLower
  , latestStartFromCompletion, completionFromLatestStart
  )
import Schedule.LCG.Atoms
  ( PrecedenceAtoms, mkPrecedenceAtoms, precLit
  , isPrecedenceVar, numTasks
  , BoundAtoms, newBoundAtoms, internStartUpper
  , boundNeighbours
  , AtomMeaning(..), litMeaning
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
  ( Propagator, propagationLoop, seedAllOf, seedMatrixWatchers )
import Schedule.Task
  ( MutableTaskInfos, TaskInfos(..), Task(..)
  , est, ect, lst, lct )
import Schedule.Time
  ( EarliestTime, LatestTime, Delta, HandedTime(handedTime) )
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
  , -- | Each task's /ground/ (initial instance) availability, snapshot before
    -- any propagation.
    --
    -- Never mutated.
    groundAvail    :: !( Boxed.Vector.Vector ( Intervals t ) )
  , -- | The schedule trail for in-place undo.
    schedTrail     :: !( Trail s task t )
  , -- | Scheduling propagators run on each theory round.
    propagators    :: ![ Propagator task t ]
  , -- | Maximum propagator-round iterations per theory step.
    maxPropRounds  :: !Int
  , -- | Whether to channel propagator bound tightenings /out/ to bound atoms with
    -- tight local reasons (and to reason overloads\/emptied domains from them).
    -- 'False' gives a coarse-reason baseline (for A\/B comparison): no initial
    -- bounds are seeded and no bounds are channelled out, so 'checkedBoundLits'
    -- always misses and every reason is the coarse trail snapshot.
    useBoundAtoms  :: !Bool
  , -- | Whether to branch on day-assignment by seeding a /decision/ bound atom
    -- at each task's internal availability-gap boundaries (see 'seedDecisionBounds').
    -- 'False' gives a precedence-only baseline (for A\/B comparison).
    useBoundDecisions :: !Bool
  , -- | Whether 'theoryDecide' proposes structural day-assignment decisions
    -- ahead of VSIDS. Only meaningful together with 'useBoundDecisions'.
    useTheoryDecide :: !Bool
  , -- | Whether 'theoryDecide' applies /conflict-ordering search/ ahead of its
    -- structural choice: revisit the decision variable most recently found
    -- to be a conflict culprit before resuming the base order.
    useConflictOrdering :: !Bool
  , -- | Monotone conflict counter ticked by 'recordConflict'; supplies the
    -- recency stamp for conflict-ordering.
    conflictClock :: !( MutVar s Int )
  , -- | Per decision variable (by 'varIndex'), the 'conflictClock' value at which
    -- it was last a conflict culprit. Higher = more recent. Entries persist
    -- across restarts (recency is global); 'conflictOrderingPick' skips those
    -- whose variable is currently assigned.
    conflictStamps :: !( MutVar s ( IntMap Int ) )
  , -- | The variable of the most recent branching decision (its culprit on the
    -- next conflict, by last-conflict reasoning).
    lastDecision :: !( MutVar s ( Maybe Var ) )
  , -- | Per gappy task, its day-assignment decision atoms in ascending threshold
    -- order (the positive literal @start ≤ boundary@), as seeded by
    -- 'seedDecisionBounds'. Read by 'theoryDecide' for first-fail day branching;
    -- written once at construction and never mutated thereafter.
    decisionBounds :: !( MutVar s ( IntMap [ Lit ] ) )
  , -- | Next SAT trail position to channel into the scheduler.
    --
    -- @[0, theoryHead)@ have already been processed; @[theoryHead, trailSize)@
    -- still need to be channeled.
    theoryHead     :: !( MutVar s SAT.TrailPos )
  , -- | Per SAT decision level, the schedule-trail mark in effect at the
    -- start of that level. Indexed by the level minus one (level @k + 1@
    -- starts at @levelMarks[k]@).
    levelMarks     :: !( Growable Primitive.MVector s Int )
  , -- | Tasks touched by a precedence edge channelled into the matrix since
    -- the last 'runPropagators'. The next round wakes only the matrix-watching
    -- propagators on these (the broadcast then wakes the rest); cheap, and the
    -- baseline propagation behaviour.
    --
    -- 'Nothing' marks the very first call: every propagator subscription is
    -- seeded with the full task set ('seedAllOf').
    dirtySeed      :: !( MutVar s ( Maybe IntSet ) )
  , -- | Tasks whose /domain/ a channelled-in bound literal actually tightened
    -- since the last 'runPropagators'. These wake /all/ propagators (a domain
    -- change can feed any of them), unlike the matrix-only 'dirtySeed'.
    boundDirty     :: !( MutVar s IntSet )
  , -- | Tasks /carved/ (an @Inside@\/@Outside@ tightening applied), accumulated
    -- across the whole search. A bound that jumps over a gap on a carved task is
    -- not soundly explained by the energetic antecedents (the gap is not ground),
    -- so such a bound literal gets a coarse reason. Monotone: never reset, so it
    -- stays sound after backjumps (only ever more conservative).
    carved         :: !( MutVar s IntSet )
  , -- | Cumulative count of theory propagations: literals the theory has
    -- promoted onto the SAT trail (derived transitive edges, propagator
    -- precedences, and channelled-out bound tightenings). For instrumentation.
    theoryPropCount :: !( MutVar s Int )
  , -- | Optional instrumentation. Erased entirely when @mode ~ 'MonitoringOff'@.
    monitor         :: !( Monitor mode s )
  }

{-# SPECIALISE newTheory @MonitoringOff #-}

-- | Allocate a fresh 'Theory' for the given scheduler state and propagators.
newTheory
  :: forall mode s task t
  .  ( Num t, Measurable t, Bounded t
     , MonitorMode mode
     )
  => MutableTaskInfos s task t
  -> [ Propagator task t ]
  -> Int                          -- ^ propagator-round cap per theory step
  -> Bool                         -- ^ channel out tight bound reasons (learning)?
  -> Bool                         -- ^ branch on day-assignment bound atoms?
  -> Bool                         -- ^ use the structural day-assignment decision heuristic?
  -> Bool                         -- ^ use conflict-ordering search in 'theoryDecide'?
  -> ST s ( Theory mode s task t )
newTheory tis props rounds boundAtomsOn boundDecisionsOn theoryDecideOn conflictOrderingOn = do
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
  bd    <- newMutVar IntSet.empty
  cv    <- newMutVar IntSet.empty
  tpc   <- newMutVar 0
  db    <- newMutVar mempty
  cclk  <- newMutVar 0
  cstmp <- newMutVar mempty
  ldec  <- newMutVar Nothing
  -- Snapshot ground availabilities now, before any propagation mutates them.
  gav   <- Boxed.Vector.generateM nT \ i ->
             taskAvailability <$> Boxed.MVector.unsafeRead ( taskAvails tis ) i
  mon   <- newMonitor @mode
  let t = Theory
        { solver          = s
        , atoms           = ps
        , boundAtoms      = ba
        , tasks           = tis
        , groundAvail     = gav
        , schedTrail      = trail
        , propagators     = props
        , maxPropRounds   = rounds
        , useBoundAtoms   = boundAtomsOn
        , useBoundDecisions = boundDecisionsOn
        , useTheoryDecide = theoryDecideOn
        , useConflictOrdering = conflictOrderingOn
        , conflictClock   = cclk
        , conflictStamps  = cstmp
        , lastDecision    = ldec
        , decisionBounds  = db
        , theoryHead      = th
        , levelMarks      = lms
        , dirtySeed       = ds
        , boundDirty      = bd
        , carved          = cv
        , theoryPropCount = tpc
        , monitor         = mon
        }
  when boundAtomsOn      ( seedInitialBounds  t nT )
  when boundDecisionsOn  ( seedDecisionBounds t nT )
  pure t

-- | Create initial inner-boundary bound atoms for decision making.
seedDecisionBounds
  :: forall mode s task t
  .  ( Num t, Measurable t, Bounded t )
  => Theory mode s task t -> Int -> ST s ()
seedDecisionBounds t nT =
  for_ [ 0 .. nT - 1 ] \ i -> do
    task <- readTask t i
    let dur        = taskDuration task
        ivals      = toList ( intervals ( taskAvailability task ) )
        -- The gap boundaries are the ends of every sub-interval but the last.
        boundaries = case ivals of { [] -> []; _ -> init ivals }
    -- Intern the decision atom at each gap boundary, in ascending threshold
    -- order, and record the literals so 'theoryDecide' can branch on them.
    lits <- for boundaries \ iv ->
      internDecisionBoundAtom t i ( latestStartFromCompletion dur ( end iv ) )
    when ( not ( null lits ) ) $
      modifyMutVar' ( decisionBounds t ) ( IntMap.insert i lits )

-- | Create initial outer boundary atoms, so that propagators can cite them
-- in tight reasons.
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
-- Structural decision heuristic.

-- | Propose the next branching literal from a CP search strategy, or 'Nothing'
-- to defer to the SAT decision logic.
--
--  1. For gappy tasks, branch on the lowest undecided inner boundary atom of
--     the most constrained task.
--  2. Critical pair sequencing (settle the most resource critical unordered task pair).
--
-- Only when both stages abstain does it return 'Nothing', letting the SAT
-- decision logic kick in.
theoryDecide
  :: forall mode s task t
  .  ( Num t, Measurable t, Bounded t )
  => Theory mode s task t
  -> ST s ( Maybe Lit )
theoryDecide t
  | not ( useTheoryDecide t ) = pure Nothing
  | otherwise = do
      -- Conflict-ordering first: revisit the most recent unsettled culprit.
      mbCos <- if useConflictOrdering t then conflictOrderingPick t else pure Nothing
      case mbCos of
        Just lit -> pure ( Just lit )
        Nothing  -> do
          -- Base order: day-assignment first-fail, then critical-pair sequencing.
          dbs  <- readMutVar ( decisionBounds t )
          best <- foldM considerTask Nothing ( IntMap.toList dbs )
          case best of
            Just ( _, _, lit ) -> pure ( Just lit )
            Nothing            -> criticalPair t
  where
    -- Keep the most-constrained candidate (fewest remaining intervals).
    considerTask
      :: Maybe ( Int, Int, Lit ) -> ( Int, [ Lit ] )
      -> ST s ( Maybe ( Int, Int, Lit ) )
    considerTask acc ( i, lits ) = do
      task <- readTask t i
      let nIvals = length ( intervals ( taskAvailability task ) )
      if nIvals <= 1
      then pure acc   -- already committed to a single interval
      else do
        mbLit <- firstUndecided lits
        pure $ case mbLit of
          Nothing  -> acc   -- no: all decided already
          Just lit -> case acc of
            Just ( bestN, _, _ ) | bestN <= nIvals -> acc
            _                                      -> Just ( nIvals, i, lit )

    -- The lowest-threshold inner-boundary atom not yet assigned.
    firstUndecided :: [ Lit ] -> ST s ( Maybe Lit )
    firstUndecided [] = pure Nothing
    firstUndecided ( l : ls ) = do
      v <- SAT.litValue ( solver t ) l
      case v of
        LUndef -> pure ( Just l )
        _      -> firstUndecided ls

-------------------------------------------------------------------------------
-- Conflict-ordering search (Gay, Hartert & Schaus, CP 2015).

-- | Record the variable just branched on, so the next conflict can blame it.
--
-- No-op unless conflict-ordering is enabled.
noteDecision :: Theory mode s task t -> Lit -> ST s ()
noteDecision t lit =
  when ( useConflictOrdering t ) $
    writeMutVar ( lastDecision t ) ( Just ( litVar lit ) )

-- | Record that a conflict just occurred: stamp the most recent decision
-- variable (the conflict's culprit, by last-conflict reasoning) with a fresh
-- 'conflictClock' tick, so 'conflictOrderingPick' will revisit it first once it
-- is unassigned again.
--
-- No-op unless conflict-ordering is enabled.
recordConflict :: Theory mode s task t -> ST s ()
recordConflict t =
  when ( useConflictOrdering t ) $ do
    mbV <- readMutVar ( lastDecision t )
    case mbV of
      Nothing -> pure ()
      Just v  -> do
        clk <- readMutVar ( conflictClock t )
        let !clk' = clk + 1
        writeMutVar ( conflictClock t ) clk'
        modifyMutVar' ( conflictStamps t ) ( IntMap.insert ( varIndex v ) clk' )

-- | The most-recently-stamped currently unassigned decision variable.
conflictOrderingPick
  :: forall mode s task t. Theory mode s task t -> ST s ( Maybe Lit )
conflictOrderingPick t = do
  stamps <- readMutVar ( conflictStamps t )
  fmap snd <$> foldM step Nothing ( IntMap.toList stamps )
  where
    -- Track the @(clock, literal)@ of the best unassigned culprit so far. Only
    -- probe a variable's assignment (via 'decideVar') when its stamp could beat
    -- the incumbent.
    step :: Maybe ( Int, Lit ) -> ( Int, Int ) -> ST s ( Maybe ( Int, Lit ) )
    step best ( vi, clk ) =
      case best of
        Just ( bclk, _ ) | clk <= bclk -> pure best
        _ -> do
          mbLit <- SAT.decideVar ( solver t ) ( Var vi )
          pure $ case mbLit of
            Just lit -> Just ( clk, lit )
            Nothing  -> best

-- | Settle the most resource-critical unordered task pair.
--
-- The most /contended/ disjunction is the pair minimising the larger of the two
-- slacks (even its looser ordering is tight). branch its larger-slack direction
-- first (textbook disjunctive-scheduling order).
--
-- (Clusivity is ignored in the slack — it shifts a bound by at most one unit,
-- which is immaterial to a branching /heuristic/.)
--
-- Returns 'Nothing' when every pair is ordered (the precedence tournament
-- is complete).
criticalPair
  :: forall mode s task t
  .  ( Num t, Measurable t, Bounded t )
  => Theory mode s task t
  -> ST s ( Maybe Lit )
criticalPair t = do
  best <- go 0 1 Nothing
  pure ( fmap snd best )
  where
    ps  = atoms t
    n   = numTasks ps
    mat = orderings ( tasks t )

    -- Scan the upper-triangular pairs, keeping the minimum-criticality candidate.
    go :: Int -> Int -> Maybe ( Delta t, Lit ) -> ST s ( Maybe ( Delta t, Lit ) )
    go i j best
      | i >= n - 1 = pure best
      | j >= n     = go ( i + 1 ) ( i + 2 ) best
      | otherwise  = do
          o <- readOrdering mat i j
          case o of
            Unknown -> do
              v <- SAT.litValue ( solver t ) ( precLit ps i j )
              case v of
                -- 'Unknown' in the matrix should mean the precedence atom is
                -- unassigned; the check guards against deciding an assigned one.
                LUndef -> do
                  cand <- evalPair i j
                  go i ( j + 1 ) ( keepMin best cand )
                _ -> go i ( j + 1 ) best
            _ -> go i ( j + 1 ) best

    keepMin :: Maybe ( Delta t, Lit ) -> ( Delta t, Lit ) -> Maybe ( Delta t, Lit )
    keepMin Nothing               cand            = Just cand
    keepMin acc@( Just ( b, _ ) ) cand@( c, _ )
      | c < b     = Just cand
      | otherwise = acc

    -- The criticality (smaller = more contended) and chosen directed literal.
    evalPair :: Int -> Int -> ST s ( Delta t, Lit )
    evalPair i j = do
      ti <- readTask t i
      tj <- readTask t j
      let ectI = handedTime ( endpoint ( ect ti ) )
          lstI = handedTime ( endpoint ( lst ti ) )
          ectJ = handedTime ( endpoint ( ect tj ) )
          lstJ = handedTime ( endpoint ( lst tj ) )
          slackIJ = ectI --> lstJ   -- room if i precedes j
          slackJI = ectJ --> lstI   -- room if j precedes i
          crit    = max slackIJ slackJI
          lit | slackIJ >= slackJI = precLit ps i j   -- larger-slack direction first
              | otherwise          = precLit ps j i
      pure ( crit, lit )

-------------------------------------------------------------------------------
-- One round of theory propagation.

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
  channelOutcome <- withPhaseTiming ( monitor t ) "channel-in" ( channelPending t )
  case channelOutcome of
    Just c  -> pure ( Just c )
    Nothing -> runPropagators t

-------------------------------------------------------------------------------
-- (1) Channel SAT trail literals into the scheduler.

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
      snapshotConflict t "cycle" Nothing
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

-- | Channel a single SAT latest-start bound assignment into the task's domain.
--
-- The atom asserts @start ≤ l@. A 'Positive' literal lowers the latest
-- completion (to the duration-shifted equivalent of @l@, via
-- 'completionFromLatestStart'); a 'Negative' literal (@start > l@) raises the
-- earliest start past @l@. If the tightening empties the domain — a bound
-- literal the SAT core forced against the domain — surface a conflict.
channelBound
  :: forall mode s task t
  .  ( Num t, Measurable t, Bounded t
     , MonitorMode mode
     )
  => Theory mode s task t
  -> Int -> Endpoint ( LatestTime t ) -> Polarity
  -> ST s ( Maybe SAT.Conflict )
channelBound t task l pol = do
  let tis = tasks t
  before <- readTask t task
  let dur = taskDuration before
  moved <- case pol of
    -- @start ≤ l@ ⟹ completion ≤ the equivalent completion bound.
    Positive ->
      constrainToBefore ( schedTrail t ) tis task ( completionFromLatestStart dur l )
    -- @start > l@ ⟹ earliest start raised past @l@.
    Negative ->
      constrainToAfter  ( schedTrail t ) tis task ( startUpperToEstLower l )
  after <- readTask t task
  if null ( intervals ( taskAvailability after ) )
  then
    -- A channelled-in (decided) bound that empties the domain. With the
    -- monotonicity clauses, a cross of an existing bound is normally caught as a
    -- native BCP conflict before reaching here; this is the fallback, explained
    -- by the coarse trail snapshot rather than continuing on an empty domain.
    snapshotConflict t "empty-domain-in" Nothing
  else do
    -- Wake every propagator on this task next round, but only if the domain
    -- actually moved: a no-op re-drain must not re-trigger the full sweep.
    when ( isJust moved ) ( markBoundDirty t task )
    pure Nothing

-- | Add a pair of task indices to the precedence-dirty set so the next
-- 'runPropagators' call wakes the matrix-watching propagators on them. While
-- 'dirtySeed' is still 'Nothing' (before the first 'runPropagators' call) we
-- leave it alone: that first call seeds every propagator with the full task
-- set anyway.
markDirtyPair :: Theory mode s task t -> Int -> Int -> ST s ()
markDirtyPair t a b =
  modifyMutVar' ( dirtySeed t ) $ \ case
    Nothing    -> Nothing
    Just dirty -> Just ( IntSet.insert a ( IntSet.insert b dirty ) )

-- | Mark a task whose domain a channelled-in bound tightened, so the next
-- 'runPropagators' wakes /all/ propagators on it.
markBoundDirty :: Theory mode s task t -> Int -> ST s ()
markBoundDirty t i = modifyMutVar' ( boundDirty t ) ( IntSet.insert i )

-- | Outcome of a single channeling step, lifted through 'ExceptT'.
data ChannelOutcome
  = -- | The closure detected a cycle in the matrix.
    LiftedCycle !CycleInfo
  | -- | The 'onNewEdge' callback discovered a contradiction with the
    -- current SAT assignment.
    LiftedConflict !SAT.Conflict

-------------------------------------------------------------------------------
-- (2) Run the unary-scheduling propagators.

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
  -- Pick the seed. On the very first call, wake every subscription with the
  -- full task set. Afterwards: a precedence edge wakes only the matrix-watching
  -- propagators (the broadcast wakes the rest) — the cheap baseline path — but
  -- if a channelled-in bound actually moved a domain, wake /every/ propagator
  -- on the affected tasks too.
  mbDirty <- readMutVar ( dirtySeed t )
  bDirty  <- readMutVar ( boundDirty t )
  let seed = case mbDirty of
        Nothing -> seedAllOf ( propagators t )
                     ( IntSet.fromList [ 0 .. numTasks ( atoms t ) - 1 ] )
        Just precDirty
          | IntSet.null bDirty -> seedMatrixWatchers ( propagators t ) precDirty
          | otherwise          -> seedAllOf ( propagators t ) ( precDirty <> bDirty )
  writeMutVar ( dirtySeed t )  ( Just IntSet.empty )
  writeMutVar ( boundDirty t ) IntSet.empty
  ( eRes, finalUpdates ) <- withPhaseTiming ( monitor t ) "propagators" $
    runSchedule ( tasks t )
      ( propagationLoop ( monitor t ) ( maxPropRounds t ) ( schedTrail t ) ( propagators t ) seed )
  -- TODO: 'propagationLoop' doesn't properly report 'GiveUp', which means we
  -- currently conflate "fixpoint, consistent" with "gave up early".
  let cts = taskConstraints finalUpdates
  -- Accumulate the tasks carved this pass; a later bound that jumps over a
  -- carved gap on such a task gets a coarse reason.
  modifyMutVar' ( carved t ) ( <> carvedTasks finalUpdates )
  carvedSet <- readMutVar ( carved t )
  -- The accumulated 'TaskUpdates' is preserved even when a propagator threw
  -- (the state sits below 'ExceptT'), so we can channel out the precedences and
  -- bound tightenings derived so far before turning the infeasibility into a
  -- conflict.
  mbConf1 <- withPhaseTiming ( monitor t ) "assert-prec" $
    assertEmittedPrecedences t ( precedences cts )
  case mbConf1 of
    Just c  -> pure ( Just c )
    Nothing -> do
      mbConf2 <-
        if useBoundAtoms t
        then withPhaseTiming ( monitor t ) "channel-out" $
               channelOutBounds t ( tightenedBounds finalUpdates ) ( boundReasons cts ) carvedSet
        else pure Nothing
      case mbConf2 of
        Just c  -> pure ( Just c )
        Nothing -> case eRes of
          Right () -> do
#ifdef DEBUG
            checkMatrixTrailInvariant t "runPropagators (end, no conflict)"
#endif
            pure Nothing
          Left infeasible ->
            buildInfeasibleConflict t ( boundReasons cts ) carvedSet infeasible

#ifdef DEBUG
-- | Check that propagators have indeed run to a fixpoint when they claim to.
-- Catches bugs to do with propagators not properly waking.
debugAuditPropagationFixpoint
  :: forall mode s task t
  .  ( Num t, Measurable t, Bounded t, Show t, Show task, MonitorMode mode )
  => Theory mode s task t -> ST s ()
debugAuditPropagationFixpoint t = do
  let allTasks = IntSet.fromList [ 0 .. numTasks ( atoms t ) - 1 ]
  ( eRes, updates ) <- runSchedule ( tasks t )
    ( propagationLoop ( monitor t ) ( maxPropRounds t ) ( schedTrail t )
        ( propagators t ) ( seedAllOf ( propagators t ) allTasks ) )
  let movedTasks =
        IntMap.keysSet $
          IntMap.filter ( \ ( e, l ) -> isJust e || isJust l ) ( tightenedBounds updates )
  case eRes of
    Right () | IntSet.null movedTasks -> pure ()
    _ -> do
      SAT.DecisionLevel lvl <- SAT.currentLevel ( solver t )
      dump                  <- SAT.dumpSolverState ( solver t )
      let finding = case eRes of
            Left inf -> "an entailed conflict was not surfaced: " <> show inf
            Right () -> "a bound tightening was not applied for tasks "
                     <> show ( IntSet.toList movedTasks )
      error $ unlines
        [ "Schedule.LCG.Theory.debugAuditPropagationFixpoint:"
        , "  - Propagation claimed a fixpoint at level " <> show lvl <> ","
        , "    but a fresh full sweep found more work:\n"
        , "      " <> finding
        , dump
        ]
#endif

-- | Unwrap one round of the 'ScheduleMonad' against the theory's mutable
-- state, returning both the success/failure and the accumulated
-- 'TaskUpdates' (which is retained even on a 'Left', as the state monad sits
-- below the error monad).
runSchedule
  :: forall s task t a
  .  Measurable t
  => MutableTaskInfos s task t
  -> ScheduleMonad s task t a
  -> ST s ( Either ( Infeasible t ) a, TaskUpdates t )
runSchedule tis action =
  runStateT ( runExceptT ( runReaderT action tis ) ) mempty

-------------------------------------------------------------------------------
-- (2a) Promote detected precedences to the SAT trail.

-- | Assert each propagator-detected precedence as a theory propagation. The
-- precedence @p ≺ i@ is an energetic consequence of the responsible subset's
-- bounds, so its reason cites those tasks' current bound atoms (falling back to
-- a coarse trail snapshot when those bounds are not reified — see the header).
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

-- | Assert @a ≺ b@ with a reason built from the bound atoms of @reasonTasks@
-- (coarse snapshot fallback when those bounds are not reified on the trail).
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
-- Bound-atom literals.

-- | Read a task's current availability record.
readTask :: Theory mode s task t -> Int -> ST s ( Task task t )
readTask t i = Boxed.MVector.unsafeRead ( taskAvails ( tasks t ) ) i

-- | Get-or-create a latest-start atom via the given variable allocator, wiring
-- its monotonicity links to the task's neighbouring thresholds the first time
-- it is created. Returns whether the atom was freshly created. The allocator
-- chooses the atom's role: an auxiliary (theory-only) variable, or a decision
-- variable for day-assignment branching.
internBoundAtomWith
  :: Measurable t
  => Theory mode s task t -> ST s Var -> Int -> Endpoint ( LatestTime t ) -> ST s ( Lit, Bool )
internBoundAtomWith t allocVar i thr = do
  ( lit, isNew ) <- internStartUpper ( boundAtoms t ) allocVar i thr
  when isNew $ do
    ( mbBelow, mbAbove ) <- boundNeighbours ( boundAtoms t ) i thr
    for_ mbBelow \ belowLit -> imply belowLit lit   -- A_below ⟹ A_thr
    for_ mbAbove \ aboveLit -> imply lit aboveLit   -- A_thr   ⟹ A_above
  pure ( lit, isNew )
  where
    -- The binary monotonicity clause @a ⟹ b@ (i.e. @¬a ∨ b@), attached directly
    -- as a lazily-generated lemma. /Not/ 'SAT.addClause': mid-search, a clause
    -- with a ground-false literal would there collapse to a unit and enqueue an
    -- 'RFact' at the current (non-ground) level, corrupting conflict analysis.
    imply a b = SAT.addBinaryLemma ( solver t ) ( negateLit a ) b

-- | Get-or-create a /decision/ latest-start atom (placed in the VSIDS heap),
-- bumping its activity on first creation so day-assignment is decided ahead of
-- within-day sequencing.
internDecisionBoundAtom
  :: Measurable t
  => Theory mode s task t -> Int -> Endpoint ( LatestTime t ) -> ST s Lit
internDecisionBoundAtom t i thr = do
  ( lit, isNew ) <- internBoundAtomWith t ( SAT.newVar ( solver t ) ) i thr
  when isNew ( SAT.bumpVarActivity ( solver t ) ( litVar lit ) )
  pure lit

-- | The literal asserting task @i@'s current lower bound @start_i ≥ est_i@. On
-- the single latest-start axis this is the /negative/ literal of the atom at
-- threshold @'estLowerToStartUpper' est_i@. Interns the atom (with its
-- monotonicity links) if needed.
currentEstLit
  :: ( Measurable t, Bounded t )
  => Theory mode s task t -> Int -> ST s Lit
currentEstLit t i = do
  task <- readTask t i
  ( lit, _ ) <- internBoundAtomWith t ( SAT.newAuxVar ( solver t ) ) i
                  ( estLowerToStartUpper ( est task ) )
  pure ( negateLit lit )

-- | The literal asserting task @i@'s current upper bound @start_i ≤ lst_i@: the
-- /positive/ literal of the atom at the latest-start threshold. The threshold is
-- taken via 'latestStartFromCompletion' from the latest /completion/ @lct_i@, so
-- it is the canonical /Inclusive/ latest start (\"start ≤ lst, lst attainable\").
-- Using the raw @lst task@ — which inherits the @Exclusive@ clusivity of the
-- completion convention — would collide on a single variable with the
-- @Exclusive@ lower-bound atom of a zero-slack task; the clusivity conversion is
-- exactly what keeps the two distinct on one axis. Interns the atom if needed.
currentLctLit
  :: ( Num t, Measurable t, Bounded t )
  => Theory mode s task t -> Int -> ST s Lit
currentLctLit t i = do
  task <- readTask t i
  fst <$> internBoundAtomWith t ( SAT.newAuxVar ( solver t ) ) i
            ( latestStartFromCompletion ( taskDuration task ) ( lct task ) )

-- | The current lower- and upper-bound literals of every task in the list
-- (two per task), but only if every one is currently /true/ on the trail —
-- i.e. each task's actual @est@\/@lst@ is a reified, asserted bound atom.
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

-- | The precedence literal between @i@ and @p@ that the matrix currently holds
-- (true on the trail), or 'Nothing' if they are unordered.
precEdgeLit
  :: forall mode s task t
  .  Theory mode s task t -> Int -> Int -> ST s ( Maybe Lit )
precEdgeLit t i p = do
  o <- readOrdering ( orderings ( tasks t ) ) p i
  pure $ case o of
    LessThan    -> Just ( precLit ( atoms t ) p i )  -- p ≺ i
    GreaterThan -> Just ( precLit ( atoms t ) i p )  -- i ≺ p
    _           -> Nothing

-- | Build a local clausal reason for a theory propagation: cite the @subset@'s
-- current bound atoms together with @extra@ (already-true literals, e.g.
-- precedence edges). Falls back to a coarse snapshot reason when any subset
-- bound atom is /not/ currently asserted — which happens when a task's actual
-- @est@\/@lst@ landed on an interior hole or was channelled in from a learnt
-- clause, so its exact bound is not a reified, on-trail atom. Citing an
-- unasserted literal would be unsound (and would crash 1-UIP), so we take the
-- always-valid full snapshot instead.
boundReasonOrSnapshot
  :: forall mode s task t
  .  ( Num t, Measurable t, Bounded t, MonitorMode mode )
  => Theory mode s task t
  -> Lit       -- ^ the propagated literal
  -> [ Int ]   -- ^ subset whose bound atoms are cited
  -> [ Lit ]   -- ^ extra antecedents already known true (e.g. precedence edges)
  -> ST s ( LazyReason s )
boundReasonOrSnapshot t propLit subset extra = do
  mbBounds <- checkedBoundLits t subset
  case mbBounds of
    Nothing     -> do
      tickReasonKind ( monitor t ) "snapshot-unreified"
      snapshotReason t propLit
    Just bounds -> do
      tickReasonKind ( monitor t ) "tight"
      pure ( LazyReason ( pure ( propLit : map negateLit ( bounds ++ extra ) ) ) )

-- | The local clausal reason for a bound tightening on task @i@: the
-- responsible subset's current bound atoms, plus any precedence literals
-- between @i@ and the subset that the matrix currently holds (which makes the
-- precedence-matrix inferences sound and is a harmless, true antecedent for
-- the energetic ones).
boundPropReason
  :: forall mode s task t
  .  ( Num t, Measurable t, Bounded t, MonitorMode mode )
  => Theory mode s task t
  -> Lit       -- ^ the propagated bound literal
  -> Int       -- ^ the constrained task
  -> [ Int ]   -- ^ the responsible subset
  -> ST s ( LazyReason s )
boundPropReason t propLit i subset = do
  precLits <- catMaybes <$> traverse ( precEdgeLit t i ) subset
  boundReasonOrSnapshot t propLit subset precLits

-------------------------------------------------------------------------------
-- Channel est/lct tightenings out as bound literals.

-- | For each task whose earliest start \/ latest completion moved this pass,
-- assert the matching bound literal with a local clausal reason. Tasks whose
-- domain emptied are skipped (handled by the infeasibility conflict).
channelOutBounds
  :: forall mode s task t
  .  ( Num t, Measurable t, Bounded t, MonitorMode mode )
  => Theory mode s task t
  -> IntMap ( Maybe BoundMove, Maybe BoundMove )  -- ^ per task, how @(est, lct)@ moved
  -> IntMap ( IntSet, IntSet )        -- ^ per task, responsible subset @(est side, lct side)@
  -> IntSet                           -- ^ carved tasks (jumps on these get coarse reasons)
  -> ST s ( Maybe SAT.Conflict )
channelOutBounds t deltas brs carvedSet = goTasks ( IntMap.toList deltas )
  where
    goTasks :: [ ( Int, ( Maybe BoundMove, Maybe BoundMove ) ) ] -> ST s ( Maybe SAT.Conflict )
    goTasks [] = pure Nothing
    goTasks ( ( i, ( estMv, lctMv ) ) : rest ) = do
      ok <- SAT.isOk ( solver t )
      if not ok then pure Nothing
      else do
        task <- readTask t i
        if null ( intervals ( taskAvailability task ) )
        then goTasks rest  -- empty domain: surfaced by the infeasibility conflict
        else do
          let ( estWhy, lctWhy ) = maybe ( IntSet.empty, IntSet.empty )
                                         id ( IntMap.lookup i brs )
              iCarved = IntSet.member i carvedSet
          mb1 <- assertEstBound t i estMv estWhy iCarved
          case mb1 of
            Just c  -> pure ( Just c )
            Nothing -> do
              mb2 <- assertLctBound t i lctMv lctWhy iCarved
              case mb2 of
                Just c  -> pure ( Just c )
                Nothing -> goTasks rest

-- | Assert task @i@'s lower bound @start_i ≥ est_i@, reasoned from the
-- responsible subset — unless the move jumped over a gap on a carved task,
-- where the energetic antecedents do not soundly explain the jump and a coarse
-- reason is taken instead.
assertEstBound
  :: forall mode s task t
  .  ( Num t, Measurable t, Bounded t, MonitorMode mode )
  => Theory mode s task t -> Int -> Maybe BoundMove -> IntSet -> Bool -> ST s ( Maybe SAT.Conflict )
assertEstBound t i mv why iCarved =
  assertMovedBound t mv iCarved ( currentEstLit t i ) i ( IntSet.toList why )

-- | Assert task @i@'s upper bound @start_i ≤ lst_i@. See 'assertEstBound'.
assertLctBound
  :: forall mode s task t
  .  ( Num t, Measurable t, Bounded t, MonitorMode mode )
  => Theory mode s task t -> Int -> Maybe BoundMove -> IntSet -> Bool -> ST s ( Maybe SAT.Conflict )
assertLctBound t i mv why iCarved =
  assertMovedBound t mv iCarved ( currentLctLit t i ) i ( IntSet.toList why )

-- | Shared driver for 'assertEstBound' \/ 'assertLctBound': skip an unmoved
-- bound; otherwise assert the bound literal with a tight reason, falling back
-- to a coarse snapshot only for a jumped move on a carved task.
assertMovedBound
  :: forall mode s task t
  .  ( Num t, Measurable t, Bounded t, MonitorMode mode )
  => Theory mode s task t
  -> Maybe BoundMove
  -> Bool          -- ^ is the task carved?
  -> ST s Lit      -- ^ how to obtain (and intern) the bound literal
  -> Int           -- ^ the constrained task
  -> [ Int ]       -- ^ the responsible subset
  -> ST s ( Maybe SAT.Conflict )
assertMovedBound t mv iCarved getLit i subset = case mv of
  Nothing          -> pure Nothing
  Just MovedExact  -> do lit <- getLit; reason <- boundPropReason t lit i subset; assertBatch t lit reason
  Just MovedJumped -> do
    lit <- getLit
    -- A jump over an instance gap is ground (sound); a jump on a carved task
    -- may cross a non-ground carved gap, so explain it coarsely.
    reason <-
      if iCarved
      then tickReasonKind ( monitor t ) "snapshot-carved-jump" *> snapshotReason t lit
      else boundPropReason t lit i subset
    assertBatch t lit reason

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
  .  MonitorMode mode
  => Theory mode s task t
  -> Lit
  -> LazyReason s
  -> ST s ( Maybe SAT.Conflict )
assertTheoryLit t lit reason = do
  val <- SAT.litValue ( solver t ) lit
  case val of
    LTrue  -> pure Nothing
    LUndef -> enqueuePropagated t lit reason *> pure Nothing
    LFalse -> do
      -- A derived transitive edge contradicted the assignment; its 3-literal
      -- reason is tight and self-contained.
      body <- forceLazyReason reason
      tickConflict ( monitor t ) "derived-edge" True
      recordReasonLen ( monitor t ) ( length body )
      literalsAsConflict "derived-edge" ( solver t ) body

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
    LFalse -> snapshotConflict t "batch" ( Just lit )

-------------------------------------------------------------------------------
-- Conflict assembly.

-- | Turn a propagator-reported infeasibility into a SAT conflict.
buildInfeasibleConflict
  :: forall mode s task t
  .  ( Num t, Measurable t, Bounded t, MonitorMode mode )
  => Theory mode s task t
  -> IntMap ( IntSet, IntSet )   -- ^ per-task responsible subsets (bound reasons)
  -> IntSet                      -- ^ carved tasks
  -> Infeasible t
  -> ST s ( Maybe SAT.Conflict )
buildInfeasibleConflict t brs carvedSet inf
  | not ( useBoundAtoms t ) = case inf of
      Overloaded    {} -> snapshotConflict t "overload"     Nothing
      EmptyDomain   {} -> snapshotConflict t "empty-domain" Nothing
      CycleDetected {} -> snapshotConflict t "cycle"        Nothing
  | otherwise = case inf of
      Overloaded { culprit } -> do
        mbLits <- checkedBoundLits t ( IntSet.toList culprit )
        case mbLits of
          Just lits -> do
            tickConflict ( monitor t ) "overload" True
            recordReasonLen ( monitor t ) ( length lits )
            literalsAsConflict "overload" ( solver t ) ( map negateLit lits )
          -- A culprit's actual bound is not a reified, on-trail atom: fall back.
          Nothing   -> snapshotConflict t "overload" Nothing
      EmptyDomain { emptiedTask = i, enforcedEarliest = lo, enforcedLatest = hi }
        -- A carved task's emptiness rests on non-ground interior holes (other
        -- tasks' compulsory parts), so its tight reason must additionally cite
        -- the carvers. If the gaps were in the ground instance, the two
        -- crossing atoms suffice.
        | IntSet.member i carvedSet -> carvedEmptyDomainConflict t brs i lo hi
        | otherwise                 -> emptyDomainConflict t brs i lo hi "empty-domain" []
      CycleDetected {} -> snapshotConflict t "cycle" Nothing

-- | Tight conflict for an emptied task @i@: its enforced earliest start @lo@ and
-- latest completion @hi@ leave no slot. Cite @i@'s two crossing bound atoms
-- @[start ≥ lo]@ and @[start ≤ lst]@ (each reasoned from the squeezing
-- predecessors\/successors), together with any @carverLits@: already-true bound
-- atoms of the tasks whose compulsory parts carved @i@'s interior.
emptyDomainConflict
  :: forall mode s task t
  .  ( Num t, Measurable t, Bounded t, MonitorMode mode )
  => Theory mode s task t
  -> IntMap ( IntSet, IntSet )
  -> Int
  -> Endpoint ( EarliestTime t )
  -> Endpoint ( LatestTime t )
  -> Text          -- ^ conflict-source label
  -> [ Lit ]       -- ^ extra carver bound atoms (already true on the trail)
  -> ST s ( Maybe SAT.Conflict )
emptyDomainConflict t brs i lo hi label carverLits = do
  let ( estWhy, lctWhy ) = maybe ( IntSet.empty, IntSet.empty ) id ( IntMap.lookup i brs )
  task <- readTask t i
  let lstThr = latestStartFromCompletion ( taskDuration task ) hi
  ( lowerAtom, _ ) <- internBoundAtomWith t ( SAT.newAuxVar ( solver t ) ) i ( estLowerToStartUpper lo )
  ( upperLit,  _ ) <- internBoundAtomWith t ( SAT.newAuxVar ( solver t ) ) i lstThr
  let lowerLit = negateLit lowerAtom   -- start ≥ lo
  -- Ensure both crossing bound atoms are on the trail (the emptied task was
  -- skipped by channel-out), each with its local reason.
  loReason <- boundPropReason t lowerLit i ( IntSet.toList estWhy )
  mb1 <- assertBatch t lowerLit loReason
  case mb1 of
    Just c  -> pure ( Just c )
    Nothing -> do
      hiReason <- boundPropReason t upperLit i ( IntSet.toList lctWhy )
      mb2 <- assertBatch t upperLit hiReason
      case mb2 of
        Just c  -> pure ( Just c )
        Nothing -> do
          let body = negateLit lowerLit : negateLit upperLit : map negateLit carverLits
          tickConflict ( monitor t ) label True
          recordReasonLen ( monitor t ) ( length body )
          literalsAsConflict label ( solver t ) body

-- | Tight conflict for a /carved/ emptied task @i@. Its emptiness rests on the
-- interior holes carved by other tasks' compulsory parts @[lst_c, ect_c]@, which
-- are /not/ ground (they follow from the carvers' current bounds), so the
-- two-atom reason of 'emptyDomainConflict' alone would be unsound.
--
-- Reconstruct the carvers (tasks with a non-empty current compulsory part) and
-- /verify/, against @i@'s retained ground availability, that restricting to
-- @[lo, hi]@ and removing those compulsory parts leaves no slot long enough for
-- @i@.
--
-- Fall-back: if the residual still admits @i@, meaning that the current carvers
-- do not explain the emptiness (e.g. it arose from carvers whose bounds have since
-- moved, or the cited carver bound is not a reified on-trail atom), fall back
-- to the coarse snapshot (always sound).
carvedEmptyDomainConflict
  :: forall mode s task t
  .  ( Num t, Measurable t, Bounded t, MonitorMode mode )
  => Theory mode s task t
  -> IntMap ( IntSet, IntSet )
  -> Int
  -> Endpoint ( EarliestTime t )
  -> Endpoint ( LatestTime t )
  -> ST s ( Maybe SAT.Conflict )
carvedEmptyDomainConflict t brs i lo hi = do
  task <- readTask t i
  let dur     = taskDuration task
      window0 = cutAfter hi ( cutBefore lo ( groundAvail t Boxed.Vector.! i ) )
  ( residual, usedCarvers ) <- collectCarvers ( numTasks ( atoms t ) - 1 ) window0 []
  -- Verified iff no surviving slot is long enough to hold @i@.
  let fits iv = measure iv >= dur
      verified = not ( any fits ( toList ( intervals residual ) ) )
  if not verified
  then snapshotConflict t "empty-domain (carved)" Nothing
  else do
    mbCarverLits <- checkedBoundLits t usedCarvers
    case mbCarverLits of
      Nothing         -> snapshotConflict t "empty-domain (carved)" Nothing
      Just carverLits -> emptyDomainConflict t brs i lo hi "empty-domain (carved)" carverLits
  where
    -- Walk tasks @c = n .. 0@, removing each non-empty compulsory part from the
    -- residual window and recording the carvers that actually shrank it.
    collectCarvers :: Int -> Intervals t -> [ Int ] -> ST s ( Intervals t, [ Int ] )
    collectCarvers c acc used
      | c < 0     = pure ( acc, used )
      | c == i    = collectCarvers ( c - 1 ) acc used
      | otherwise = do
          taskC <- readTask t c
          let comp = compulsoryPart taskC
          if isEmpty comp
          then collectCarvers ( c - 1 ) acc used
          else
            let acc' = remove acc comp
            in if acc' == acc
               then collectCarvers ( c - 1 ) acc  used        -- did not shrink: skip
               else collectCarvers ( c - 1 ) acc' ( c : used )

    -- A task's compulsory part @[lst, ect]@: the interval it necessarily
    -- occupies under its current bounds (the same construction 'timetable' carves
    -- with). Empty when the task is not yet fixed enough to have one.
    compulsoryPart :: Task task t -> Interval t
    compulsoryPart taskC =
      Interval ( flipClusivity ( coerce ( lst taskC ) ) )
               ( flipClusivity ( coerce ( ect taskC ) ) )

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

{-# SPECIALISE snapshotConflict @MonitoringOff #-}
-- | Capture a snapshot of the active trail (optionally appending @propLit@)
-- and materialise it eagerly as a coarse 'SAT.Conflict', recording its
-- @label@ (the conflict source) for instrumentation.
snapshotConflict
  :: forall mode s task t
  .  MonitorMode mode
  => Theory mode s task t
  -> Text         -- ^ conflict source label
  -> Maybe Lit
  -> ST s ( Maybe SAT.Conflict )
snapshotConflict t label mbPropLit = do
  bound <- SAT.trailSize ( solver t )
  body  <- snapshotBody t bound mbPropLit
  tickConflict ( monitor t ) label False
  recordReasonLen ( monitor t ) ( length body )
  literalsAsConflict label ( solver t ) body

-- | Materialise a list of literals as a SAT 'Conflict' value. The @label@
-- names the theory rule that produced the conflict; it is carried only for the
-- DEBUG-gated soundness check in 'debugAssertCurrentLevelLit'.
literalsAsConflict
  :: Text          -- ^ conflict-source label (for DEBUG diagnostics)
  -> SAT.Solver s
  -> [ Lit ]
  -> ST s ( Maybe SAT.Conflict )
literalsAsConflict _label s body = do
#ifdef DEBUG
  debugAssertCurrentLevelLit _label s body
#endif
  case body of
    []       -> SAT.markFalse s *> pure Nothing
    -- TODO: a unit conflict is encoded as 'ConflictBinary x x' (a fake 2-lit
    -- clause); this only works because 'analyse' dedups via the 'seen' marker.
    [ x ]    -> pure ( Just ( SAT.ConflictBinary x x ) )
    [ a, b ] -> pure ( Just ( SAT.ConflictBinary a b ) )
    longer   -> Just . SAT.ConflictClause <$> SAT.recordTheoryClause s longer

#ifdef DEBUG
-- | Verify a conflict mentions at least one literal at the current decision level.
--
-- An empty body is a genuine ground-level inconsistency (handled by 'markFalse',
-- never passed to 'analyse') and is exempt.
debugAssertCurrentLevelLit
  :: forall s. Text -> SAT.Solver s -> [ Lit ] -> ST s ()
debugAssertCurrentLevelLit _     _ []   = pure ()
debugAssertCurrentLevelLit label s body = do
  cur   <- SAT.currentLevel s
  descs <- traverse ( describe cur ) body
  when ( not ( any fst descs ) ) $
    error $ "Schedule.LCG.Theory.literalsAsConflict: conflict " <> show label
         <> " has no literal at the current level (" <> show cur <> ")\n"
         <> unlines ( map snd descs )
  where
    describe :: SAT.DecisionLevel -> Lit -> ST s ( Bool, String )
    describe cur l = do
      v <- SAT.litValue s l
      case v of
        LUndef -> pure ( False, "    " <> show l <> "  assign=LUndef  lvl=UNASSIGNED" )
        _      -> do
          lvl <- SAT.levelOfAssignedVar s ( litVar l )
          pure ( lvl == cur
               , "    " <> show l <> "  assign=" <> show v <> "  lvl=" <> show lvl )
#endif
