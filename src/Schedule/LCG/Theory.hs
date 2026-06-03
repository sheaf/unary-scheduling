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
  ( empty, toList, lookup, insert, findWithDefault
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
import Data.Lattice
  ( BoundedLattice(top, bottom) )
import Schedule.Constraint
  ( Constraints(..), Infeasible(..)
  , BoundMove(..), Applied(..)
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
  ( Propagator, propagationLoop, seedAllOf, seedMatrixWatchers
  , PassChanneller(..)
  )
import Schedule.Task
  ( MutableTaskInfos, TaskInfos(..), Task(..)
  , est, ect, lst, lct )
import Schedule.Time
  ( EarliestTime, LatestTime, Delta, HandedTime(handedTime)
  , Handedness(Earliest, Latest)
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
  , -- | Whether to branch on day-assignment by seeding a /decision/ bound atom
    -- at each task's internal availability-gap boundaries (see 'seedDecisionBounds').
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
  , -- | Inference-time antecedent snapshot of the propagation pass currently
    -- being applied (see 'capturePass'). Written before each pass is applied and
    -- read when channelling it (or when a pass empties a domain).
    passCapture    :: !( MutVar s ( PassCapture t ) )
  , -- | Conflict produced while channelling a propagation pass to the SAT trail,
    -- if any. Set by 'channelPass', read by 'runPropagators' after the loop.
    pendingConflict :: !( MutVar s ( Maybe SAT.Conflict ) )
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
  -> Bool                         -- ^ branch on day-assignment bound atoms?
  -> Bool                         -- ^ use the structural day-assignment decision heuristic?
  -> Bool                         -- ^ use conflict-ordering search in 'theoryDecide'?
  -> ST s ( Theory mode s task t )
newTheory tis props rounds boundDecisionsOn theoryDecideOn conflictOrderingOn = do
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
  pcap  <- newMutVar emptyPassCapture
  pconf <- newMutVar Nothing
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
        , passCapture     = pcap
        , pendingConflict = pconf
        , theoryPropCount = tpc
        , monitor         = mon
        }
  seedInitialBounds t nT
  when boundDecisionsOn ( seedDecisionBounds t nT )
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
      -- A matrix cycle: the new edge @predTask ≺ succTask@ closes a path
      -- @succTask ≺ … ≺ predTask@ of true precedence literals into a cycle.
      reconstructCycle t predTask succTask
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
  let dur  = taskDuration before
      est0 = est before
      lct0 = lct before
  moved <- case pol of
    -- @start ≤ l@ ⟹ completion ≤ the equivalent completion bound.
    Positive ->
      constrainToBefore ( schedTrail t ) tis task ( completionFromLatestStart dur l )
    -- @start > l@ ⟹ earliest start raised past @l@.
    Negative ->
      constrainToAfter  ( schedTrail t ) tis task ( startUpperToEstLower l )
  after <- readTask t task
  if null ( intervals ( taskAvailability after ) )
  then do
    -- A channelled-in (decided) bound crossed an existing bound, emptying the
    -- domain. With the monotonicity clauses this is normally caught as a native
    -- BCP conflict first; here we build the tight crossing conflict. The
    -- enforced bounds pit the channelled bound against the surviving one
    -- (@est0@\/@lct0@); 'emptyDomainConflict' cites both crossing bound atoms
    -- (each already on the trail) plus any carvers. The current state is the
    -- previous round's fixpoint, captured by 'currentCapture'.
    let ( lo, hi ) = case pol of
          Positive -> ( est0, completionFromLatestStart dur l )
          Negative -> ( startUpperToEstLower l, lct0 )
    cap <- currentCapture t
    emptyDomainConflict t cap task lo hi
  else do
    -- Wake every propagator on this task next round, but only if the domain
    -- actually moved: a no-op re-drain must not re-trigger the full sweep.
    when ( isJust moved ) ( markBoundDirty t task )
    -- Citability invariant: a channel-in /jump/ over a gap leaves the new
    -- canonical @est@\/@lst@ at a threshold whose atom is not the channelled-in
    -- one, so reify and assert it here with a tight reason (the channelled-in
    -- literal, plus carvers for any non-ground gap skipped). An /exact/ move
    -- lands on the channelled-in atom itself.
    case moved of
      Just MovedJumped -> do
        ( channelAtom, _ ) <- internBoundAtomWith t ( SAT.newAuxVar ( solver t ) ) task l
        let channelledLit = case pol of { Positive -> channelAtom; Negative -> negateLit channelAtom }
            side          = case pol of { Positive -> Latest;      Negative -> Earliest }
        assertChannelInJump t side task [ channelledLit ]
      _ -> pure Nothing

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
  writeMutVar ( pendingConflict t ) Nothing
  -- The propagation loop channels each pass's inferences as it applies them,
  -- via 'passChanneller': bound tightenings and precedences reach the SAT trail
  -- with tight reasons built from the pass's inference-time (pre-pass)
  -- antecedents, captured before the pass mutates anything. A channel conflict
  -- is stashed in 'pendingConflict'.
  ( eRes, _finalUpdates ) <- withPhaseTiming ( monitor t ) "propagators" $
    runSchedule ( tasks t )
      ( propagationLoop ( monitor t ) ( maxPropRounds t ) ( schedTrail t )
          ( propagators t ) ( Just ( passChanneller t ) ) seed )
  -- TODO: 'propagationLoop' doesn't properly report 'GiveUp', which means we
  -- currently conflate "fixpoint, consistent" with "gave up early".
  mbChannelConf <- readMutVar ( pendingConflict t )
  case mbChannelConf of
    Just c  -> pure ( Just c )
    Nothing -> case eRes of
      Right () -> do
#ifdef DEBUG
        checkMatrixTrailInvariant t "runPropagators (end, no conflict)"
        debugAssertCitability t "runPropagators (end, no conflict)"
#endif
        pure Nothing
      Left infeasible ->
        -- A propagator emptied a domain (or overloaded the resource). Its
        -- inference-time antecedents were captured by the throwing pass and are
        -- in 'passCapture'.
        buildInfeasibleConflict t infeasible

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
        ( propagators t ) Nothing ( seedAllOf ( propagators t ) allTasks ) )
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
-- bounds, so its reason cites those tasks' pre-pass bound atoms (from @cap@),
-- all already on the trail.
assertEmittedPrecedences
  :: forall mode s task t
  .  ( Num t, Measurable t, Bounded t, MonitorMode mode )
  => Theory mode s task t
  -> PassCapture t
  -> IntMap ( IntSet, IntSet )
  -> ST s ( Maybe SAT.Conflict )
assertEmittedPrecedences t cap precsMap = goEntries ( IntMap.toList precsMap )
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
      mb <- assertOnePrecedence t cap a b why
      case mb of
        Just c  -> pure ( Just c )
        Nothing -> goEdges rest

-- | Assert @a ≺ b@ with a tight reason built from the pre-pass bound atoms of
-- @reasonTasks@ — the energetic antecedents the propagator read to detect the
-- precedence, all already on the trail.
assertOnePrecedence
  :: forall mode s task t
  .  ( Num t, Measurable t, Bounded t, MonitorMode mode )
  => Theory mode s task t
  -> PassCapture t
  -> Int -> Int
  -> [ Int ]   -- ^ tasks whose bounds justify the precedence
  -> ST s ( Maybe SAT.Conflict )
assertOnePrecedence t cap a b reasonTasks = do
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
    bounds <- capSubsetLits t cap reasonTasks
    reason <- boundReasonLits lit bounds
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

-- | The literal asserting the /lower/ bound @start_i ≥ e@ for the given earliest
-- start @e@: the /negative/ literal of the atom at threshold
-- @'estLowerToStartUpper' e@. Interns the atom (with its monotonicity links) if
-- needed. Interning at a value @e@ already on the trail returns the asserted
-- atom.
--
-- See also 'lctLitAt'.
estLitAt
  :: ( Measurable t, Bounded t )
  => Theory mode s task t -> Int -> Endpoint ( EarliestTime t ) -> ST s Lit
estLitAt t i e = do
  ( lit, _ ) <- internBoundAtomWith t ( SAT.newAuxVar ( solver t ) ) i
                  ( estLowerToStartUpper e )
  pure ( negateLit lit )

-- | The literal asserting the /upper/ bound @start_i ≤ lst@ for the given latest
-- completion @l@: the /positive/ literal of the atom at the latest-start
-- threshold.
--
-- See also 'estLitAt'.
lctLitAt
  :: ( Num t, Measurable t, Bounded t )
  => Theory mode s task t -> Int -> Endpoint ( LatestTime t ) -> ST s Lit
lctLitAt t i l = do
  task <- readTask t i
  fst <$> internBoundAtomWith t ( SAT.newAuxVar ( solver t ) ) i
            ( latestStartFromCompletion ( taskDuration task ) l )

-- | The literal asserting task @i@'s /current/ (domain) lower bound
-- @start_i ≥ est_i@.
currentEstLit
  :: ( Num t, Measurable t, Bounded t )
  => Theory mode s task t -> Int -> ST s Lit
currentEstLit t i = readTask t i >>= estLitAt t i . est

-- | The literal asserting task @i@'s /current/ (domain) upper bound
-- @start_i ≤ lst_i@.
currentLctLit
  :: ( Num t, Measurable t, Bounded t )
  => Theory mode s task t -> Int -> ST s Lit
currentLctLit t i = readTask t i >>= lctLitAt t i . lct

-- | The current bound literal of task @i@ on the given side, interning its atom
-- if needed: the lower bound @start ≥ est@ at 'Earliest' handedness, the upper
-- bound @start ≤ lst@ at 'Latest'.
sideLit
  :: ( Num t, Measurable t, Bounded t )
  => Theory mode s task t -> Handedness -> Int -> ST s Lit
sideLit t Earliest i = currentEstLit t i
sideLit t Latest   i = currentLctLit t i

-- | The current lower- and upper-bound literals of every task in the list
-- (two per task: @start ≥ est@ and @start ≤ lst@), interning their atoms.
--
-- /Citability invariant:/ each is already asserted true on the trail. A
-- propagator only ever reads a task's current @est@\/@lst@ to make an
-- inference, and every bound that is set — by 'seedInitialBounds', by
-- 'channelBound' (channel-in), or by 'channelOutBounds' (channel-out) — reifies
-- and asserts its atom at the new threshold, jumps included. So citing these is
-- sound, and the lazy reason capturing them resolves against on-trail literals
-- when 1-UIP forces it.
boundLits
  :: ( Num t, Measurable t, Bounded t )
  => Theory mode s task t -> [ Int ] -> ST s [ Lit ]
boundLits t = fmap concat . traverse one
  where
    one i = do
      e <- currentEstLit t i
      l <- currentLctLit t i
      pure [ e, l ]

-- | Assemble a tight lazy reason for a theory propagation: the @propLit@,
-- resolved against the negations of its @antecedents@ (all currently true on
-- the trail). The closure captures the literals directly (interned atoms are
-- stable), so forcing it during 1-UIP yields the supporting clause.
boundReasonLits
  :: Lit -> [ Lit ] -> ST s ( LazyReason s )
boundReasonLits propLit antecedents = do
  pure ( LazyReason ( pure ( propLit : map negateLit antecedents ) ) )

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

-------------------------------------------------------------------------------
-- Compulsory parts and carver reconstruction.

-- | A task's compulsory part @[lst, ect]@: the interval it necessarily occupies
-- under its current bounds (the construction 'timetable' carves with). Empty
-- when the task is not yet fixed enough to have one.
compulsoryPart :: ( Num t, Measurable t, Bounded t ) => Task task t -> Interval t
compulsoryPart taskC =
  Interval ( flipClusivity ( coerce ( lst taskC ) ) )
           ( flipClusivity ( coerce ( ect taskC ) ) )

-- | The window of @i@'s /ground/ availability that a bound jump on @side@
-- skipped, given the new (post-jump) bound: the span strictly below the new
-- earliest start ('Earliest'), or strictly above the new latest start
-- ('Latest'). The carvers covering this span explain the jump.
jumpWindow
  :: ( Num t, Measurable t, Bounded t )
  => Theory mode s task t -> Handedness -> Int
  -> Endpoint ( EarliestTime t )   -- ^ new earliest start (for 'Earliest')
  -> Endpoint ( LatestTime t )     -- ^ new latest start  (for 'Latest')
  -> Intervals t
jumpWindow t side i newEst newLst =
  case side of
    Earliest -> cutAfter  ( estLowerToStartUpper newEst ) ground
    Latest   -> cutBefore ( startUpperToEstLower newLst ) ground
  where
    ground = groundAvail t Boxed.Vector.! i

-- | Walk every task @c ≠ i@, removing its (non-empty) compulsory part — looked
-- up via @compOf@ — from the given window of @i@'s /ground/ availability; return
-- the residual together with the carvers whose compulsory part actually shrank
-- it.
--
-- Ground gaps and prune-removed short slots are absent from the residual to
-- begin with, so they contribute no carver — they are ground facts (the
-- instance availability and @i@'s own duration). Only @timetable@ carvings
-- attribute to a (cited) carver, which is exactly the non-ground removals.
collectCarversWith
  :: ( Num t, Measurable t, Bounded t )
  => ( Int -> ST s ( Interval t ) )   -- ^ compulsory part of a task
  -> Int                              -- ^ number of tasks
  -> Int                              -- ^ the carved task @i@ (excluded)
  -> Intervals t                      -- ^ window of @i@'s ground availability
  -> ST s ( Intervals t, [ Int ] )
collectCarversWith compOf n i window0 = go ( n - 1 ) window0 []
  where
    go c acc used
      | c < 0     = pure ( acc, used )
      | c == i    = go ( c - 1 ) acc used
      | otherwise = do
          comp <- compOf c
          if isEmpty comp
          then go ( c - 1 ) acc used
          else
            let acc' = remove acc comp
            in if acc' == acc
               then go ( c - 1 ) acc  used          -- did not shrink: skip
               else go ( c - 1 ) acc' ( c : used )

-- | Carver bound literals (current state) justifying that the bound on @side@
-- /jumped/ to @i@'s current bound: the tasks whose /current/ compulsory parts
-- removed @i@'s ground availability across the skipped span. Used by the
-- channel-in path, where the current domain is the previous round's fixpoint and
-- every cited bound is already on the trail.
jumpCarverLits
  :: ( Num t, Measurable t, Bounded t )
  => Theory mode s task t -> Handedness -> Int -> ST s [ Lit ]
jumpCarverLits t side i = do
  task <- readTask t i
  let window = jumpWindow t side i ( est task )
                 ( latestStartFromCompletion ( taskDuration task ) ( lct task ) )
  ( _residual, carvers ) <-
    collectCarversWith ( fmap compulsoryPart . readTask t ) ( numTasks ( atoms t ) ) i window
  boundLits t carvers

-- | Reify and assert task @i@'s current bound on @side@ after a /channel-in/
-- jump, with a tight reason: the @base@ antecedents (the channelled-in literal)
-- plus the carvers of the skipped span.
--
-- Only jumps need this: an /exact/ channel-in move lands the canonical
-- @est@\/@lst@ atom on the channelled-in atom itself (the registry canonicalises
-- both thresholds, see 'Schedule.Interval.canonicalStartUpper'), so it is already
-- on the trail. A jump lands on a further threshold whose atom must be asserted.
-- The current state is the previous round's fixpoint, so every cited literal is
-- already on the trail.
assertChannelInJump
  :: forall mode s task t
  .  ( Num t, Measurable t, Bounded t, MonitorMode mode )
  => Theory mode s task t -> Handedness -> Int -> [ Lit ] -> ST s ( Maybe SAT.Conflict )
assertChannelInJump t side i base = do
  lit     <- sideLit t side i
  carvers <- jumpCarverLits t side i
  reason  <- boundReasonLits lit ( base ++ carvers )
  assertBatch t lit reason

-------------------------------------------------------------------------------
-- Per-pass channelling (capture / channel).
--
-- A propagation /pass/ (one propagator's emitted constraints) is channelled to
-- the SAT trail right after it is applied. Reasons cite the antecedents the
-- propagator read — the /pre-pass/ bounds and matrix edges, captured by
-- 'capturePass' before 'Schedule.Constraint.applyConstraints' mutates anything.
-- Pre-pass antecedents were asserted by earlier passes (or seeded), so they sit
-- strictly earlier on the trail than this pass's freshly-asserted bounds; the
-- implication graph stays acyclic and 1-UIP resolves correctly.

-- | Inference-time snapshot of a propagation pass, taken before it is applied.
data PassCapture t = PassCapture
  { -- | Per task, its pre-pass @(est, lct, compulsory part)@. The bounds are
    -- re-interned (as on-trail atoms) when cited; the compulsory part drives
    -- carver reconstruction for jumps.
    capBounds  :: !( IntMap ( Endpoint ( EarliestTime t ), Endpoint ( LatestTime t ), Interval t ) )
  , -- | Per constrained task, the matrix precedence edges between it and its
    -- est-side responsible subset (pre-pass; empty for energetically-detected
    -- precedences whose edge is only created this pass).
    capEstPrec :: !( IntMap [ Lit ] )
  , -- | As 'capEstPrec', for the lct-side subset.
    capLctPrec :: !( IntMap [ Lit ] )
  , -- | The pass's responsible subsets (@boundReasons@), so a domain emptied by
    -- the pass can cite the same energetic antecedents for its crossing bounds.
    capBR      :: !( IntMap ( IntSet, IntSet ) )
  }

emptyPassCapture :: PassCapture t
emptyPassCapture = PassCapture IntMap.empty IntMap.empty IntMap.empty IntMap.empty

-- | The captured pre-pass compulsory part of a task (empty when absent).
capCompOf :: ( Num t, Measurable t, Bounded t ) => PassCapture t -> Int -> Interval t
capCompOf cap c = case IntMap.lookup c ( capBounds cap ) of
  Just ( _, _, comp ) -> comp
  Nothing             -> Interval top bottom   -- empty (no compulsory part)

-- | Snapshot every non-empty task's current @(est, lct, compulsory part)@. The
-- bounds re-intern as on-trail atoms when cited; the compulsory part drives
-- carver reconstruction.
snapshotBounds
  :: forall mode s task t
  .  ( Num t, Measurable t, Bounded t )
  => Theory mode s task t
  -> ST s ( IntMap ( Endpoint ( EarliestTime t ), Endpoint ( LatestTime t ), Interval t ) )
snapshotBounds t =
  foldM
    ( \ acc i -> do
        task <- readTask t i
        pure $
          if null ( intervals ( taskAvailability task ) )
          then acc
          else IntMap.insert i ( est task, lct task, compulsoryPart task ) acc
    ) IntMap.empty [ 0 .. numTasks ( atoms t ) - 1 ]

-- | A capture of the /current/ state, with no responsible subsets or precedence
-- edges: used by the channel-in path, where the current domain is stable and on
-- the trail, so a conflict it raises cites current atoms directly.
currentCapture
  :: forall mode s task t
  .  ( Num t, Measurable t, Bounded t )
  => Theory mode s task t -> ST s ( PassCapture t )
currentCapture t = do
  bnds <- snapshotBounds t
  pure ( PassCapture bnds IntMap.empty IntMap.empty IntMap.empty )

-- | Snapshot the inference-time antecedents of a pass, before it is applied.
capturePass
  :: forall mode s task t
  .  ( Num t, Measurable t, Bounded t )
  => Theory mode s task t -> Constraints t -> ST s ()
capturePass t ( Constraints { boundReasons = brs } ) = do
#ifdef DEBUG
  -- Capturing a task's pre-pass bound only yields an on-trail atom if the
  -- citability invariant held coming into this pass. Check it here so a
  -- violation is attributed to the prior pass that left a bound unasserted,
  -- rather than surfacing later as an undef antecedent in some reason.
  debugAssertCitability t "capturePass (start)"
#endif
  bnds <- snapshotBounds t
  ( eP, lP ) <- foldM
    ( \ ( ep, lp ) ( i, ( estWhy, lctWhy ) ) -> do
        eLits <- catMaybes <$> traverse ( precEdgeLit t i ) ( IntSet.toList estWhy )
        lLits <- catMaybes <$> traverse ( precEdgeLit t i ) ( IntSet.toList lctWhy )
        pure ( IntMap.insert i eLits ep, IntMap.insert i lLits lp )
    ) ( IntMap.empty, IntMap.empty ) ( IntMap.toList brs )
  writeMutVar ( passCapture t ) ( PassCapture bnds eP lP brs )

-- | The pre-pass bound literals (est + lst) of a subset, interned from the
-- captured values so they are the on-trail atoms the propagator read.
capSubsetLits
  :: ( Num t, Measurable t, Bounded t )
  => Theory mode s task t -> PassCapture t -> [ Int ] -> ST s [ Lit ]
capSubsetLits t cap = fmap concat . traverse one
  where
    one s = case IntMap.lookup s ( capBounds cap ) of
      Just ( eV, lV, _ ) -> do
        el <- estLitAt t s eV
        ll <- lctLitAt t s lV
        pure [ el, ll ]
      -- A cited task absent from the snapshot had an empty pre-pass domain,
      -- which cannot happen for a task a live inference depends on.
      Nothing -> boundLits t [ s ]

-- | Carver bound literals (pre-pass) for a jump to @newBound@: reconstruct the
-- carvers from the /captured/ compulsory parts and cite their captured bounds.
capCarverLits
  :: ( Num t, Measurable t, Bounded t )
  => Theory mode s task t -> PassCapture t -> Handedness -> Int
  -> Endpoint ( EarliestTime t ) -> Endpoint ( LatestTime t ) -> ST s [ Lit ]
capCarverLits t cap side i newEst newLst = do
  let window = jumpWindow t side i newEst newLst
      compOf c = pure $ case IntMap.lookup c ( capBounds cap ) of
        Just ( _, _, comp ) -> comp
        Nothing             -> Interval top bottom   -- empty (no compulsory part)
  ( _residual, carvers ) <- collectCarversWith compOf ( numTasks ( atoms t ) ) i window
  capSubsetLits t cap carvers

-- | Channel a freshly-applied propagation pass: assert its bound tightenings,
-- then its detected precedences, each with a tight pre-pass reason. Returns the
-- conflict if a channelled literal contradicted the trail (which, for bounds,
-- the domain-emptiness check rules out).
channelPass
  :: forall mode s task t
  .  ( Num t, Measurable t, Bounded t, MonitorMode mode )
  => Theory mode s task t
  -> Constraints t
  -> IntMap ( Maybe BoundMove, Maybe BoundMove )  -- ^ how each task's @(est, lct)@ moved
  -> ST s ( Maybe SAT.Conflict )
channelPass t cts deltas = do
  cap <- readMutVar ( passCapture t )
  mbB <- channelBounds cap ( IntMap.toList deltas )
  case mbB of
    Just c  -> pure ( Just c )
    Nothing -> assertEmittedPrecedences t cap ( precedences cts )
  where
    brs = boundReasons cts

    channelBounds :: PassCapture t -> [ ( Int, ( Maybe BoundMove, Maybe BoundMove ) ) ] -> ST s ( Maybe SAT.Conflict )
    channelBounds _   [] = pure Nothing
    channelBounds cap ( ( i, ( estMv, lctMv ) ) : rest ) = do
      ok <- SAT.isOk ( solver t )
      if not ok then pure Nothing
      else do
        task <- readTask t i
        if null ( intervals ( taskAvailability task ) )
        then channelBounds cap rest  -- empty domain: surfaced by the infeasibility conflict
        else do
          let ( estWhy, lctWhy ) = maybe ( IntSet.empty, IntSet.empty ) id ( IntMap.lookup i brs )
          mb1 <- channelMove cap Earliest i estMv ( IntSet.toList estWhy ) ( capEstPrec cap )
          case mb1 of
            Just c  -> pure ( Just c )
            Nothing -> do
              mb2 <- channelMove cap Latest i lctMv ( IntSet.toList lctWhy ) ( capLctPrec cap )
              case mb2 of
                Just c  -> pure ( Just c )
                Nothing -> channelBounds cap rest

    channelMove
      :: PassCapture t -> Handedness -> Int -> Maybe BoundMove -> [ Int ] -> IntMap [ Lit ]
      -> ST s ( Maybe SAT.Conflict )
    channelMove _   _    _ Nothing       _      _    = pure Nothing
    channelMove cap side i ( Just move ) subset prec = do
      lit        <- sideLit t side i
      subsetLits <- capSubsetLits t cap subset
      let precLits = IntMap.findWithDefault [] i prec
      carvers <- case move of
        MovedExact  -> pure []
        MovedJumped -> do
          task <- readTask t i
          capCarverLits t cap side i ( est task )
            ( latestStartFromCompletion ( taskDuration task ) ( lct task ) )
      reason <- boundReasonLits lit ( subsetLits ++ precLits ++ carvers )
      assertBatch t lit reason

-- | The per-pass channeller wiring 'capturePass' \/ 'channelPass' into
-- 'propagationLoop'. A channel conflict is stashed in 'pendingConflict' and
-- reported to the loop ('True') so it stops.
passChanneller
  :: forall mode s task t
  .  ( Num t, Measurable t, Bounded t, MonitorMode mode )
  => Theory mode s task t -> PassChanneller s task t
passChanneller t = PassChanneller
  { onCapture = capturePass t
  , onChannel = \ cts applied -> do
      let deltas = fmap ( \ a -> ( estMove a, lctMove a ) ) applied
      mbC <- channelPass t cts deltas
      case mbC of
        Just c  -> writeMutVar ( pendingConflict t ) ( Just c ) *> pure True
        Nothing -> pure False
  }

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
#ifdef DEBUG
    debugCheckReasonAntecedents t lit reason
#endif
    -- TODO: the lazy-reason table is never reclaimed on backjump.
    lref <- SAT.recordLazyReason ( solver t ) reason
    SAT.enqueueUndef ( solver t ) lit ( RLazy lref )
  modifyMutVar' ( theoryPropCount t ) ( + 1 )

#ifdef DEBUG
-- | Verify, at enqueue time, that a theory-propagation reason is a valid unit
-- reason for @propLit@: every other literal of the (forced) clause is currently
-- /false/, i.e. each antecedent is true and was asserted strictly earlier on the
-- trail. A 'LUndef' antecedent is a /future antecedent/ (cited before it is on
-- the trail) and would corrupt 1-UIP; a 'LTrue' clause literal means a false
-- antecedent was cited as if true. Either is a reason-construction bug.
debugCheckReasonAntecedents
  :: forall mode s task t
  .  Theory mode s task t -> Lit -> LazyReason s -> ST s ()
debugCheckReasonAntecedents t propLit reason = do
  body <- forceLazyReason reason
  let check []         = pure ()
      check ( l : ls )
        | litVar l == litVar propLit = check ls
        | otherwise = do
            v <- SAT.litValue ( solver t ) l
            if v == LFalse
            then check ls
            else do
              mbMeaning <- litMeaning ( atoms t ) ( boundAtoms t ) l
              dump      <- SAT.dumpSolverState ( solver t )
              error $ "Schedule.LCG.Theory.enqueuePropagated: reason for "
                   <> show propLit <> " cites antecedent " <> show l <> " which is "
                   <> show v <> " (expected the clause literal to be LFalse, i.e. the "
                   <> "antecedent true and earlier on the trail)\n"
                   <> "  antecedent meaning: " <> debugMeaning mbMeaning <> "\n"
                   <> "full clause: " <> show body <> "\n" <> dump
  check body

-- | Render a decoded 'AtomMeaning' for diagnostics (the @t@-valued threshold is
-- elided to avoid a 'Show' constraint rippling through 'enqueuePropagated').
debugMeaning :: Maybe ( AtomMeaning t ) -> String
debugMeaning Nothing                          = "unknown atom"
debugMeaning ( Just ( MeansPrecedence p s ) ) = "precedence " <> show p <> " ≺ " <> show s
debugMeaning ( Just ( MeansBound i _ pol ) )  = "bound task=" <> show i <> " pol=" <> show pol
#endif

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
      tickConflict ( monitor t ) "derived-edge"
      recordReasonLen ( monitor t ) ( length body )
      literalsAsConflict "derived-edge" ( solver t ) body

-- | Assert a theory-propagated literal carrying a tight lazy @reason@: enqueue
-- it (the common case), skip it if already true, or — if it is already false —
-- turn it directly into a conflict by forcing its reason.
--
-- The reason only cites antecedents already on the trail (the citability
-- invariant), so forcing it on the immediate-conflict path is sound: the bound
-- channel-out pass asserts every bound before precedences, so a precedence's
-- reason resolves against on-trail bound atoms even when it conflicts at once.
-- (Bound channel-out itself never reaches the false case — a bound that would
-- contradict the trail empties the domain first, surfaced as 'EmptyDomain'.)
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
    LFalse -> do
      body <- forceLazyReason reason
      tickConflict ( monitor t ) "bound"
      recordReasonLen ( monitor t ) ( length body )
      literalsAsConflict "bound" ( solver t ) body

-------------------------------------------------------------------------------
-- Conflict assembly.

-- | Turn a propagator-reported infeasibility into a tight SAT conflict.
buildInfeasibleConflict
  :: forall mode s task t
  .  ( Num t, Measurable t, Bounded t, MonitorMode mode )
  => Theory mode s task t
  -> Infeasible t
  -> ST s ( Maybe SAT.Conflict )
buildInfeasibleConflict t = \ case
  Overloaded { culprit } -> do
    -- 'overloadCheck' reads (and never mutates) the current domains, so the
    -- culprit's /current/ @est@\/@lst@ atoms are on the trail (channelled by
    -- earlier passes). A conflict clause needs only that its literals are
    -- currently false, so citing the current bounds directly is sound.
    lits <- boundLits t ( IntSet.toList culprit )
    tickConflict ( monitor t ) "overload"
    recordReasonLen ( monitor t ) ( length lits )
    literalsAsConflict "overload" ( solver t ) ( map negateLit lits )
  EmptyDomain { emptiedTask = i, enforcedEarliest = lo, enforcedLatest = hi } -> do
    -- The emptying pass's pre-pass antecedents are in 'passCapture'.
    cap <- readMutVar ( passCapture t )
    emptyDomainConflict t cap i lo hi
  CycleDetected {} ->
    -- The LCG path never adds precedence edges through 'Schedule.Precedence';
    -- cycles arise only in 'channelLit' during channel-in. A propagator-reported
    -- cycle would be a structural bug.
    error "Schedule.LCG.Theory.buildInfeasibleConflict: unexpected CycleDetected from a propagator"

-- | Tight conflict for an emptied task @i@: its enforced earliest start @lo@ and
-- latest completion @hi@ leave no slot. Assert @i@'s two crossing bound atoms
-- @[start ≥ lo]@ and @[start ≤ lst]@ (each reasoned from its pre-pass squeezing
-- predecessors\/successors), then emit the conflict citing them together with
-- the carvers whose compulsory parts removed @i@'s interior across @[lo, hi]@
-- (reconstructed from @i@'s ground availability and the pre-pass compulsory
-- parts; empty when @[lo, hi]@ has no room in the ground instance).
--
-- Asserting the crossing bounds — rather than citing only the antecedents —
-- guarantees the conflict mentions a current-level literal (the newly enforced
-- crossing bound), which 1-UIP requires.
emptyDomainConflict
  :: forall mode s task t
  .  ( Num t, Measurable t, Bounded t, MonitorMode mode )
  => Theory mode s task t
  -> PassCapture t
  -> Int
  -> Endpoint ( EarliestTime t )
  -> Endpoint ( LatestTime t )
  -> ST s ( Maybe SAT.Conflict )
emptyDomainConflict t cap i lo hi = do
  let ( estWhy, lctWhy ) = maybe ( IntSet.empty, IntSet.empty ) id ( IntMap.lookup i ( capBR cap ) )
  task <- readTask t i
  let dur    = taskDuration task
      lstThr = latestStartFromCompletion dur hi
      window = cutAfter hi ( cutBefore lo ( groundAvail t Boxed.Vector.! i ) )
  ( residual, carvers ) <- collectCarversWith ( pure . capCompOf cap ) ( numTasks ( atoms t ) ) i window
#ifdef DEBUG
  -- The crossing bounds plus the carvers must genuinely leave no slot for @i@;
  -- otherwise the reconstruction (and hence the learnt clause) is unsound. With
  -- only @prune@\/@timetable@ removals this always holds (the others are ground).
  let fits iv = measure iv >= dur
  when ( any fits ( toList ( intervals residual ) ) ) $ do
    dump <- SAT.dumpSolverState ( solver t )
    error $ "Schedule.LCG.Theory.emptyDomainConflict: residual still admits task "
         <> show i <> " (carver reconstruction incomplete)\n" <> dump
#else
  let _ = residual
#endif
  carverLits <- capSubsetLits t cap carvers
  ( lowerAtom, _ ) <- internBoundAtomWith t ( SAT.newAuxVar ( solver t ) ) i ( estLowerToStartUpper lo )
  ( upperLit,  _ ) <- internBoundAtomWith t ( SAT.newAuxVar ( solver t ) ) i lstThr
  let lowerLit = negateLit lowerAtom   -- start ≥ lo
  -- Assert both crossing bound atoms (the emptied task was skipped by
  -- channel-out), each with a tight pre-pass reason: the squeezing subset plus
  -- the matrix precedence edges captured for that side.
  estAnte <- ( ++ IntMap.findWithDefault [] i ( capEstPrec cap ) ) <$> capSubsetLits t cap ( IntSet.toList estWhy )
  loReason <- boundReasonLits lowerLit estAnte
  mb1 <- assertBatch t lowerLit loReason
  case mb1 of
    Just c  -> pure ( Just c )
    Nothing -> do
      lctAnte <- ( ++ IntMap.findWithDefault [] i ( capLctPrec cap ) ) <$> capSubsetLits t cap ( IntSet.toList lctWhy )
      hiReason <- boundReasonLits upperLit lctAnte
      mb2 <- assertBatch t upperLit hiReason
      case mb2 of
        Just c  -> pure ( Just c )
        Nothing -> do
          let body = negateLit lowerLit : negateLit upperLit : map negateLit carverLits
          tickConflict ( monitor t ) "empty-domain"
          recordReasonLen ( monitor t ) ( length body )
          literalsAsConflict "empty-domain" ( solver t ) body

-- | Tight conflict for a matrix cycle closed by the new edge @predTask ≺
-- succTask@: a path @succTask ≺ x₁ ≺ … ≺ predTask@ of precedence literals
-- already true on the trail. Together with the new edge (also true) they form a
-- cycle, so the negation of their conjunction is an all-false conflict clause.
reconstructCycle
  :: forall mode s task t
  .  MonitorMode mode
  => Theory mode s task t
  -> Int          -- ^ @predTask@: tail of the new edge
  -> Int          -- ^ @succTask@: head of the new edge
  -> ST s ( Maybe SAT.Conflict )
reconstructCycle t predTask succTask = do
  mbPath <- findPath ( IntSet.singleton succTask ) succTask
  case mbPath of
    Nothing      ->
      error "Schedule.LCG.Theory.reconstructCycle: cycle reported but no true precedence path found"
    Just pathLits -> do
      let body = map negateLit ( precLit ( atoms t ) predTask succTask : pathLits )
      tickConflict ( monitor t ) "cycle"
      recordReasonLen ( monitor t ) ( length body )
      literalsAsConflict "cycle" ( solver t ) body
  where
    n = numTasks ( atoms t )
    -- Depth-first search over the /true/ precedence edges from @x@ to
    -- @predTask@, returning the edge literals along a path (acyclic on the
    -- true-edge DAG, so the @visited@ set guarantees termination).
    findPath :: IntSet -> Int -> ST s ( Maybe [ Lit ] )
    findPath visited x
      | x == predTask = pure ( Just [] )
      | otherwise     = tryEdges visited x 0
    tryEdges :: IntSet -> Int -> Int -> ST s ( Maybe [ Lit ] )
    tryEdges visited x y
      | y >= n                      = pure Nothing
      | y == x                      = tryEdges visited x ( y + 1 )
      | IntSet.member y visited     = tryEdges visited x ( y + 1 )
      | otherwise                   = do
          let edge = precLit ( atoms t ) x y
          v <- SAT.litValue ( solver t ) edge
          case v of
            LTrue -> do
              mb <- findPath ( IntSet.insert y visited ) y
              case mb of
                Just rest -> pure ( Just ( edge : rest ) )
                Nothing   -> tryEdges visited x ( y + 1 )
            _     -> tryEdges visited x ( y + 1 )

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
-- | Verify the /citability invariant/ as a post-condition of bound channel-out:
-- every non-empty task's current @est@ and @lst@ atoms are asserted true on the
-- trail. This is what makes citing them in tight reasons sound — a reason built
-- in this round is only forced (during a later 1-UIP) once channel-out is
-- complete, at which point every bound it cites is on the trail. A violation
-- means a bound move failed to reify\/assert its atom (a bug).
--
-- (The check is a post-condition, not a per-cite check: within 'channelOutBounds'
-- a reason may cite a task whose bound is asserted later in the same pass, which
-- is sound precisely because the reason is forced only after the pass finishes.)
debugAssertCitability
  :: forall mode s task t
  .  ( Num t, Measurable t, Bounded t )
  => Theory mode s task t -> String -> ST s ()
debugAssertCitability t ctx = go 0
  where
    n = numTasks ( atoms t )
    go i
      | i >= n    = pure ()
      | otherwise = do
          task <- readTask t i
          if null ( intervals ( taskAvailability task ) )
          then go ( i + 1 )   -- empty domain: surfaced as an infeasibility, not channelled
          else do
            e <- currentEstLit t i
            l <- currentLctLit t i
            check i "est" e
            check i "lst" l
            go ( i + 1 )
    check i which lit = do
      v <- SAT.litValue ( solver t ) lit
      when ( v /= LTrue ) $ do
        dump <- SAT.dumpSolverState ( solver t )
        error $ "Schedule.LCG.Theory.debugAssertCitability [" <> ctx <> "]: task "
             <> show i <> "'s " <> which <> " bound atom " <> show lit <> " is " <> show v
             <> ", not LTrue (citability invariant violated)\n" <> dump

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
