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
--       (2) /Interval commitment./ For each task whose availability has
--           interior gaps, a /decision/ bound atom is seeded at every gap
--           boundary. Allows for some meaningful structural branching.
--
--     Binary monotonicity lemmata (@[start ≤ a] ⟹ [start ≤ b]@ for @a ≤ b@)
--     keep a task's bound atoms mutually consistent, so a decided or
--     channelled-in bound propagates along the axis.
module Schedule.LCG.Theory
  ( -- * Theory state
    TheoryState(..), TheoryOptions(..)
  , newTheory
    -- * SAT-decision-level synchronisation
  , pushLevel
  , popToLevel
    -- * One round of theory propagation
  , theoryPropagate
    -- * Failure-directed decision heuristic
  , theoryDecide
  , measureSpace
    -- * Failure-directed rating updates
  , noteDecision
  , settlePending
  , settleConflict
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
  ( foldM, replicateM_, when
#ifdef DEBUG
  , unless
#endif
  )
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
import Control.Monad.Primitive
  ( stToPrim )
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
  , negateLit, litVar, varIndex, litIndex
  )
import SAT.Clause
  ( Reason(..), LazyReason(..), forceLazyReason )
import qualified SAT.Solver as SAT
import Data.Lattice
  ( BoundedLattice(top, bottom) )
import Schedule.Constraint
  ( Constraint(notEarlierThan, notLaterThan)
  , Constraints(..), Infeasible(..)
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
  , isPrecedenceVar, precedenceAtomsNumTasks
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
  , TransitiveClosureScratch, newTransitiveClosureScratch, insertEdgeTransitively
  , Order(..), readOrdering
  )
import Schedule.Propagators
  ( Propagator, propagationLoop, seedAllOf, seedMatrixWatchers
  , PassChanneller(..)
#ifdef DEBUG
  , nullChanneller
#endif
  )
import Schedule.Task
  ( MutableTaskInfos, TaskInfos(..), Task(..)
  , est, ect, lst, lct )
import Schedule.Time
  ( EarliestTime, LatestTime, Delta(getDelta), HandedTime(handedTime)
  , Time(getTime)
  , Handedness(Earliest, Latest)
  )
import Schedule.Trail
  ( Trail, newTrail, currentMark, undoTo, orderingCellWriter )

-------------------------------------------------------------------------------
-- Theory state.

-- | The DPLL(T) theory state for unary scheduling.
data TheoryState mode s task t = TheoryState
  { -- | The CDCL core driving search.
    theorySolverState  :: !( SAT.SolverState s )
  , -- | The bijection between task pairs and SAT decision variables.
    atoms          :: !PrecedenceAtoms
  , -- | The lazily-grown registry of start-time bound atoms.
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
  , -- | Reusable scratch space for transitive closure computations.
    transitiveClosureScratch :: !( TransitiveClosureScratch s )
  , -- | Scheduling propagators run on each theory round.
    propagators    :: ![ Propagator task t ]
    -- | Configuration options.
  , theoryOptions  :: !TheoryOptions
  , -- | Per-branch failure-directed rating, indexed by 'litIndex' (so the two
    -- polarities of a variable are scored independently). Lower = more
    -- failure-prone = preferred by 'theoryDecide'.
    --
    -- Each entry is an exponential moving average of the branch's per-application
    -- /local rating/ (@0@ on a wipeout, else @1 + R@ for the search-space
    -- reduction @R@; see 'settlePending' \/ 'settleConflict'), starting from the
    -- neutral 'initialRating'. Grown on demand to cover every interned literal;
    -- entries persist across restarts (a matured rating re-steers the top of the
    -- tree on the next dive).
    branchRating :: !( Growable Primitive.MVector s Double )
  , -- | Per search depth (SAT decision level), the running average local rating
    -- of branches rated at that depth (the paper's @avgRating[d]@), used to
    -- normalise a branch's rating in 'settleBranch'. Indexed by depth, grown on
    -- demand, 'initialRating' until a branch at that depth is rated.
    avgRating :: !( Growable Primitive.MVector s Double )
  , -- | The branch chosen by the most recent decision, paired with the (log)
    -- search-space measure ('measureSpace') in effect when it was taken. A
    -- one-slot pending observation: settled into 'branchRating' when the next
    -- decision is taken ('settlePending') or a conflict fires ('settleConflict',
    -- a wipeout), then cleared.
    pendingDecision :: !( MutVar s ( Maybe ( Lit, Double ) ) )
  , -- | Per gappy task, its interval-commitment decision atoms in ascending
    -- threshold order (the positive literal @start ≤ boundary@). Written once at
    -- construction and never mutated thereafter.
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
  , -- | Inference-time antecedent capture of the propagation pass currently
    -- being applied (see 'capturePass'). Written before each pass is applied and
    -- read when channelling it (or when a pass empties a domain).
    passCapture    :: !( MutVar s ( PassCapture t ) )
  , -- | A conflict produced while channelling a propagation pass to the SAT
    -- trail, if any; held until the propagation loop ends, then consumed.
    pendingConflict :: !( MutVar s ( Maybe SAT.Conflict ) )
  , -- | Cumulative count of theory propagations: literals the theory has
    -- promoted onto the SAT trail (derived transitive edges, propagator
    -- precedences, and channelled-out bound tightenings). For instrumentation.
    theoryPropCount :: !( MutVar s Int )
  , -- | Optional instrumentation. Erased entirely when @mode ~ 'MonitoringOff'@.
    monitor         :: !( Monitor mode s )
  }

-- | Configuration options for the theory-side of the DPLL(T) loop.
data TheoryOptions
  = TheoryOptions
  { -- | Maximum propagator-round iterations per theory step.
    maxPropRounds  :: !Int
  , -- | Whether to perform interval commitment decision branching by seeding
    -- a /decision/ bound atom at each task's internal availability-gap
    -- boundaries (see 'seedDecisionBounds').
    useBoundDecisions :: !Bool
  , -- | Whether 'theoryDecide' drives failure-directed branch selection ahead of
    -- VSIDS. 'False' makes the search pure VSIDS, with the ratings left inert.
    useTheoryDecide :: !Bool
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
  -> TheoryOptions
  -> ST s ( TheoryState mode s task t )
newTheory tis props opts = do
  theorySolverState <- SAT.newSolver
  let
    !numTasks = Boxed.Vector.length ( taskNames tis )
    !numAtoms = ( numTasks * ( numTasks - 1 ) ) `shiftR` 1
  atoms <-
    if numAtoms == 0
    then pure ( mkPrecedenceAtoms numTasks 0 )
    else do
      v0 <- SAT.newVar theorySolverState
      replicateM_ ( numAtoms - 1 ) ( SAT.newVar theorySolverState )
      pure ( mkPrecedenceAtoms numTasks ( varIndex v0 ) )
  -- Bound atoms occupy variable indices above the fixed precedence block.
  boundAtoms               <- newBoundAtoms numAtoms
  schedTrail               <- newTrail
  transitiveClosureScratch <- newTransitiveClosureScratch numTasks
  theoryHead               <- newMutVar 0
  levelMarks               <- Growable.new 16
  dirtySeed                <- newMutVar Nothing
  boundDirty               <- newMutVar IntSet.empty
  passCapture              <- newMutVar emptyPassCapture
  pendingConflict          <- newMutVar Nothing
  theoryPropCount          <- newMutVar 0
  decisionBounds           <- newMutVar mempty
  branchRating             <- Growable.new 16
  avgRating                <- Growable.new 16
  pendingDecision          <- newMutVar Nothing
  -- Snapshot ground availabilities now, before any propagation mutates them.
  groundAvail <-
    Boxed.Vector.generateM numTasks \ i ->
      taskAvailability <$> Boxed.MVector.unsafeRead ( taskAvails tis ) i
  monitor <- newMonitor @mode
  let
    t =
      TheoryState
        { tasks         = tis
        , propagators   = props
        , theoryOptions = opts
        , ..
        }
  seedInitialBounds t numTasks
  when ( useBoundDecisions opts ) ( seedDecisionBounds t numTasks )
  pure t

-- | Create initial inner-boundary bound atoms for decision making.
seedDecisionBounds
  :: forall mode s task t
  .  ( Num t, Measurable t, Bounded t )
  => TheoryState mode s task t -> Int -> ST s ()
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
  => TheoryState mode s task t -> Int -> ST s ()
seedInitialBounds t nT =
  for_ [ 0 .. nT - 1 ] \ i -> do
    task <- readTask t i
    if null ( intervals ( taskAvailability task ) )
    then pure ()  -- a degenerate empty instance; surfaced by the first propagation
    else do
      estL <- currentEstLit t i
      lctL <- currentLctLit t i
      -- @estL@ (@start ≥ est@) and @lctL@ (@start ≤ lst@) coincide on a single
      -- atom with opposite polarities exactly when @est > lst@: a task whose
      -- availability has slots but none long enough for its duration, hence no
      -- feasible start. Seeding both then contradicts, so seed defensively and
      -- surface the contradiction as a root infeasibility.
      ok1 <- SAT.tryEnqueue ( theorySolverState t ) estL RFact
      ok2 <- SAT.tryEnqueue ( theorySolverState t ) lctL RFact
      when ( not ( ok1 && ok2 ) ) ( SAT.markFalse ( theorySolverState t ) )

-------------------------------------------------------------------------------
-- SAT-decision-level synchronisation.

-- | Snapshot the current schedule-trail mark to associate it with a fresh
-- SAT decision level. Must be called immediately after 'SAT.pushNewLevel'.
--
-- The semantics mirror 'SAT.Solver.levelStarts': @levelMarks[k]@ holds the
-- schedule-trail mark captured at the start of level @k + 1@ (i.e. just
-- before the level-@(k+1)@ decision is asserted), so undoing back to that
-- mark restores the trail to the state right after level @k@'s effects.
pushLevel :: TheoryState mode s task t -> ST s ()
pushLevel t = do
  m <- currentMark ( schedTrail t )
  Growable.push ( levelMarks t ) m

-- | Roll the schedule trail back to the mark associated with the given
-- SAT decision level. Must be called immediately after 'SAT.cancelUntil'.
--
-- Precondition: @lvl@ is strictly less than the current SAT level
-- (i.e. we are actually backjumping). This matches how
-- 'SAT.Solver.cancelUntil' itself indexes 'SAT.Solver.levelStarts'.
popToLevel :: TheoryState mode s task t -> SAT.DecisionLevel -> ST s ()
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
  newSize <- SAT.solverTrailSize ( theorySolverState t )
  writeMutVar ( theoryHead t ) newSize

-- | Number of precedence literals currently on the SAT trail.
--
-- Used only for debugging/instrumentation.
numPrecedenceDecisions :: TheoryState mode s task t -> ST s Int
numPrecedenceDecisions t = do
  SAT.TrailPos sz <- SAT.solverTrailSize ( theorySolverState t )
  let
    loop !i !acc
      | i >= sz   = pure acc
      | otherwise = do
          lit <- SAT.trailAt ( theorySolverState t ) ( SAT.TrailPos i )
          if isPrecedenceVar ( atoms t ) ( litVar lit )
          then loop ( i + 1 ) ( acc + 1 )
          else loop ( i + 1 ) acc
  loop 0 0

-------------------------------------------------------------------------------
-- Failure-directed decision heuristic.
--
-- Failure-Directed Search (Vilím, Laborie & Shaw, CPAIOR 2015) rates each
-- /branch/ (a variable+polarity) by how close it tends to come to a wipeout, and
-- dives the branch most likely to fail first — provably shrinking the space
-- fastest, which is what closes a search on feasible and infeasible alike. Each
-- branch's rating ('branchRating') matures via an EMA of its per-decision local
-- ratings (see 'settlePending' \/ 'settleConflict'); 'theoryDecide' is what
-- consults the ratings to choose a branch.
--
-- Two deviations from the paper, both order-only:
--
--   * The paper warm-starts ratings by strong branching at each restart root; we
--     instead leave untrained ratings at the neutral 'initialRating' and break
--     /score ties/ among them by critical-pair criticality. On a conflict-free
--     dive no candidate is ever rated (only /decided/ branches are), so every
--     candidate stays neutral and the tie-break reproduces the structural
--     critical-pair dive exactly — protecting the 0-conflict feasibles. Once a
--     branch is rated (post-conflict), its learned rating governs and pure FDS
--     takes over.
--
--   * Restarts follow the surrounding Luby schedule rather than the paper's
--     geometric one.

-- | The neutral starting value for every branch rating and depth average.
initialRating :: Double
initialRating = 1

-- | EMA retention weight @α@ in the rating update.
--
-- The paper uses a slow decay @α ∈ [0.9, 0.99]@: a single observation nudges a
-- rating, and it takes a run of failures to drive a branch toward @0@.
fdsAlpha :: Double
fdsAlpha = 0.95

-- | Floor on a depth's average rating, guarding the per-depth normalisation
-- against a depth whose observations have driven the average toward @0@.
avgRatingFloor :: Double
avgRatingFloor = 1e-3

-- | Grow 'branchRating' to cover the given literal, filling fresh cells with the
-- neutral 'initialRating'.
ensureRating :: TheoryState mode s task t -> Lit -> ST s ()
ensureRating t lit =
  Growable.ensureSize ( branchRating t ) ( litIndex lit + 1 ) initialRating

-- | The current rating of a branch ('initialRating' if never rated), growing the
-- store as needed.
readRating :: TheoryState mode s task t -> Lit -> ST s Double
readRating t lit = do
  ensureRating t lit
  Growable.read ( branchRating t ) ( litIndex lit )

writeRating :: TheoryState mode s task t -> Lit -> Double -> ST s ()
writeRating t lit r = do
  ensureRating t lit
  Growable.write ( branchRating t ) ( litIndex lit ) r

-- | The running average rating at a search depth (the paper's @avgRating[d]@),
-- 'initialRating' until any branch at that depth is rated.
readAvgRating :: TheoryState mode s task t -> Int -> ST s Double
readAvgRating t d = do
  Growable.ensureSize ( avgRating t ) ( d + 1 ) initialRating
  Growable.read ( avgRating t ) d

writeAvgRating :: TheoryState mode s task t -> Int -> Double -> ST s ()
writeAvgRating t d r = do
  Growable.ensureSize ( avgRating t ) ( d + 1 ) initialRating
  Growable.write ( avgRating t ) d r

-- | The current SAT decision level as a plain depth.
currentDepth :: TheoryState mode s task t -> ST s Int
currentDepth t = do
  SAT.DecisionLevel d <- SAT.currentLevel ( theorySolverState t )
  pure d

-- | The log of the remaining search-space size: @Σ_tasks log |domain|@, the
-- domain of a task being the measure of its current availability (its feasible
-- start positions). The paper's reduction @R@ is the /product/ of per-variable
-- domain ratios before and after a decision, so working in this log-sum lets
-- 'settlePending' recover @R = exp(after − before)@ in one subtraction.
--
-- A fixed task contributes a unit (log @0@) domain; an /emptied/ domain is a
-- failure, surfaced as a conflict and rated by 'settleConflict', so it is never
-- measured here (the @max 1@ only guards against @log 0@ on a degenerate slot).
measureSpace
  :: forall mode s task t
  .  ( Real t, Measurable t )
  => TheoryState mode s task t -> ST s Double
measureSpace t = go 0 0
  where
    n = precedenceAtomsNumTasks ( atoms t )
    go :: Int -> Double -> ST s Double
    go !i !acc
      | i >= n    = pure acc
      | otherwise = do
          task <- readTask t i
          let vol = sum [ getDelta ( measure iv )
                        | iv <- toList ( intervals ( taskAvailability task ) ) ]
          go ( i + 1 ) ( acc + log ( max 1 ( realToFrac vol ) ) )

-- | Propose the next branching literal by failure-directed selection, or
-- 'Nothing' to defer to VSIDS.
--
-- The precedence tournament is the /primary/ choice set: a complete acyclic
-- ordering plus propagation determines a schedule, so precedences alone are a
-- sound and complete branching. Each undecided pair's variable @v@ is scored by
-- the combined rating of its two branches,
--
-- > score v = rating[pos v] + rating[neg v]
--
-- (both branches failure-prone ⇒ a /closing choice/, the best). The
-- minimum-score candidate is branched on its lower-rated — more failure-prone —
-- side first (fail-first); score ties are broken by criticality (see 'evalPair'),
-- which on an untrained dive reproduces the structural critical-pair heuristic.
--
-- Interval-commit atoms are /completion/ choices: redundant given the
-- precedences, they are considered only once every precedence is decided but the
-- formula is not yet fully assigned (cf. the paper completing a fully-decided
-- choice set). Mixing them into the primary pool lets shallow interval-commit
-- failures crowd out the precedence proof, which the per-instance sweep confirms
-- hurts the infeasible families without helping the feasible ones.
--
-- 'Nothing' once every structural atom is decided (or when 'useTheoryDecide' is
-- off): any remaining decision variables fall through to VSIDS, so search
-- stays complete.
theoryDecide
  :: forall mode s task t
  .  ( Real t, Measurable t, Bounded t )
  => TheoryState mode s task t
  -> ST s ( Maybe Lit )
theoryDecide t
  | not ( useTheoryDecide $ theoryOptions t ) = pure Nothing
  | otherwise = do
      mbPrec <- scanPrecedences t Nothing
      case mbPrec of
        Just cand -> pure ( Just ( candidateLit cand ) )
        Nothing   -> fmap candidateLit <$> scanBoundDecisions t Nothing

-- | A scored failure-directed candidate: its combined @score@ (lower =
-- preferred), a @tieKey@ breaking equal scores (lower = preferred), and the
-- branch literal to assert first (its lower-rated, more failure-prone side).
type Candidate = ( Double, Double, Lit )

candidateLit :: Candidate -> Lit
candidateLit ( _, _, lit ) = lit

-- | Keep the better of an incumbent candidate and a new one, comparing by
-- @(score, tieKey)@ lexicographically.
keepBest :: Maybe Candidate -> Candidate -> Maybe Candidate
keepBest Nothing cand = Just cand
keepBest acc@( Just ( bScore, bTie, _ ) ) cand@( cScore, cTie, _ )
  | ( cScore, cTie ) < ( bScore, bTie ) = Just cand
  | otherwise                            = acc

-- | Assemble a candidate from a variable's two branch ratings, a score-tie key,
-- and the side to branch first when the two ratings are equal.
mkCandidate :: Lit -> Lit -> Double -> Double -> Double -> Lit -> Candidate
mkCandidate posLit negLit ratPos ratNeg tieKey tieSide =
  ( ratPos + ratNeg
  , tieKey
  , case compare ratPos ratNeg of
      LT -> posLit
      GT -> negLit
      EQ -> tieSide
  )

-- | Scan the undecided precedence pairs (the upper-triangular ordering matrix),
-- scoring each and keeping the best-scoring candidate.
scanPrecedences
  :: forall mode s task t
  .  ( Real t, Measurable t, Bounded t )
  => TheoryState mode s task t -> Maybe Candidate -> ST s ( Maybe Candidate )
scanPrecedences t = go 0 1
  where
    ps  = atoms t
    n   = precedenceAtomsNumTasks ps
    mat = orderings ( tasks t )
    go :: Int -> Int -> Maybe Candidate -> ST s ( Maybe Candidate )
    go i j best
      | i >= n - 1 = pure best
      | j >= n     = go ( i + 1 ) ( i + 2 ) best
      | otherwise  = do
          o <- readOrdering mat i j
          case o of
            Unknown -> do
              v <- SAT.litValue ( theorySolverState t ) ( precLit ps i j )
              case v of
                -- 'Unknown' in the matrix should mean the precedence atom is
                -- unassigned; the check guards against branching an assigned one.
                LUndef -> do
                  cand <- precCandidate t i j
                  go i ( j + 1 ) ( keepBest best cand )
                _ -> go i ( j + 1 ) best
            _ -> go i ( j + 1 ) best

-- | Score one undecided precedence pair: combined branch rating, with the pair's
-- criticality ('evalPair') as the score-tie key and its larger-slack direction
-- as the within-pair tie side. On an untrained dive every rating is neutral, so
-- the criticality tie-break drives selection — the structural critical-pair dive.
precCandidate
  :: ( Real t, Measurable t, Bounded t )
  => TheoryState mode s task t -> Int -> Int -> ST s Candidate
precCandidate t i j = do
  let ps     = atoms t
      posLit = precLit ps i j   -- i ≺ j
      negLit = precLit ps j i   -- j ≺ i
  ( crit, dirLit ) <- evalPair t i j
  rPos <- readRating t posLit
  rNeg <- readRating t negLit
  pure ( mkCandidate posLit negLit rPos rNeg ( realToFrac ( getDelta crit ) ) dirLit )

-- | Scan each gappy task's lowest undecided interval-commit atom (a completion
-- choice; see 'theoryDecide') and keep the best-scoring candidate. With no
-- precedence left to compete with, score alone decides; equal scores fall to the
-- first (lowest-threshold) atom.
scanBoundDecisions
  :: forall mode s task t
  .  TheoryState mode s task t -> Maybe Candidate -> ST s ( Maybe Candidate )
scanBoundDecisions t acc0 = do
  dbs <- readMutVar ( decisionBounds t )
  foldM step acc0 ( IntMap.toList dbs )
  where
    step :: Maybe Candidate -> ( Int, [ Lit ] ) -> ST s ( Maybe Candidate )
    step acc ( i, lits ) = do
      task <- readTask t i
      let nIvals = length ( intervals ( taskAvailability task ) )
      if nIvals <= 1
      then pure acc   -- already committed to a single interval
      else do
        mbLit <- firstUndecided t lits
        case mbLit of
          Nothing     -> pure acc   -- all decided already
          Just posLit -> do
            let negLit = negateLit posLit
            rPos <- readRating t posLit
            rNeg <- readRating t negLit
            pure ( keepBest acc ( mkCandidate posLit negLit rPos rNeg 0 posLit ) )

-- | The lowest-threshold interval-commit atom of the list not yet assigned.
firstUndecided :: TheoryState mode s task t -> [ Lit ] -> ST s ( Maybe Lit )
firstUndecided _ [] = pure Nothing
firstUndecided t ( l : ls ) = do
  v <- SAT.litValue ( theorySolverState t ) l
  case v of
    LUndef -> pure ( Just l )
    _      -> firstUndecided t ls

-- | The criticality of an unordered task pair (the larger of the two ordering
-- slacks; smaller = more contended) together with the larger-slack directed
-- precedence literal — the textbook direction to branch first.
--
-- (Clusivity is ignored in the slack — it shifts a bound by at most one unit,
-- immaterial to a branching /heuristic/.)
evalPair
  :: ( Num t, Measurable t, Bounded t )
  => TheoryState mode s task t -> Int -> Int -> ST s ( Delta t, Lit )
evalPair t i j = do
  ti <- readTask t i
  tj <- readTask t j
  let ps   = atoms t
      ectI = handedTime ( endpoint ( ect ti ) )
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
-- Failure-directed rating updates.
--
-- A one-slot pending observation links the two hook points: 'noteDecision'
-- records the branch just taken with the (log) search-space measure then in
-- effect; 'settlePending' \/ 'settleConflict' fold its measured failure-directed
-- local rating into the branch's EMA when the next decision is taken or a
-- conflict fires. Because nothing happens between a decision and its settlement
-- but that branch's own propagation, the settlement sees exactly the branch's
-- effect (the paper's "update rating of branch right after it propagates").

-- | Record the branch just taken, with the (log) search-space measure
-- ('measureSpace') in effect when it was chosen, as the one-slot pending
-- observation to be settled later.
noteDecision :: TheoryState mode s task t -> Lit -> Double -> ST s ()
noteDecision t lit spaceBefore =
  writeMutVar ( pendingDecision t ) ( Just ( lit, spaceBefore ) )

-- | Settle the pending decision against the (log) search-space measure now in
-- effect (after it propagated to a fixpoint). Its local rating is the paper's
-- @1 + R@, where @R = exp(after − before) ∈ (0, 1]@ is the product of per-task
-- domain ratios — so a non-failing branch rates in @(1, 2]@, sharply above the
-- @0@ a wipeout earns ('settleConflict'). A no-op when no decision is pending.
settlePending :: TheoryState mode s task t -> Double -> ST s ()
settlePending t spaceAfter = do
  mb <- readMutVar ( pendingDecision t )
  case mb of
    Nothing -> pure ()
    Just ( lit, spaceBefore ) -> do
      let r = min 1 ( exp ( spaceAfter - spaceBefore ) )
      settleBranch t lit ( 1 + r )
      writeMutVar ( pendingDecision t ) Nothing

-- | Settle the pending decision as a wipeout (local rating @0@): the branch led
-- straight to a conflict, the maximally failure-directed outcome. A no-op when
-- no decision is pending.
settleConflict :: TheoryState mode s task t -> ST s ()
settleConflict t = do
  mb <- readMutVar ( pendingDecision t )
  case mb of
    Nothing -> pure ()
    Just ( lit, _ ) -> do
      settleBranch t lit 0
      writeMutVar ( pendingDecision t ) Nothing

-- | Fold a branch's fresh local rating into its EMA, normalised by the running
-- average rating at the current depth (so a branch is judged against its peers
-- at the same depth, where local ratings are systematically higher near the
-- root): @rating ← α·rating + (1−α)·localRating \/ avgRating[d]@. The depth's
-- average absorbs the same observation.
settleBranch :: TheoryState mode s task t -> Lit -> Double -> ST s ()
settleBranch t lit localRating = do
  d   <- currentDepth t
  avg <- readAvgRating t d
  r0  <- readRating t lit
  let avg' = max avgRatingFloor avg
      r'   = fdsAlpha * r0  + ( 1 - fdsAlpha ) * ( localRating / avg' )
      avgN = fdsAlpha * avg + ( 1 - fdsAlpha ) * localRating
  writeRating t lit r'
  writeAvgRating t d avgN

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
  => TheoryState mode s task t
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
  => TheoryState mode s task t
  -> ST s ( Maybe SAT.Conflict )
channelPending t = do
#ifdef DEBUG
  checkMatrixTrailInvariant t "channelPending (start)"
#endif
  loop
  where
    loop :: ST s ( Maybe SAT.Conflict )
    loop = do
      ok <- SAT.isOk ( theorySolverState t )
      if not ok
      then pure Nothing  -- theorySolverState already marked UNSAT; outer loop will bail.
      else do
        h@( SAT.TrailPos hi ) <- readMutVar ( theoryHead t )
        SAT.TrailPos sz       <- SAT.solverTrailSize ( theorySolverState t )
        if hi >= sz
        then pure Nothing
        else do
          lit <- SAT.trailAt ( theorySolverState t ) h
          writeMutVar ( theoryHead t ) ( SAT.TrailPos ( hi + 1 ) )
          meaning <- litMeaning ( atoms t ) ( boundAtoms t ) lit
          case meaning of
            Nothing                       -> loop
            Just ( MeansPrecedence p s )  -> do
              -- The precedence path runs the O(dim²) transitive-closure
              -- insertion ('addIncidentEdgesTransitively'); the bound path only
              -- tightens one domain. Splitting them localises channel-in's cost.
              mbConf <- withPhaseTiming ( monitor t ) "channel-in/precedence" ( channelLit t p s )
              case mbConf of
                Just c  -> pure ( Just c )
                Nothing -> loop
            Just ( MeansBound task thr pol ) -> do
              mbConf <- withPhaseTiming ( monitor t ) "channel-in/bound" ( channelBound t task thr pol )
              case mbConf of
                Just c  -> pure ( Just c )
                Nothing -> loop

#ifdef DEBUG
-- | Diagnostic invariant: every 'LessThan' or 'GreaterThan' cell in the
-- ordering matrix must correspond to an assigned precedence literal on the
-- SAT trail.
checkMatrixTrailInvariant
  :: forall mode s task t
  .  TheoryState mode s task t
  -> String
  -> ST s ()
checkMatrixTrailInvariant t ctx = iterPairs 0 1
  where
    ps     = atoms t
    nTasks = precedenceAtomsNumTasks ps
    mat    = orderings ( tasks t )
    bad :: Int -> Int -> Order -> LBool -> String -> ST s ()
    bad i j o val expected = do
      dump <- SAT.dumpSolverState ( theorySolverState t )
      error $ "Schedule.LCG.Theory.checkMatrixTrailInvariant [" <> ctx <> "]: "
           <> "mat[" <> show i <> "," <> show j <> "] = " <> show o
           <> " but lit " <> show ( precLit ps i j ) <> " is " <> show val
           <> " (expected " <> expected <> ")\n" <> dump
    checkPair :: Int -> Int -> ST s ()
    checkPair i j = do
      o   <- readOrdering mat i j
      val <- SAT.litValue ( theorySolverState t ) ( precLit ps i j )
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
  => TheoryState mode s task t
  -> Int -> Int
  -> ST s ( Maybe SAT.Conflict )
channelLit t predTask succTask = do
  let tis = tasks t
  tickChannelCall ( monitor t )
#ifdef DEBUG
  let ps = atoms t
      d = precedenceAtomsNumTasks ps
  when ( predTask < 0 || predTask >= d || succTask < 0 || succTask >= d ) $
    error $ "Schedule.LCG.Theory.channelLit: decoded pair=("
         <> show predTask <> "," <> show succTask <> ") out of range; dim="
         <> show d
  when ( predTask == succTask ) $
    error "Schedule.LCG.Theory.channelLit: decoded pair has equal indices"
#endif
  result <- runExceptT $
    insertEdgeTransitively
      ( transitiveClosureScratch t )
      ( orderingCellWriter ( schedTrail t ) tis )
      onNewEdge
      LiftedCycle
      ( orderings tis )
      predTask
      succTask
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
              -- The 3-literal clause ¬p(a→u) ∨ ¬p(u→b) ∨ p(a→b); its antecedents
              -- are already in hand, so nothing to defer.
              reason   = boundReasonLits derived ( pure [ antePred, anteSucc ] )
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
  => TheoryState mode s task t
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
    -- (each already on the trail as per Note [Upholding the citability invariant])
    -- plus any carvers.
    -- The current state is the previous round's fixpoint, captured by
    -- 'currentCapture'.
    let ( lo, hi ) = case pol of
          Positive -> ( est0, completionFromLatestStart dur l )
          Negative -> ( startUpperToEstLower l, lct0 )
    cap <- currentCapture t
    emptyDomainConflict t cap task lo hi
  else do
    -- Wake every propagator on this task next round, but only if the domain
    -- actually moved: a no-op re-drain must not re-trigger the full sweep.
    when ( isJust moved ) ( markBoundDirty t task )
    -- See Note [Upholding the citability invariant]: a channel-in /jump/ over a
    -- gap leaves the new canonical @est@\/@lst@ at a threshold whose atom is
    -- not the channelled-in one, so reify and assert it here with a tight reason
    -- (the channelled-in literal, plus carvers for any non-ground gap skipped).
    -- An /exact/ move lands on the channelled-in atom itself.
    case moved of
      Just MovedJumped -> do
        ( channelAtom, _ ) <- internBoundAtomWith t ( SAT.newAuxVar ( theorySolverState t ) ) task l
        let channelledLit = case pol of { Positive -> channelAtom; Negative -> negateLit channelAtom }
            side          = case pol of { Positive -> Latest;      Negative -> Earliest }
        assertChannelInJump t side task l [ channelledLit ]
      _ -> pure Nothing

-- | Add a pair of task indices to the precedence-dirty set so the next
-- 'runPropagators' call wakes the matrix-watching propagators on them. While
-- 'dirtySeed' is still 'Nothing' (before the first 'runPropagators' call) we
-- leave it alone: that first call seeds every propagator with the full task
-- set anyway.
markDirtyPair :: TheoryState mode s task t -> Int -> Int -> ST s ()
markDirtyPair t a b =
  modifyMutVar' ( dirtySeed t ) $ \ case
    Nothing    -> Nothing
    Just dirty -> Just ( IntSet.insert a ( IntSet.insert b dirty ) )

-- | Mark a task whose domain a channelled-in bound tightened, so the next
-- 'runPropagators' wakes /all/ propagators on it.
markBoundDirty :: TheoryState mode s task t -> Int -> ST s ()
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
  => TheoryState mode s task t
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
                     ( IntSet.fromList [ 0 .. precedenceAtomsNumTasks ( atoms t ) - 1 ] )
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
      ( propagationLoop ( monitor t ) ( maxPropRounds $ theoryOptions t ) ( schedTrail t )
          ( propagators t ) ( passChanneller t ) seed )
  -- TODO: 'propagationLoop' doesn't properly report 'GiveUp', which means we
  -- currently conflate "fixpoint, consistent" with "gave up early".
  mbChannelConf <- readMutVar ( pendingConflict t )
  case mbChannelConf of
    Just c  -> pure ( Just c )
    Nothing -> case eRes of
      Right () -> do
#ifdef DEBUG
        checkMatrixTrailInvariant t "runPropagators (end, no conflict)"
        checkCitabilityInvariant t "runPropagators (end, no conflict)"
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
  => TheoryState mode s task t -> ST s ()
debugAuditPropagationFixpoint t = do
  let allTasks = IntSet.fromList [ 0 .. precedenceAtomsNumTasks ( atoms t ) - 1 ]
  ( eRes, updates ) <- runSchedule ( tasks t )
    ( propagationLoop ( monitor t ) ( maxPropRounds $ theoryOptions t ) ( schedTrail t )
        ( propagators t ) nullChanneller ( seedAllOf ( propagators t ) allTasks ) )
  let movedTasks =
        IntMap.keysSet $
          IntMap.filter ( \ ( e, l ) -> isJust e || isJust l ) ( tightenedBounds updates )
  case eRes of
    Right () | IntSet.null movedTasks -> pure ()
    _ -> do
      SAT.DecisionLevel lvl <- SAT.currentLevel ( theorySolverState t )
      dump                  <- SAT.dumpSolverState ( theorySolverState t )
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
-- all already on the trail (see Note [Upholding the citability invariant]).
assertEmittedPrecedences
  :: forall mode s task t
  .  ( Num t, Measurable t, Bounded t, MonitorMode mode )
  => TheoryState mode s task t
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
-- precedence, all already on the trail (as per Note [Upholding the citability invariant]).
assertOnePrecedence
  :: forall mode s task t
  .  ( Num t, Measurable t, Bounded t, MonitorMode mode )
  => TheoryState mode s task t
  -> PassCapture t
  -> Int -> Int
  -> [ Int ]   -- ^ tasks whose bounds justify the precedence
  -> ST s ( Maybe SAT.Conflict )
assertOnePrecedence t cap a b reasonTasks = do
  ok <- SAT.isOk ( theorySolverState t )
  if not ok then pure Nothing
  else do
#ifdef DEBUG
    let !d = precedenceAtomsNumTasks ( atoms t )
    when ( a < 0 || a >= d || b < 0 || b >= d ) $
      error $ "Schedule.LCG.Theory.assertOnePrecedence: pair=("
           <> show a <> "," <> show b <> ") out of range; dim=" <> show d
    when ( a == b ) $
      error "Schedule.LCG.Theory.assertOnePrecedence: self-precedence"
#endif
    let lit = precLit ( atoms t ) a b
    -- The responsible subset's pre-pass bound atoms; deferred so the interning
    -- only happens if 1-UIP forces this reason. See Note [Deferred reason construction].
    assertBatch t lit ( boundReasonLits lit ( capSubsetLits t cap reasonTasks ) )

-------------------------------------------------------------------------------
-- Bound-atom literals.

-- | Read a task's current availability record.
readTask :: TheoryState mode s task t -> Int -> ST s ( Task task t )
readTask t i = Boxed.MVector.unsafeRead ( taskAvails ( tasks t ) ) i

-- | Get-or-create a latest-start atom via the given variable allocator, wiring
-- its monotonicity links to the task's neighbouring thresholds the first time
-- it is created. Returns whether the atom was freshly created.
internBoundAtomWith
  :: forall {s} t mode task
  .  Measurable t
  => TheoryState mode s task t
  -> ST s Var -> Int -> Endpoint ( LatestTime t ) -> ST s ( Lit, Bool )
internBoundAtomWith t allocVar i thr = do
  ( lit, isNew ) <- internStartUpper ( boundAtoms t ) allocVar i thr
  when isNew $ do
#ifdef DEBUG
    -- A freshly-interned atom owns a brand-new SAT variable, so it must
    -- start off unassigned.
    freshVal <- SAT.valueOf ( theorySolverState t ) ( litVar lit )
    case freshVal of
      LUndef -> pure ()
      _      -> error $ "internBoundAtomWith: freshly-interned atom already assigned: "
                     <> show lit <> " = " <> show freshVal
#endif
    ( mbBelow, mbAbove ) <- boundNeighbours ( boundAtoms t ) i thr
    for_ mbBelow \ belowLit -> belowLit ⟹ lit
    for_ mbAbove \ aboveLit -> lit ⟹ aboveLit
  pure ( lit, isNew )
  where
    -- The binary monotonicity clause @a ⟹ b@ (i.e. @¬a ∨ b@).
    (⟹) :: Lit -> Lit -> ST s ()
    a ⟹ b = SAT.addBinaryLemma ( theorySolverState t ) ( negateLit a ) b
      -- NB: not 'addClause', as that is invalid mid-search.

-- | Get-or-create a bound atom as a /decision/ variable (in the VSIDS heap),
-- bumping its activity on first creation.
internDecisionBoundAtom
  :: Measurable t
  => TheoryState mode s task t -> Int -> Endpoint ( LatestTime t ) -> ST s Lit
internDecisionBoundAtom t i thr = do
  ( lit, isNew ) <- internBoundAtomWith t ( SAT.newVar ( theorySolverState t ) ) i thr
  when isNew ( SAT.bumpVarActivity ( theorySolverState t ) ( litVar lit ) )
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
  => TheoryState mode s task t -> Int -> Endpoint ( EarliestTime t ) -> ST s Lit
estLitAt t i e = do
  ( lit, _ ) <- internBoundAtomWith t ( SAT.newAuxVar ( theorySolverState t ) ) i
                  ( estLowerToStartUpper e )
  pure ( negateLit lit )

-- | Intern the latest-start atom for the latest /completion/ @l@ under the
-- duration of the given task snapshot, returning the positive literal
-- @start ≤ lst@.
internLatestStart
  :: ( Num t, Measurable t, Bounded t )
  => TheoryState mode s task t
  -> Int
  -> Task task t
  -> Endpoint ( LatestTime t )
  -> ST s Lit
internLatestStart t i task l =
  fst <$> internBoundAtomWith t ( SAT.newAuxVar ( theorySolverState t ) ) i
            ( latestStartFromCompletion ( taskDuration task ) l )

-- | The literal asserting the /upper/ bound @start_i ≤ lst@ for the given latest
-- completion @l@: the /positive/ literal of the atom at the latest-start
-- threshold.
--
-- See also 'estLitAt'.
lctLitAt
  :: ( Num t, Measurable t, Bounded t )
  => TheoryState mode s task t -> Int -> Endpoint ( LatestTime t ) -> ST s Lit
lctLitAt t i l = readTask t i >>= \ task -> internLatestStart t i task l

-- | The bound literal on @side@ for an /already-read/ task snapshot, interning
-- its atom: the lower bound @start ≥ est@ ('Earliest') or the upper bound
-- @start ≤ lst@ ('Latest').
boundLitOfTask
  :: ( Num t, Measurable t, Bounded t )
  => TheoryState mode s task t -> Handedness -> Int -> Task task t -> ST s Lit
boundLitOfTask t Earliest i task = estLitAt t i ( est task )
boundLitOfTask t Latest   i task = internLatestStart t i task ( lct task )

-- | The current bound literal of task @i@ on the given side, reading its domain
-- once and interning the atom if needed: @start ≥ est@ at 'Earliest', @start ≤ lst@
-- at 'Latest'.
sideLit
  :: ( Num t, Measurable t, Bounded t )
  => TheoryState mode s task t -> Handedness -> Int -> ST s Lit
sideLit t side i = readTask t i >>= boundLitOfTask t side i

-- | The literal asserting task @i@'s /current/ (domain) lower bound
-- @start_i ≥ est_i@.
currentEstLit
  :: ( Num t, Measurable t, Bounded t )
  => TheoryState mode s task t -> Int -> ST s Lit
currentEstLit t i = sideLit t Earliest i

-- | The literal asserting task @i@'s /current/ (domain) upper bound
-- @start_i ≤ lst_i@.
currentLctLit
  :: ( Num t, Measurable t, Bounded t )
  => TheoryState mode s task t -> Int -> ST s Lit
currentLctLit t i = sideLit t Latest i

{- Note [Upholding the citability invariant]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The unary-scheduling theory's lazy reasons cite the atoms responsible for an
inference. Note [Citability invariant] (in SAT.Solver) requires every cited atom
to be true on the trail when the reason is forced; this is how the theory
ensures it.

Cited atoms come in two kinds, and the invariant holds for each:

  * Bound atoms: the current est/lst of a task involved in the inference.

    Every bound the theory holds is matched by a corresponding atom on the trail.
    This atom is asserted at seeding (seedInitialBounds) and on channel-out
    (channelPass) as theory propagations, and on channel-in (channelBound)
    reflecting the SAT assignment that is already there.

  * Precedence atoms.

    Every edge of the precedence matrix is on the trail: it was either
    channelled in from a SAT precedence assignment, or derived by transitive
    closure and asserted as a theory propagation (see precEdgeLit).

This invariant is a post-condition of a *completed* channel pass, not a per-cite
invariant: within channel-out, a reason may cite a bound that is only asserted
later in the same pass. That is still sound, because a reason is forced only
during a *subsequent* 1-UIP, by which point the pass has finished and all its
bounds are on the trail. The post-condition is checked by the debug assertion
checkCitabilityInvariant.

Example:

  - Given a ≺ b and b ≺ c, transitivity deduces a ≺ c.
    The associated reason is ¬p(a≺b) ∨ ¬p(b≺c) ∨ p(a≺c), where 'p' denotes the
    precedence atom associated with a precedence.
    The two antecedents of this reason are matrix edges: they are already true
    on the trail, allowing 1-UIP to resolve through them.
-}

-- | The current lower- and upper-bound literals of every task in the list
-- (two per task: @start ≥ est@ and @start ≤ lst@), interning their atoms.
--
-- See also Note [Upholding the citability invariant].
boundLits
  :: ( Num t, Measurable t, Bounded t )
  => TheoryState mode s task t -> [ Int ] -> ST s [ Lit ]
boundLits t = fmap concat . traverse one
  where
    one i = do
      e <- currentEstLit t i
      l <- currentLctLit t i
      pure [ e, l ]

{- Note [Deferred reason construction]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
A channel-out theory propagation records a lazy reason that is forced only if a
/later/ 1-UIP resolves through it. Most never are (a backjump discards the
literal first), so building the supporting clause eagerly is wasted work.

Soundness rule: the deferred action must not read mutable state that can change
under it; it should rely on the immutable pass capture or never-mutated
information (e.g. ground availabilities, task durations).
-}

-- | Assemble a tight lazy reason for a theory propagation: disjunction
-- of @propLit@ and the negations of the antecedents produced by @mkAntecedents@.
--
-- The antecedent action is lazy, run only when the reason is forced.
boundReasonLits
  :: Lit -> ST s [ Lit ] -> LazyReason s
boundReasonLits propLit mkAntecedents =
  LazyReason ( stToPrim ( ( propLit : ) . map negateLit <$> mkAntecedents ) )

-- | The precedence literal between @i@ and @p@ that the matrix currently holds
-- (true on the trail), or 'Nothing' if they are unordered.
precEdgeLit
  :: forall mode s task t
  .  TheoryState mode s task t -> Int -> Int -> ST s ( Maybe Lit )
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

-- | Given a task, remove from its ground availability the compulsory part
-- of all other tasks (timetabling).
--
-- Returns the residual availability of the task, together with the other tasks
-- responsible for the carving.
collectCarversWith
  :: ( Num t, Measurable t, Bounded t )
  => ( Int -> ST s ( Interval t ) )   -- ^ get compulsory part of a task
  -> Int                              -- ^ number of tasks
  -> Int                              -- ^ task to carve
  -> Intervals t                      -- ^ task's ground availability
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

-- | Reify and assert a task's current bound on the given @side@ after a
-- /channel-in/ jump, with a tight reason.
--
-- Only jumps need this: an /exact/ channel-in move lands the canonical
-- @est@\/@lst@ atom on the channelled-in atom itself, so it is already on the
-- trail. A jump lands on a further threshold whose atom must be asserted.
--
-- The current state is the previous round's fixpoint, so every cited literal is
-- already on the trail (as per Note [Upholding the citability invariant]).
assertChannelInJump
  :: forall mode s task t
  .  ( Num t, Measurable t, Bounded t, MonitorMode mode )
  => TheoryState mode s task t -> Handedness -> Int
  -> Endpoint ( LatestTime t )   -- ^ the channelled-in bound threshold @l@ (the anchor)
  -> [ Lit ]                     -- ^ the channelled-in literal (the anchor's justification)
  -> ST s ( Maybe SAT.Conflict )
assertChannelInJump t side i l base = do
  -- The carvers cite the /current/ (previous-fixpoint) state and are built
  -- eagerly: there is no shared pass capture to defer against. The anchor is the
  -- channelled-in bound @l@ (justified by @base@); see Note [Bound-move reason completeness].
  post   <- readTask t i
  lit    <- boundLitOfTask t side i post
  let dur    = taskDuration post
      newEst = est post
      newLst = latestStartFromCompletion dur ( lct post )
  reason <- case side of
    Earliest ->
      boundMoveReason t i dur ( Interval (startUpperToEstLower l ) ( estLowerToStartUpper newEst ) )
        ( fmap compulsoryPart . readTask t ) ( boundLits t ) base
    Latest   ->
      boundMoveReason t i dur ( Interval ( startUpperToEstLower newLst ) l )
        ( fmap compulsoryPart . readTask t ) ( boundLits t ) base
  assertBatch t lit ( boundReasonLits lit ( pure reason ) )

-------------------------------------------------------------------------------
-- Per-pass channelling (capture / channel).
--
-- A propagation /pass/ (one propagator's emitted constraints) is channelled to
-- the SAT trail right after it is applied. Reasons cite the antecedents the
-- propagator read: the /pre-pass/ bounds and matrix edges, captured by
-- 'capturePass' before 'Schedule.Constraint.applyConstraints' mutates anything.
-- Pre-pass antecedents were asserted by earlier passes (or seeded), as per
-- Note [Upholding the citability invariant], so they sit strictly earlier on the
-- trail than this pass's freshly-asserted bounds; the implication graph stays
-- acyclic and 1-UIP resolves correctly.

-- | Inference-time capture of a propagation pass, taken before it is applied.
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
  => TheoryState mode s task t
  -> ST s ( IntMap ( Endpoint ( EarliestTime t ), Endpoint ( LatestTime t ), Interval t ) )
snapshotBounds t =
  foldM
    ( \ acc i -> do
        task <- readTask t i
        pure $
          if null ( intervals ( taskAvailability task ) )
          then acc
          else IntMap.insert i ( est task, lct task, compulsoryPart task ) acc
    ) IntMap.empty [ 0 .. precedenceAtomsNumTasks ( atoms t ) - 1 ]

-- | A capture of the /current/ state, carrying no responsible subsets or
-- precedence edges, so a conflict raised from it cites the current atoms
-- directly. Sound only when the current domain is stable and already on the
-- trail (see Note [Upholding the citability invariant]).
currentCapture
  :: forall mode s task t
  .  ( Num t, Measurable t, Bounded t )
  => TheoryState mode s task t -> ST s ( PassCapture t )
currentCapture t = do
  bnds <- snapshotBounds t
  pure ( PassCapture bnds IntMap.empty IntMap.empty IntMap.empty )

-- | Capture the inference-time antecedents of a pass, before it is applied.
capturePass
  :: forall mode s task t
  .  ( Num t, Measurable t, Bounded t )
  => TheoryState mode s task t -> Constraints t -> ST s ()
capturePass t ( Constraints { boundReasons = brs } ) = do
#ifdef DEBUG
  -- Capturing a task's pre-pass bound only yields an on-trail atom if the
  -- citability invariant held coming into this pass.
  -- Check it here so a violation is attributed to the prior pass that
  -- left a bound unasserted, rather than surfacing later as an undef antecedent
  -- in some reason.
  --
  -- See Note [Upholding the citability invariant].
  checkCitabilityInvariant t "capturePass (start)"
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
  => TheoryState mode s task t -> PassCapture t -> [ Int ] -> ST s [ Lit ]
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

{- Note [Bound-move reason completeness]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Running propagators updates the bounds of tasks, providing an explanation
for the SAT core. This happens in two steps; for example, the EST of a task is
updated thusly:

  old_est --> anchor
  anchor  --> new_est

where we update the old_est to the anchor by e.g. energetic reasoning, and then
update the anchor to new_est by carving: the compulsory parts of other tasks
cover [anchor, new_est).

The explanation provided to the SAT core consists of the following antecedents:

  anchor antecedents ++ carvers

These are computed 'boundMoveReason'.
-}

-- | Assemble the antecedents of a bound move, as per Note [Bound-move reason completeness].
boundMoveReason
  :: forall mode s task t
  .  ( Num t, Measurable t, Bounded t )
  => TheoryState mode s task t
  -> Int                              -- ^ task number
  -> Delta t                          -- ^ task duration
  -> Interval t                       -- ^ skipped start span
  -> ( Int -> ST s ( Interval t ) )   -- ^ a task's compulsory part
  -> ( [ Int ] -> ST s [ Lit ] )      -- ^ carver tasks to their bound literals
  -> [ Lit ]                          -- ^ anchor antecedents (the imposed bound's justification)
  -> ST s [ Lit ]
boundMoveReason t i dur ( Interval lowerStart upperStart ) compOf carverLitsOf anchorLits = do
  let ground   = groundAvail t Boxed.Vector.! i
      window   = cutAfter upperStart ( cutBefore lowerStart ground )
      holdsDur ivals = any ( \ iv -> measure iv >= dur ) ( toList ( intervals ivals ) )
  if not ( holdsDur window )
  then
    -- The skipped span has no slot long enough for the task even before any
    -- carving, so ground gaps + the anchor already entail the move: no carver is
    -- load-bearing. (An exact move's span is a point, so this is the common case,
    -- and it avoids the O(n) carver walk.) See Note [Bound-move reason completeness].
    pure anchorLits
  else do
    ( _residual, carvers ) <- collectCarversWith compOf ( precedenceAtomsNumTasks ( atoms t ) ) i window
#ifdef DEBUG
    -- The anchor + carvers + ground gaps must genuinely leave no feasible slot in
    -- the skipped span; otherwise the antecedents do not entail the bound and the
    -- learnt clause would be unsound. See Note [Bound-move reason completeness].
    when ( holdsDur _residual ) $ do
      dump <- SAT.dumpSolverState ( theorySolverState t )
      error $ unlines
        [ "Schedule.LCG.Theory.boundMoveReason: incomplete reason (does not entail new bound)."
        , "Cited antecedents leave a feasible slot in the skipped span for task " <> show i <> "."
        , dump
        ]
#endif
    carverLits <- carverLitsOf carvers
    pure ( anchorLits ++ carverLits )

-- | Channel a freshly-applied propagation pass: assert its bound tightenings,
-- then its detected precedences, each with a tight pre-pass reason. Returns the
-- conflict if a channelled literal contradicted the trail (which, for bounds,
-- the domain-emptiness check rules out).
channelPass
  :: forall mode s task t
  .  ( Num t, Measurable t, Bounded t, MonitorMode mode )
  => TheoryState mode s task t
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
      ok <- SAT.isOk ( theorySolverState t )
      if not ok then pure Nothing
      else do
        task <- readTask t i
        if null ( intervals ( taskAvailability task ) )
        then channelBounds cap rest  -- empty domain: surfaced by the infeasibility conflict
        else do
          let ( estWhy, lctWhy ) = maybe ( IntSet.empty, IntSet.empty ) id ( IntMap.lookup i brs )
              ct = IntMap.findWithDefault mempty i ( constraints cts )
          mb1 <- channelMove cap ct Earliest i estMv ( IntSet.toList estWhy ) ( capEstPrec cap )
          case mb1 of
            Just c  -> pure ( Just c )
            Nothing -> do
              mb2 <- channelMove cap ct Latest i lctMv ( IntSet.toList lctWhy ) ( capLctPrec cap )
              case mb2 of
                Just c  -> pure ( Just c )
                Nothing -> channelBounds cap rest

    channelMove
      :: PassCapture t -> Constraint t -> Handedness -> Int -> Maybe BoundMove -> [ Int ] -> IntMap [ Lit ]
      -> ST s ( Maybe SAT.Conflict )
    channelMove _   _  _    _ Nothing _ _ = pure Nothing
    channelMove cap ct side i ( Just _move ) subset prec = do
      -- Read the post-pass task once. It is an immutable snapshot, so both the
      -- propagated literal and the post-pass bounds the deferred reason needs come
      -- from it as pure values (captured like 'cap'); the closure never touches
      -- the live domain. See Note [Deferred reason construction].
      post <- readTask t i
      lit  <- boundLitOfTask t side i post
      let
        dur      = taskDuration post
        newEst   = est post
        newLst   = latestStartFromCompletion dur ( lct post )
        precLits = IntMap.findWithDefault [] i prec
        -- @i@'s pre-pass bound, the anchor for an availability-only (prune\/
        -- timetable) move (which imposes no @NotEarlierThan@\/@NotLaterThan@).
        ( preEst, preLct ) = case IntMap.lookup i ( capBounds cap ) of
          Just ( eV, lV, _ ) -> ( eV, lV )
          Nothing            -> ( est post, lct post )
        -- Every bound move is anchored at the task's own prior bound on the moved
        -- side. See Note [Bound-move reason completeness].
        mkAntecedents =
          case side of
            Earliest -> do
              selfLit <- estLitAt t i preEst
              ( anchorLits, lowerStart ) <-
                case notEarlierThan ct of
                  Just v  -> do { ss <- capSubsetLits t cap subset; pure ( selfLit : ss ++ precLits, v ) }
                  Nothing -> pure ( [ selfLit ], preEst )
              boundMoveReason t i dur
                ( Interval lowerStart ( estLowerToStartUpper newEst ) )
                ( pure . capCompOf cap ) ( capSubsetLits t cap ) anchorLits
            Latest -> do
              selfLit <- lctLitAt t i preLct
              ( anchorLits, upperStart ) <-
                case notLaterThan ct of
                  Just v  -> do { ss <- capSubsetLits t cap subset; pure ( selfLit : ss ++ precLits, v ) }
                  Nothing -> pure ( [ selfLit ], latestStartFromCompletion dur preLct )
              boundMoveReason t i dur
                ( Interval ( startUpperToEstLower newLst ) upperStart )
                ( pure . capCompOf cap ) ( capSubsetLits t cap ) anchorLits
      assertBatch t lit ( boundReasonLits lit mkAntecedents )

-- | The per-pass channeller wiring 'capturePass' \/ 'channelPass' into
-- 'propagationLoop'. A channel conflict is stashed in 'pendingConflict' and
-- reported to the loop ('True') so it stops.
passChanneller
  :: forall mode s task t
  .  ( Num t, Measurable t, Bounded t, MonitorMode mode )
  => TheoryState mode s task t -> PassChanneller s task t
passChanneller t = PassChanneller
  { onCapture = \ cts -> stToPrim $
      withPhaseTiming ( monitor t ) "propagators/capture" ( capturePass t cts )
  , onChannel = \ cts applied -> stToPrim $
      withPhaseTiming ( monitor t ) "propagators/channel-out" do
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
  .  MonitorMode mode
  => TheoryState mode s task t -> Lit -> LazyReason s -> ST s ()
enqueuePropagated t lit reason = do
  lvl <- SAT.currentLevel ( theorySolverState t )
  if lvl == SAT.GroundLevel
  then
    -- A ground-level theory propagation is an unconditional fact; 1-UIP never
    -- resolves against ground-level literals, so it needs no reason clause.
    SAT.enqueueUndef ( theorySolverState t ) lit RFact
  else do
#ifdef DEBUG
    debugCheckReasonAntecedents t lit reason
#endif
    tickLazyRecord ( monitor t )
    lref <- SAT.recordLazyReason ( theorySolverState t )
              ( instrumentedLazyReason ( monitor t ) reason )
    SAT.enqueueUndef ( theorySolverState t ) lit ( RLazy lref )
  modifyMutVar' ( theoryPropCount t ) ( + 1 )

-- | Instrument a lazy reason to tick when it gets forced.
instrumentedLazyReason
  :: MonitorMode mode
  => Monitor mode s -> LazyReason s -> LazyReason s
instrumentedLazyReason mon reason =
  LazyReason do
    ls <- forceLazyReason reason
    tickLazyForce mon ( length ls )
    pure ls
{-# SPECIALISE instrumentedLazyReason @MonitoringOff #-}

#ifdef DEBUG
-- | Verify, at enqueue time, that a theory-propagation reason is a valid unit
-- reason for @propLit@: every other literal of the (forced) clause is currently
-- /false/, i.e. each antecedent is true and was asserted strictly earlier on the
-- trail. A 'LUndef' antecedent is a /future antecedent/ (cited before it is on
-- the trail) and would corrupt 1-UIP; a 'LTrue' clause literal means a false
-- antecedent was cited as if true. Either is a reason-construction bug.
debugCheckReasonAntecedents
  :: forall mode s task t
  .  TheoryState mode s task t -> Lit -> LazyReason s -> ST s ()
debugCheckReasonAntecedents t propLit reason = do
  body <- forceLazyReason reason
  let check []         = pure ()
      check ( l : ls )
        | litVar l == litVar propLit = check ls
        | otherwise = do
            v <- SAT.litValue ( theorySolverState t ) l
            if v == LFalse
            then check ls
            else do
              mbMeaning <- litMeaning ( atoms t ) ( boundAtoms t ) l
              dump      <- SAT.dumpSolverState ( theorySolverState t )
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

-- | Try to assert a theory-inferred literal whose reason is /self-contained/,
-- forcing the reason into a conflict if the literal is already false.
--
-- Used for transitive-closure derived edges.
--
-- NB: every cited literal is already on the trail as per Note [Upholding the citability invariant].
assertTheoryLit
  :: forall mode s task t
  .  MonitorMode mode
  => TheoryState mode s task t
  -> Lit
  -> LazyReason s
  -> ST s ( Maybe SAT.Conflict )
assertTheoryLit t lit reason = do
  val <- SAT.litValue ( theorySolverState t ) lit
  case val of
    LTrue  -> pure Nothing
    LUndef -> enqueuePropagated t lit reason *> pure Nothing
    LFalse -> do
      -- A derived transitive edge contradicted the assignment; its 3-literal
      -- reason is tight and self-contained.
      body <- forceLazyReason reason
      tickConflict ( monitor t ) "derived-edge"
      recordReasonLen ( monitor t ) ( length body )
      literalsAsConflict "derived-edge" ( theorySolverState t ) body

-- | Assert a theory-propagated literal carrying a tight lazy @reason@: enqueue
-- it (the common case), skip it if already true, or — if it is already false —
-- turn it directly into a conflict by forcing its reason.
--
-- The reason only cites antecedents already on the trail, as per
-- Note [Upholding the citability invariant], so forcing it on the
-- immediate-conflict path is sound.
assertBatch
  :: forall mode s task t
  .  MonitorMode mode
  => TheoryState mode s task t
  -> Lit
  -> LazyReason s
  -> ST s ( Maybe SAT.Conflict )
assertBatch t lit reason = do
  val <- SAT.litValue ( theorySolverState t ) lit
  case val of
    LTrue  -> pure Nothing
    LUndef -> enqueuePropagated t lit reason *> pure Nothing
    LFalse -> do
      body <- forceLazyReason reason
      tickConflict ( monitor t ) "bound"
      recordReasonLen ( monitor t ) ( length body )
      literalsAsConflict "bound" ( theorySolverState t ) body

-------------------------------------------------------------------------------
-- Conflict assembly.

#ifdef DEBUG
-- | Verify a reported overload is genuine: some time window @[a, b)@ is filled by
-- culprit tasks confined to it (@est ≥ a@, @lct ≤ b@) whose total duration exceeds
-- @b − a@, so they provably cannot all fit.
assertValidOverload
  :: forall mode s task t
  .  ( Num t, Ord t, Measurable t, Bounded t )
  => TheoryState mode s task t -> IntSet -> ST s ()
assertValidOverload t culprit = do
  rows <- for ( IntSet.toList culprit ) \ c -> do
    tc <- readTask t c
    pure ( getTime ( handedTime ( endpoint ( est tc ) ) )
         , getTime ( handedTime ( endpoint ( lct tc ) ) )
         , getDelta ( taskDuration tc ) )
  let does_overload = or
        [ sum [ d | ( e, l, d ) <- rows, e >= a, l <= b ] > b - a
        | ( a, _, _ ) <- rows, ( _, b, _ ) <- rows, b > a ]
  unless does_overload do
    dump <- SAT.dumpSolverState ( theorySolverState t )
    error $ unlines
      [ "Schedule.LCG.Theory.buildInfeasibleConflict: invalid overload."
      , dump
      ]
#endif

-- | Turn a propagator-reported infeasibility into a tight SAT conflict.
buildInfeasibleConflict
  :: forall mode s task t
  .  ( Num t, Measurable t, Bounded t, MonitorMode mode )
  => TheoryState mode s task t
  -> Infeasible t
  -> ST s ( Maybe SAT.Conflict )
buildInfeasibleConflict t = \ case
  Overloaded { culprit } -> do
    -- 'overloadCheck' reads (and never mutates) the current domains, so the
    -- culprit's /current/ @est@\/@lst@ atoms are on the trail, as per
    -- Note [Upholding the citability invariant].
    --
    -- A conflict clause needs only that its literals are currently false,
    -- so citing the current bounds directly is sound.
    lits <- boundLits t ( IntSet.toList culprit )
#ifdef DEBUG
    assertValidOverload t culprit
#endif
    tickConflict ( monitor t ) "overload"
    recordReasonLen ( monitor t ) ( length lits )
    literalsAsConflict "overload" ( theorySolverState t ) ( map negateLit lits )
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
  => TheoryState mode s task t
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
  ( residual, carvers ) <- collectCarversWith ( pure . capCompOf cap ) ( precedenceAtomsNumTasks ( atoms t ) ) i window
#ifdef DEBUG
  -- The crossing bounds plus the carvers must genuinely leave no slot for @i@;
  -- otherwise the reconstruction (and hence the learnt clause) is unsound. With
  -- only @prune@\/@timetable@ removals this always holds (the others are ground).
  let fits iv = measure iv >= dur
  when ( any fits ( toList ( intervals residual ) ) ) $ do
    dump <- SAT.dumpSolverState ( theorySolverState t )
    error $ "Schedule.LCG.Theory.emptyDomainConflict: residual still admits task "
         <> show i <> " (carver reconstruction incomplete)\n" <> dump
#else
  let _ = residual
#endif
  carverLits <- capSubsetLits t cap carvers
  ( lowerAtom, _ ) <- internBoundAtomWith t ( SAT.newAuxVar ( theorySolverState t ) ) i ( estLowerToStartUpper lo )
  ( upperLit,  _ ) <- internBoundAtomWith t ( SAT.newAuxVar ( theorySolverState t ) ) i lstThr
  let lowerLit = negateLit lowerAtom   -- start ≥ lo
  -- Assert both crossing bound atoms (the emptied task was skipped by
  -- channel-out), each with a tight pre-pass reason: the squeezing subset plus
  -- the matrix precedence edges captured for that side.
  estAnte <- ( ++ IntMap.findWithDefault [] i ( capEstPrec cap ) ) <$> capSubsetLits t cap ( IntSet.toList estWhy )
  mb1 <- assertBatch t lowerLit ( boundReasonLits lowerLit ( pure estAnte ) )
  case mb1 of
    Just c  -> pure ( Just c )
    Nothing -> do
      lctAnte <- ( ++ IntMap.findWithDefault [] i ( capLctPrec cap ) ) <$> capSubsetLits t cap ( IntSet.toList lctWhy )
      mb2 <- assertBatch t upperLit ( boundReasonLits upperLit ( pure lctAnte ) )
      case mb2 of
        Just c  -> pure ( Just c )
        Nothing -> do
          let body = negateLit lowerLit : negateLit upperLit : map negateLit carverLits
          tickConflict ( monitor t ) "empty-domain"
          recordReasonLen ( monitor t ) ( length body )
          literalsAsConflict "empty-domain" ( theorySolverState t ) body

-- | Tight conflict for a matrix cycle closed by the new edge @predTask ≺
-- succTask@: a path @succTask ≺ x₁ ≺ … ≺ predTask@ of precedence literals
-- already true on the trail (as per Note [Upholding the citability invariant]).
-- Together with the new edge (also true) they form a cycle, so the negation of
-- their conjunction is an all-false conflict clause.
reconstructCycle
  :: forall mode s task t
  .  MonitorMode mode
  => TheoryState mode s task t
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
      literalsAsConflict "cycle" ( theorySolverState t ) body
  where
    n = precedenceAtomsNumTasks ( atoms t )
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
          v <- SAT.litValue ( theorySolverState t ) edge
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
  -> SAT.SolverState s
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
-- | Verify the citability invariant as a post-condition of a channel pass: every
-- non-empty task's current @est@ and @lst@ atoms are asserted true on the trail.
-- A violation means a bound move failed to reify\/assert its atom (a bug).
--
-- See Note [Upholding the citability invariant].
checkCitabilityInvariant
  :: forall mode s task t
  .  ( Num t, Measurable t, Bounded t )
  => TheoryState mode s task t -> String -> ST s ()
checkCitabilityInvariant t ctx = go 0
  where
    n = precedenceAtomsNumTasks ( atoms t )
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
      v <- SAT.litValue ( theorySolverState t ) lit
      when ( v /= LTrue ) $ do
        dump <- SAT.dumpSolverState ( theorySolverState t )
        error $ "Schedule.LCG.Theory.checkCitabilityInvariant [" <> ctx <> "]: task "
             <> show i <> "'s " <> which <> " bound atom " <> show lit <> " is " <> show v
             <> ", not LTrue (citability invariant violated)\n" <> dump

-- | Verify a conflict mentions at least one literal at the current decision level.
--
-- An empty body is a genuine ground-level inconsistency (handled by 'markFalse',
-- never passed to 'analyse') and is exempt.
debugAssertCurrentLevelLit
  :: forall s. Text -> SAT.SolverState s -> [ Lit ] -> ST s ()
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
