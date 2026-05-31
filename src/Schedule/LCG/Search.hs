{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions    #-}

-- | DPLL(T) search for the unary-scheduling problem.
--
-- The search interleaves the SAT core ("SAT.Solver") with the scheduling
-- theory ("Schedule.LCG.Theory") over a single shared trail. SAT decisions
-- assign precedence atoms; the theory channels each assignment into the
-- ordering matrix and runs the scheduling propagators, promoting any
-- emitted precedence inferences back to the SAT trail as theory
-- propagations with lazy clausal reasons. Conflicts (cycles, overloads,
-- contradictions) flow through 1-UIP analysis, which learns a clause and
-- backjumps both the SAT trail and the schedule trail in lockstep.
module Schedule.LCG.Search
  ( -- * Search driver
    SearchResult(..)
  , SearchStats(..)
  , lcgSearch
    -- * Options
  , SearchOptions(..)
  , defaultSearchOptions
    -- * Building blocks (re-export of the inner pieces)
  , module Schedule.LCG.Theory
  , module Schedule.LCG.Atoms
  )
  where

-- base
import Control.Monad.ST
  ( ST, runST )

-- deepseq
import Control.DeepSeq
  ( NFData )

-- generics
import GHC.Generics
  ( Generic )

-- primitive
import Data.Primitive.MutVar
  ( readMutVar )

-- text
import Data.Text
  ( Text )

-- unary-scheduling
import Data.Vector.PhaseTransition
  ( Freeze(freeze) )
import SAT.Clause
  ( Reason(..) )
import qualified SAT.Solver as SAT
import Schedule.Interval
  ( Measurable )
import Schedule.LCG.Atoms
import Schedule.LCG.Theory
import Schedule.Monad
  ( SchedulableData
      ( initialTaskData )
  )
import Schedule.Monitor
  ( Monitoring(..), MonitorMode(..), MonitorReport )
import Schedule.Propagators
  ( Propagator )
import Schedule.Task
  ( ImmutableTaskInfos )

-------------------------------------------------------------------------------
-- Options.

-- | Options for 'lcgSearch'.
data SearchOptions = SearchOptions
  { -- | Maximum propagator-loop iterations per theory step.
    optPropRounds :: !Int
  , -- | SAT-solver options.
    --
    -- TODO: currently IGNORED by 'lcgSearch'.
    optSolver     :: !SAT.SolverOptions
  , -- | Channel propagator bound tightenings /out/ to bound atoms with tight
    -- local clausal reasons, and explain overloads\/emptied domains from those
    -- atoms (\"lazy clause generation\" proper). 'False' gives a coarse-reason
    -- baseline where every theory reason is the full trail snapshot. See
    -- "Schedule.LCG.Theory".
    optBoundAtoms :: !Bool
  , -- | Branch on /day-assignment/: seed, for each gappy task, a decision bound
    -- atom at every internal availability-gap boundary (\"does this task start
    -- by the end of day @j@?\"), prioritised so the search commits a task to a
    -- sub-interval before sequencing within it. 'False' gives a precedence-only
    -- baseline (for A\/B comparison). See "Schedule.LCG.Theory".
    optBoundDecisions :: !Bool
  , -- | Use the theory's structural decision heuristic ('theoryDecide') ahead of
    -- VSIDS.
    --
    -- Ensures we prioritise structural decisions to avoid VSIDS hijacking.
    optTheoryDecide   :: !Bool
  }

defaultSearchOptions :: SearchOptions
defaultSearchOptions = SearchOptions
  { optPropRounds     = 1000
  , optSolver         = SAT.defaultOptions
  , optBoundAtoms     = True
  , optBoundDecisions = True
  , optTheoryDecide   = True
  }

-------------------------------------------------------------------------------
-- Results.

-- | The outcome of a single search invocation.
data SearchResult task t = SearchResult
  { -- | Either an explanation of unsatisfiability, or the final task state
    -- of a feasible schedule (every precedence pair decided).
    --
    -- 'Right' carries the immutable snapshot of the scheduler state at the
    -- moment the SAT core reported @Sat@.
    solution :: !( Either Text ( ImmutableTaskInfos task t ) )
  , -- | Cumulative search statistics.
    stats    :: !SearchStats
  , -- | Instrumentation report. Empty ('Schedule.Monitor.emptyReport') unless
    -- the search was run at @mode ~ 'Schedule.Monitor.MonitoringOn'@.
    monitorReport :: !MonitorReport
  }
  deriving stock    ( Generic )
  deriving anyclass NFData

deriving stock instance
  ( Show task, Show t
  ) => Show ( SearchResult task t )

-- | Cumulative counters reported by 'lcgSearch'.
data SearchStats = SearchStats
  { numConflicts :: !Int
  , numDecisions :: !Int
  , numLearnts   :: !Int
  , numTheoryPropagations :: !Int
  }
  deriving stock    ( Show, Generic )
  deriving anyclass NFData

-------------------------------------------------------------------------------
-- Search driver.

{-# INLINABLE lcgSearch #-}
{-# SPECIALISE lcgSearch @MonitoringOff #-}

-- | Run the DPLL(T) search over the given task data with the given
-- propagators.
--
-- Returns a 'SearchResult' containing either a feasible schedule or an
-- unsatisfiability witness, together with cumulative statistics.
lcgSearch
  :: forall mode taskData task t
  .  ( Num t, Measurable t, Bounded t
     , Show t, Show task
     , SchedulableData taskData task t
     , MonitorMode mode
     )
  => SearchOptions
  -> [ Propagator task t ]
  -> taskData
  -> SearchResult task t
lcgSearch opts props givenTasks = runST do
  -- Allocate scheduler state and theory in one go.
  tis    <- initialTaskData @taskData @task @t givenTasks
  theory <- newTheory @mode tis props ( optPropRounds opts )
              ( optBoundAtoms opts ) ( optBoundDecisions opts ) ( optTheoryDecide opts )

  -- Drive the DPLL(T) loop. Its first iteration runs the propagators on
  -- the starting state, seeding any unconditional inferences before the
  -- SAT core takes its first decision.
  finalVerdict <- driveLoop ( solver theory ) theory

  -- Build the result.
  mbSolution <- case finalVerdict of
    SAT.Sat     ->
      -- TODO: this is not a verified concrete schedule.
      -- Feasibility relies on completeness of the propagators (e.g. a fully-decided
      -- acyclic tournament with no overload always admits a schedule).
      --
      -- We should extract a greedy earliest-start schedule and check it is
      -- indeed a valid schedule.
      Right <$> freeze tis
    SAT.Unsat   -> pure ( Left "unary-scheduling: instance is infeasible" )
    SAT.Unknown ->
      -- TODO: driveLoop never reports 'Unknown' at the moment.
      pure ( Left "unary-scheduling: search budget exhausted" )

  cc <- SAT.numConflicts ( solver theory )
  dc <- SAT.numDecisions ( solver theory )
  lc <- SAT.numLearnts   ( solver theory )
  tp <- readMutVar ( theoryPropCount theory )
  let !stats0 = SearchStats
        { numConflicts          = cc
        , numDecisions          = dc
        , numLearnts            = lc
        , numTheoryPropagations = tp
        }
  report <- readReport ( monitor theory )
  pure SearchResult
    { solution      = mbSolution
    , stats         = stats0
    , monitorReport = report
    }

{-# INLINABLE driveLoop #-}
{-# SPECIALISE driveLoop @MonitoringOff #-}

-- | The DPLL(T) loop proper.
driveLoop
  :: forall mode s task t
  .  ( Num t, Measurable t, Bounded t
     , Show t, Show task
     , MonitorMode mode
     )
  => SAT.Solver s
  -> Theory mode s task t
  -> ST s SAT.Verdict
driveLoop solver theory = step
  -- NB: Conflict bookkeeping (counters, VSIDS decay) and the
  -- analyse/backjump/install sequence are shared with 'SAT.solveWith' via
  -- 'SAT.resolveConflict' and 'SAT.decide', but there is still some drift
  -- in implementations because we are missing a restart schedule and conflict
  -- budget, so 'SAT.Unknown' is never produced and 'optSolver' is ignored
  -- entirely.
  --
  -- TODO: solve this in a way that doesn't introduce two different codepaths
  -- that can keep drifting out-of-sync.

  where
    step :: ST s SAT.Verdict
    step = do
      ok <- SAT.isOk solver
      if not ok
      then pure SAT.Unsat
      else do
        -- 1. Binary Constraint Propagation
        mbConf <- SAT.propagate solver
        case mbConf of
          Just c  -> handleConflict c
          Nothing -> do
            -- 2. Theory propagation.
            szBefore <- SAT.trailSize solver
            mbTConf <- theoryPropagate theory
            case mbTConf of
              Just c  -> handleConflict c
              Nothing -> do
                -- Theory may have marked the solver UNSAT via a ground-level
                -- snapshot conflict; re-check 'isOk' before continuing.
                okAfter <- SAT.isOk solver
                if not okAfter
                then pure SAT.Unsat
                else do
                  szAfter <- SAT.trailSize solver
                  if szAfter > szBefore
                  -- Theory pushed new literals — re-run BCP before deciding.
                  then step
                  else decideStep

    -- Pick the next decision (or stop if everything is assigned). The theory's
    -- structural heuristic gets first refusal ('theoryDecide'); when it abstains
    -- the VSIDS heuristic ('SAT.decide') picks the literal.
    decideStep :: ST s SAT.Verdict
    decideStep = do
      mbTheory <- theoryDecide theory
      mbLit <- case mbTheory of
        -- A theory-proposed branch is still a decision: count it so that
        -- 'numDecisions' reflects the full search-tree size.
        Just lit -> SAT.countDecision solver *> pure ( Just lit )
        Nothing  -> SAT.decide solver
      case mbLit of
        Nothing  -> pure SAT.Sat
        Just lit -> do
          SAT.pushNewLevel solver
          pushLevel theory
          SAT.enqueueUndef solver lit RDecision
          step

    -- Common conflict-handling path (used for both BCP and theory conflicts).
    handleConflict :: SAT.Conflict -> ST s SAT.Verdict
    handleConflict c = do
      lvl <- SAT.currentLevel solver
      if lvl == SAT.GroundLevel
      then do
        SAT.markFalse solver
        pure SAT.Unsat
      else do
        SAT.resolveConflict solver c ( popToLevel theory )
        step
