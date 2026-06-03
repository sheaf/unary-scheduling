{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE CPP                 #-}
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
import Control.Monad
  ( when )
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
import qualified SAT.Restart as Restart
  ( luby )
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
  , -- | Branch on /day-assignment/: seed, for each gappy task, a decision bound
    -- atom at every internal availability-gap boundary (\"does this task start
    -- by the end of day @j@?\"), prioritised so the search commits a task to a
    -- sub-interval before sequencing within it. 'False' gives a precedence-only
    -- baseline (for A\/B comparison). See "Schedule.LCG.Theory".
    optBoundDecisions :: !Bool
  , -- | Use the theory's structural decision heuristic ('theoryDecide') in
    -- /structural/ search windows. With 'optAlternateSearch' on, structural and
    -- VSIDS windows alternate (see 'optRestartUnit'); with it off, every window
    -- is structural. 'False' disables the structural heuristic entirely (pure
    -- VSIDS), regardless of 'optAlternateSearch'.
    optTheoryDecide   :: !Bool
  , -- | Base Luby restart window, in conflicts: the @k@-th window allows
    -- @optRestartUnit * 'SAT.Restart.luby' k@ conflicts before restarting to the
    -- ground level (keeping learnt clauses). @<= 0@ disables restarts — a single
    -- unbounded window, so the search never alternates off its first mode.
    --
    -- The Luby schedule makes this scale-free: there is no constant tied to the
    -- problem size, and the window count (not a decision count) is what drives
    -- the structural↔VSIDS alternation.
    optRestartUnit    :: !Int
  , -- | Alternate the decision strategy between restart windows: the first
    -- window is structural (good at /finding/ a schedule), the next is VSIDS
    -- (good at /proving/ infeasibility), and so on. This is how conflict-driven
    -- learning regains control of the search order without a hard, size-blind
    -- handoff. Only meaningful with 'optTheoryDecide' on; 'False' keeps every
    -- window on the structural heuristic.
    --
    -- A feasible instance that the structural dive cracks within the first
    -- window never reaches a VSIDS window, so it is unaffected.
    optAlternateSearch :: !Bool
  , -- | Apply conflict-ordering search within the structural heuristic
    -- ('Schedule.LCG.Theory.theoryDecide'): revisit the decision variable most
    -- recently found to be a conflict culprit before resuming the base
    -- (day-first-fail + critical-pair) order. Folds conflict information into the
    -- structural search so it stops re-diving into the same dead ends. Only
    -- meaningful with 'optTheoryDecide' on; inert until the first conflict, so it
    -- never perturbs an instance the structural dive solves cleanly.
    --
    -- Off by default: measurement shows it is a strong win on bin-packing
    -- fragmentation (copies=2: 145 → 36 conflicts) but a ~2x regression on
    -- structural-friendly UNSAT instances (interval pigeonhole: 19 → 36
    -- conflicts), where its culprit-reordering disrupts the critical-pair order.
    -- Available as an opt-in pending a gentler integration (e.g. last-conflict
    -- only, or conflict-ordering restricted to precedence sequencing).
    optConflictOrdering :: !Bool
  }

defaultSearchOptions :: SearchOptions
defaultSearchOptions = SearchOptions
  { optPropRounds     = 1000
  , optSolver         = SAT.defaultOptions
  , optBoundDecisions = True
  , optTheoryDecide   = True
  , optRestartUnit    = 100
  , optAlternateSearch = True
  , optConflictOrdering = False
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
  , -- | Lazy reasons forced by 1-UIP.
    numLazyForces    :: !Int
    -- | Total literals returned by lazy reasons forced by 1-UIP.
  , numLazyForceLits :: !Int
  }
  deriving stock    ( Show, Generic )
  deriving anyclass NFData

-------------------------------------------------------------------------------
-- Search driver.

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
              ( optBoundDecisions opts )
              ( optTheoryDecide opts ) ( optConflictOrdering opts )

  -- Drive the DPLL(T) loop. Its first iteration runs the propagators on
  -- the starting state, seeding any unconditional inferences before the
  -- SAT core takes its first decision.
  finalVerdict <- driveLoop ( optRestartUnit opts ) ( optAlternateSearch opts )
                    ( solver theory ) theory

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
  lf <- SAT.numLazyForces    ( solver theory )
  ll <- SAT.numLazyForceLits ( solver theory )
  let !stats0 = SearchStats
        { numConflicts          = cc
        , numDecisions          = dc
        , numLearnts            = lc
        , numTheoryPropagations = tp
        , numLazyForces         = lf
        , numLazyForceLits      = ll
        }
  report <- readReport ( monitor theory )
  pure SearchResult
    { solution      = mbSolution
    , stats         = stats0
    , monitorReport = report
    }

-- | Which decision strategy drives the current restart window.
data SearchMode
  = -- | The theory's structural heuristic ('theoryDecide') gets first refusal;
    -- VSIDS only picks when it abstains. Good at /finding/ a schedule.
    Structural
  | -- | VSIDS alone. Good at /proving/ infeasibility (conflict-driven learning
    -- steers the order).
    Activity
  deriving stock Eq

-- | The outcome of one restart window.
data WindowResult
  = -- | A final verdict was reached inside the window.
    Solved !SAT.Verdict
  | -- | The window's conflict budget was spent; restart and open the next.
    Restart

{-# SPECIALISE driveLoop @MonitoringOff #-}

-- | The DPLL(T) loop proper, run as a sequence of Luby restart windows that
-- alternate the decision strategy (see 'SearchMode').
driveLoop
  :: forall mode s task t
  .  ( Num t, Measurable t, Bounded t
     , Show t, Show task
     , MonitorMode mode
     )
  => Int                      -- ^ base Luby restart window, in conflicts (@<= 0@: no restarts)
  -> Bool                     -- ^ alternate structural / VSIDS between windows
  -> SAT.Solver s
  -> Theory mode s task t
  -> ST s SAT.Verdict
driveLoop restartUnit alternate solver theory =
  driveRestarts 1 initialMode
  where
    restartEnabled :: Bool
    restartEnabled = restartUnit > 0

    -- The structural heuristic only runs when enabled; otherwise every window
    -- is pure VSIDS.
    initialMode :: SearchMode
    initialMode = if useTheoryDecide theory then Structural else Activity

    -- Flip the mode for the next window, but only when both alternation and the
    -- structural heuristic are on; otherwise every window keeps 'initialMode'.
    nextMode :: SearchMode -> SearchMode
    nextMode m
      | alternate && useTheoryDecide theory = case m of Structural -> Activity; Activity -> Structural
      | otherwise                           = m

    -- Run window @k@; on a restart, roll back to ground and open window @k + 1@.
    driveRestarts :: Int -> SearchMode -> ST s SAT.Verdict
    driveRestarts !k mode = do
      let limit = restartUnit * Restart.luby k
      res <- searchWindow limit mode
      case res of
        Solved v -> pure v
        Restart  -> do
          -- Restart all the way to ground, keeping learnt clauses. Guard the
          -- theory rollback: the triggering conflict may have already backjumped
          -- to ground (so there is no level to pop).
          cur <- SAT.currentLevel solver
          when ( cur > SAT.GroundLevel ) do
            SAT.cancelUntil solver SAT.GroundLevel
            popToLevel theory SAT.GroundLevel
          driveRestarts ( k + 1 ) ( nextMode mode )

    -- One restart window: the inner BCP/theory/decide loop, bounded by @limit@
    -- conflicts. @confs@ counts conflicts resolved in this window.
    searchWindow :: Int -> SearchMode -> ST s WindowResult
    searchWindow !limit mode = step 0
      where
        step :: Int -> ST s WindowResult
        step !confs = do
          ok <- SAT.isOk solver
          if not ok
          then pure ( Solved SAT.Unsat )
          else do
            -- 1. Binary Constraint Propagation
            mbConf <- withPhaseTiming ( monitor theory ) "BCP" ( SAT.propagate solver )
            case mbConf of
              Just c  -> onConflict confs c
              Nothing -> do
                -- 2. Theory propagation.
                szBefore <- SAT.trailSize solver
                mbTConf <- theoryPropagate theory
                case mbTConf of
                  Just c  -> onConflict confs c
                  Nothing -> do
                    -- Theory may have marked the solver UNSAT via a ground-level
                    -- snapshot conflict; re-check 'isOk' before continuing.
                    okAfter <- SAT.isOk solver
                    if not okAfter
                    then pure ( Solved SAT.Unsat )
                    else do
                      szAfter <- SAT.trailSize solver
                      if szAfter > szBefore
                      -- Theory pushed new literals — re-run BCP before deciding.
                      then step confs
                      else decideStep confs

        -- Pick the next decision (or stop if everything is assigned). In a
        -- 'Structural' window the theory heuristic gets first refusal and VSIDS
        -- picks only when it abstains; in an 'Activity' window VSIDS drives.
        decideStep :: Int -> ST s WindowResult
        decideStep !confs = do
#ifdef DEBUG
          -- Propagation has claimed a fixpoint with no conflict; before branching,
          -- assert a fresh full sweep agrees (no stranded propagator left work undone).
          debugAuditPropagationFixpoint theory
#endif
          mbLit <- withPhaseTiming ( monitor theory ) "decide" do
            mbTheory <- case mode of
              Structural -> theoryDecide theory
              Activity   -> pure Nothing
            case mbTheory of
              -- A theory-proposed branch is still a decision: count it so that
              -- 'numDecisions' reflects the full search-tree size.
              Just lit -> SAT.countDecision solver *> pure ( Just lit )
              Nothing  -> SAT.decide solver
          case mbLit of
            Nothing  -> pure ( Solved SAT.Sat )
            Just lit -> do
              -- Remember the culprit for conflict-ordering (no-op when off).
              noteDecision theory lit
              SAT.pushNewLevel solver
              pushLevel theory
              SAT.enqueueUndef solver lit RDecision
              step confs

        -- Common conflict-handling path (used for both BCP and theory conflicts).
        onConflict :: Int -> SAT.Conflict -> ST s WindowResult
        onConflict !confs c = do
          lvl <- SAT.currentLevel solver
          if lvl == SAT.GroundLevel
          then do
            SAT.markFalse solver
            pure ( Solved SAT.Unsat )
          else do
            -- Stamp the culprit for conflict-ordering (no-op when off), then
            -- analyse/backjump/install/decay.
            recordConflict theory
            withPhaseTiming ( monitor theory ) "analysis"
              ( SAT.resolveConflict solver c ( popToLevel theory ) )
            if restartEnabled && confs + 1 >= limit
            then pure Restart
            else step ( confs + 1 )
