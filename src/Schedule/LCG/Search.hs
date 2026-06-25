{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE CPP                 #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions    #-}

-- | DPLL(T) search for the unary-scheduling problem.
--
-- Drives the search loop, interleaving the SAT core ("SAT.Solver") with the
-- scheduling theory ("Schedule.LCG.Theory") over a single shared trail, and
-- returns either a feasible schedule or a witness of infeasibility.
module Schedule.LCG.Search
  ( -- * Search driver
    SearchResult(..)
  , SearchStats(..)
  , lcgSearch
    -- * Options
  , SearchOptions(..)
  , defaultSearchOptions
  , TheoryOptions(..) -- re-export
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
import Schedule.LCG.FDS
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
  { -- | SAT-solver options.
    --
    -- TODO: currently IGNORED by 'lcgSearch'.
    optSolver     :: !SAT.SolverOptions
    -- | Theory-side options.
  , optTheoryOpts :: !TheoryOptions
  , -- | Base Luby restart window, in conflicts: the @k@-th window allows
    -- @optRestartUnit * 'SAT.Restart.luby' k@ conflicts before restarting to the
    -- ground level (keeping learnt clauses and the matured failure-directed
    -- ratings).
    --
    -- @<= 0@ disables restarts.
    optRestartUnit    :: !Int
  , -- | Strong-branching width: at the root of each restart, pre-evaluate this
    -- many best-rated precedence choices by probing both branches (FDS §6.3),
    -- maturing their ratings, shaving any infeasible branch, and pre-selecting
    -- the best-localRating branch. @<= 0@ disables strong branching.
    optStrongBranchWidth :: !Int
  }

defaultSearchOptions :: SearchOptions
defaultSearchOptions = SearchOptions
  { optSolver          = SAT.defaultOptions
  , optRestartUnit     = 100
  , optStrongBranchWidth = 8
  , optTheoryOpts =
      TheoryOptions
        { maxPropRounds = 1000
        , useBoundDecisions = True
        , useTheoryDecide = True
        }
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
  , -- | Instrumentation report.
    --
    -- Empty ('Schedule.Monitor.emptyReport') unless
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

{-# SPECIALISE lcgSearch @MonitoringOff #-}

-- | Run the DPLL(T) search over the given task data with the given
-- propagators.
--
-- Returns a 'SearchResult' containing either a feasible schedule or an
-- unsatisfiability witness, together with cumulative statistics.
lcgSearch
  :: forall mode taskData task t
  .  ( Real t, Num t, Measurable t, Bounded t
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
  theory <- newTheory @mode tis props ( optTheoryOpts opts )
  let solverState = theorySolverState theory

  -- Drive the DPLL(T) loop. Its first iteration runs the propagators on
  -- the starting state, seeding any unconditional inferences before the
  -- SAT core takes its first decision.
  finalVerdict <-
    driveLoop
      ( optRestartUnit opts )
      ( optStrongBranchWidth opts )
      theory

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

  cc <- SAT.numConflicts ( theorySolverState theory )
  dc <- SAT.numDecisions solverState
  lc <- SAT.numLearnts   solverState
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

-- | The outcome of one restart window.
data WindowResult
  = -- | A final verdict was reached inside the window.
    Solved !SAT.Verdict
  | -- | The window's conflict budget was spent; restart and open the next.
    Restart

{-# SPECIALISE driveLoop @MonitoringOff #-}

-- | The DPLL(T) loop proper, run as a sequence of Luby restart windows.
--
-- Each decision is failure-directed ('theoryDecide' over the structural atom
-- pool, falling through to VSIDS), and its measured reduction matures the branch
-- ratings: 'measureSpace' before the decision is its rating denominator, settled
-- against the post-propagation measure at the next decision ('settlePending') or
-- as a wipeout on conflict ('settleConflict'). Restarts let ratings matured deep
-- in the tree re-steer its top. With 'useTheoryDecide' off, the ratings stay
-- inert and the search is pure VSIDS.
driveLoop
  :: forall mode s task t
  .  ( Real t, Num t, Measurable t, Bounded t
     , Show t, Show task
     , MonitorMode mode
     )
  => Int -- ^ base Luby restart window, in conflicts (@<= 0@: no restarts)
  -> Int -- ^ strong-branching width (@<= 0@: no strong branching)
  -> TheoryState mode s task t
  -> ST s SAT.Verdict
driveLoop restartUnit strongWidth theoryState = driveRestarts 1
  where
    solverState :: SAT.SolverState s
    solverState = theorySolverState theoryState
    restartEnabled :: Bool
    restartEnabled = restartUnit > 0

    fdsEnabled :: Bool
    fdsEnabled = useTheoryDecide ( theoryOptions theoryState )

    -- Run window @k@; on a restart, roll back to ground and open window @k + 1@.
    driveRestarts :: Int -> ST s SAT.Verdict
    driveRestarts !k = do
      -- Strong branching + shaving at the root of each restart.
      sb <-
        if fdsEnabled && strongWidth > 0 && k > 1
        then strongBranch theoryState strongWidth
        else pure StrongBranchOk
      case sb of
        StrongBranchUnsat -> do
          SAT.markFalse solverState
          pure SAT.Unsat
        StrongBranchOk -> driveWindow k

    driveWindow :: Int -> ST s SAT.Verdict
    driveWindow !k = do
      let limit = restartUnit * Restart.luby k
      res <- searchWindow limit
      case res of
        Solved v -> pure v
        Restart  -> do
          -- Restart all the way to ground, keeping learnt clauses and the matured
          -- ratings. Guard the theory rollback: the triggering conflict may have
          -- already backjumped to ground (so there is no level to pop).
          cur <- SAT.currentLevel ( theorySolverState theoryState )
          when ( cur > SAT.GroundLevel ) do
            SAT.cancelUntil solverState SAT.GroundLevel
            popToLevel theoryState SAT.GroundLevel
          driveRestarts ( k + 1 )

    -- One restart window: the inner BCP/theory/decide loop, bounded by @limit@
    -- conflicts. @confs@ counts conflicts resolved in this window.
    searchWindow :: Int -> ST s WindowResult
    searchWindow !limit = step 0
      where
        step :: Int -> ST s WindowResult
        step !confs = do
          ok <- SAT.isOk solverState
          if not ok
          then pure ( Solved SAT.Unsat )
          else do
            -- 1. Binary Constraint Propagation
            mbConf <- withPhaseTiming ( monitor theoryState ) "BCP" ( SAT.propagate solverState )
            case mbConf of
              Just c  -> onConflict confs c
              Nothing -> do
                -- 2. Theory propagation.
                szBefore <- SAT.solverTrailSize solverState
                mbTConf <- theoryPropagate theoryState
                case mbTConf of
                  Just c  -> onConflict confs c
                  Nothing -> do
                    -- Theory may have marked the solver UNSAT directly on a
                    -- ground-level inconsistency; re-check 'isOk' before continuing.
                    okAfter <- SAT.isOk solverState
                    if not okAfter
                    then pure ( Solved SAT.Unsat )
                    else do
                      szAfter <- SAT.solverTrailSize solverState
                      if szAfter > szBefore
                      -- Theory pushed new literals — re-run BCP before deciding.
                      then step confs
                      else decideStep confs

        -- Pick the next decision (or stop if everything is assigned): the
        -- failure-directed heuristic gets first refusal, VSIDS picks when it
        -- abstains.
        decideStep :: Int -> ST s WindowResult
        decideStep !confs = do
#ifdef DEBUG
          -- Propagation has claimed a fixpoint with no conflict; before branching,
          -- assert a fresh full sweep agrees (no stranded propagator left work undone).
          debugAuditPropagationFixpoint theoryState
#endif
          -- The size of this node is both the post-propagation measure settling
          -- the decision that led here and the denominator of the decision taken
          -- now (measured once and reused).
          szNow <- if fdsEnabled then measureSpace theoryState else pure 0
          when fdsEnabled ( settlePending theoryState szNow )
          mbLit <- withPhaseTiming ( monitor theoryState ) "decide" do
            mbTheory <- theoryDecide theoryState
            case mbTheory of
              -- A theory-proposed branch is still a decision: count it so that
              -- 'numDecisions' reflects the full search-tree size.
              Just lit -> SAT.countDecision solverState *> pure ( Just lit )
              Nothing  -> SAT.decide solverState
          case mbLit of
            Nothing  -> pure ( Solved SAT.Sat )
            Just lit -> do
              when fdsEnabled ( noteDecision theoryState lit szNow )
              SAT.pushNewLevel solverState
              pushLevel theoryState
              SAT.enqueueUndef solverState lit RDecision
              step confs

        -- Common conflict-handling path (used for both BCP and theory conflicts).
        onConflict :: Int -> SAT.Conflict -> ST s WindowResult
        onConflict !confs c = do
          lvl <- SAT.currentLevel solverState
          if lvl == SAT.GroundLevel
          then do
            SAT.markFalse solverState
            pure ( Solved SAT.Unsat )
          else do
            -- Settle the pending decision as a wipeout (no-op when nothing is
            -- pending, e.g. with FDS off), then analyse/backjump/install/decay.
            settleConflict theoryState
            withPhaseTiming ( monitor theoryState ) "analysis"
              ( SAT.resolveConflict solverState c ( popToLevel theoryState ) )
            if restartEnabled && confs + 1 >= limit
            then pure Restart
            else step ( confs + 1 )
