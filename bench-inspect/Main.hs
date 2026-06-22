{-# OPTIONS_GHC -fno-full-laziness #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

-- | A self-contained harness that runs scheduling benchmarks through the LCG
-- search and reports /search-tree size/ (decisions, conflicts, learnt clauses,
-- theory propagations) alongside wall-clock time. Two views:
--
--   * an A\/B matrix over different parameter choices
--
--   * a size sweep over the benchmark instance families, reporting the node
--     counts (not just time) that show whether the cost is the search tree.
--
-- For profiling, Core dumps, and gauging where the milestones move the numbers.
module Main ( main ) where

-- base
import Control.Exception
  ( SomeException, evaluate, try )
import Control.Monad
  ( forM, forM_ )
import Data.Word
  ( Word64 )
import GHC.Clock
  ( getMonotonicTimeNSec )
import System.Environment
  ( getArgs )
import System.Timeout
  ( timeout )
import Text.Printf
  ( printf )

-- code-page
import System.IO.CodePage
  ( withCP65001 )

-- containers
import qualified Data.Map.Strict as Map
  ( findWithDefault )

-- deepseq
import Control.DeepSeq
  ( force )

-- unary-scheduling
import Schedule.LCG.Search
  ( SearchResult(..), SearchStats(..), SearchOptions(..)
  , defaultSearchOptions, lcgSearch, TheoryOptions (..)
  )
import Schedule.Monitor
  ( Monitoring(..), MonitorReport(..), renderReport )
import Schedule.Propagators
  ( Propagator, basicPropagators
  , prunePropagator, timetablePropagator, overloadPropagator
  , detectablePrecedencesPropagator, detectableSuccedencesPropagator
  , notLastPropagator, notFirstPropagator
  , edgeLastPropagator, edgeFirstPropagator
  , predecessorPropagator, successorPropagator
  )

-- bench:unary-scheduling
import Schedule.Bench.Instances
  ( BenchTime, Instance )
import qualified Schedule.Bench.Instances as Instances

-------------------------------------------------------------------------------
-- Configuration under test.

-- | The fixed instance for the A\/B matrix. A near-boundary feasible rehearsal
-- that /forces conflicts/, so the decision-strategy knobs (FDS vs VSIDS,
-- interval-commitment, restarts) actually diverge — a slacker instance solves at
-- 0 conflicts and makes every configuration identical.
theInstance :: Instance
theInstance = Instances.rehearsalInstance 1.0 0.4 6 24 8 9

instanceLabel :: String
instanceLabel = "rehearsalInstance util=1.0 avail=0.4 days=6 songs=24 maxDur=8 seed=9 (forces conflicts)"

-- | Timing iterations (per-run statistics are deterministic and measured once;
-- only the wall-clock minimum is repeated).
iterations :: Int
iterations = 1
{-# NOINLINE iterations #-}

-- | A named search configuration.
data Cfg = Cfg
  { cfgLabel :: !String
  , cfgOpts  :: !SearchOptions
  }

-- | Decision-strategy configurations.
abConfigs :: [ Cfg ]
abConfigs =
  [ Cfg "FDS (default)"     base
  , Cfg "FDS no-restart"    $ base { optRestartUnit = 0 }
  , Cfg "FDS no-interval"   $ setBoundDecisions False base
  , Cfg "VSIDS only"        $ setDecide False base
  ]
  where

    base = defaultSearchOptions

setDecide, setBoundDecisions :: Bool -> SearchOptions -> SearchOptions
setDecide b opts = opts { optTheoryOpts = ( optTheoryOpts opts ) { useTheoryDecide = b } }
setBoundDecisions b opts = opts { optTheoryOpts = ( optTheoryOpts opts ) { useBoundDecisions = b } }

-------------------------------------------------------------------------------
-- Measurement.

-- | Run one configuration, returning the minimum wall-clock over 'iterations'
-- (from the uninstrumented path) and one instrumented (deterministic) result.
measure :: SearchOptions -> Instance -> IO ( Word64, SearchResult () BenchTime )
measure opts inst = do
  times <- forM [ 1 .. iterations ] \ _ -> do
    t0 <- getMonotonicTimeNSec
    _  <- evaluate ( force ( lcgSearch @MonitoringOff opts basicPropagators inst ) )
    t1 <- getMonotonicTimeNSec
    pure ( t1 - t0 )
  instr <- evaluate ( force ( lcgSearch @MonitoringOn opts basicPropagators inst ) )
  pure ( minimum times, instr )

-- | Like 'measure', but the returned result is from the uninstrumented run, so
-- no second (potentially very slow) instrumented solve is paid. The 'stats' and
-- 'verdict' are still exact; only the detailed 'monitorReport' is empty. Used for
-- the A\/B matrix rows, whose columns are all in 'stats'.
measureOff :: SearchOptions -> Instance -> IO ( Word64, SearchResult () BenchTime )
measureOff opts inst = do
  let solve = evaluate ( force ( lcgSearch @MonitoringOff opts basicPropagators inst ) )
  -- Time each of 'iterations' solves (the result is deterministic; keep the
  -- first). One solve when iterations == 1 — important for the slow configs.
  runs <- forM [ 1 .. iterations ] \ _ -> do
    t0 <- getMonotonicTimeNSec
    r  <- solve
    t1 <- getMonotonicTimeNSec
    pure ( t1 - t0, r )
  case runs of
    ( ( _, r0 ) : _ ) -> pure ( minimum ( map fst runs ), r0 )
    []                -> error "measureOff: iterations must be >= 1"

-------------------------------------------------------------------------------

main :: IO ()
main = withCP65001 do
  args <- getArgs
  case args of
    -- Focused profiling entry point: solve a single named anchor instance once,
    -- on the real (uninstrumented) default-config path, so a cost-centre profile
    -- is attributable to that one workload. Usage: lcg-inspect prof <name>.
    ( "prof" : rest ) -> mapM_ profRun ( if null rest then [ "d6s24", "copies2" ] else rest )
    ( "exp" : _ )     -> propagatorSubsetExperiment
    ( "opts" : _ )    -> optionToggleExperiment
    ( "lazy" : _ )    -> lazyReasonReport
    _ -> do
      _ <- evaluate ( force theInstance )
      printf "=== unary-scheduling LCG inspection harness ===\n\n"

      abMatrix
      putStrLn ""
      sizeSweeps

-- | Select among some representative instances for a profiling run.
profInstance :: String -> Instance
profInstance "d6s24"   = Instances.rehearsalInstance 1.0 0.4 6 24 8 9
profInstance "copies2" = Instances.infeasibleRehearsalInstance 2
profInstance other     = error ( "lcg-inspect prof: unknown instance " ++ show other )

-- | Solve one anchor instance once, on the uninstrumented default path, forcing
-- the result. Prints the node counts so the profile can be read against them.
profRun :: String -> IO ()
profRun name = do
  let inst = profInstance name
  _   <- evaluate ( force inst )
  t0  <- getMonotonicTimeNSec
  res <- evaluate ( force ( lcgSearch @MonitoringOff defaultSearchOptions basicPropagators inst ) )
  t1  <- getMonotonicTimeNSec
  let st = stats res
  printf "%-8s %-11s %-11s dec=%d conf=%d learnt=%d tprop=%d\n"
    name ( fmtNs ( t1 - t0 ) ) ( verdict res )
    ( numDecisions st ) ( numConflicts st ) ( numLearnts st ) ( numTheoryPropagations st )

-- | Two views of the lazy-reason machinery across representative instances, from
-- one 'MonitoringOn' solve each (the counters\/timers are zero-cost and absent
-- otherwise):
--
--   * /utilisation/ — of the deferred theory-propagation reasons /recorded/, how
--     many are ever actually /forced/ by conflict analysis, and the re-force
--     factor. This is the waste that deferring reason construction (Design B)
--     would reclaim; the counts are exact and meaningful even on small instances.
--
--   * /phase breakdown/ — what share of wall-clock the explanation machinery
--     costs ("channel-out" builds the reasons, "capture" is the eager pre-pass
--     snapshot), sizing the pie Design B draws from. Both nest inside
--     "propagators"; wall-clock has noise, so read only the rows whose solve is
--     well above a millisecond (the larger infeasible ones).
lazyReasonReport :: IO ()
lazyReasonReport = do
  results <- forM lazyInstances \ ( iname, inst ) -> do
    _   <- evaluate ( force inst )
    t0  <- getMonotonicTimeNSec
    rep <- evaluate ( force ( lcgSearch @MonitoringOn defaultSearchOptions basicPropagators inst ) )
    t1  <- getMonotonicTimeNSec
    pure ( iname, t1 - t0, rep )

  printf "Lazy-reason utilisation (recorded = deferred theory props; forced = used by 1-UIP/minimise):\n\n"
  printf "  %-22s %-11s %8s %8s %7s %8s %8s %8s\n"
    ( "instance" :: String ) ( "verdict" :: String )
    ( "recorded" :: String ) ( "forced" :: String ) ( "used%" :: String )
    ( "calls" :: String ) ( "reforce" :: String ) ( "meanLen" :: String )
  forM_ results \ ( iname, _t, rep ) -> do
    let m     = monitorReport rep
        recd  = lazyRecorded m
        dist  = lazyForceDistinct m
        calls = lazyForceCalls m
        lits  = lazyForceLits m
    printf "  %-22s %-11s %8d %8d %6.1f%% %8d %7.2fx %8.1f\n"
      iname ( verdict rep ) recd dist ( 100 * ratio dist recd )
      calls ( ratio calls dist ) ( ratio lits calls )
  putStrLn ""

  printf "Phase breakdown (%% of instrumented wall-clock).\n"
  printf "  capture/chanOut are SUB-phases of prop (already in prop%%); fixpoint = prop - capture - chanOut.\n"
  printf "  Read sub-phases as an UPPER bound; never add them to prop%%.\n\n"
  printf "  %-22s %-10s %7s %9s %11s %10s %7s %10s\n"
    ( "instance" :: String ) ( "time" :: String ) ( "prop%" :: String )
    ( "·capture%" :: String ) ( "·chanOut%" :: String ) ( "·fixpoint%" :: String )
    ( "BCP%" :: String ) ( "analysis%" :: String )
  forM_ results \ ( iname, total, rep ) -> do
    let m       = monitorReport rep
        ph name = fromIntegral ( Map.findWithDefault 0 name ( phaseTime m ) ) :: Double
        pct ns  = if total == 0 then 0 else 100 * ns / fromIntegral total
        prop    = ph "propagators"
        capt    = ph "propagators/capture"
        chanOut = ph "propagators/channel-out"
    printf "  %-22s %-10s %6.0f%% %8.0f%% %10.0f%% %9.0f%% %6.0f%% %9.0f%%\n"
      iname ( fmtNs total )
      ( pct prop ) ( pct capt ) ( pct chanOut ) ( pct ( prop - capt - chanOut ) )
      ( pct ( ph "BCP" ) ) ( pct ( ph "analysis" ) )
  putStrLn ""
  where
    ratio :: Int -> Int -> Double
    ratio a b = if b == 0 then 0 else fromIntegral a / fromIntegral b
    lazyInstances :: [ ( String, Instance ) ]
    lazyInstances =
      [ ( "d6s24 (feasible)",     profInstance "d6s24" )
      , ( "reh tight 5x20/3",     Instances.rehearsalInstance 1.0 0.4 5 20 8 3 )
      , ( "bin copies1 (inf)",    Instances.infeasibleRehearsalInstance 1 )
      , ( "bin copies2 (inf)",    profInstance "copies2" )
      , ( "bin copies3 (inf)",    Instances.infeasibleRehearsalInstance 3 )
      , ( "bin copies4 (inf)",    Instances.infeasibleRehearsalInstance 4 )
      , ( "pigeonhole m=5 (inf)", Instances.intervalPigeonholeInstance 5 2 )
      , ( "pigeonhole m=6 (inf)", Instances.intervalPigeonholeInstance 6 2 )
      ]

-- | Measure how much each (group of) expensive global propagator earns its
-- keep.
propagatorSubsetExperiment :: IO ()
propagatorSubsetExperiment = do
  printf "Propagator-subset experiment (verdict must not change vs full; per-solve timeout 8s):\n\n"
  forM_ instances \ ( iname, inst ) -> do
    _ <- evaluate ( force inst )
    printf "%s:\n" iname
    printf "  %-12s %-11s %6s %6s %7s %-10s\n"
      ( "config" :: String ) ( "time" :: String )
      ( "dec" :: String ) ( "conf" :: String ) ( "tprop" :: String ) ( "verdict" :: String )
    forM_ subsets \ ( label, props ) -> do
      t0  <- getMonotonicTimeNSec
      mbRes <- timeout 8_000_000 ( evaluate ( force ( lcgSearch @MonitoringOff defaultSearchOptions props inst ) ) )
      t1  <- getMonotonicTimeNSec
      case mbRes of
        Nothing  -> printf "  %-12s %-11s %6s %6s %7s %-10s\n" label ( "TIMEOUT" :: String ) ( "-" :: String ) ( "-" :: String ) ( "-" :: String ) ( "-" :: String )
        Just res -> do
          let st = stats res
          printf "  %-12s %-11s %6d %6d %7d %-10s\n"
            label ( fmtNs ( t1 - t0 ) )
            ( numDecisions st ) ( numConflicts st ) ( numTheoryPropagations st )
            ( verdict res )
    putStrLn ""
  where
    instances :: [ ( String, Instance ) ]
    instances =
      -- Feasible rehearsal, slack (0.9 / 0.6), several sizes & seeds.
      [ ( "reh slack 3x9",    Instances.rehearsalInstance 0.9 0.6 3 9  8 42 )
      , ( "reh slack 5x15",   Instances.rehearsalInstance 0.9 0.6 5 15 8 42 )
      , ( "reh slack 5x20",   Instances.rehearsalInstance 0.9 0.6 5 20 8 42 )
      , ( "reh slack 5x20/7", Instances.rehearsalInstance 0.9 0.6 5 20 8 7  )
      -- Feasible rehearsal, tight (1.0 / 0.4), forces backtracking.
      , ( "reh tight 4x16/5", Instances.rehearsalInstance 1.0 0.4 4 16 8 5  )
      , ( "reh tight 5x20/3", Instances.rehearsalInstance 1.0 0.4 5 20 8 3  )
      , ( "reh tight 6x24/9", profInstance "d6s24" )
      , ( "reh tight 6x24/1", Instances.rehearsalInstance 1.0 0.4 6 24 8 1  )
      -- Feasible staggered windows.
      , ( "windows n=12",     Instances.randomWindowedInstance 0.7 4 12 3 42 )
      , ( "windows n=16",     Instances.randomWindowedInstance 0.7 4 16 3 42 )
      -- Feasible disjunctive cliques.
      , ( "clique n=8",       Instances.tightCliqueInstance 8  2 )
      , ( "clique n=12",      Instances.tightCliqueInstance 12 2 )
      , ( "clique n=16",      Instances.tightCliqueInstance 16 2 )
      -- Infeasible: interval pigeonhole.
      , ( "pigeonhole m=4",   Instances.intervalPigeonholeInstance 4 2 )
      , ( "pigeonhole m=5",   Instances.intervalPigeonholeInstance 5 2 )
      , ( "pigeonhole m=6",   Instances.intervalPigeonholeInstance 6 2 )
      -- Infeasible: bin-packing fragmentation (symmetric copies).
      , ( "bin copies1",      Instances.infeasibleRehearsalInstance 1 )
      , ( "bin copies2",      profInstance "copies2" )
      , ( "bin copies3",      Instances.infeasibleRehearsalInstance 3 )
      -- Infeasible: heterogeneous (asymmetric) fragmentation.
      , ( "frag [6789]/3",    Instances.fragmentationInstance [ 6, 7, 8, 9 ] 3 )
      , ( "frag [678910]/4",  Instances.fragmentationInstance [ 6, 7, 8, 9, 10 ] 4 )
      , ( "frag [667789]/5",  Instances.fragmentationInstance [ 6, 6, 7, 7, 8, 9 ] 5 )
      -- Infeasible: resource overload.
      , ( "overload n=12",    Instances.overloadedInstance 12 3 )
      , ( "overload n=16",    Instances.overloadedInstance 16 3 )
      ]
    -- The local + completeness propagators that every subset keeps.
    base, detect, notExt, edge :: [ Propagator () BenchTime ]
    base = [ prunePropagator, timetablePropagator, overloadPropagator
           , predecessorPropagator, successorPropagator ]
    detect = [ detectablePrecedencesPropagator, detectableSuccedencesPropagator ]
    notExt = [ notLastPropagator, notFirstPropagator ]
    edge   = [ edgeLastPropagator, edgeFirstPropagator ]
    subsets :: [ ( String, [ Propagator () BenchTime ] ) ]
    subsets =
      [ ( "full",        basicPropagators )
      , ( "no-detect",   base ++ notExt ++ edge )
      , ( "no-edge",     base ++ detect ++ notExt )
      , ( "no-notExtr",  base ++ detect ++ edge )
      , ( "base-only",   base )
      ]

-- | Sweep the search-option toggles across the representative instance families,
-- to tell an instance-specific win from a broad one (guards against tuning to a
-- single hand-picked instance). Columns: default, interval commitment branching off,
-- channel-out learning off.
optionToggleExperiment :: IO ()
optionToggleExperiment = do
  printf "Option-toggle sweep (time / dec / conf / tprop; verdict must not change):\n\n"
  printf "  %-22s %-22s %-22s\n"
    ( "instance" :: String ) ( "default" :: String )
    ( "no-interval-commitment" :: String )
  forM_ optInstances \ ( iname, inst ) -> do
    _ <- evaluate ( force inst )
    cells <- forM optConfigs \ ( _, opts ) -> do
      ( t, res ) <- measureOff opts inst
      let st = stats res
      pure ( verdict res
           , printf "%s/%d/%d/%d" ( fmtNs t )
               ( numDecisions st ) ( numConflicts st ) ( numTheoryPropagations st ) :: String )
    let verdicts = map fst cells
        tag = case verdicts of
          ( v0 : _ ) | all ( == v0 ) verdicts -> ""
          _                                    -> "  DISAGREE " ++ show verdicts
    printf "  %-22s" iname
    forM_ cells \ ( _, c ) -> printf " %-22s" c
    printf "%s\n" tag
  where
    optConfigs :: [ ( String, SearchOptions ) ]
    optConfigs =
      [ ( "default"               , defaultSearchOptions )
      , ( "no-interval-commitment", setBoundDecisions False $ defaultSearchOptions )
      ]
    optInstances :: [ ( String, Instance ) ]
    optInstances =
      [ ( "reh tight 4x16/5",  Instances.rehearsalInstance 1.0 0.4 4 16 8 5 )
      , ( "reh tight 5x20/3",  Instances.rehearsalInstance 1.0 0.4 5 20 8 3 )
      , ( "reh tight 6x24/9",  Instances.rehearsalInstance 1.0 0.4 6 24 8 9 )
      , ( "reh tight 6x24/1",  Instances.rehearsalInstance 1.0 0.4 6 24 8 1 )
      , ( "reh slack 5x20",    Instances.rehearsalInstance 0.9 0.6 5 20 8 42 )
      , ( "reh slack 5x20/7",  Instances.rehearsalInstance 0.9 0.6 5 20 8 7 )
      , ( "windows n=16",      Instances.randomWindowedInstance 0.7 4 16 3 42 )
      , ( "clique n=16",       Instances.tightCliqueInstance 16 2 )
      , ( "pigeonhole m=6",    Instances.intervalPigeonholeInstance 6 2 )
      , ( "bin copies2",       Instances.infeasibleRehearsalInstance 2 )
      , ( "bin copies3",       Instances.infeasibleRehearsalInstance 3 )
      ]

-- | The bound-atom role A\/B matrix on 'theInstance'.
abMatrix :: IO ()
abMatrix = do
  printf "A/B matrix on: %s   (tasks: %d)\n\n" instanceLabel ( length theInstance )
  printf "  %-18s %-12s %-12s %6s %6s %7s %7s\n"
    ( "config" :: String ) ( "time" :: String ) ( "verdict" :: String )
    ( "dec" :: String ) ( "conf" :: String ) ( "learnt" :: String ) ( "tprop" :: String )
  forM_ abConfigs \ ( Cfg { cfgLabel, cfgOpts } ) -> do
    ( t, res ) <- measureOff cfgOpts theInstance
    let st = stats res
    printf "  %-18s %-12s %-12s %6d %6d %7d %7d\n"
      cfgLabel ( fmtNs t ) ( verdict res )
      ( numDecisions st ) ( numConflicts st ) ( numLearnts st ) ( numTheoryPropagations st )
  putStrLn ""
  putStrLn "FDS default-config instrumentation:"
  -- One instrumented solve, just for the detailed report (cheap on this config).
  case [ cfgOpts c | c <- abConfigs, cfgLabel c == "FDS (default)" ] of
    ( dfltOpts : _ ) -> do
      t0  <- getMonotonicTimeNSec
      rep <- evaluate ( force ( lcgSearch @MonitoringOn dfltOpts basicPropagators theInstance ) )
      t1  <- getMonotonicTimeNSec
      putStr ( renderReport ( monitorReport rep ) )
      let propSum = sum ( perPropagatorTime ( monitorReport rep ) )
      printf "  instrumented total %s  (propagator compute %.2f ms = %.0f%%)\n"
        ( fmtNs ( t1 - t0 ) )
        ( fromIntegral propSum / 1e6 :: Double )
        ( 100 * fromIntegral propSum / fromIntegral ( t1 - t0 ) :: Double )
    [] -> pure ()

-------------------------------------------------------------------------------
-- Size sweeps: node counts across the instance families.

sizeSweeps :: IO ()
sizeSweeps = do
  sweep "staggered windows (randomWindowed 0.7 slack=4 maxDur=3 seed=42)"
    [ ( "n=" ++ show n, Instances.randomWindowedInstance 0.7 4 n 3 42 )
    | n <- [ 4, 6, 8, 12, 16 ]
    ]
  sweep "disjunctive clique (tightClique d=2)"
    [ ( "n=" ++ show n, Instances.tightCliqueInstance n 2 )
    | n <- [ 4, 6, 8, 12, 16 ]
    ]
  sweep "multi-day rehearsal (util=0.9 avail=0.6 maxDur=8 seed=42)"
    [ ( "days=" ++ show d ++ " songs=" ++ show s
      , Instances.rehearsalInstance 0.9 0.6 d s 8 42 )
    | ( d, s ) <- [ ( 3, 9 ), ( 4, 12 ), ( 5, 15 ), ( 5, 20 ) ]
    ]
  -- Tight feasible rehearsal (util=1.0 avail=0.4): near the feasibility boundary,
  -- where even the structural heuristic backtracks. Seeds chosen per size so each
  -- is feasible /and/ forces conflicts (most feasible rehearsals are 0-conflict
  -- under the interval-commitment-first + critical-pair heuristic).
  sweep "tight feasible rehearsal (util=1.0 avail=0.4; forces backtracking)"
    [ ( "days=" ++ show d ++ " songs=" ++ show s ++ " seed=" ++ show sd
      , Instances.rehearsalInstance 1.0 0.4 d s 8 sd )
    | ( d, s, sd ) <- [ ( 4, 16, 5 ), ( 5, 20, 3 ), ( 6, 24, 3 ) ]
    ]
  sweep "interval pigeonhole (search-hard UNSAT; dur=2)"
    [ ( "slots=" ++ show m, Instances.intervalPigeonholeInstance m 2 )
    | m <- [ 3, 4, 5, 6 ]
    ]
  sweep "infeasible bin-packing fragmentation (overload-free; search-hard)"
    [ ( "copies=" ++ show c ++ " (" ++ show ( 5 * c ) ++ " songs)"
      , Instances.infeasibleRehearsalInstance c )
    | c <- [ 1, 2, 3 ]
    ]
  detailReport "infeasible bin-packing fragmentation, copies=4"
    ( Instances.infeasibleRehearsalInstance 4 )

  -- The no-restart structural baseline ('structOpts') is the old behaviour; it
  -- blows up on bin-packing copies=3 (~minutes), so that column is omitted there.
  strategySweep "decision strategy — infeasible (search-hard)"
    (  [ ( "pigeonhole slots=" ++ show m, Instances.intervalPigeonholeInstance m 2 )
       | m <- [ 5, 6 ] ]
    ++ [ ( "bin-packing copies=" ++ show c, Instances.infeasibleRehearsalInstance c )
       | c <- [ 1, 2 ] ]
    ++ [ ( "oversized " ++ show n ++ "-bin (heterog.)", Instances.fragmentationInstance items n )
       | ( n, items ) <- [ ( 3, [ 6, 7, 8, 9 ] )
                         , ( 4, [ 6, 7, 8, 9, 10 ] )
                         , ( 5, [ 6, 6, 7, 7, 8, 9 ] )
                         , ( 6, [ 6, 6, 7, 7, 8, 8, 9 ] )
                         ] ]
    )
  strategySweep "decision strategy — feasible (must not regress)"
    (  [ ( "rehearsal d=5 s=20 sd=" ++ show sd, Instances.rehearsalInstance 0.9 0.6 5 20 8 sd )
       | sd <- [ 7, 11 ] ]
    ++ [ ( "tight-feasible d=6 s=24 sd=" ++ show sd, Instances.rehearsalInstance 1.0 0.4 6 24 8 sd )
       | sd <- [ 1, 2, 3, 5, 9 ] ]
    ++ [ ( "clique n=12", Instances.tightCliqueInstance 12 2 ) ]
    )

strategyConfigs :: [ ( String, SearchOptions ) ]
strategyConfigs =
  [ ( "FDS",       defaultSearchOptions )
  , ( "FDS(no-rs)", defaultSearchOptions { optRestartUnit = 0 } )
  , ( "VSIDS",     setDecide False $ defaultSearchOptions )
  ]

-- | Run every 'strategyConfigs' column on each instance, holding propagators and
-- learning fixed, printing @time/conflicts@ per cell. The trailing tag is the
-- verdict, with @DISAGREE@ if the columns do not all agree (a correctness red
-- flag), or @CRASH@ for a column that threw.
strategySweep :: String -> [ ( String, Instance ) ] -> IO ()
strategySweep title sizes = do
  printf "%s:\n" title
  printf "  %-26s" ( "size" :: String )
  forM_ strategyConfigs \ ( lbl, _ ) -> printf " %-15s" lbl
  putStrLn "  verdict"
  forM_ sizes \ ( lbl, inst ) -> do
    _ <- evaluate ( force inst )
    cells <- forM strategyConfigs \ ( _, opts ) -> do
      r <- try @SomeException ( measureOff opts inst )
      pure $ case r of
        Left  _             -> ( "CRASH", "CRASH" :: String )
        Right ( time, res ) ->
          ( verdict res, printf "%s/%dc" ( fmtNs time ) ( numConflicts ( stats res ) ) )
    let verdicts = map fst cells
        tag = case verdicts of
          []         -> "?"
          ( v0 : _ ) | all ( == v0 ) verdicts -> v0
                     | otherwise              -> "DISAGREE " ++ show verdicts
    printf "  %-26s" lbl
    forM_ cells \ ( _, c ) -> printf " %-15s" c
    printf "  %s\n" tag
  putStrLn ""

-- | Run the default configuration over a family of sizes, printing the
-- search-tree node counts.
sweep :: String -> [ ( String, Instance ) ] -> IO ()
sweep title sizes = do
  printf "%s:\n" title
  printf "  %-16s %-11s %6s %6s %7s %7s %8s %-9s\n"
    ( "size" :: String ) ( "time" :: String )
    ( "dec" :: String ) ( "conf" :: String ) ( "learnt" :: String ) ( "tprop" :: String )
    ( "meanLen" :: String ) ( "verdict" :: String )
  forM_ sizes \ ( lbl, inst ) -> do
    _ <- evaluate ( force inst )
    ( t, res ) <- measure defaultSearchOptions inst
    let st           = stats res
        rep          = monitorReport res
    printf "  %-16s %-11s %6d %6d %7d %7d %8.1f %-9s\n"
      lbl ( fmtNs t )
      ( numDecisions st ) ( numConflicts st ) ( numLearnts st ) ( numTheoryPropagations st )
      ( meanReasonLen rep ) ( verdict res )
  putStrLn ""

-- | Print the detailed monitor report (conflict sources, reason lengths,
-- per-propagator) for one instance under the default configuration — to see
-- /which/ source the conflicts come from.
detailReport :: String -> Instance -> IO ()
detailReport label inst = do
  printf "%s (default config):\n" label
  rep <- evaluate ( force ( lcgSearch @MonitoringOn defaultSearchOptions basicPropagators inst ) )
  putStr ( renderReport ( monitorReport rep ) )
  putStrLn ""

meanReasonLen :: MonitorReport -> Double
meanReasonLen rep
  | reasonCount rep == 0 = 0
  | otherwise = fromIntegral ( reasonTotalLen rep ) / fromIntegral ( reasonCount rep )

-------------------------------------------------------------------------------

-- | One-line verdict from a search result.
verdict :: SearchResult task t -> String
verdict res = case solution res of
  Left  _ -> "infeasible"
  Right _ -> "feasible"

-- | Format a nanosecond count with an appropriate unit.
fmtNs :: Word64 -> String
fmtNs ns
  | ns >= 1_000_000_000 = printf "%.3f s"  ( fromIntegral ns / 1e9 :: Double )
  | ns >= 1_000_000     = printf "%.3f ms" ( fromIntegral ns / 1e6 :: Double )
  | ns >= 1_000         = printf "%.3f µs" ( fromIntegral ns / 1e3 :: Double )
  | otherwise           = printf "%d ns" ns
