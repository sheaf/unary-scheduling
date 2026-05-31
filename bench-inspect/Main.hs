{-# OPTIONS_GHC -fno-full-laziness #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

-- | A self-contained harness that runs scheduling benchmarks through the LCG
-- search and reports /search-tree size/ (decisions, conflicts, learnt clauses,
-- theory propagations) alongside wall-clock time. Two views:
--
--   * an A\/B matrix over the four combinations of the bound-atom roles
--     (channel-out learning × day-assignment decisions) on one fixed instance,
--     so each role's net effect — including learning held against a coarse
--     baseline — is isolated; plus the full conflict\/reason breakdown for the
--     default configuration;
--
--   * a size sweep over the benchmark instance families, reporting the node
--     counts (not just time) that show whether the cost is the search tree.
--
-- For profiling, Core dumps, and gauging where the milestones move the numbers.
module Main ( main ) where

-- base
import Control.Exception
  ( evaluate )
import Control.Monad
  ( forM, forM_ )
import Data.Word
  ( Word64 )
import GHC.Clock
  ( getMonotonicTimeNSec )
import Text.Printf
  ( printf )

-- deepseq
import Control.DeepSeq
  ( force )

-- unary-scheduling
import Schedule.LCG.Search
  ( SearchResult(..), SearchStats(..), SearchOptions(..)
  , defaultSearchOptions, lcgSearch
  )
import Schedule.Monitor
  ( Monitoring(..), MonitorReport(..), renderReport )
import Schedule.Propagators
  ( basicPropagators )

-- bench:unary-scheduling
import Schedule.Bench.Instances
  ( BenchTime, Instance )
import qualified Schedule.Bench.Instances as Instances

-------------------------------------------------------------------------------
-- Configuration under test.

-- | The fixed instance for the A\/B matrix. The multi-day rehearsal target is
-- where day-assignment decisions are designed to help and where we currently
-- trail Z3, so it is the most informative instance for the role comparison.
theInstance :: Instance
theInstance = Instances.rehearsalInstance 0.9 0.6 8 20 8 7

instanceLabel :: String
instanceLabel = "rehearsalInstance util=0.9 avail=0.6 days=8 songs=20 maxDur=8 seed=7"

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

abConfigs :: [ Cfg ]
abConfigs =
  [ -- Too slow
    -- Cfg "precedence-only" base { optBoundAtoms = False, optBoundDecisions = False, optTheoryDecide = False }
    Cfg "+learning"       base { optBoundAtoms = True , optBoundDecisions = False, optTheoryDecide = False }
  , Cfg "+day (VSIDS)"    base { optBoundAtoms = False, optBoundDecisions = True , optTheoryDecide = False }
  , Cfg "+both (VSIDS)"   base { optBoundAtoms = True , optBoundDecisions = True , optTheoryDecide = False }
  , Cfg "+both +struct"   base { optBoundAtoms = True , optBoundDecisions = True , optTheoryDecide = True  }
  ]
  where
    base = defaultSearchOptions

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
main = do
  _ <- evaluate ( force theInstance )
  printf "=== unary-scheduling LCG inspection harness ===\n\n"

  abMatrix
  putStrLn ""
  sizeSweeps

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
  putStrLn "default-config (+both +struct) instrumentation:"
  -- One instrumented solve, just for the detailed report (cheap on this config).
  case [ cfgOpts c | c <- abConfigs, cfgLabel c == "+both +struct" ] of
    ( dfltOpts : _ ) -> do
      rep <- evaluate ( force ( lcgSearch @MonitoringOn dfltOpts basicPropagators theInstance ) )
      putStr ( renderReport ( monitorReport rep ) )
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
  -- under the day-first-fail + critical-pair heuristic).
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
    | c <- [ 1, 2 ] -- c=3 takes minutes
    ]
  detailReport "infeasible bin-packing fragmentation, copies=2"
    ( Instances.infeasibleRehearsalInstance 2 )

-- | Run the default configuration over a family of sizes, printing the
-- search-tree node counts (and the tight\/coarse conflict split) per size.
sweep :: String -> [ ( String, Instance ) ] -> IO ()
sweep title sizes = do
  printf "%s:\n" title
  printf "  %-16s %-11s %6s %6s %7s %7s %11s %8s %-9s\n"
    ( "size" :: String ) ( "time" :: String )
    ( "dec" :: String ) ( "conf" :: String ) ( "learnt" :: String ) ( "tprop" :: String )
    ( "tight/coarse" :: String ) ( "meanLen" :: String ) ( "verdict" :: String )
  forM_ sizes \ ( lbl, inst ) -> do
    _ <- evaluate ( force inst )
    ( t, res ) <- measure defaultSearchOptions inst
    let st        = stats res
        rep       = monitorReport res
        ( tight, coarse ) = conflictTotals rep
    printf "  %-16s %-11s %6d %6d %7d %7d %5d/%-5d %8.1f %-9s\n"
      lbl ( fmtNs t )
      ( numDecisions st ) ( numConflicts st ) ( numLearnts st ) ( numTheoryPropagations st )
      tight coarse ( meanReasonLen rep ) ( verdict res )
  putStrLn ""

-- | Print the detailed monitor report (conflict sources, reason lengths,
-- per-propagator) for one instance under the default configuration — to see
-- /which/ source the conflicts come from, not just the tight\/coarse split.
detailReport :: String -> Instance -> IO ()
detailReport label inst = do
  printf "%s (default config):\n" label
  rep <- evaluate ( force ( lcgSearch @MonitoringOn defaultSearchOptions basicPropagators inst ) )
  putStr ( renderReport ( monitorReport rep ) )
  putStrLn ""

-- | Sum the @(tight, coarse)@ conflict counts across all sources.
conflictTotals :: MonitorReport -> ( Int, Int )
conflictTotals rep =
  foldr ( \ ( a, b ) ( accA, accB ) -> ( a + accA, b + accB ) )
        ( 0, 0 ) ( conflictBreakdown rep )

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
