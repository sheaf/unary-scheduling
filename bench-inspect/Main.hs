{-# OPTIONS_GHC -fno-full-laziness #-}

-- | A self-contained harness that runs a single scheduling benchmark
-- through the LCG search.
--
-- For profiling or looking at Core dumps.
module Main ( main ) where

-- base
import Control.Exception
  ( evaluate )
import Control.Monad
  ( forM )
import Data.Word
  ( Word64 )
import GHC.Clock
  ( getMonotonicTimeNSec )
import Text.Printf
  ( printf )

-- deepseq
import Control.DeepSeq
  ( force )

-- text
import qualified Data.Text as Text
  ( unpack )

-- unary-scheduling
import Schedule.LCG.Search
  ( SearchResult(..), SearchStats(..), defaultSearchOptions, lcgSearch )
import Schedule.Monitor
  ( Monitoring(..), renderReport )
import Schedule.Propagators
  ( basicPropagators )

-- bench:unary-scheduling
import Schedule.Bench.Instances
  ( BenchTime, Instance )
import qualified Schedule.Bench.Instances as Instances

-------------------------------------------------------------------------------

theInstance :: Instance
theInstance = Instances.randomWindowedInstance 0.7 4 16 3 42

iterations :: Int
iterations = 1
{-# NOINLINE iterations #-}

-------------------------------------------------------------------------------
-- Runners.

solveRaw :: Instance -> SearchResult () BenchTime
solveRaw = lcgSearch @MonitoringOff defaultSearchOptions basicPropagators

solveInstrumented :: Instance -> SearchResult () BenchTime
solveInstrumented = lcgSearch @MonitoringOn defaultSearchOptions basicPropagators

-------------------------------------------------------------------------------

main :: IO ()
main = do
  -- Hoist instance construction out of every measurement.
  _ <- evaluate ( force theInstance )
  printf "=== unary-scheduling LCG inspection harness ===\n"
  printf "tasks: %d   iterations: %d\n\n" ( length theInstance ) iterations

  -- Run 1: raw (uninstrumented) timing.
  putStrLn "--- raw run (lcgSearch @MonitoringOff) ---"
  ( times, rawRes ) <- timeRaw iterations
  let !mn = minimum times
      !mean = fromIntegral ( sum times ) / fromIntegral iterations :: Double
  printf "time: min %s   mean %s\n"
    ( fmtNs mn ) ( fmtNs ( round mean ) )
  putStrLn ( "verdict: " ++ verdict rawRes )
  putStr ( renderStats ( stats rawRes ) )
  putStrLn ""

  -- Run 2: instrumented.
  putStrLn "--- instrumented run (lcgSearch @MonitoringOn) ---"
  instrRes <- evaluate ( force ( solveInstrumented theInstance ) )
  putStrLn ( "verdict: " ++ verdict instrRes )
  putStr ( renderStats ( stats instrRes ) )
  putStr ( renderReport ( monitorReport instrRes ) )

-- | Run the raw path @n@ times, returning each run's wall-clock duration (ns)
-- and the (identical) result of the final run.
timeRaw :: Int -> IO ( [ Word64 ], SearchResult () BenchTime )
timeRaw n = do
  results <- forM [ 1 .. n ] \ _ -> do
    t0 <- getMonotonicTimeNSec
    r  <- evaluate ( force ( solveRaw theInstance ) )
    t1 <- getMonotonicTimeNSec
    pure ( t1 - t0, r )
  pure ( map fst results, snd ( last results ) )

-- | One-line verdict from a search result.
verdict :: SearchResult task t -> String
verdict res = case solution res of
  Left  msg -> "infeasible — " ++ takeFirstLine ( Text.unpack msg )
  Right _   -> "feasible"
  where
    takeFirstLine = takeWhile ( /= '\n' )

-- | Render the always-on search statistics.
renderStats :: SearchStats -> String
renderStats s = unlines
  [ "search stats:"
  , row "decisions"      ( numDecisions s )
  , row "conflicts"      ( numConflicts s )
  , row "learnt clauses" ( numLearnts s )
  , row "theory props"   ( numTheoryPropagations s )
  ]
  where
    row :: String -> Int -> String
    row name v = printf "  %-22s %d" name v

-- | Format a nanosecond count with an appropriate unit.
fmtNs :: Word64 -> String
fmtNs ns
  | ns >= 1_000_000_000 = printf "%.3f s"  ( fromIntegral ns / 1e9 :: Double )
  | ns >= 1_000_000     = printf "%.3f ms" ( fromIntegral ns / 1e6 :: Double )
  | ns >= 1_000         = printf "%.3f µs" ( fromIntegral ns / 1e3 :: Double )
  | otherwise           = printf "%d ns" ns
