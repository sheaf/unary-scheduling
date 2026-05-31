{-# OPTIONS_GHC -fno-full-laziness #-}

-- | A self-contained harness that runs a single scheduling benchmark through
-- the LCG search, /with/ and /without/ the bound-atom machinery, and prints an
-- A\/B comparison. For profiling, Core dumps, and gauging where bound atoms
-- (tight clausal reasons + monotonicity) actually help the search.
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
  ( SearchResult(..), SearchStats(..), SearchOptions(..)
  , defaultSearchOptions, lcgSearch
  )
import Schedule.Monitor
  ( Monitoring(..), renderReport )
import Schedule.Propagators
  ( basicPropagators )

-- bench:unary-scheduling
import Schedule.Bench.Instances
  ( BenchTime, Instance )
import qualified Schedule.Bench.Instances as Instances

-------------------------------------------------------------------------------

-- | The instance under test. Candidates (edit this line):
--   * @rehearsalInstance util availProb days songs maxDur seed@ — multi-day
--     day-assignment bin-packing; raise @util@ towards 1 and lower @availProb@
--     until @conflicts > 0@. The bound-atom / bound-decision testbed.
--   * @randomWindowedInstance 0.7 4 n maxDur seed@ — dense ordering-hard (does
--     produce conflicts, but bounds are precedence-determined → bound atoms
--     don't help).
--   * @tightCliqueInstance n d@ — pure precedence search baseline.
theInstance :: Instance
theInstance = Instances.rehearsalInstance 0.9 0.6 8 20 8 7

-- | A short description of 'theInstance' for the report header.
instanceLabel :: String
instanceLabel = "rehearsalInstance util=0.9 avail=0.6 days=8 songs=20 maxDur=8 seed=7"

-- | Timing iterations (the per-run statistics are deterministic and measured
-- once; only wall-clock timing is repeated for a stable minimum). Lower this if
-- a harder instance makes each solve slow.
iterations :: Int
iterations = 1
{-# NOINLINE iterations #-}

-------------------------------------------------------------------------------
-- The two configurations under comparison.

-- | The comparison: plain precedence-only search versus branching on
-- day-assignment bound atoms (the design — see "Schedule.LCG.Theory").
optsWith, optsWithout :: SearchOptions
optsWithout = defaultSearchOptions { optBoundDecisions = False }
optsWith    = defaultSearchOptions { optBoundDecisions = True }

solveRaw :: SearchOptions -> Instance -> SearchResult () BenchTime
solveRaw opts = lcgSearch @MonitoringOff opts basicPropagators

solveInstrumented :: SearchOptions -> Instance -> SearchResult () BenchTime
solveInstrumented opts = lcgSearch @MonitoringOn opts basicPropagators

-- | One configuration's measured outcome.
data Outcome = Outcome
  { oMinNs  :: !Word64
  , oResult :: !( SearchResult () BenchTime )   -- ^ the instrumented result
  }

runMode :: SearchOptions -> IO Outcome
runMode opts = do
  -- Repeat the raw (uninstrumented) path for a stable minimum wall-clock time.
  times <- forM [ 1 .. iterations ] \ _ -> do
    t0 <- getMonotonicTimeNSec
    _  <- evaluate ( force ( solveRaw opts theInstance ) )
    t1 <- getMonotonicTimeNSec
    pure ( t1 - t0 )
  -- Statistics come from one instrumented run (deterministic).
  instr <- evaluate ( force ( solveInstrumented opts theInstance ) )
  pure ( Outcome ( minimum times ) instr )

-------------------------------------------------------------------------------

main :: IO ()
main = do
  _ <- evaluate ( force theInstance )
  printf "=== unary-scheduling LCG inspection harness (bound-atom A/B) ===\n"
  printf "instance: %s   tasks: %d   timing iterations: %d\n\n"
    instanceLabel ( length theInstance ) iterations

  on  <- runMode optsWith
  off <- runMode optsWithout

  let col :: String -> String -> String -> String
      col label a b = printf "  %-22s %-18s %s" label a b
  putStrLn ( col "" "+ day decisions" "precedence-only" )
  putStrLn ( col "time (min)"     ( fmtNs ( oMinNs on ) )         ( fmtNs ( oMinNs off ) ) )
  putStrLn ( col "verdict"        ( verdict ( oResult on ) )      ( verdict ( oResult off ) ) )
  putStrLn ( col "decisions"      ( stat numDecisions on )        ( stat numDecisions off ) )
  putStrLn ( col "conflicts"      ( stat numConflicts on )        ( stat numConflicts off ) )
  putStrLn ( col "learnt clauses" ( stat numLearnts on )          ( stat numLearnts off ) )
  putStrLn ( col "theory props"   ( stat numTheoryPropagations on ) ( stat numTheoryPropagations off ) )
  putStrLn ""

  putStrLn "+day-decisions instrumentation:"
  putStr ( renderReport ( monitorReport ( oResult on ) ) )
  where
    stat :: ( SearchStats -> Int ) -> Outcome -> String
    stat f = show . f . stats . oResult

-------------------------------------------------------------------------------

-- | One-line verdict from a search result.
verdict :: SearchResult task t -> String
verdict res = case solution res of
  Left  msg -> "infeasible — " ++ takeWhile ( /= '\n' ) ( Text.unpack msg )
  Right _   -> "feasible"

-- | Format a nanosecond count with an appropriate unit.
fmtNs :: Word64 -> String
fmtNs ns
  | ns >= 1_000_000_000 = printf "%.3f s"  ( fromIntegral ns / 1e9 :: Double )
  | ns >= 1_000_000     = printf "%.3f ms" ( fromIntegral ns / 1e6 :: Double )
  | ns >= 1_000         = printf "%.3f µs" ( fromIntegral ns / 1e3 :: Double )
  | otherwise           = printf "%d ns" ns
