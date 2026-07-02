{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Benchmarks for the unary-scheduling solvers.
--
-- For each instance family we report three timings on the same instance:
--
--  * /LCG/     — the full 'lcgSearch' (BCP + theory propagation + 1-UIP).
--  * /Z3/      — Z3 SMT solver
--  * /Chuffed/ — the MiniZinc lazy-clause-generation solver
--
-- See @bench/sat/SAT/Bench.hs@ for the SAT-core-only counterpart.
module Schedule.Bench
  ( benchmarks )
  where

-- base
import Control.Monad
  ( replicateM_ )
import Control.Exception
  ( Exception, evaluate, throwIO )
import Data.IORef
  ( IORef, newIORef, readIORef, modifyIORef' )
import Data.Maybe
  ( fromMaybe, isJust )
import Data.Word
  ( Word64 )
import System.Environment
  ( lookupEnv )

-- deepseq
import Control.DeepSeq
  ( NFData(rnf) )

-- tasty
import Test.Tasty
  ( localOption, mkTimeout )

-- tasty-bench
import Test.Tasty.Bench
  ( Benchmark, Benchmarkable(..), RelStDev(..), TimeMode(..)
  , bgroup, bench, env, whnf )

-- scheduling-bench-instances
import Schedule.Bench.Instances
  ( BenchTime(..)  -- in scope for the @Coercible BenchTime Int@ used by 'benchZ3'
  , Instance
  , runLCG
  , randomWindowedInstance, rehearsalInstance
  , performerRehearsalInstance
  , overloadedInstance
  , tightCliqueInstance
  , intervalPigeonholeInstance
  , infeasibleRehearsalInstance
  , phaseTransitionAt
  )

-- z3-oracle
import Schedule.Z3
  ( Z3Feasibility(..), newZ3Env, z3FeasibleIn )

-- minizinc-oracle
import Schedule.MiniZinc
  ( MiniZincOptions(..), MiniZincOutcome(..), MiniZincStatus(..)
  , defaultMiniZincOptions, minizincFeasible
  )

-------------------------------------------------------------------------------
-- The Z3 oracle.

-- | Thrown to abort a Z3 benchmark case as soon as a single solver call hits
-- the Z3 timeout.
--
-- Deals with the fact that Z3 invocations use unsafe FFI calls, which Tasty
-- cannot properly cancel.
data Z3Timeout = Z3Timeout
  deriving stock Show
  deriving anyclass Exception

-- | Z3 feasibility benchmark.
benchZ3 :: Instance -> Benchmarkable
benchZ3 inst = Benchmarkable \ n -> do
  -- Don't include the Z3 setup cost in the benchmark (~6ms)
  z3Env <- newZ3Env $ fromIntegral ( timeout_us `div` 1000 )
  let tasks = map fst inst
  replicateM_ ( fromIntegral n ) do
    res <- z3FeasibleIn z3Env tasks
    case res of
      Z3TimedOut    -> throwIO Z3Timeout
      Z3Decided mb  -> evaluate ( isJust mb )

-------------------------------------------------------------------------------
-- The MiniZinc/Chuffed oracle.

-- | Thrown to abort a Chuffed benchmark case as soon as a single solve hits the
-- MiniZinc time limit, mirroring 'Z3Timeout'.
data MiniZincTimeout = MiniZincTimeout
  deriving stock Show
  deriving anyclass Exception

-- | Chuffed feasibility benchmark.
--
-- We invoke @minizinc@ as an external process, so to properly report its time
-- we need to use 'CustomTime' instead of relying on tasty-bench.
benchMiniZinc :: IORef Word64 -> Instance -> Benchmarkable
benchMiniZinc timeAccRef inst = Benchmarkable \ n -> do
  exe <- fromMaybe "minizinc" <$> lookupEnv "MINIZINC"
  let opts = defaultMiniZincOptions
        { minizincExe = exe
        , timeLimitMs = fromIntegral ( timeout_us `div` 1000 )
        }
      tasks = map fst inst
  replicateM_ ( fromIntegral n ) do
    outcome <- minizincFeasible opts tasks
    case status outcome of
      Unknown    -> throwIO MiniZincTimeout
      Feasible{} -> pure ()
      Infeasible -> pure ()
    -- MiniZinc reports solveTime in seconds (millisecond resolution).
    let solvePicoSecs = max 1_000_000_000 -- Chuffed has 1ms resolution
                      $ round ( fromMaybe 0 ( solveTime outcome ) * 1e12 ) :: Word64
    modifyIORef' timeAccRef ( + solvePicoSecs )

-------------------------------------------------------------------------------
-- Suite.

-- | Wall-clock budget for each benchmark, in microseconds.
timeout_us :: Integer
timeout_us = 60_000_000 -- μs

data BenchEnv =
  BenchEnv
    { chuffedTimer  :: IORef Word64
    , benchInstance :: Instance
    }
instance NFData BenchEnv where
  rnf ( BenchEnv { benchInstance = inst } ) = rnf inst

solverGroup :: String -> Instance -> Benchmark
solverGroup label inst =
  -- NB: lazy pattern match required by tasty-bench.
  env mkEnv \ ~( BenchEnv { chuffedTimer, benchInstance = i } ) ->
    bgroup label
      [ bench "LCG"     ( whnf runLCG i )
      , bench "Z3"      ( benchZ3 i )
      , localOption ( CustomTime ( readIORef chuffedTimer ) )
          -- Use 'CustomTime' to retrieve the solve time reported by minizinc.
      $ localOption ( RelStDev ( 1 / 0 ) )
      $ bench "Chuffed" ( benchMiniZinc chuffedTimer i )
      ]
  where
    mkEnv :: IO BenchEnv
    mkEnv = do
      chuffedTimer <- newIORef 0
      pure $ BenchEnv { benchInstance = inst, chuffedTimer }

benchmarks :: [ Benchmark ]
benchmarks =
  -- tolerate higher variance to avoid tests taking too long
  map ( localOption ( RelStDev 0.2 ) . localOption ( mkTimeout timeout_us ) )

  -- One benchmark group per distinct workload class.
  [ bgroup "staggered windows ~70% (heterogeneous; propagation + search)"
      [ solverGroup ( "n=" ++ show n ++ " maxDur=" ++ show d )
               ( randomWindowedInstance 0.7 4 n d 42 )
      | ( n, d ) <- [ ( 4, 3 ), ( 6, 3 ), ( 8, 3 ), ( 12, 3 ), ( 16, 3 ) ]
      ]
  , bgroup "disjunctive clique (shared window; propagators idle, pure search)"
      [ solverGroup ( "n=" ++ show n ++ " d=" ++ show d )
               ( tightCliqueInstance n d )
      | ( n, d ) <- [ ( 4, 2 ), ( 6, 2 ), ( 8, 2 ), ( 12, 2 ), ( 16, 2 ) ]
      ]
  , bgroup "multi-day rehearsal (single director; day-assignment bin-packing)"
      [ solverGroup ( "days=" ++ show days ++ " songs=" ++ show songs )
               ( rehearsalInstance 0.9 0.6 days songs 8 42 )
      | ( days, songs ) <- [ ( 3, 9 ), ( 4, 12 ), ( 5, 15 ), ( 5, 20 ) ]
      ]
  , bgroup "tight feasible rehearsal (near boundary; forces backtracking)"
      [ solverGroup ( "days=" ++ show days ++ " songs=" ++ show songs )
               ( rehearsalInstance 1.0 0.4 days songs 8 seed )
      | ( days, songs, seed ) <- [ ( 4, 16, 5 ), ( 5, 20, 3 ), ( 6, 24, 3 ) ]
      ]
  , bgroup "infeasible: resource overload (demand twice the horizon)"
      [ solverGroup ( "n=" ++ show n ++ " d=" ++ show d )
               ( overloadedInstance n d )
      | ( n, d ) <- [ ( 4, 3 ), ( 6, 3 ), ( 8, 3 ), ( 12, 3 ) ]
      ]
  , bgroup "infeasible: interval pigeonhole (search-hard; overload-free)"
      [ solverGroup ( "slots=" ++ show m ++ " (" ++ show ( m + 1 ) ++ " tasks)" )
               ( intervalPigeonholeInstance m 2 )
      | m <- [ 3, 4, 5, 6 ]
      ]
  , bgroup "infeasible: bin-packing fragmentation (overload-free; search-hard)"
      [ solverGroup ( "copies=" ++ show c ++ " (" ++ show ( 5 * c ) ++ " songs, " ++ show ( 3 * c ) ++ " days)" )
               ( infeasibleRehearsalInstance c )
      | c <- [ 1, 2, 3 ]
      ]
  -- Mined hard instances from the single-machine solvability phase-transition
  -- model (Wang, O'Gorman, Tran, Rieffel, Frank & Do, ICAPS 2017).
  , bgroup "phase transition (Wang et al. 2017; hard)"
      [ solverGroup
          ( "n=" ++ show n ++ " T/np\776=" ++ show ratioT
            ++ " w/T=" ++ show ratioW ++ " s=" ++ show seed )
          ( phaseTransitionAt ( 3, 19 ) n ratioT ratioW seed )
      | ( n, ratioT, ratioW, seed ) <-
          [ (  50, 1.20, 0.50, 14 )   -- ~0.2 s,  244 decisions
          , (  70, 1.10, 0.50, 36 )   -- ~0.8 s,  962 decisions
          , (  90, 1.15, 0.50, 29 )   -- ~1.7 s, 1532 decisions
          , ( 110, 1.15, 0.60, 29 )   -- stress test
          ]
      ]
  -- Mined hard instances of the performer-driven rehearsal model.
  , bgroup "performer-driven rehearsal (hard)"
      [ solverGroup
          ( "d=" ++ show days ++ " s=" ++ show songs ++ " perf=" ++ show perf
            ++ " k=" ++ show k ++ " s=" ++ show seed )
          ( performerRehearsalInstance util perf dens k days songs 8 seed )
      | ( util, perf, dens, k, days, songs, seed ) <-
          [ ( 1.00,  8, 0.75, 3,  5, 20,  7 )   -- feasible,   ~1 s,  1729 conf
          , ( 0.95,  8, 0.60, 3,  5, 20, 18 )   -- infeasible, ~1.7s, 2994 conf
          , ( 1.00, 10, 0.75, 3,  6, 28,  5 )   -- feasible,   ~2.6s, 2507 conf
          , ( 1.00, 10, 0.75, 3,  6, 28,  6 )   -- infeasible, ~4.1s, 4606 conf
          , ( 1.00, 10, 0.75, 3,  7, 35, 20 )   -- feasible,   ~5.1s, 2973 conf
          , ( 0.95, 10, 0.75, 3,  7, 35, 15 )   -- infeasible, ~6.1s, 4072 conf
          , ( 1.00, 10, 0.75, 2,  6, 28, 17 )   -- feasible,   ~46ms,  Chuffed >60s
          , ( 1.00, 10, 0.75, 3,  7, 35,  9 )   -- infeasible, ~0.6ms, Chuffed 6.9s
          ]
      ]
  ]
