{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Benchmarks for the unary-scheduling solvers.
--
-- For each instance family we report two timings on the same instance:
--
--  * /LCG/ — the full 'lcgSearch' (BCP + theory propagation + 1-UIP).
--  * /Z3/  — 'z3Feasible' as an external oracle.
--
-- The ratio @LCG / Z3@ is the north-star comparison against an industrial
-- solver. See @bench/SAT/Bench.hs@ for the SAT-core-only counterpart.
module Schedule.Bench
  ( benchmarks )
  where

-- base
import Control.Monad
  ( replicateM_ )
import Control.Exception
  ( Exception, evaluate, throwIO )
import Data.Maybe
  ( isJust )

-- tasty
import Test.Tasty
  ( localOption, mkTimeout )

-- tasty-bench
import Test.Tasty.Bench
  ( Benchmark, Benchmarkable(..), RelStDev(..)
  , bgroup, bench, env, whnf )

-- unary-scheduling bench suite
import Schedule.Bench.Instances
  ( BenchTime(..)  -- in scope for the @Coercible BenchTime Int@ used by 'benchZ3'
  , Instance
  , runLCG
  , randomWindowedInstance, rehearsalInstance
  , overloadedInstance
  , tightCliqueInstance
  , intervalPigeonholeInstance
  , infeasibleRehearsalInstance
  , phaseTransitionAt
  )

-- z3-oracle
import Schedule.Z3
  ( Z3Feasibility(..), newZ3Env, z3FeasibleIn )

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
-- Suite.

-- | Wall-clock budget for each benchmark, in microseconds.
timeout_us :: Integer
timeout_us = 60_000_000 -- μs

-- | Two benchmarks (LCG, Z3) sharing one cached instance, presented as a
-- labelled group.
triple :: String -> Instance -> Benchmark
triple label inst =
  env ( pure inst ) \ i ->
    bgroup label
      [ bench "LCG" ( whnf runLCG i )
      , bench "Z3"  ( benchZ3 i )
      ]

benchmarks :: [ Benchmark ]
benchmarks =
  -- tolerate higher variance to avoid tests taking too long
  map ( localOption ( RelStDev 0.2 ) . localOption ( mkTimeout timeout_us ) )

  -- One benchmark group per distinct workload class.
  [ bgroup "staggered windows ~70% (heterogeneous; propagation + search)"
      [ triple ( "n=" ++ show n ++ " maxDur=" ++ show d )
               ( randomWindowedInstance 0.7 4 n d 42 )
      | ( n, d ) <- [ ( 4, 3 ), ( 6, 3 ), ( 8, 3 ), ( 12, 3 ), ( 16, 3 ) ]
      ]
  , bgroup "disjunctive clique (shared window; propagators idle, pure search)"
      [ triple ( "n=" ++ show n ++ " d=" ++ show d )
               ( tightCliqueInstance n d )
      | ( n, d ) <- [ ( 4, 2 ), ( 6, 2 ), ( 8, 2 ), ( 12, 2 ), ( 16, 2 ) ]
      ]
  , bgroup "multi-day rehearsal (single director; day-assignment bin-packing)"
      [ triple ( "days=" ++ show days ++ " songs=" ++ show songs )
               ( rehearsalInstance 0.9 0.6 days songs 8 42 )
      | ( days, songs ) <- [ ( 3, 9 ), ( 4, 12 ), ( 5, 15 ), ( 5, 20 ) ]
      ]
  , bgroup "tight feasible rehearsal (near boundary; forces backtracking)"
      [ triple ( "days=" ++ show days ++ " songs=" ++ show songs )
               ( rehearsalInstance 1.0 0.4 days songs 8 seed )
      | ( days, songs, seed ) <- [ ( 4, 16, 5 ), ( 5, 20, 3 ), ( 6, 24, 3 ) ]
      ]
  , bgroup "infeasible: resource overload (demand twice the horizon)"
      [ triple ( "n=" ++ show n ++ " d=" ++ show d )
               ( overloadedInstance n d )
      | ( n, d ) <- [ ( 4, 3 ), ( 6, 3 ), ( 8, 3 ), ( 12, 3 ) ]
      ]
  , bgroup "infeasible: interval pigeonhole (search-hard; overload-free)"
      [ triple ( "slots=" ++ show m ++ " (" ++ show ( m + 1 ) ++ " tasks)" )
               ( intervalPigeonholeInstance m 2 )
      | m <- [ 3, 4, 5, 6 ]
      ]
  , bgroup "infeasible: bin-packing fragmentation (overload-free; search-hard)"
      [ triple ( "copies=" ++ show c ++ " (" ++ show ( 5 * c ) ++ " songs, " ++ show ( 3 * c ) ++ " days)" )
               ( infeasibleRehearsalInstance c )
      | c <- [ 1, 2, 3 ]
      ]
  -- Mined hard instances from the single-machine solvability phase-transition
  -- model (Wang, O'Gorman, Tran, Rieffel, Frank & Do, ICAPS 2017).
  , bgroup "phase transition (Wang et al. 2017; hard)"
      [ triple
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
  ]
