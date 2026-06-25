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
  ( evaluate )
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
  )

-- z3-oracle
import Schedule.Z3
  ( newZ3Env, z3FeasibleIn )

-------------------------------------------------------------------------------
-- The Z3 oracle.

-- | Z3 feasibility benchmark.
benchZ3 :: Instance -> Benchmarkable
benchZ3 inst = Benchmarkable \ n -> do
  -- Don't include the Z3 setup cost (~6ms)
  z3Env <- newZ3Env
  let tasks = map fst inst
  replicateM_ ( fromIntegral n ) do
    res <- z3FeasibleIn z3Env tasks
    evaluate ( isJust res )

-------------------------------------------------------------------------------
-- Suite.

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
  map ( localOption ( RelStDev 0.1 ) . localOption ( mkTimeout 5_000_000 ) )

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
      | ( n, d ) <- [ ( 4, 3 ), ( 6, 3 ), ( 8, 3 ), ( 12, 3 ), ( 16, 3 ) ]
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
  ]
