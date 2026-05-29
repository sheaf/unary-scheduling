{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Benchmarks for the unary-scheduling solvers.
--
-- For each instance family we report three timings on the same instance:
--
--  * /LCG/         — the full 'lcgSearch' (BCP + theory propagation + 1-UIP).
--  * /propagators/ — 'propagateConstraints' alone, no SAT search.
--  * /Z3/          — 'z3Feasible' as an external oracle.
--
-- The ratio @LCG / propagators@ quantifies how much we are paying for the
-- SAT integration on instances the propagators alone can fully decide;
-- the ratio @LCG / Z3@ is the north-star comparison against an industrial
-- solver. See @bench/SAT/Bench.hs@ for the SAT-core-only counterpart.
module Schedule.Bench
  ( benchmarks )
  where

-- base
import Data.Maybe
  ( isJust )

-- tasty
import Test.Tasty
  ( localOption, mkTimeout )

-- tasty-bench
import Test.Tasty.Bench
  ( Benchmark, RelStDev(..), bgroup, bench, env, whnf, nfIO )

-- unary-scheduling bench suite
import Schedule.Bench.Instances
  ( BenchTime(..), Instance
  , runLCG, runPropOnly
  , randomInstanceAtUtilisation, overloadedInstance, twoSegmentInstance
  , tightCliqueInstance, chainedWindowInstance, chainedOverloadedInstance
  )

-- z3-oracle
import Schedule.Z3
  ( z3Feasible )

-------------------------------------------------------------------------------
-- The Z3 oracle.

-- | Z3 feasibility check (no objective). Returns 'True' iff Z3 reports a
-- satisfying schedule exists; the actual start times are forced but
-- discarded by 'isJust' to match the bool-valued verdict.
runZ3 :: Instance -> IO Bool
runZ3 inst = isJust <$> z3Feasible ( map fst inst )

-------------------------------------------------------------------------------
-- Suite.

-- | Three benchmarks (LCG, propagators only, Z3) sharing one cached
-- instance, presented as a labelled group.
triple :: String -> Instance -> Benchmark
triple label inst =
  env ( pure inst ) \ i ->
    bgroup label
      [ bench "LCG"         ( whnf runLCG i )
      , bench "propagators" ( whnf runPropOnly i )
      , bench "Z3"          ( nfIO ( runZ3 i ) )
      ]

benchmarks :: [ Benchmark ]
benchmarks =
  -- tolerate higher variance to avoid tests taking too long
  map ( localOption ( RelStDev 0.1 ) . localOption ( mkTimeout 5_000_000 ) )
  [ bgroup "tight feasible (~95% utilisation)"
      [ triple ( "n=" ++ show n ++ " maxDur=" ++ show d )
               ( randomInstanceAtUtilisation 0.95 n d 42 )
      | ( n, d ) <- [ ( 4, 3 ), ( 6, 3 ), ( 8, 3 ), ( 12, 3 ), ( 16, 3 ) ]
      ]
  , bgroup "moderately constrained feasible (~60% utilisation)"
      [ triple ( "n=" ++ show n ++ " maxDur=" ++ show d )
               ( randomInstanceAtUtilisation 0.6 n d 42 )
      | ( n, d ) <- [ ( 4, 3 ), ( 6, 3 ), ( 8, 3 ), ( 12, 3 ), ( 16, 3 ) ]
      ]
  , bgroup "under-constrained feasible (~20% utilisation; overhead baseline)"
      [ triple ( "n=" ++ show n ++ " maxDur=" ++ show d )
               ( randomInstanceAtUtilisation 0.2 n d 42 )
      | ( n, d ) <- [ ( 4, 3 ), ( 6, 3 ), ( 8, 3 ), ( 12, 3 ), ( 16, 3 ) ]
      ]
  , bgroup "infeasible (demand twice the horizon)"
      [ triple ( "n=" ++ show n ++ " d=" ++ show d )
               ( overloadedInstance n d )
      | ( n, d ) <- [ ( 4, 3 ), ( 6, 3 ), ( 8, 3 ), ( 12, 3 ), ( 16, 3 ) ]
      ]
  , bgroup "two-segment availability"
      [ triple ( "n=" ++ show n ++ " win=" ++ show h ++ " d=" ++ show d )
               ( twoSegmentInstance n h 2 d )
      | ( n, h, d ) <- [ ( 4, 8, 2 ), ( 6, 12, 2 ), ( 8, 16, 2 ) ]
      ]
  , bgroup "tight clique (n duration-d tasks, horizon n·d)"
      [ triple ( "n=" ++ show n ++ " d=" ++ show d )
               ( tightCliqueInstance n d )
      | ( n, d ) <- [ ( 4, 2 ), ( 6, 2 ), ( 8, 2 ), ( 12, 2 ) ]
      ]
  , bgroup "chained window (each task k in [k, k+w])"
      [ triple ( "n=" ++ show n ++ " w=" ++ show w )
               ( chainedWindowInstance n w 1 )
      | ( n, w ) <- [ ( 4, 2 ), ( 6, 2 ), ( 8, 2 ), ( 12, 2 ) ]
      ]
  , bgroup "chained-window + extra task (structured infeasibility)"
      [ triple ( "n=" ++ show n ++ " w=" ++ show w )
               ( chainedOverloadedInstance n w 1 )
      | ( n, w ) <- [ ( 4, 2 ), ( 6, 2 ), ( 8, 2 ) ]
      ]
  ]
