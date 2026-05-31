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
  , randomWindowedInstance, rehearsalInstance
  , overloadedInstance
  , tightCliqueInstance
  , intervalPigeonholeInstance
  , infeasibleRehearsalInstance
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
    -- Near the feasibility boundary (util=1.0, avail=0.4): feasible, but the
    -- structural heuristic backtracks. Seeds chosen per size so each is feasible
    -- (Z3-verified) yet forces conflicts — the only feasible family that exercises
    -- conflict-driven learning, since slacker rehearsals solve with 0 conflicts.
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
    -- Capped at 2 for runtime: copies=3's search is exponential (minutes).
  , bgroup "infeasible: bin-packing fragmentation (overload-free; search-hard)"
      [ triple ( "copies=" ++ show c ++ " (" ++ show ( 5 * c ) ++ " songs, " ++ show ( 3 * c ) ++ " days)" )
               ( infeasibleRehearsalInstance c )
      | c <- [ 1, 2 ]
      ]
  ]
