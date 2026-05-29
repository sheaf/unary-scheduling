-- | Microbenchmarks for the MiniSAT/CDCL component.
--
-- Each iteration sets up a fresh 'Solver', posts the CNF, and calls
-- 'solveWith'. Solver creation is part of every measurement; for tracking
-- regressions on the cumulative "post a problem and solve it" path that
-- is what we want. CNF construction itself is hoisted out via 'env' so
-- it doesn't pollute the timing.
--
-- The CNF representation, the @solve@ runners, and the instance families
-- live in "SAT.Bench.Instances" (which carries no @tasty@ dependency); this
-- module is only the @tasty-bench@ wiring around them.
module SAT.Bench
  ( benchmarks )
  where

-- tasty
import Test.Tasty
  ( localOption, mkTimeout )

-- tasty-bench
import Test.Tasty.Bench
  ( Benchmark, RelStDev(..), bgroup, bench, env, whnf )

-- unary-scheduling
import SAT
  ( Polarity(..) )

-- unary-scheduling bench suite
import SAT.Bench.Instances
  ( CNF(..)
  , solveCNF, solveTwice
  , pigeonhole, random3SAT, implicationChain, graphColouringCNF
  , precedenceTransitivityCNF, precedenceWithForcedCNF
  )

-------------------------------------------------------------------------------
-- Suite.

-- | The full benchmark suite.
benchmarks :: [ Benchmark ]
benchmarks =
  -- tolerate higher variance to avoid tests taking too long
  map ( localOption ( RelStDev 0.1 ) . localOption ( mkTimeout 5_000_000 ) )
  [ bgroup "baseline (solver-setup-dominated)"
      [ bench "empty CNF"
          $ whnf solveCNF ( CNF 0 [] )
      , bench "single unit clause"
          $ whnf solveCNF ( CNF 1 [ [ ( 0, Positive ) ] ] )
      , bench "1000 vars, no clauses"
          $ whnf solveCNF ( CNF 1000 [] )
      ]
  , bgroup "pigeonhole"
      [ pigeon n | n <- [ 4, 5, 6, 7 ] ]
  , bgroup "random 3-SAT near the phase transition (m/n ≈ 4.26)"
      [ threeSAT n m seed
      | ( n, m ) <- [ ( 20, 85 ), ( 40, 170 ), ( 60, 255 ) ]
      , seed     <- [ 1, 42 ]
      ]
  , bgroup "binary implication chain"
      [ binaryChain n | n <- [ 100, 1000, 10000 ] ]
  , bgroup "graph 3-colouring near the threshold (|E|/|V| ≈ 2.27)"
      [ graphColouring nV nE seed
      | ( nV, nE ) <- [ ( 20, 46 ), ( 30, 68 ) ]
      , seed       <- [ 1, 42 ]
      ]
  , bgroup "incremental: solve + block + re-solve"
      [ incremental n m seed
      | ( n, m ) <- [ ( 15, 45 ), ( 25, 70 ) ]
      , seed     <- [ 1, 42 ]
      ]
  , bgroup "precedence transitivity"
      [ precTrans n
      | n <- [ 6, 8, 12, 16 ]
      ]
  , bgroup "precedence transitivity + random forced units"
      [ precForced n nForced seed
      | ( n, nForced ) <- [ ( 8, 6 ), ( 12, 10 ), ( 16, 14 ), ( 20, 18 ) ]
      , seed           <- [ 1, 42 ]
      ]
  ]
  where
    pigeon n =
      env ( pure $ pigeonhole n ) \ cnf ->
        bench ( "PHP " ++ show n ) ( whnf solveCNF cnf )
    threeSAT n m seed =
      env ( pure $ random3SAT n m seed ) \ cnf ->
        bench
          ( "N=" ++ show n ++ " M=" ++ show m ++ " seed=" ++ show seed )
          ( whnf solveCNF cnf )
    binaryChain n =
      env ( pure $ implicationChain n ) \ cnf ->
        bench ( "N=" ++ show n ) ( whnf solveCNF cnf )
    graphColouring nV nE seed =
      env ( pure $ graphColouringCNF nV nE seed ) \ cnf ->
        bench
          ( "V=" ++ show nV ++ " E=" ++ show nE ++ " seed=" ++ show seed )
          ( whnf solveCNF cnf )
    incremental n m seed =
      env ( pure $ random3SAT n m seed ) \ cnf ->
        bench
          ( "N=" ++ show n ++ " M=" ++ show m ++ " seed=" ++ show seed )
          ( whnf solveTwice cnf )
    precTrans n =
      env ( pure $ precedenceTransitivityCNF n ) \ cnf ->
        bench ( "n=" ++ show n ) ( whnf solveCNF cnf )
    precForced n nForced seed =
      env ( pure $ precedenceWithForcedCNF n nForced seed ) \ cnf ->
        bench
          ( "n=" ++ show n ++ " forced=" ++ show nForced ++ " seed=" ++ show seed )
          ( whnf solveCNF cnf )
