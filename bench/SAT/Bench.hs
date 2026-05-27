{-# LANGUAGE ScopedTypeVariables #-}

-- | Microbenchmarks for the MiniSAT/CDCL component.
--
-- Each iteration sets up a fresh 'Solver', posts the CNF, and calls
-- 'solveWith'. Solver creation is part of every measurement; for tracking
-- regressions on the cumulative "post a problem and solve it" path that
-- is what we want. CNF construction itself is hoisted out via 'env' so
-- it doesn't pollute the timing.
module SAT.Bench
  ( benchmarks )
  where

-- base
import Control.Monad
  ( foldM, replicateM_ )
import Control.Monad.ST
  ( ST, runST )
import GHC.Generics
  ( Generic )

-- deepseq
import Control.DeepSeq
  ( NFData )

-- random
import System.Random
  ( StdGen, mkStdGen, randomR )

-- tasty-bench
import Test.Tasty.Bench
  ( Benchmark, bgroup, bench, env, whnf )

-- unary-scheduling
import SAT
  ( Var(..), mkLit
  , Polarity(..)
  , Verdict(..)
  , newSolver, newVar
  , addClause, PostResult(..)
  , solveWith, defaultOptions
  )

-------------------------------------------------------------------------------
-- A small CNF representation local to the benchmarks.

-- | A single literal, encoded as (variable index, polarity).
--
-- The 'Int' is a 0-based variable index.
type RawLit = ( Int, Polarity )

-- | A clause is a disjunction of 'RawLit's.
type Clause = [ RawLit ]

-- | A CNF formula: number of variables and clauses.
data CNF = CNF !Int [ Clause ]
  deriving stock    Generic
  deriving anyclass NFData

solveCNF :: CNF -> Verdict
solveCNF ( CNF nVars cls ) = runST \ @s -> do
  solver <- newSolver @( ST s )
  replicateM_ nVars ( newVar solver )
  let toLit ( i, pol ) = mkLit ( Var i ) pol
      addStep :: Bool -> Clause -> ST s Bool
      addStep False _  = pure False
      addStep True  cl = do
        r <- addClause solver ( map toLit cl )
        pure ( r /= InstantUnsat )
  ok <- foldM addStep True cls
  if not ok
  then pure Unsat
  else solveWith defaultOptions solver

-------------------------------------------------------------------------------
-- Pigeonhole (UNSAT).

-- | Encode the pigeonhole principle PHP(@n+1@, @n@): @n+1@ pigeons must
-- each fit in one of @n@ holes, and no two pigeons share a hole.
--
-- Always unsatisfiable; the size of the resolution proof is exponential in @n@
-- so even modest values stress conflict learning.
pigeonhole :: Int -> CNF
pigeonhole n = CNF numVars ( atLeastOneHole ++ atMostOnePigeon )
  where
    pigeons = [ 0 .. n ]        -- n+1 pigeons
    holes   = [ 0 .. n - 1 ]    -- n holes
    numVars = ( n + 1 ) * n
    -- The variable representing "pigeon @i@ sits in hole @j@".
    var i j = i * n + j
    -- Every pigeon must occupy at least one hole.
    atLeastOneHole =
      [ [ ( var i j, Positive ) | j <- holes ]
      | i <- pigeons
      ]
    -- For every (hole, pigeon-pair): at most one of them is in the hole.
    atMostOnePigeon =
      [ [ ( var i j, Negative ), ( var k j, Negative ) ]
      | j <- holes, i <- pigeons, k <- pigeons, k > i
      ]

-------------------------------------------------------------------------------
-- Random 3-SAT.

-- | Generate a random 3-SAT instance with @n@ variables and @m@ clauses.
--
-- Each clause picks three variable indices independently and uniformly
-- with random polarities.
random3SAT
  :: Int  -- ^ number of variables
  -> Int  -- ^ number of clauses
  -> Int  -- ^ PRNG seed
  -> CNF
random3SAT nVars nClauses seed =
  CNF nVars ( build ( mkStdGen seed ) nClauses )
  where
    build :: StdGen -> Int -> [ Clause ]
    build _ 0 = []
    build g k =
      let ( cl, g' ) = genClause g
      in cl : build g' ( k - 1 )

    genClause :: StdGen -> ( Clause, StdGen )
    genClause g0 =
      let ( i1, g1 ) = randomR ( 0, nVars - 1 ) g0
          ( i2, g2 ) = randomR ( 0, nVars - 1 ) g1
          ( i3, g3 ) = randomR ( 0, nVars - 1 ) g2
          ( p1, g4 ) = genPol g3
          ( p2, g5 ) = genPol g4
          ( p3, g6 ) = genPol g5
      in ( [ ( i1, p1 ), ( i2, p2 ), ( i3, p3 ) ], g6 )

    genPol :: StdGen -> ( Polarity, StdGen )
    genPol g = case randomR ( 0 :: Int, 1 ) g of
      ( 0, g' ) -> ( Positive, g' )
      ( _, g' ) -> ( Negative, g' )

-------------------------------------------------------------------------------
-- Suite.

-- | The full benchmark suite.
benchmarks :: [ Benchmark ]
benchmarks =
  [ bgroup "pigeonhole (UNSAT)"
      [ phpBench n | n <- [ 4, 5, 6 ] ]
  , bgroup "random 3-SAT near the phase transition (m/n ≈ 4.26)"
      [ r3Bench n m seed
      | ( n, m ) <- [ ( 20, 85 ), ( 40, 170 ), ( 60, 255 ) ]
      , seed     <- [ 1, 42 ]
      ]
  , bgroup "baseline (solver-setup-dominated)"
      [ bench "empty CNF"
          $ whnf solveCNF ( CNF 0 [] )
      , bench "single unit clause"
          $ whnf solveCNF ( CNF 1 [ [ ( 0, Positive ) ] ] )
      , bench "1000 vars, no clauses"
          $ whnf solveCNF ( CNF 1000 [] )
      ]
  ]
  where
    phpBench n =
      env ( pure $ pigeonhole n ) \ cnf ->
        bench ( "PHP " ++ show n ) ( whnf solveCNF cnf )
    r3Bench n m seed =
      env ( pure $ random3SAT n m seed ) \ cnf ->
        bench
          ( "N=" ++ show n ++ " M=" ++ show m ++ " seed=" ++ show seed )
          ( whnf solveCNF cnf )
