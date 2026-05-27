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
import Data.Maybe
  ( mapMaybe )
import GHC.Generics
  ( Generic )

-- deepseq
import Control.DeepSeq
  ( NFData )

-- random
import System.Random
  ( StdGen, mkStdGen, randomR )

-- tasty
import Test.Tasty
  ( localOption )

-- tasty-bench
import Test.Tasty.Bench
  ( Benchmark, RelStDev(..), bgroup, bench, env, whnf )

-- unary-scheduling
import SAT
  ( Var(..), Lit, mkLit
  , Polarity(..)
  , LBool(..)
  , Verdict(..)
  , newSolver, newVar
  , addClause, PostResult(..)
  , solveWith, defaultOptions
  , getModel, assignmentValue
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
-- Binary implication chain (BCP-only, SAT).

-- | A binary implication chain problem. Solving this is pure
-- Binary Constraint Propagation.
implicationChain :: Int -> CNF
implicationChain n = CNF n ( unit : chain )
  where
    unit  = [ ( 0, Positive ) ]
    chain = [ [ ( i, Negative ), ( i + 1, Positive ) ] | i <- [ 0 .. n - 2 ] ]

-------------------------------------------------------------------------------
-- Random graph @k@-colouring.

-- | A random graph 3-colouring instance with @nVerts@ vertices and up to
-- @nEdges@ edges.
--
-- The 3-colouring satisfiability threshold for Erdős–Rényi graphs lies
-- near @|E|/|V| ≈ 2.27@; instances generated at that density mix
-- satisfiable and unsatisfiable cases depending on the seed.
graphColouringCNF
  :: Int  -- ^ number of vertices
  -> Int  -- ^ number of edges
  -> Int  -- ^ PRNG seed
  -> CNF
graphColouringCNF nVerts nEdges seed =
  CNF ( nVerts * k ) ( atLeastOne ++ atMostOne ++ edgeConstraints )
  where
    k :: Int
    k = 3

    var i c = i * k + c

    atLeastOne =
      [ [ ( var i c, Positive ) | c <- [ 0 .. k - 1 ] ]
      | i <- [ 0 .. nVerts - 1 ]
      ]

    atMostOne =
      [ [ ( var i c1, Negative ), ( var i c2, Negative ) ]
      | i  <- [ 0 .. nVerts - 1 ]
      , c1 <- [ 0 .. k - 1 ]
      , c2 <- [ c1 + 1 .. k - 1 ]
      ]

    edgeConstraints =
      [ [ ( var i c, Negative ), ( var j c, Negative ) ]
      | ( i, j ) <- edges
      , c <- [ 0 .. k - 1 ]
      ]

    edges :: [ ( Int, Int ) ]
    edges = genEdges nEdges ( mkStdGen seed )

    genEdges :: Int -> StdGen -> [ ( Int, Int ) ]
    genEdges 0 _ = []
    genEdges m g0 =
      let ( i, g1 ) = randomR ( 0, nVerts - 1 ) g0
          ( j, g2 ) = randomR ( 0, nVerts - 1 ) g1
      in if i == j
         then genEdges m g2
         else ( i, j ) : genEdges ( m - 1 ) g2

-------------------------------------------------------------------------------
-- Incremental solve: solve, block the model, solve again.

-- | Post the CNF, solve it; on 'Sat', add a blocking clause derived from
-- the model and solve again. Returns the second solve's verdict; the
-- first is forced as a by-product.
--
-- Exercises the 'addClause'/'solveWith' cycle.
solveTwice :: CNF -> Verdict
solveTwice ( CNF nVars cls ) = runST \ @s -> do
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
  else do
    v1 <- solveWith defaultOptions solver
    case v1 of
      Sat -> do
        m <- getModel solver
        let blockingLit :: Int -> Maybe Lit
            blockingLit i = case assignmentValue ( Var i ) m of
              LTrue  -> Just ( mkLit ( Var i ) Negative )
              LFalse -> Just ( mkLit ( Var i ) Positive )
              LUndef -> Nothing
            blocking = mapMaybe blockingLit [ 0 .. nVars - 1 ]
        r <- addClause solver blocking
        case r of
          InstantUnsat -> pure Unsat
          Tautology    -> pure Sat  -- only possible if the model is empty
          Posted       -> solveWith defaultOptions solver
      _ -> pure v1

-------------------------------------------------------------------------------
-- Suite.

-- | The full benchmark suite.
benchmarks :: [ Benchmark ]
benchmarks =
  -- tolerate higher variance to avoid tests taking too long
  map ( localOption ( RelStDev 0.2 ) )
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
