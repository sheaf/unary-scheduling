{-# LANGUAGE ScopedTypeVariables #-}

-- | CNF instance generators and pure solver runners for the MiniSAT/CDCL
-- benchmarks, with no dependency on @tasty@ or @tasty-bench@.
module SAT.Bench.Instances
  ( -- * CNF representation
    CNF(..), RawLit, Clause
    -- * Runners
  , solveCNF, solveTwice
    -- * Instance families
  , pigeonhole
  , random3SAT
  , implicationChain
  , graphColouringCNF
  , precedenceTransitivityCNF
  , precedenceWithForcedCNF
  )
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
import Schedule.Ordering
  ( upperTriangular )

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
-- Precedence-transitivity CNFs

-- | Variable index for the unordered pair @(i, j)@ with @i < j@.
precVarIx :: Int -> Int -> Int -> Int
precVarIx dim i j = upperTriangular dim i j

-- | The acyclicity-over-triples CNF for @n@ tasks: @2 · C(n, 3)@ clauses
-- of length 3, over @C(n, 2)@ variables.
precedenceTransitivityCNF :: Int -> CNF
precedenceTransitivityCNF n = CNF numVars clauses
  where
    numVars = n * ( n - 1 ) `div` 2
    v i j   = precVarIx n i j
    clauses = concat
      [ [ -- forbids i→j ∧ j→k ∧ k→i
          [ ( v i j, Negative ), ( v j k, Negative ), ( v i k, Positive ) ]
        , -- forbids j→i ∧ k→j ∧ i→k
          [ ( v i j, Positive ), ( v j k, Positive ), ( v i k, Negative ) ]
        ]
      | i <- [ 0 .. n - 1 ]
      , j <- [ i + 1 .. n - 1 ]
      , k <- [ j + 1 .. n - 1 ]
      ]

-- | Add @nForced@ random unit clauses (a random partial ordering) on top
-- of 'precedenceTransitivityCNF'. The result is SAT iff the forced units
-- are jointly acyclic; the SAT core has to propagate the transitive closure
-- of the units across the acyclicity clauses.
precedenceWithForcedCNF :: Int -> Int -> Int -> CNF
precedenceWithForcedCNF n nForced seed =
  CNF numVars ( transitivity ++ units )
  where
    CNF numVars transitivity = precedenceTransitivityCNF n
    units                    = take nForced ( genUnits ( mkStdGen seed ) )
    -- All ordered (i, j) pairs with i ≠ j; each contributes one possible
    -- forced unit (positive if i < j, negative otherwise).
    genUnits :: StdGen -> [ Clause ]
    genUnits g0 =
      let ( i, g1 ) = randomR ( 0, n - 1 ) g0
          ( j, g2 ) = randomR ( 0, n - 1 ) g1
      in case compare i j of
           EQ -> genUnits g2
           LT -> [ ( precVarIx n i j, Positive ) ] : genUnits g2
           GT -> [ ( precVarIx n j i, Negative ) ] : genUnits g2

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
