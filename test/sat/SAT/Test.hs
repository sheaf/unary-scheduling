{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Differential testing of the CDCL core against Z3.
module SAT.Test ( tests ) where

-- base
import Control.Monad
  ( foldM, replicateM_ )
import Control.Monad.ST
  ( ST, runST )
import Data.Foldable
  ( for_ )

-- hedgehog
import Hedgehog
  ( Gen, Property
  , annotateShow, evalIO, forAll, property, (===), withTests
  )
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

-- tasty
import Test.Tasty
  ( TestTree, testGroup )
import Test.Tasty.Hedgehog
  ( testPropertyNamed )

-- vector
import qualified Data.Vector as Boxed.Vector
  ( generateM, (!) )

-- z3
import qualified Z3.Monad as Z3

-- unary-scheduling
import SAT.Base
  ( Var(..), Lit, mkLit
  , Polarity(..)
  , Ł3(..)
  )
import SAT.Solver
  ( SolverState, newSolver, newVar
  , addClause, PostResult(..)
  , solveWith, getModel
  , Assignment, assignmentValue
  , solverAssignments
  , SolverOptions(..), defaultSolverOptions
  , Verdict(..)
  )

--------------------------------------------------------------------------------
-- A simple CNF representation, generator-side.

-- | Variables are labelled @0 .. nVars - 1@.
data RawLit = RawLit !Int !Polarity
  deriving stock ( Eq, Ord, Show )

data CNF = CNF
  { cnfVars    :: !Int
  , cnfClauses :: ![ [ RawLit ] ]
  }
  deriving stock ( Eq, Show )

--------------------------------------------------------------------------------
-- Generators.

genCNF :: Gen CNF
genCNF = do
  nVars <- Gen.int ( Range.linear 1 8 )
  let
    genLit :: Gen RawLit
    genLit = RawLit
      <$> Gen.int ( Range.constant 0 ( nVars - 1 ) )
      <*> Gen.element [ Positive, Negative ]
    genClause :: Gen [ RawLit ]
    genClause = Gen.list ( Range.linear 1 5 ) genLit
  nCls <- Gen.int ( Range.linear 0 ( 4 * nVars ) )
  cls  <- Gen.list ( Range.singleton nCls ) genClause
  pure ( CNF nVars cls )

--------------------------------------------------------------------------------
-- Native solver driver.

-- | Run the CDCL solver on a CNF, returning the verdict and, when SAT, the
-- satisfying assignment.
--
-- Variables are minted in order, so a 'RawLit' index @i@ corresponds to
-- 'Var' @i@ directly without an indirection table.
nativeSolve :: CNF -> ( Verdict, Maybe Assignment )
nativeSolve ( CNF nVars cls ) = runST \ @s -> do
  s <- newSolver @( ST s )
  replicateM_ nVars ( newVar s )
  ok <- addAll s ( map ( map rawToLit ) cls )
  if not ok
  then pure ( Unsat, Nothing )
  else do
    v <- solveWith options s
    case v of
      Sat -> do
        m <- getModel ( solverAssignments s )
        pure ( Sat, Just m )
      _ -> pure ( v, Nothing )
  where
    options :: SolverOptions
    options = defaultSolverOptions { optConflictBudget = 50000 }

rawToLit :: RawLit -> Lit
rawToLit ( RawLit i pol ) = mkLit ( Var ( fromIntegral i ) ) pol

-- | Post every clause. Returns 'False' once any clause makes the problem
-- instantly UNSAT; subsequent clauses are skipped.
addAll :: SolverState s -> [ [ Lit ] ] -> ST s Bool
addAll s = foldM step True
  where
    step False _ = pure False
    step True  c = do
      r <- addClause s c
      pure ( r /= InstantUnsat )

--------------------------------------------------------------------------------
-- Z3 oracle.

-- | Decide SAT for a CNF using Z3.
z3SolveCNF :: CNF -> IO Bool
z3SolveCNF ( CNF nVars cls ) = Z3.evalZ3 do
  vs <- Boxed.Vector.generateM nVars \ i ->
    Z3.mkFreshBoolVar ( "x" <> show i )
  let
    z3Lit :: RawLit -> Z3.Z3 Z3.AST
    z3Lit ( RawLit i pol ) = case pol of
      Positive -> pure ( vs Boxed.Vector.! i )
      Negative -> Z3.mkNot ( vs Boxed.Vector.! i )
  for_ cls \ clause -> do
    lits <- mapM z3Lit clause
    case lits of
      []   -> Z3.assert =<< Z3.mkFalse
      [ a ] -> Z3.assert a
      as   -> Z3.assert =<< Z3.mkOr as
  res <- Z3.check
  pure ( res == Z3.Sat )

--------------------------------------------------------------------------------
-- Local clause checker (verifies a native model without calling Z3).

modelSatisfies :: Assignment -> CNF -> Bool
modelSatisfies a ( CNF _ cls ) = all clauseHolds cls
  where
    clauseHolds = any litHolds
    litHolds ( RawLit i pol ) = case assignmentValue ( Var ( fromIntegral i ) ) a of
      ŁTrue  -> case pol of { Positive -> True;  Negative -> False }
      ŁFalse -> case pol of { Positive -> False; Negative -> True  }
      ŁUndef -> True   -- free variable: the model is consistent under either value

--------------------------------------------------------------------------------
-- Properties.

-- | Whenever our solver reports SAT, the assignment must satisfy every clause.
prop_native_model_is_a_model :: Property
prop_native_model_is_a_model = withTests 200 $ property do
  cnf <- forAll genCNF
  case nativeSolve cnf of
    ( Sat, Just m ) -> do
      annotateShow m
      modelSatisfies m cnf === True
    _ -> pure ()

-- | Native SAT/UNSAT must agree with Z3.
prop_native_agrees_with_z3 :: Property
prop_native_agrees_with_z3 = withTests 200 $ property do
  cnf <- forAll genCNF
  let ( nat, _ ) = nativeSolve cnf
  case nat of
    Unknown -> pure ()    -- conflict budget exhausted; skip
    _ -> do
      z3 <- evalIO ( z3SolveCNF cnf )
      annotateShow ( nat, z3 )
      ( nat == Sat ) === z3

--------------------------------------------------------------------------------
-- Edge cases.

solveLits :: Int -> [ [ RawLit ] ] -> Verdict
solveLits n cls = fst ( nativeSolve ( CNF n cls ) )

unitTests :: TestTree
unitTests = testGroup "edge cases"
  [ testPropertyNamed "empty CNF is SAT"
      "prop_empty_cnf_sat"
      ( withTests 1 $ property $ solveLits 0 [] === Sat )
  , testPropertyNamed "empty clause is UNSAT"
      "prop_empty_clause_unsat"
      ( withTests 1 $ property $ solveLits 1 [ [] ] === Unsat )
  , testPropertyNamed "unit and its negation"
      "prop_unit_contradiction"
      ( withTests 1 $ property $
          solveLits 1 [ [ RawLit 0 Positive ], [ RawLit 0 Negative ] ] === Unsat )
  , testPropertyNamed "tautological clause kept"
      "prop_tautology"
      ( withTests 1 $ property $
          solveLits 1 [ [ RawLit 0 Positive, RawLit 0 Negative ] ] === Sat )
  , testPropertyNamed "pigeonhole 3-into-2 is UNSAT"
      "prop_php32"
      ( withTests 1 $ property $ solveLits 6 php32 === Unsat )
  ]
  where
    -- Three pigeons (rows), two holes (columns). x_{i,j} = pigeon i in hole j.
    -- Encoded with variable index i*2 + j.
    php32 :: [ [ RawLit ] ]
    php32 =
      -- Every pigeon goes in some hole.
      [ [ RawLit ( i * 2 + j ) Positive | j <- [ 0, 1 ] ] | i <- [ 0, 1, 2 ] ]
      ++
      -- No two pigeons share a hole.
      [ [ RawLit ( i * 2 + j ) Negative, RawLit ( k * 2 + j ) Negative ]
      | j <- [ 0, 1 ], i <- [ 0, 1, 2 ], k <- [ i + 1 .. 2 ]
      ]

--------------------------------------------------------------------------------
-- Test tree.

tests :: TestTree
tests = testGroup "SAT"
  [ unitTests
  , testGroup "differential against Z3"
      [ testPropertyNamed "native model satisfies its CNF"
          "prop_native_model_is_a_model"
          prop_native_model_is_a_model
      , testPropertyNamed "native and Z3 agree on SAT/UNSAT"
          "prop_native_agrees_with_z3"
          prop_native_agrees_with_z3
      ]
  ]
