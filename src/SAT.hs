-- | A Conflict-Driven Clause-Learning (CDCL) SAT core.
module SAT
  ( -- * Literals
    module SAT.Base
    -- * Solver
  , SolverState
  , newSolver
    -- * Building the problem
  , newVar
  , addClause
  , PostResult(..)
  , numVariables
    -- * Solving
  , Verdict(..)
  , solve
  , solveWith
  , SolverOptions(..)
  , defaultOptions
    -- * Inspection
  , Assignment
  , assignmentValue
  , getModel
  , valueOf
  , numConflicts
  , numDecisions
  , numLearnts
  )
  where

import SAT.Base
import SAT.Solver
