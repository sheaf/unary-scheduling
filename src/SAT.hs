-- | A small Clause-Driven Conflict Learning core.
--
-- This module re-exports the public surface of the SAT subsystem: the
-- literal vocabulary ('SAT.Base'), the solver state ('SAT.Solver') and its
-- top-level entry points. Clauses and reasons are exposed by their own
-- module ('SAT.Clause') for callers that want to construct them directly.
module SAT
  ( -- * Literals
    module SAT.Base
    -- * Solver
  , module SAT.Solver
  )
  where

import SAT.Base
import SAT.Solver
