{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Add a precedence to the scheduler state (without LCG).
--
-- This is the unified, non-SAT entry point for adding a precedence
-- @T_i ≺ T_j@ to the ordering matrix and emitting the immediate
-- bound-tightening consequences.
module Schedule.Precedence
  ( addEdge )
  where

-- containers
import qualified Data.IntSet as IntSet
  ( singleton )
import qualified Data.Sequence as Seq
  ( singleton )

-- lens
import Control.Lens
  ( modifying )

-- generic-lens
import Data.Generics.Product.Fields
  ( field' )

-- mtl
import Control.Monad.Reader
  ( ask )

-- vector
import qualified Data.Vector.Mutable as Boxed
  ( MVector )

-- unary-scheduling
import Data.Vector.Generic.Index
  ( unsafeIndex )
import Schedule.Constraint
  ( Constraint(..), Infeasible(..), Justification(..), tightenMany )
import Schedule.Interval
  ( Measurable )
import Schedule.Monad
  ( MonadSchedule
  , constrain
  )
import Schedule.Ordering
  ( CycleInfo
  , addIncidentEdgesTransitively
  )
import Schedule.Task
  ( Task, TaskInfos(..)
  , lst, ect
  )
import Schedule.Trail
  ( Trail, orderingCellWriter )

-------------------------------------------------------------------------------

-- | Add a precedence @T_start ≺ T_end@ to the ordering matrix, computing
-- the transitive closure and emitting bound-tightening constraints for
-- each genuinely new edge.
--
-- Throws via 'MonadError' if the addition would create a cycle.
addEdge
  :: forall m task t s
  .  ( MonadSchedule s task t m
     , Num t, Measurable t, Bounded t
     )
  => Trail s task t
  -> Int                 -- ^ start task index
  -> Int                 -- ^ end task index
  -> m ()
addEdge trail start end = do
  tis@( TaskInfos { taskAvails, orderings } ) <- ask

  -- Structured audit-log entry for the inference explanation channel.
  modifying ( field' @"taskConstraints" . field' @"justifications" )
    ( <> Seq.singleton ( SearchPrecedence { earlier = start, later = end } ) )

  addIncidentEdgesTransitively
    ( orderingCellWriter trail tis )
    ( \ _origin i j -> propagateNewEdge taskAvails i j )
    errorMessage
    orderings
    end ( IntSet.singleton start ) mempty

  where
    propagateNewEdge :: Boxed.MVector s ( Task task t ) -> Int -> Int -> m ()
    propagateNewEdge avails i j = do
      tk_i <- avails `unsafeIndex` i
      tk_j <- avails `unsafeIndex` j
      constrain $
        tightenMany
          -- NB: the precedence itself is added by the matrix update; here
          -- we only emit the immediate bound consequences.
          [ ( i, NotLaterThan   $ lst tk_j )
          , ( j, NotEarlierThan $ ect tk_i )
          ]

    errorMessage :: CycleInfo -> Infeasible t
    errorMessage info = CycleDetected { cycleInfo = info, addedEdge = ( start, end ) }
