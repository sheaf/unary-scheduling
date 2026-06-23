{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Adding a precedence to the scheduler state.
module Schedule.Precedence
  ( addEdge, addMatrixEdge )
  where

-- containers
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
  ( EdgeOrigin
  , OrderingMatrix(..)
  , TransitiveClosureScratch, newTransitiveClosureScratch
  , insertEdgeTransitively
  )
import Schedule.Task
  ( Task, TaskInfos(..)
  , lst, ect
  )
import Schedule.Trail
  ( Trail, orderingCellWriter )

-------------------------------------------------------------------------------

-- | Insert a single precedence edge @T_u ≺ T_w@ into the ordering matrix,
-- maintaining the transitive closure ('insertEdgeTransitively') and reporting a
-- closure-closing cycle as an 'Infeasible' 'CycleDetected'.
addMatrixEdge
  :: forall m task t s
  .  MonadSchedule s task t m
  => Trail s task t
  -> TransitiveClosureScratch s
  -> ( EdgeOrigin -> Int -> Int -> m () ) -- ^ reaction to a genuinely new edge
  -> Int -- ^ @u@: predecessor task index
  -> Int -- ^ @w@: successor task index
  -> m ()
addMatrixEdge trail scratch onNewEdge u w = do
  tis@( TaskInfos { orderings } ) <- ask
  insertEdgeTransitively scratch
    ( orderingCellWriter trail tis )
    onNewEdge
    ( \ info -> CycleDetected { cycleInfo = info, addedEdge = ( u, w ) } )
    orderings u w

-- | Add a precedence @T_start ≺ T_end@ to the ordering matrix, computing the
-- transitive closure and emitting bound-tightening constraints for each
-- genuinely new edge.
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
  TaskInfos { taskAvails, orderings = OrderingMatrix { dim } } <- ask

  -- Structured audit-log entry for the inference explanation channel.
  modifying ( field' @"taskConstraints" . field' @"justifications" )
    ( <> Seq.singleton ( SearchPrecedence { earlier = start, later = end } ) )

  scratch <- newTransitiveClosureScratch dim
  addMatrixEdge trail scratch
    ( \ _origin i j -> propagateNewEdge taskAvails i j )
    start end

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
