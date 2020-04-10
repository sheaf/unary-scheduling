{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

module Schedule
  ( Propagator(..), allPropagators
  , propagateConstraints, propagationLoop
  )
  where

-- mtl
import Control.Monad.Writer
  ( listen )

-- text
import Data.Text
  ( Text )

-- unary-scheduling
import Schedule.Constraint
  ( Constraints(..), applyConstraints )
import Schedule.Interval
  ( Normalisable )
import Schedule.Monad
  ( ScheduleMonad, runScheduleMonad )
import Schedule.Propagators
  ( normalise, prune, timetable
  , overloadCheck, detectablePrecedences
  , notExtremal, edgeFinding
  )
import Schedule.Task
  ( Task, ImmutableTasks )
import Schedule.Time
  ( Handedness
    ( Earliest, Latest )
  )

-------------------------------------------------------------------------------

-- | Wrapper for a propagator (to avoid impredicativity).
newtype Propagator task t =
  Propagator { runPropagator :: forall s. ScheduleMonad s task t () }

allPropagators :: ( Num t, Ord t, Bounded t, Normalisable t, Show t ) => [ Propagator task t ]
allPropagators =
  [ Propagator $ normalise
  , Propagator $ prune
  , Propagator $ overloadCheck
  , Propagator $ timetable
  , Propagator $ detectablePrecedences @Earliest
  , Propagator $ detectablePrecedences @Latest
  , Propagator $ notExtremal @Earliest -- not last
  , Propagator $ notExtremal @Latest   -- not first
  , Propagator $ edgeFinding @Earliest
  , Propagator $ edgeFinding @Latest
  ]

-- | Propagates constraints for the scheduling of a given collection of (named) tasks,
-- using the provided propagators.
--
-- Propagation proceeds in a loop, returning to the beginning of the loop
-- when any subsequent propagator emits new constraints.
--
-- Returns the constrained tasks, an explanation of how the constraints arose,
-- and, if the tasks proved to be unschedulable, an explanation for that too.
propagateConstraints
   :: forall task t
   .  ( Num t, Ord t, Bounded t, Show t, Show task )
   => ( Either [ ( Task task t, Text ) ] ( ImmutableTasks task t ) )
   -> Int
   -> [ Propagator task t ]
   -> ( ImmutableTasks task t, Text, Maybe Text )
propagateConstraints taskData maxLoopIterations propagators =
  case runScheduleMonad taskData ( propagationLoop maxLoopIterations propagators ) of
    ( updatedTasks, ( mbGaveUpText, Constraints { justifications } ) ) ->
      ( updatedTasks, justifications, either Just (const Nothing) mbGaveUpText )


-- | Run the given propagators in a loop until no new constraints are emitted.
--
-- Goes back to the start of the list of propagators each time a new constraint is emitted.
propagationLoop
  :: forall s task t
  .  ( Num t, Ord t, Bounded t
     -- debugging
     , Show t, Show task
     )
  => Int
  -> [ Propagator task t ]
  -> ScheduleMonad s task t ()
propagationLoop maxLoopIterations propagators = go 0 propagators
  where
    go :: Int -> [ Propagator task t ] -> ScheduleMonad s task t ()
    go _ []
      = pure ()
    go i _
      | i >= maxLoopIterations
      = pure ()
    go i ( Propagator { runPropagator = runCurrentPropagator } : followingPropagators ) = do
      ( _, newConstraints ) <- listen runCurrentPropagator
      if null ( constraints newConstraints )
      then go i followingPropagators
      else do
        applyConstraints newConstraints
        go (i+1) propagators
