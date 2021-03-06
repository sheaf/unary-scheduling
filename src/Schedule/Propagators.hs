{-# LANGUAGE AllowAmbiguousTypes        #-}
{-# LANGUAGE BlockArguments             #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE NamedFieldPuns             #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE QuantifiedConstraints      #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE UndecidableInstances       #-}

module Schedule.Propagators
  ( -- * Propagator framework.
    Propagator(..), basicPropagators
  , propagateConstraints, propagationLoop
    -- * Local constraint propagators.
  , prune, prunePropagator
  , timetable, timetablePropagator
    -- * Global constraint propagators.
    -- ** Overload checking
  , overloadCheck, overloadPropagator
    -- ** Detectable precedences
  , detectablePrecedences, detectablePrecedencesPropagator, detectableSuccedencesPropagator
    -- ** Not first / not last
  , notExtremal, notLastPropagator, notFirstPropagator
    -- ** Edge finding
  , edgeFinding, edgeLastPropagator, edgeFirstPropagator
    -- ** Precedence matrix
  , precedenceMatrix, predecessorPropagator, successorPropagator
    -- ** Experimental makespan propagator.
  , makespan
  )
  where

-- base
import Control.Monad
  ( when, unless, void )
import Data.Coerce
  ( coerce )
import Data.Functor.Identity
  ( Identity(..) )
import Data.Kind
  ( Type )
import Data.Semigroup
  ( Arg(..) )
import Data.Foldable
  ( for_ )

-- acts
import Data.Act
  ( Act((•)) )

-- containers
import qualified Data.IntMap.Strict as IntMap
  ( singleton )
import Data.IntSet
  ( IntSet )
import qualified Data.IntSet as IntSet
  ( fromList, delete )
import qualified Data.Sequence as Seq
  ( singleton )

-- dependent-map
import qualified Data.Dependent.Map.Lens as DMap
  ( dmat )

-- generic-lens
import Data.GenericLens.Internal
  ( view, set, over )
import Data.Generics.Product.Fields
  ( field' )

-- lens
import Control.Lens
  ( assign )
import Control.Lens.Fold
  ( forOf_, foldMapOf )
import qualified Data.IntSet.Lens as IntSet
  ( members )

-- mtl
import Control.Monad.Except
  ( MonadError ( throwError ) )
import Control.Monad.Reader
  ( MonadReader ( ask ) )
import Control.Monad.State.Strict
  ( MonadState, modify'
  , execStateT, get, put
  )

-- primitive
import Control.Monad.Primitive
  ( PrimMonad(PrimState) )

-- text
import Data.Text
  ( Text )
import qualified Data.Text as Text
  ( pack )

-- transformers
import Control.Monad.Trans.Class
  ( lift )

-- vector
import Data.Vector as Boxed.Vector
  ( length, (!) )

-- unary-scheduling
import Data.Lattice
  ( Lattice
    ( (/\) )
  , BoundedLattice
    ( top )
  , TotallyOrderedLattice
  )
import Data.Vector.Generic.Index
  ( ReadableVector
    ( unsafeIndex )
  )
import Data.Vector.Ranking
  ( Ranking(..) )
import Schedule.Constraint
  ( Constraint
    ( NotEarlierThan, NotLaterThan, Outside, Inside )
  , HandedTimeConstraint
    ( handedTimeConstraint )
  , Constraints(..), applyConstraints
  )
import Schedule.Interval
  ( Endpoint(..)
  , Interval(..), validInterval, duration
  , Intervals(..)
  , pruneShorterThan
  )
import Schedule.Monad
  ( ScheduleMonad, runScheduleMonad
  , constrain
  , SchedulableData
  , TaskUpdates(..)
  , Notifiee(..)
  , BroadcastTarget(..), broadcastModifications
  )
import Schedule.Ordering
  ( Order, readOrdering )
import Schedule.Task
  ( Task(..), TaskInfos(..)
  , ImmutableTaskInfos
  , ect, lct, lst
  , Limit(Outer, Inner)
  , PickEndpoint
    ( pickEndpoint, _ranking )
  )
import Schedule.Time
  ( Delta
  , Handedness(..), OtherHandedness
  , HandedTime(..), EarliestTime, LatestTime
  )
import Schedule.Tree
  ( newTree, cloneTree, fmapTree
  , Propagatable
    ( overloaded, handedIndex, handedPrecedences, inHandedOrder, propagateLeafChange )
  , DurationInfo(..), BaseDurationInfo
  , DurationExtraInfo(..)
  )

-------------------------------------------------------------------------------
-- Propagators.

-- | Wrapper for a propagator.
--
-- We keep track of the propagator name at the type level,
-- so that we can notify all *other* (local) propagators of stale tasks
-- that they need to process.
data Propagator task t where
  Propagator
    :: forall ( n :: Type ) ( task :: Type ) ( t :: Type )
    .  { mbNotifiee    :: Maybe ( Notifiee n )
       , notifyTarget  :: BroadcastTarget
       , runPropagator :: forall s. ScheduleMonad s task t ()
       }
    -> Propagator task t


prunePropagator, timetablePropagator,
  overloadPropagator,
  detectablePrecedencesPropagator, detectableSuccedencesPropagator,
  notLastPropagator, notFirstPropagator,
  edgeLastPropagator, edgeFirstPropagator,
  predecessorPropagator, successorPropagator
 :: ( Num t, Ord t, Bounded t, Show t )
 => Propagator task t
prunePropagator =
  Propagator
    { mbNotifiee    = Just ( Coarse "prune" )
    , notifyTarget  = TellEveryoneBut "prune"
    , runPropagator = prune
    }
timetablePropagator =
  Propagator
    { mbNotifiee    = Just ( Coarse "timetable" )
    , notifyTarget  = TellEveryone
    , runPropagator = timetable
    }  
overloadPropagator =
  Propagator
    { mbNotifiee    = Nothing
    , notifyTarget  = TellEveryone
    , runPropagator = overloadCheck
    }
detectablePrecedencesPropagator =
  Propagator
    { mbNotifiee    = Nothing
    , notifyTarget  = TellEveryone
    , runPropagator = detectablePrecedences @Earliest
    }
detectableSuccedencesPropagator =
  Propagator
    { mbNotifiee    = Nothing
    , notifyTarget  = TellEveryone
    , runPropagator = detectablePrecedences @Latest
    }
notLastPropagator =
  Propagator
    { mbNotifiee    = Nothing
    , notifyTarget  = TellEveryone
    , runPropagator = notExtremal @Earliest
    }
notFirstPropagator =
  Propagator
    { mbNotifiee    = Nothing
    , notifyTarget  = TellEveryone
    , runPropagator = notExtremal @Latest
    }
edgeLastPropagator =
  Propagator
    { mbNotifiee    = Nothing
    , notifyTarget  = TellEveryone
    , runPropagator = edgeFinding @Earliest
    }
edgeFirstPropagator =
  Propagator
    { mbNotifiee    = Nothing
    , notifyTarget  = TellEveryone
    , runPropagator = edgeFinding @Latest
    }
predecessorPropagator =
  Propagator
    { mbNotifiee    = Nothing
    , notifyTarget  = TellEveryone
    , runPropagator = precedenceMatrix @Earliest
    }
successorPropagator =
  Propagator
    { mbNotifiee    = Nothing
    , notifyTarget  = TellEveryone
    , runPropagator = precedenceMatrix @Latest
    }

-- | List of all propagators, in a convenient order for running all propagation algorithms.
basicPropagators
  :: ( Num t, Ord t, Bounded t, Show t )
  => [ Propagator task t ]
basicPropagators =
  -- Local propagators (need to be notified of tasks which have been modified).
  [ prunePropagator
  , timetablePropagator
  -- Global propagators (run on all tasks at once as soon as any task has been modified).
  , overloadPropagator
  , detectablePrecedencesPropagator
  , detectableSuccedencesPropagator
  , notLastPropagator
  , notFirstPropagator
  , edgeLastPropagator
  , edgeFirstPropagator
  , predecessorPropagator
  , successorPropagator
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
  :: forall task t taskData
  .  ( Num t, Ord t, Bounded t, Show t, Show task
     , SchedulableData taskData task t
     )
  => taskData
  -> Int
  -> [ Propagator task t ]
  -> ( ImmutableTaskInfos task t, Text, Maybe Text )
propagateConstraints taskData maxLoopIterations propagators =
  case runScheduleMonad taskData ( propagationLoop maxLoopIterations propagators ) of
    ( updatedTasks, ( mbGaveUpText, Constraints { justifications } ) ) ->
      ( updatedTasks, justifications, either Just ( const Nothing ) mbGaveUpText )

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
propagationLoop maxLoopIterations propagators = do
  -- Apply the currently existing constraints, notifying
  -- all propagators that need this information.
  -- Then start the propagation loop.
  updateConstraints TellEveryone
    ( go 0 propagators )
    ( go 0 propagators )
  where
    go :: Int -> [ Propagator task t ] -> ScheduleMonad s task t ()
    go _ []
      = pure ()
    go i _
      | i >= maxLoopIterations
      = pure ()
    go i ( Propagator { notifyTarget, runPropagator = runCurrentProp } : followingProps ) 
      = do
        runCurrentProp
        updateConstraints notifyTarget
          ( go   i       followingProps )
          ( go ( i + 1 ) propagators    )
    updateConstraints
      :: BroadcastTarget
      -> ScheduleMonad s task t () 
      -> ScheduleMonad s task t ()
      -> ScheduleMonad s task t ()
    updateConstraints toNotify noCtsAction newCtsAction = do
      cts <- view ( field' @"taskConstraints" ) <$> get
      if null ( constraints cts )
      then
        noCtsAction
      else do
        modifs <- applyConstraints cts
        modify'
          -- Reset constraints: they have been applied.
          $ set  ( field' @"taskConstraints" . field' @"constraints" ) mempty
          -- Broadcast which tasks have been newly modified to all
          -- the other propagators which make use of such modification information.
          . over ( field' @"tasksModified" ) ( broadcastModifications toNotify modifs )
        newCtsAction

-------------------------------------------------------------------------------
-- Convenience class synonym for polymorphism over scheduling tree handedness.

class
  ( PickEndpoint h  Inner, PickEndpoint h  Outer
  , PickEndpoint oh Inner, PickEndpoint oh Outer
  , HandedTimeConstraint h, HandedTimeConstraint oh
  , oh ~ OtherHandedness h, OtherHandedness oh ~ h
  , Propagatable h
  , forall t. ( Ord t, Bounded t ) => BoundedLattice        ( Endpoint ( HandedTime h t ) )
  , forall t. ( Ord t, Bounded t ) => TotallyOrderedLattice ( Endpoint ( HandedTime h t ) )
  , forall t. Num t => Act ( Delta t ) ( HandedTime h t )
  , forall t. Show t => Show ( HandedTime h  t )
  , forall t. Show t => Show ( HandedTime oh t )
  ) => KnownHandedness ( h :: Handedness ) ( oh :: Handedness ) | h -> oh, oh -> h where

instance
  ( PickEndpoint h  Inner, PickEndpoint h  Outer
  , PickEndpoint oh Inner, PickEndpoint oh Outer
  , HandedTimeConstraint h, HandedTimeConstraint oh
  , oh ~ OtherHandedness h, OtherHandedness oh ~ h
  , Propagatable h
  , forall t. ( Ord t, Bounded t ) => BoundedLattice        ( Endpoint ( HandedTime h t ) )
  , forall t. ( Ord t, Bounded t ) => TotallyOrderedLattice ( Endpoint ( HandedTime h t ) )
  , forall t. Num t => Act ( Delta t ) ( HandedTime h t )
  , forall t. Show t => Show ( HandedTime h  t )
  , forall t. Show t => Show ( HandedTime oh t )
  ) => KnownHandedness h oh
  where
  {-# SPECIALISE instance KnownHandedness Earliest Latest   #-}
  {-# SPECIALISE instance KnownHandedness Latest   Earliest #-}


-------------------------------------------------------------------------------
-- Local propagators.

-- | Prune task intervals that are too short for the task to complete.
--
-- Runs on tasks that have been modified since last pruning.
--
-- The emitted constraints are logged (using the 'MonadState' instance),
-- but not applied.
prune
  :: forall s task t m bvec uvec
  .  ( MonadReader ( TaskInfos bvec uvec task t ) m
     , MonadState  ( TaskUpdates t ) m
     , PrimMonad m, s ~ PrimState m
     , Num t, Ord t, Show t
     , ReadableVector m ( Task task t ) ( bvec ( Task task t ) )
     )
  => m ()
prune = do
  TaskInfos { taskNames, taskAvails } <- ask
  let
    nbTasks :: Int
    nbTasks = Boxed.Vector.length taskNames
  mbToUpdate <- view ( field' @"tasksModified" . DMap.dmat ( Coarse "prune" ) ) <$> get
  let
    forEachModifiedTask = case mbToUpdate of
      Nothing                    -> for_ [ 0 .. nbTasks - 1 ]
      Just ( Identity toUpdate ) -> forOf_ IntSet.members toUpdate
  forEachModifiedTask \ taskNb -> do
    task <- taskAvails `unsafeIndex` taskNb
    for_ ( pruneShorterThan ( taskDuration task ) ( taskAvailability task ) ) \ ( kept, removed ) ->
      constrain
        ( Constraints
          { constraints    = IntMap.singleton taskNb ( Inside kept )
          , justifications =
            "The following time slots have been removed from \"" <> taskNames Boxed.Vector.! taskNb <> "\",\n\
            \as they are too short to allow the task to complete:\n" <>
            ( Text.pack ( show removed ) ) <> "\n\n"
          , precedences    = mempty
          }
        )
  assign ( field' @"tasksModified" . DMap.dmat ( Coarse "prune" ) ) ( Just mempty )

-- | Check time spans for which a task is necessarily scheduled, and remove them
-- from all other tasks (as they can't be scheduled concurrently).
--
-- Runs on tasks that have been modified since last timetabling.
--
-- The emitted constraints are logged (using the 'MonadState' instance),
-- but not applied.
timetable
  :: forall s task t m bvec uvec
  .  ( MonadReader ( TaskInfos bvec uvec task t ) m
     , MonadState  ( TaskUpdates t ) m
     , PrimMonad m, s ~ PrimState m
     , Num t, Ord t, Bounded t, Show t
     , ReadableVector m ( Task task t ) ( bvec ( Task task t ) )
     )
  => m ()
timetable = do
  TaskInfos { taskNames, taskAvails } <- ask
  let
    nbTasks :: Int
    nbTasks = Boxed.Vector.length taskNames
  mbToUpdate <- view ( field' @"tasksModified" . DMap.dmat ( Coarse "timetable" ) ) <$> get
  assign ( field' @"tasksModified" . DMap.dmat ( Coarse "timetable" ) ) ( Just mempty )
  let
    forEachModifiedTask = case mbToUpdate of
      Nothing                    -> for_ [ 0 .. nbTasks - 1 ]
      Just ( Identity toUpdate ) -> forOf_ IntSet.members toUpdate
  forEachModifiedTask \ taskNb -> do
    task <- taskAvails `unsafeIndex` taskNb
    let
      taskLST = lst task
      taskECT = ect task
      necessaryInterval :: Interval t
      necessaryInterval = Interval ( coerce taskLST ) ( coerce taskECT )
    when ( duration necessaryInterval > mempty ) do
      let
        necessaryIntervals :: Intervals t
        necessaryIntervals = Intervals ( Seq.singleton necessaryInterval )
      for_ [ 0 .. nbTasks - 1 ] \ otherTaskNb ->
        unless ( otherTaskNb == taskNb ) do
          otherAvailability <- taskAvailability <$> taskAvails `unsafeIndex` otherTaskNb
          let
            removedIntervals :: Intervals t
            removedIntervals = necessaryIntervals /\ otherAvailability
          unless ( null $ intervals removedIntervals ) do
            constrain
              ( Constraints
                { constraints    = IntMap.singleton otherTaskNb ( Outside necessaryIntervals )
                , justifications =
                  "\"" <> taskNames Boxed.Vector.! taskNb <> "\" must be in progress during\n\
                  \  * " <> Text.pack ( show necessaryInterval ) <> "\n\
                  \As a result, the intervals \n\
                  \  * " <> Text.pack ( show removedIntervals ) <> "\n\
                  \have been removed from \"" <> taskNames Boxed.Vector.! otherTaskNb <> "\"\n\n"
                , precedences    = mempty
                }
              )

-------------------------------------------------------------------------------
-- Global propagators.

-- | Propagates the precedence information stored in the precedence matrix.
--
-- Runs on tasks that have been modified since last time.
--
-- The emitted constraints are logged (using the 'MonadState' instance),
-- but not applied.
precedenceMatrix
  :: forall h oh s task t m bvec uvec
  .  ( MonadReader ( TaskInfos bvec uvec task t ) m
     , MonadState  ( TaskUpdates t ) m
     , PrimMonad m, s ~ PrimState m
     , Num t, Ord t, Bounded t, Show t
     , ReadableVector m ( Task task t ) ( bvec ( Task task t ) )
     , ReadableVector m Order           ( uvec Order )
     , ReadableVector m Int             ( uvec Int )
     , KnownHandedness h oh
     )
  => m ()
precedenceMatrix = do
  
  allTasks@( TaskInfos { taskNames, taskAvails, orderings } ) :: TaskInfos bvec uvec task t <- ask
  let
    nbTasks :: Int
    nbTasks = Boxed.Vector.length taskNames
  
  let
    go :: Int -> Endpoint ( HandedTime h t ) -> Endpoint ( HandedTime h t ) -> [Int] -> Int -> m ()
    go taskNb taskOuterTime limitTime subsetTaskNbs j
      | j >= nbTasks
      -- Done with the inner loop: report the new earliest start time / latest completion time,
      -- if it imposes a new constraint.
      = when ( overloaded limitTime ( coerce taskOuterTime ) ) do
        let
          constraint :: Constraint t
          constraint = handedTimeConstraint limitTime
          precedesOrSuccedes, afterOrBefore :: Text
          ( precedesOrSuccedes, afterOrBefore )
            | NotEarlierThan _ <- constraint
            = ( "succedes", "after" )
            | otherwise
            = ( "precedes", "before" )
          currentSubsetTaskNames :: Text
          currentSubsetTaskNames =
            foldMap
              ( \ i -> "  * \"" <> taskNames Boxed.Vector.! i <> "\"\n" )
              subsetTaskNbs
          reason :: Text
          reason =
            "Precedence matrix: \"" <> taskNames Boxed.Vector.! taskNb <> "\" " <> precedesOrSuccedes <> " the following tasks:\n" <>
            currentSubsetTaskNames <> "\n\
            \As a result, \"" <> taskNames Boxed.Vector.! taskNb <> "\" must be scheduled " <> afterOrBefore <>
            "  * " <> Text.pack ( show limitTime ) <> "\n\n"
        constrain
          ( Constraints
            { constraints    = IntMap.singleton taskNb constraint
            , justifications = reason
            , precedences    = mempty
            }
          )
      | otherwise
      -- Loop over predecessors in increasing earliest start time / successors in decreasing latest completion time,
      -- to propagate information from the precedence matrix.
      = do
        otherTaskNb <- ( ordered $ view ( _ranking @h @Outer ) allTasks ) `unsafeIndex` ( handedIndex @h nbTasks j )
        otherTask   <-                                         taskAvails `unsafeIndex` otherTaskNb
        let
          otherTaskOuterTime :: Endpoint ( HandedTime h t )
          otherTaskOuterTime = pickEndpoint @h @Outer otherTask
          otherTaskDuration :: Delta t
          otherTaskDuration = taskDuration otherTask
        order <- readOrdering orderings otherTaskNb taskNb
        if inHandedOrder @h order
        then
          -- Other task is a predecessor (Earliest) / successor (Latest) of the current task:
          -- add it to the subset for computation of earliest completion time / latest start time.
          go taskNb taskOuterTime ( otherTaskDuration • ( limitTime /\ otherTaskOuterTime ) ) ( otherTaskNb : subsetTaskNbs ) ( j + 1 )
        else
          go taskNb taskOuterTime limitTime subsetTaskNbs ( j + 1 )

  for_ [ 0 .. nbTasks - 1 ] \ taskNb -> do
    task <- taskAvails `unsafeIndex` taskNb
    let
      taskOuterTime :: Endpoint ( HandedTime h t )
      taskOuterTime = pickEndpoint @h @Inner task
    go taskNb taskOuterTime top [] 0


-- | Checks whether any collection of tasks overloads the resource,
-- throwing an exception when overloading is detected.
--
-- This function detects any subset of tasks whose total duration does not fit between
-- the earliest start time and the latest completion time of the subset.
--
-- Does /not/ take gaps in task availabilities under consideration,
-- i.e. this check only depends on earliest start times and latest completion times.
overloadCheck
  :: forall s task t m bvec uvec
  .  ( MonadReader ( TaskInfos bvec uvec task t ) m
     , MonadError Text  m
     , PrimMonad m, s ~ PrimState m
     , Num t, Ord t, Bounded t, Show t
     , ReadableVector m ( Task task t ) ( bvec ( Task task t ) )
     , ReadableVector m Int             ( uvec Int )
     )
  => m ()
overloadCheck = do
  allTasks@( TaskInfos { taskNames, taskAvails, rankingLCT } ) <- ask
  let
    nbTasks :: Int
    nbTasks = Boxed.Vector.length taskNames
  tree <- newTree @Earliest @(BaseDurationInfo Earliest t) nbTasks
  let
    go :: Int -> [Int] -> m ()
    go j seenTaskNbs
      | j >= nbTasks = pure ()
      | otherwise = do
        -- For the overload check, we add tasks by non-decreasing latest completion time.
        taskNb <- ordered rankingLCT `unsafeIndex` j
        task   <-         taskAvails `unsafeIndex` taskNb
        let
          nodeInfo :: BaseDurationInfo Earliest t
          nodeInfo =
            DurationInfo
              { subsetInnerTime = ect task
              , totalDuration   = taskDuration task
              }
        estimatedECT <-
          subsetInnerTime <$> propagateLeafChange tree nodeInfo allTasks taskNb
        let
          currentLCT :: Endpoint (LatestTime t)
          currentLCT = lct task
        -- When the unary resource is overloaded, throw an error to put an end to constraint propagation.
        when ( overloaded estimatedECT currentLCT ) do
          let
            currentTaskName, currentSubsetTaskNames :: Text
            currentTaskName = taskNames Boxed.Vector.! taskNb
            currentSubsetTaskNames =
              foldMap
                ( \ i -> "  * \"" <> taskNames Boxed.Vector.! i <> "\"\n" )
                ( taskNb : seenTaskNbs )
          throwError $
            "Could not schedule tasks:\n\
            \  - \"" <> currentTaskName <> "\" must complete by\n\
            \      * " <> Text.pack ( show currentLCT ) <> "\n\
            \  - the following set of tasks cannot complete before\n\
            \      * " <> Text.pack ( show estimatedECT ) <> "\n"
            <> currentSubsetTaskNames <> "\n"
        
        go (j+1) (taskNb:seenTaskNbs)

  go 0 []

-- | Computes constraints deduced from detectable precedences.
--
-- At 'Earliest' handedness, given a task `i`, 
-- this function finds subsets of tasks which must occur before `i`,
-- because the earliest completion time of `i` occurs /after/ the latest start time of the subset.
--
-- That is, scheduling `i` before any of the tasks of the subset would preclude
-- the tasks in the subset from finishing in time.
-- From this, we deduce that task `i` must succede all tasks in the subset.
--
-- Similarly, with 'Latest' handedness,
-- this function detects when the task `i` must precede all tasks in the subset.
--
-- The emitted constraints are logged (using the 'MonadState' instance),
-- but not applied.
detectablePrecedences
  :: forall h oh s task t m bvec uvec
  .  ( MonadReader ( TaskInfos bvec uvec task t ) m
     , MonadState  ( TaskUpdates t ) m
     , PrimMonad m, s ~ PrimState m
     , Num t, Ord t, Bounded t, Show t
     , ReadableVector m ( Task task t ) ( bvec ( Task task t ) )
     , ReadableVector m Int             ( uvec Int )
     , KnownHandedness h oh
     )
  => m ()
detectablePrecedences = do
  allTasks@( TaskInfos { taskNames, taskAvails } ) <- ask
  let
    nbTasks :: Int
    nbTasks = Boxed.Vector.length taskNames
  tree <- newTree @h @(BaseDurationInfo h t) nbTasks
  let
    -- Finding detectable precedences:
    --
    --  - run `i` over tasks ordered by       inner time ( increasing earliest completion time / decreasing latest start time )
    --  - run `j` over tasks ordered by other inner time ( increasing latest start time / decreasing earliest completion time )
    --
    go :: Int -> Int -> [Int] -> m ()
    go i j js
      | max i j >= nbTasks
      = pure ()
      | otherwise
      = do
        let
        taskNb   <- ( ordered $ view ( _ranking @h @Inner ) allTasks ) `unsafeIndex` ( handedIndex @h nbTasks i )
        currTask <-                                         taskAvails `unsafeIndex` taskNb
        innerLoop taskNb currTask i j js

    innerLoop :: Int -> Task task t -> Int -> Int -> [Int] -> m ()
    innerLoop taskNb currentTask i j otherTaskNbs = do
      otherTaskNb <- ( ordered $ view ( _ranking @oh @Inner ) allTasks ) `unsafeIndex` ( handedIndex @h nbTasks j )
      otherTask   <-                                          taskAvails `unsafeIndex` otherTaskNb
      let
        currentInnerTime :: Endpoint ( HandedTime h t )
        currentInnerTime = pickEndpoint @h @Inner currentTask
        otherInnerTime :: Endpoint ( HandedTime oh t )
        otherInnerTime = pickEndpoint @oh @Inner otherTask
        addNode :: Bool
        addNode = overloaded currentInnerTime otherInnerTime
      when addNode do
        let
          nodeInfo :: BaseDurationInfo h t
          nodeInfo =
            DurationInfo
              { subsetInnerTime = pickEndpoint @h @Inner otherTask
              , totalDuration   = taskDuration otherTask
              }
        void $ propagateLeafChange tree nodeInfo allTasks otherTaskNb
      let
        j' :: Int
        otherTaskNbs' :: [Int]
        ( j', otherTaskNbs' )
          | addNode
          = ( j + 1, if otherTaskNb == taskNb then otherTaskNbs else otherTaskNb : otherTaskNbs )
          | otherwise
          = ( j, otherTaskNbs )

      if addNode && j' < nbTasks
      then
        innerLoop taskNb currentTask i j' otherTaskNbs'
      else do
        -- End of inner loop: gather results.
        when ( j > 0 ) do
          clone <- cloneTree tree
          -- Compute the estimated earliest completion time / latest start time
          -- from the subset excluding the current task.
          excludeCurrentTaskSubsetInnerTime
            <- subsetInnerTime <$> propagateLeafChange clone mempty allTasks taskNb
          let
            currentOuterTime :: Endpoint ( HandedTime h t )
            currentOuterTime = pickEndpoint @h @Outer currentTask
          -- Check that this succedence/precedence would induce a nontrivial constraint on the current task availability.
          when ( not $ overloaded currentOuterTime ( coerce excludeCurrentTaskSubsetInnerTime ) ) do
            let
              currentTaskSubset :: Text
              currentTaskSubset =
                foldMap
                  ( \ tk -> "  * \"" <> taskNames Boxed.Vector.! tk <> "\"\n" )
                  otherTaskNbs
              constraint :: Constraint t
              constraint = handedTimeConstraint excludeCurrentTaskSubsetInnerTime
              succedeOrPrecede, earlierOrLater :: Text
              ( succedeOrPrecede, earlierOrLater )
                | NotEarlierThan _ <- constraint
                = ( "succede", "start after" )
                | otherwise
                = ( "precede", "end before" )
              reason :: Text
              reason =
                "Precedence detected:\n" <>
                "\"" <> taskNames Boxed.Vector.! taskNb <> "\" must " <> succedeOrPrecede <> " all of the following tasks:\n" <>
                currentTaskSubset <>
                "As a consequence, this task is constrained to " <> earlierOrLater <> "\n\
                \  * " <> Text.pack ( show excludeCurrentTaskSubsetInnerTime ) <> "\n\n"
            -- TODO: add precedence to precedence graph to avoid unnecessary duplication of effort.
            constrain
              ( Constraints
                { constraints    = IntMap.singleton taskNb constraint
                , justifications = reason
                , precedences    = IntMap.singleton taskNb ( handedPrecedences @h $ IntSet.fromList otherTaskNbs )
                }
              )
        -- Continue to next iteration of outer loop.
        go ( i + 1 ) j' otherTaskNbs'

  go 0 0 []

-- | Computes constraints derived from deducing that a task cannot be scheduled before/after a certain subset.
--
-- If the earliest completion time of a subset exceeds the latest start time of a task,
-- then that task cannot be scheduled after all tasks in the subset (`not last`).
--
-- Dually, if the latest start time of a subset is inferior to the earliest completion time of a task,
-- then that task cannot be scheduled before all tasks in the subset (`not first`).
--
-- The emitted constraints are logged (using the 'MonadState' instance),
-- but not applied.
notExtremal
  :: forall h oh s task t m bvec uvec
  .  ( MonadReader ( TaskInfos bvec uvec task t ) m
     , MonadState  ( TaskUpdates t ) m
     , PrimMonad m, s ~ PrimState m
     , Num t, Ord t, Bounded t, Show t
     , ReadableVector m ( Task task t ) ( bvec ( Task task t ) )
     , ReadableVector m Int             ( uvec Int )
     , KnownHandedness h oh
     )
  => m ()
notExtremal = do
  allTasks@( TaskInfos { taskNames, taskAvails } ) <- ask
  let
    nbTasks :: Int
    nbTasks = Boxed.Vector.length taskNames
  tree <- newTree @h @(BaseDurationInfo h t) nbTasks

  let
    -- Not last / not first algorithm.
    --
    --  - outer loop over `i`, ranking by other outer time ( increasing latest completion time / decreasing earliest start time )
    --  - inner loop over `j`, ranking by other inner time ( increasing latest start time / decreasing earliest completion time )
    --
    go :: Int -> Int -> [Int] -> m ()
    go i j currentSubset = unless ( i >= nbTasks ) do
      currentTaskNb <- ( ordered $ view ( _ranking @oh @Outer ) allTasks ) `unsafeIndex` ( handedIndex @h nbTasks i )
      currentTask   <-                                          taskAvails `unsafeIndex` currentTaskNb
      let
        currentOtherOuterTime :: Endpoint ( HandedTime oh t )
        currentOtherOuterTime = pickEndpoint @oh @Outer currentTask

      -- Inner loop: find all tasks in the set `NotLast'(tasks, currentTask)`  / `NotFirst'(tasks, currentTask)`,
      -- adding them to the task tree as we go.
      ( j', currentSubset' ) <- innerLoop currentOtherOuterTime j currentSubset

      -- Obtain the relevant task for the current task: the latest task that was added which is distinct from the current task.
      let
        mbRelevantTaskNb = case currentSubset' of
          ( otherTaskNb : _ )
            | otherTaskNb /= currentTaskNb
            -> Just otherTaskNb
          ( _ : otherTaskNb : _ )
            -> Just otherTaskNb
          _ -> Nothing

      for_ mbRelevantTaskNb \ relevantTaskNb -> do

        clone <- cloneTree tree
        -- Compute the estimated earliest completion time / latest start time
        -- from the subset excluding the current task.
        -- TODO: implement the optimisation from the paper that computes
        -- a constraint relative to the secondary task before inserting it in the Theta-tree.
        excludeCurrentTaskSubsetInnerTime
          <- subsetInnerTime <$> propagateLeafChange clone mempty allTasks currentTaskNb
        relevantTask <- taskAvails `unsafeIndex` relevantTaskNb
        let
          associatedOtherInnerTime :: Endpoint ( HandedTime oh t )
          associatedOtherInnerTime = pickEndpoint @oh @Inner relevantTask
        when
          -- check that the current task can't be scheduled after / before all the other tasks in the current subset
          ( overloaded excludeCurrentTaskSubsetInnerTime ( pickEndpoint @oh @Inner currentTask ) 
          -- check that this observation imposes a nontrivial constraint on the current task
          && not ( overloaded ( coerce associatedOtherInnerTime :: Endpoint ( HandedTime h t ) ) currentOtherOuterTime )
          )
          do
            let
              subsetText :: Text
              subsetText = foldMap ( \ tk -> "  * \"" <> taskNames Boxed.Vector.! tk <> "\"\n" ) currentSubset'
              constraint :: Constraint t
              constraint = handedTimeConstraint associatedOtherInnerTime
              lastOrFirst, earlierOrLater :: Text
              ( lastOrFirst, earlierOrLater )
                | NotLaterThan _ <- constraint
                = ( "last", "finish before" )
                | otherwise
                = ( "first", "start after" )
              reason :: Text
              reason =
                "\"" <> taskNames Boxed.Vector.! currentTaskNb <> "\" cannot be scheduled " <> lastOrFirst <> " among the following tasks:\n" <>
                subsetText <>
                "As a consequence, the task is constrained to " <> earlierOrLater <> "\n\
                \  * " <> Text.pack ( show associatedOtherInnerTime ) <> "\n\n"
            constrain
              ( Constraints
                { constraints    = IntMap.singleton currentTaskNb constraint
                , justifications = reason
                , precedences    = mempty
                }
              )

      -- Next step of outer loop.
      go ( i + 1 ) j' currentSubset'

    innerLoop
      :: Endpoint ( HandedTime oh t )
      -> Int
      -> [Int]
      -> m ( Int, [Int] )
    innerLoop currentOtherOuterTime j currentSubset = let j' = j + 1 in
      if j' >= nbTasks
      then
        pure ( j, currentSubset )
      else do
      -- Check whether we can add further tasks to the task tree.
        otherTaskNb' <- ( ordered $ view ( _ranking @oh @Inner ) allTasks ) `unsafeIndex` ( handedIndex @h nbTasks j' )
        otherTask'   <-                                          taskAvails `unsafeIndex` otherTaskNb'
        if overloaded ( coerce currentOtherOuterTime :: Endpoint ( HandedTime h t ) ) ( pickEndpoint @oh @Inner otherTask' )
        then do
        -- Can add another `j`.
          let
            nodeInfo :: BaseDurationInfo h t
            nodeInfo =
              DurationInfo
                { subsetInnerTime = pickEndpoint @h @Inner otherTask'
                , totalDuration   = taskDuration otherTask'
                }
          void $ propagateLeafChange tree nodeInfo allTasks otherTaskNb'
          innerLoop currentOtherOuterTime j' ( otherTaskNb' : currentSubset )
        else
          pure ( j, currentSubset )

  -- Start process with first task (ordered by other inner time).
  firstTaskNb <- ( ordered $ view ( _ranking @oh @Inner ) allTasks ) `unsafeIndex` ( handedIndex @h nbTasks 0 )
  firstTask   <-                                          taskAvails `unsafeIndex` firstTaskNb
  let
    nodeInfo :: BaseDurationInfo h t
    nodeInfo =
      DurationInfo
        { subsetInnerTime = pickEndpoint @h @Inner firstTask
        , totalDuration   = taskDuration firstTask
        }
  void $ propagateLeafChange tree nodeInfo allTasks firstTaskNb

  go 0 0 [ firstTaskNb ]

-- | Computes constraints derived from edge-finding.
--
-- Given a certain set of tasks Θ, we can ask whether there is enough time to schedule an additional task
-- somewhere among them.
--
-- If the earliest completion time of the union of the subset Θ with the extra task
-- exceeds the latest completion time of the original subset Θ, this would be impossible,
-- so this extra task must be scheduled after all the tasks in Θ.
--
-- Dually, if the latest start time of the union of the subset Θ with the extra task
-- is inferior to the earliest start time of the original subset Θ,
-- the extra task must be scheduled before all the tasks in Θ.
--
-- The emitted constraints are logged (using the 'MonadState' instance),
-- but not applied.
edgeFinding
  :: forall h oh s  task t m bvec uvec
  .  ( MonadReader ( TaskInfos bvec uvec task t ) m
     , MonadState  ( TaskUpdates t ) m
     , PrimMonad m, s ~ PrimState m
     , Num t, Ord t, Bounded t, Show t
     , ReadableVector m ( Task task t ) ( bvec ( Task task t ) )
     , ReadableVector m Int             ( uvec Int )
     , KnownHandedness h oh
     )
  => m ()
edgeFinding = do
  allTasks@( TaskInfos { taskNames, taskAvails } ) <- ask
  let
    nbTasks :: Int
    nbTasks = Boxed.Vector.length taskNames
  startingTree <- newTree @h @(BaseDurationInfo h t) nbTasks

  -- Start by adding all tasks to the task tree,
  -- in order ( increasing earliest start time / decreasing latest completion time ).
  for_ [ 0 .. ( nbTasks - 1 ) ] \ i -> do
    taskNb <- ( ordered $ view ( _ranking @h @Outer ) allTasks ) `unsafeIndex` ( handedIndex @h nbTasks i )
    task   <-                                         taskAvails `unsafeIndex` taskNb
    let
      nodeInfo :: BaseDurationInfo h t
      nodeInfo =
        DurationInfo
          { subsetInnerTime = pickEndpoint @h @Inner task
          , totalDuration   = taskDuration task
          }
    void $ propagateLeafChange startingTree nodeInfo allTasks taskNb
  -- Convert the task tree to a coloured task tree, starting off with no coloured nodes.
  tree <-
    fmapTree
      ( \ durInfo -> mempty { baseDurationInfo = durInfo } )
      startingTree

  -- Edge finding algorithm.
  --
  -- Loop over `j`, reverse ranking by other outer time ( decreasing latest completion time / increasing earliest start time ).

  let
    go :: Int -> IntSet -> m ()
    go j currentTaskSubset = when ( j > 1 ) do
      taskNb <- ( ordered $ view ( _ranking @oh @Outer ) allTasks ) `unsafeIndex` ( handedIndex @h nbTasks j )
      task   <-                                          taskAvails `unsafeIndex` taskNb

      -- Set the current task to be coloured in the task tree (normal --> coloured).
      let
        colouredNodeInfo :: DurationExtraInfo h t Int
        colouredNodeInfo =
          DurationExtraInfo
            { baseDurationInfo = mempty -- trivial base task information (coloured task)
            , extraDurationInfo =
              DurationInfo
                { subsetInnerTime = Just $ Arg ( pickEndpoint @h @Inner task ) taskNb
                , totalDuration   = Just $ Arg ( taskDuration task ) taskNb
                }
            }
        j' :: Int
        j' = j - 1
      
      DurationExtraInfo
        { baseDurationInfo  = DurationInfo { subsetInnerTime = currentSubsetInnerTime      }
        , extraDurationInfo = DurationInfo { subsetInnerTime = currentSubsetExtraInnerTime }
        } <- propagateLeafChange tree colouredNodeInfo allTasks taskNb

      nextTaskNb <- ( ordered $ view ( _ranking @oh @Outer ) allTasks ) `unsafeIndex` ( handedIndex @h nbTasks j' )
      nextTask   <-                                          taskAvails `unsafeIndex` nextTaskNb
      
      let
        nextOtherOuterTime :: Endpoint ( HandedTime oh t )
        nextOtherOuterTime = pickEndpoint @oh @Outer nextTask

      innerLoop j' ( IntSet.delete taskNb currentTaskSubset ) nextOtherOuterTime currentSubsetInnerTime currentSubsetExtraInnerTime

    innerLoop
      :: Int
      -> IntSet
      -> Endpoint ( HandedTime oh t )
      -> Endpoint ( HandedTime h t )
      -> Maybe ( Arg ( Endpoint ( HandedTime h t ) ) Int )
      -> m ()
    innerLoop j currentTaskSubset nextOtherOuterTime currentSubsetInnerTime ( Just ( Arg subsetExtraInnerTime blamedTaskNb ) )
      | overloaded subsetExtraInnerTime nextOtherOuterTime
      = do
          -- Entirely remove blamed activity from the task tree (coloured --> removed).
          DurationExtraInfo { extraDurationInfo = DurationInfo { subsetInnerTime = subsetExtraInnerTime' } }
            <- propagateLeafChange tree mempty allTasks blamedTaskNb
          -- Emit induced constraint (if necessary).
          blamedTask <- taskAvails `unsafeIndex` blamedTaskNb
          let
            blamedOuterTime :: Endpoint ( HandedTime h t )
            blamedOuterTime = pickEndpoint @h @Outer blamedTask
          when ( not $ overloaded blamedOuterTime ( coerce currentSubsetInnerTime :: Endpoint ( HandedTime oh t ) ) ) do
            let
              constraint :: Constraint t
              constraint = handedTimeConstraint currentSubsetInnerTime
              subsetText :: Text
              subsetText = foldMapOf IntSet.members ( \ tk -> "  * \"" <> taskNames Boxed.Vector.! tk <> "\"\n" ) currentTaskSubset
              afterOrBefore, laterOrEarlier :: Text
              ( afterOrBefore, laterOrEarlier )
                | NotEarlierThan _ <- constraint
                = ( "after", "start after" )
                | otherwise
                = ( "before", "finish before" )
              reason :: Text
              reason =
                "Edge found:\n" <>
                "\"" <> taskNames Boxed.Vector.! blamedTaskNb <> "\" must be scheduled " <> afterOrBefore <> " all the following tasks:\n" <>
                subsetText <>
                "As a consequence, the task is constrained to " <> laterOrEarlier <> "\n\
                \  * " <> Text.pack ( show currentSubsetInnerTime ) <> "\n\n"
            -- TODO: add precedence to precedence graph to avoid unnecessary duplication of effort.
            constrain
              ( Constraints
                { constraints    = IntMap.singleton blamedTaskNb constraint
                , justifications = reason
                , precedences    = IntMap.singleton blamedTaskNb ( handedPrecedences @h currentTaskSubset )
                }
              )
          -- Continue to see if more activities can be removed.
          innerLoop j currentTaskSubset nextOtherOuterTime currentSubsetInnerTime subsetExtraInnerTime'
    innerLoop j currentTaskSubset _ _ _
      = go j currentTaskSubset

  go ( nbTasks - 1 ) ( IntSet.fromList [ 0 .. ( nbTasks - 1 ) ] )


-- | Constrain a set of tasks to have a maximum makespan in given intervals (experimental).
--
-- The emitted constraints are logged (using the 'MonadState' instance),
-- but not applied.
makespan
  :: forall f1 f2 s task t m bvec uvec
  .  ( MonadReader ( TaskInfos bvec uvec task t ) m
     , MonadState  ( TaskUpdates t ) m
     , PrimMonad m, s ~ PrimState m
     , Num t, Ord t, Bounded t, Show t
     , ReadableVector m (Task task t) ( bvec ( Task task t ) )
     , ReadableVector m Int           ( uvec Int )
     , Foldable f1
     , Foldable f2
     )
  => Text
  -> f1 Int
  -> f2 ( Interval t, Delta t )
  -> m ()
makespan label taskNbs mkspans = do

  allTasks@( TaskInfos { taskNames, taskAvails } ) <- ask
  let
    nbTasks :: Int
    nbTasks = Boxed.Vector.length taskNames

  -- Compute the estimated ECT and LST of the given subset of tasks.

  -- TODO: here we create full size task trees.
  -- At the cost of recomputing some rankings, we could instead create
  -- task trees the size of the given subset of tasks.
  treeECT <- newTree @Earliest @(BaseDurationInfo Earliest t) nbTasks
  treeLST <- newTree @Latest   @(BaseDurationInfo Latest   t) nbTasks
  ( subsetECT, subsetLST ) <-
    ( `execStateT` ( top, top ) ) $ for_ taskNbs \ taskNb -> do
      task <- lift $ taskAvails `unsafeIndex` taskNb
      let
        infoECT :: BaseDurationInfo Earliest t
        infoECT =
          DurationInfo
            { subsetInnerTime = pickEndpoint @Earliest @Inner task
            , totalDuration   = taskDuration task
            }
        infoLST :: BaseDurationInfo Latest t
        infoLST =
          DurationInfo
            { subsetInnerTime = pickEndpoint @Latest   @Inner task
            , totalDuration   = taskDuration task
            }
      subsetECT <- lift $ subsetInnerTime <$> propagateLeafChange @_ @m treeECT infoECT allTasks taskNb
      subsetLST <- lift $ subsetInnerTime <$> propagateLeafChange @_ @m treeLST infoLST allTasks taskNb
      put ( subsetECT, subsetLST )

  -- For each makespan constraint, use the computed estimates of the subset ECT and LST
  -- to see whether there are any constraints to propagate.
  for_ mkspans \ ( mkspan, cap ) -> do
    -- Check whether we need to constrain tasks to not start near the beginning of the makespan range,
    -- because the subset must be in progress near the end of the makespan range.
    when ( validInterval $ Interval subsetECT ( end mkspan ) ) do
      let
        latestStart :: Endpoint ( LatestTime t )
        latestStart = cap • ( coerce subsetECT /\ end mkspan )
        outside :: Interval t
        outside = Interval ( start mkspan ) latestStart
        outsides :: Intervals t
        outsides = Intervals ( Seq.singleton outside )
      when ( validInterval outside ) do
        for_ taskNbs \ taskNb -> do
          avail <- taskAvailability <$> taskAvails `unsafeIndex` taskNb
          let
            removedIntervals :: Intervals t
            removedIntervals = avail /\ outsides
          unless ( null $ intervals removedIntervals ) do
            constrain
              ( Constraints
                { constraints    = IntMap.singleton taskNb ( Outside outsides )
                , justifications =
                  "The makespan constraint " <> Text.pack ( show mkspan ) <> ", " <> Text.pack ( show cap ) <> "\n\
                  \with label " <> label <> ",\n\
                  \prevents the task \"" <> taskNames Boxed.Vector.! taskNb <> "\"\n\
                  \from being scheduled before " <> Text.pack ( show latestStart ) <> " within the makespan interval.\n\
                  \As a result, the intervals \n\
                  \  * " <> Text.pack ( show removedIntervals ) <> "\n\
                  \have been removed from this task.\n\n"
                , precedences    = mempty
                }
              )
    -- Check whether we need to constrain tasks to not finish near the end of the makespan range,
    -- because the subset must be in progress near the start of the makespan range.
    when ( validInterval $ Interval ( start mkspan ) subsetLST ) do
      let
        earliestEnd :: Endpoint ( EarliestTime t )
        earliestEnd = cap • ( coerce subsetLST /\ start mkspan )
        outside :: Interval t
        outside = Interval earliestEnd ( end mkspan )
        outsides :: Intervals t
        outsides = Intervals ( Seq.singleton outside )
      when ( validInterval outside ) do
        for_ taskNbs \ taskNb -> do
          avail <- taskAvailability <$> taskAvails `unsafeIndex` taskNb
          let
            removedIntervals :: Intervals t
            removedIntervals = avail /\ outsides
          unless ( null $ intervals removedIntervals ) do
            constrain
              ( Constraints
                { constraints    = IntMap.singleton taskNb ( Outside outsides )
                , justifications =
                  "The makespan constraint " <> Text.pack ( show mkspan ) <> ", " <> Text.pack ( show cap ) <> "\n\
                  \with label " <> label <> ",\n\
                  \prevents the task \"" <> taskNames Boxed.Vector.! taskNb <> "\"\n\
                  \from being scheduled after " <> Text.pack ( show earliestEnd ) <> " within the makespan interval.\n\
                  \As a result, the intervals \n\
                  \  * " <> Text.pack ( show removedIntervals ) <> "\n\
                  \have been removed from this task.\n\n"
                , precedences    = mempty
                }
              )
