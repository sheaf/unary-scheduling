{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE BlockArguments         #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MonoLocalBinds         #-}
{-# LANGUAGE NamedFieldPuns         #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE QuantifiedConstraints  #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE UndecidableInstances   #-}

module Schedule.Propagators
  ( normalise, prune, timetable
  , overloadCheck, detectablePrecedences
  , notExtremal, edgeFinding
  , makespan
  )
  where

-- base
import Control.Monad
  ( when, unless, void )
import Control.Monad.ST
  ( ST )
import Data.Coerce
  ( coerce )
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
import qualified Data.Sequence as Seq
  ( singleton )
import Data.Set
  ( Set )
import qualified Data.Set as Set
  ( fromList, delete )

-- mtl
import Control.Monad.Except
  ( MonadError ( throwError ) )
import Control.Monad.Reader
  ( MonadReader ( ask ) )
import Control.Monad.Writer
  ( MonadWriter ( tell ) )

-- text
import Data.Text
  ( Text )
import qualified Data.Text as Text
  ( pack )

-- transformers
import Control.Monad.State.Strict
  ( execStateT, put )
import Control.Monad.Trans.Class
  ( lift )

-- transformers-base
import Control.Monad.Base
  ( MonadBase ( liftBase ) )

{-
-- tree-view
import qualified Data.Tree.View as TreeView
  ( showTree )
-}

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
  , Constraints(..)
  )
import Schedule.Interval
  ( EndPoint(..)
  , Interval(..), validInterval, Intervals(..)
  , pruneShorterThan
  , Normalisable
    ( normaliseIntervals )
  )
import Schedule.Task
  ( Task(..), Tasks(..), TaskInfos(..)
  , ect, lct, lst
  , Limit(Outer, Inner)
  , PickEndPoint
    ( pickEndPoint, pickRanking )
  )
import Schedule.Time
  ( Delta
  , Handedness(..), OtherHandedness
  , HandedTime(..), EarliestTime, LatestTime
  )
import Schedule.Tree
  ( newTree, cloneTree, fmapTree
--  , toRoseTree
  , Propagatable
    ( overloaded, handedIndex, propagateLeafChange )
  , DurationInfo(..), BaseDurationInfo
  , DurationExtraInfo(..)
  )

-------------------------------------------------------------------------------
-- Convenience class synonym for polymorphism over scheduling tree handedness.

class
  ( PickEndPoint h  Inner, PickEndPoint h  Outer
  , PickEndPoint oh Inner, PickEndPoint oh Outer
  , HandedTimeConstraint h, HandedTimeConstraint oh
  , oh ~ OtherHandedness h, OtherHandedness oh ~ h
  , Propagatable h
  , forall t. ( Ord t, Bounded t ) => BoundedLattice        ( EndPoint ( HandedTime h t ) )
  , forall t. ( Ord t, Bounded t ) => TotallyOrderedLattice ( EndPoint ( HandedTime h t ) )
  , forall t. Num t => Act ( Delta t ) ( HandedTime h t )
  , forall t. Show t => Show ( HandedTime h  t )
  , forall t. Show t => Show ( HandedTime oh t )
  ) => KnownHandedness ( h :: Handedness ) ( oh :: Handedness ) | h -> oh, oh -> h where

instance
  ( PickEndPoint h  Inner, PickEndPoint h  Outer
  , PickEndPoint oh Inner, PickEndPoint oh Outer
  , HandedTimeConstraint h, HandedTimeConstraint oh
  , oh ~ OtherHandedness h, OtherHandedness oh ~ h
  , Propagatable h
  , forall t. ( Ord t, Bounded t ) => BoundedLattice        ( EndPoint ( HandedTime h t ) )
  , forall t. ( Ord t, Bounded t ) => TotallyOrderedLattice ( EndPoint ( HandedTime h t ) )
  , forall t. Num t => Act ( Delta t ) ( HandedTime h t )
  , forall t. Show t => Show ( HandedTime h  t )
  , forall t. Show t => Show ( HandedTime oh t )
  ) => KnownHandedness h oh where

-------------------------------------------------------------------------------
-- Local constraints.


-- | Normalise task intervals, e.g. by shrinking "exclusive" endpoints for discrete domains.
--
-- The emitted constraints are logged (using the 'MonadWriter' instance),
-- but not applied.
normalise
  :: forall s task t m tvec ivec
  .  ( MonadReader ( Tasks tvec ivec task t ) m
     , MonadWriter ( Constraints t ) m
     , MonadBase (ST s) m
     , Num t, Ord t, Normalisable t, Show t
     , ReadableVector m (Task task t) ( tvec (Task task t) )
     )
  => m ()
normalise = do
  Tasks { taskNames, taskInfos = TaskInfos { tasks } } <- ask
  let
    nbTasks :: Int
    nbTasks = Boxed.Vector.length taskNames
  -- TODO: avoid repeating this computation for tasks that haven't been modified since the last time.
  -- TODO: avoid doing this computation altogether for types which never need normalisation.
  for_ [ 0 .. nbTasks - 1 ] \ taskNb -> do
    task <- tasks `unsafeIndex` taskNb
    case normaliseIntervals ( taskAvailability task ) of
      Nothing -> pure ()
      Just newIntervals ->
        tell 
          ( Constraints
            { constraints    = IntMap.singleton taskNb ( Inside $ newIntervals )
            , justifications =
              "Performed normalisation for \"" <> taskNames Boxed.Vector.! taskNb <> "\"\n\n"
            }
          )

-- | Prune task intervals that are too short for the task to complete.
--
-- The emitted constraints are logged (using the 'MonadWriter' instance),
-- but not applied.
prune
  :: forall s task t m tvec ivec
  .  ( MonadReader ( Tasks tvec ivec task t ) m
     , MonadWriter ( Constraints t ) m
     , MonadBase (ST s) m
     , Num t, Ord t, Show t
     , ReadableVector m (Task task t) ( tvec (Task task t) )
     )
  => m ()
prune = do
  Tasks { taskNames, taskInfos = TaskInfos { tasks } } <- ask
  let
    nbTasks :: Int
    nbTasks = Boxed.Vector.length taskNames
  -- TODO: avoid repeating this computation for tasks that haven't been modified since the last time.
  for_ [ 0 .. nbTasks - 1 ] \ taskNb -> do
    task <- tasks `unsafeIndex` taskNb
    for_ ( pruneShorterThan ( taskDuration task ) ( taskAvailability task ) ) \ ( kept, removed ) -> do
      tell 
        ( Constraints
          { constraints    = IntMap.singleton taskNb ( Inside kept )
          , justifications =
            "The following time slots have been removed from \"" <> taskNames Boxed.Vector.! taskNb <> "\",\n\
            \as they are too short to allow the task to complete:\n" <>
            ( Text.pack ( show removed ) ) <> "\n\n"
          }
        )

-- | Check time spans for which a task is necessarily scheduled, and remove them
-- from all other tasks (as they can't be scheduled concurrently).
--
-- The emitted constraints are logged (using the 'MonadWriter' instance),
-- but not applied.
timetable
  :: forall s task t m tvec ivec
  .  ( MonadReader ( Tasks tvec ivec task t ) m
     , MonadWriter ( Constraints t ) m
     , MonadBase (ST s) m
     , Num t, Ord t, Bounded t, Show t
     , ReadableVector m (Task task t) ( tvec (Task task t) )
     )
  => m ()
timetable = do
  Tasks { taskNames, taskInfos = TaskInfos { tasks } } <- ask
  let
    nbTasks :: Int
    nbTasks = Boxed.Vector.length taskNames
  -- TODO: avoid repeating this computation for tasks that haven't been modified since the last time
  for_ [ 0 .. nbTasks - 1 ] \ taskNb -> do
    task <- tasks `unsafeIndex` taskNb
    let
      taskLST = lst task
      taskECT = ect task
      necessaryInterval :: Interval t
      necessaryInterval = Interval ( coerce taskLST ) ( coerce taskECT )
    when ( validInterval necessaryInterval ) do
      let
        necessaryIntervals :: Intervals t
        necessaryIntervals = Intervals ( Seq.singleton necessaryInterval )
      for_ [ 0 .. nbTasks - 1 ] \ otherTaskNb -> do
        unless ( otherTaskNb == taskNb ) do
          otherAvailability <- taskAvailability <$> tasks `unsafeIndex` otherTaskNb
          let
            removedIntervals :: Intervals t
            removedIntervals = necessaryIntervals /\ otherAvailability
          unless ( null $ intervals removedIntervals ) do
            tell
              ( Constraints
                { constraints    = IntMap.singleton otherTaskNb ( Outside necessaryIntervals )
                , justifications =
                  "\"" <> taskNames Boxed.Vector.! taskNb <> "\" must be in progress during\n\
                  \  * " <> Text.pack ( show necessaryInterval ) <> "\n\
                  \As a result, the intervals \n\
                  \  * " <> Text.pack ( show removedIntervals ) <> "\n\
                  \have been removed from \"" <> taskNames Boxed.Vector.! otherTaskNb <> "\"\n\n"
                }
              )

-------------------------------------------------------------------------------
-- Global constraints.

-- | Checks whether any collection of tasks overloads the resource,
-- throwing an exception when overloading is detected.
--
-- This function detects any subset of tasks whose total duration does not fit between
-- the earliest start time and the latest completion time of the subset.
--
-- Does /not/ take gaps in task availabilities under consideration,
-- i.e. this check only depends on earliest start times and latest completion times.
overloadCheck
  :: forall s task t m tvec ivec
  .  ( MonadReader ( Tasks tvec ivec task t ) m
     , MonadError Text  m
     , MonadBase (ST s) m
     , Num t, Ord t, Bounded t, Show t
     , ReadableVector m (Task task t) ( tvec (Task task t) )
     , ReadableVector m      Int      ( ivec Int )
     )
  => m ()
overloadCheck = do
  allTasks@( Tasks { taskNames, taskInfos = TaskInfos { tasks, rankingLCT } } ) <- ask
  let
    nbTasks :: Int
    nbTasks = Boxed.Vector.length taskNames
  tree <- liftBase $ newTree @Earliest @(BaseDurationInfo Earliest t) nbTasks
  let
    go :: Int -> [Int] -> m ()
    go j seenTaskNbs
      | j >= nbTasks = pure ()
      | otherwise = do
        -- For the overload check, we add tasks by non-decreasing latest completion time.
        taskNb <- ordered rankingLCT `unsafeIndex` j
        task   <-              tasks `unsafeIndex` taskNb
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
          currentLCT :: EndPoint (LatestTime t)
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
-- The emitted constraints are logged (using the 'MonadWriter' instance),
-- but not applied.
detectablePrecedences
  :: forall h oh s task t m tvec ivec
  .  ( MonadReader ( Tasks tvec ivec task t ) m
     , MonadWriter ( Constraints t ) m
     , MonadBase (ST s) m
     , Num t, Ord t, Bounded t, Show t
     , ReadableVector m (Task task t) ( tvec (Task task t) )
     , ReadableVector m Int           ( ivec Int )
     , KnownHandedness h oh
     )
  => m ()
detectablePrecedences = do
  allTasks@( Tasks { taskNames, taskInfos = rankings@(TaskInfos { tasks }) } ) <- ask
  let
    nbTasks :: Int
    nbTasks = Boxed.Vector.length taskNames
  tree <- liftBase $ newTree @h @(BaseDurationInfo h t) nbTasks
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
        taskNb   <- ( ordered $ pickRanking @h @Inner rankings ) `unsafeIndex` ( handedIndex @h nbTasks i )
        currTask <-                                        tasks `unsafeIndex` taskNb
        innerLoop taskNb currTask i j js

    innerLoop :: Int -> Task task t -> Int -> Int -> [Int] -> m ()
    innerLoop taskNb currentTask i j js = do
      otherTaskNb <- ( ordered $ pickRanking @oh @Inner rankings ) `unsafeIndex` ( handedIndex @h nbTasks j )
      otherTask   <-                                         tasks `unsafeIndex` otherTaskNb
      let
        currentInnerTime :: EndPoint ( HandedTime h t )
        currentInnerTime = pickEndPoint @h @Inner currentTask
        otherInnerTime :: EndPoint ( HandedTime oh t )
        otherInnerTime = pickEndPoint @oh @Inner otherTask
        addNode :: Bool
        addNode = overloaded currentInnerTime otherInnerTime
      when addNode do
        let
          nodeInfo :: BaseDurationInfo h t
          nodeInfo =
            DurationInfo
              { subsetInnerTime = pickEndPoint @h @Inner otherTask
              , totalDuration   = taskDuration otherTask
              }
        void $ propagateLeafChange tree nodeInfo allTasks otherTaskNb
      let
        j' :: Int
        js' :: [Int]
        ( j', js' ) = if addNode then ( j + 1, j : js ) else ( j, js )

      if addNode && j' < nbTasks
      then do
        innerLoop taskNb currentTask i j' js'
      else do
        -- End of inner loop: gather results.
        when ( j > 0 ) do
          clone <- liftBase $ cloneTree tree
          -- Compute the estimated earliest completion time / latest start time
          -- from the subset excluding the current task.
          excludeCurrentTaskSubsetInnerTime
            <- subsetInnerTime <$> propagateLeafChange clone mempty allTasks taskNb
          let
            currentOuterTime :: EndPoint ( HandedTime h t )
            currentOuterTime = pickEndPoint @h @Outer currentTask
          -- Check that this succedence/precedence would induce a nontrivial constraint on the current task availability.
          when ( not $ overloaded currentOuterTime ( coerce excludeCurrentTaskSubsetInnerTime ) ) do
            let
              currentTaskSubset :: Text
              currentTaskSubset =
                foldMap
                  ( \ tk -> if tk == taskNb then "" else "  * \"" <> taskNames Boxed.Vector.! tk <> "\"\n" )
                  js'
              constraint :: Constraint t
              constraint = handedTimeConstraint excludeCurrentTaskSubsetInnerTime
              succedeOrPrecede, earlierOrLater :: Text
              ( succedeOrPrecede, earlierOrLater )
                | NotEarlierThan _ _ <- constraint
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
            tell
              ( Constraints
                { constraints    = IntMap.singleton taskNb constraint
                , justifications = reason
                }
              )
        -- Continue to next iteration of outer loop.
        go ( i + 1 ) j' js'

  go 0 0 []

-- | Computes constraints derived from deducing that a task cannot be scheduled before/after a certain subset.
--
-- If the earliest completion time of a subset exceeds the latest start time of a task,
-- then that task cannot be scheduled after all tasks in the subset (`not last`).
--
-- Dually, if the latest start time of a subset is inferior to the earliest completion time of a task,
-- then that task cannot be scheduled before all tasks in the subset (`not first`).
--
-- The emitted constraints are logged (using the 'MonadWriter' instance),
-- but not applied.
notExtremal
  :: forall h oh s task t m tvec ivec
  .  ( MonadReader ( Tasks tvec ivec task t ) m
     , MonadWriter ( Constraints t ) m
     , MonadBase (ST s) m
     , Num t, Ord t, Bounded t, Show t
     , ReadableVector m (Task task t) ( tvec (Task task t) )
     , ReadableVector m Int           ( ivec Int )
     , KnownHandedness h oh
     )
  => m ()
notExtremal = do
  allTasks@( Tasks { taskNames, taskInfos = rankings@(TaskInfos { tasks }) } ) <- ask
  let
    nbTasks :: Int
    nbTasks = Boxed.Vector.length taskNames
  tree <- liftBase $ newTree @h @(BaseDurationInfo h t) nbTasks

  let
    -- Not last / not first algorithm.
    --
    --  - outer loop over `i`, ranking by other outer time ( increasing latest completion time / decreasing earliest start time )
    --  - inner loop over `j`, ranking by other inner time ( increasing latest start time / decreasing earliest completion time )
    --
    go :: Int -> Int -> [Int] -> m ()
    go i j currentSubset = unless ( i >= nbTasks ) do
      currentTaskNb <- ( ordered $ pickRanking @oh @Outer rankings ) `unsafeIndex` ( handedIndex @h nbTasks i )
      currentTask   <-                                         tasks `unsafeIndex` currentTaskNb
      let
        currentOtherOuterTime :: EndPoint ( HandedTime oh t )
        currentOtherOuterTime = pickEndPoint @oh @Outer currentTask

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

        clone <- liftBase $ cloneTree tree
        -- Compute the estimated earliest completion time / latest start time
        -- from the subset excluding the current task.
        -- TODO: implement the optimisation from the paper that computes
        -- a constraint relative to the secondary task before inserting it in the Theta-tree.
        excludeCurrentTaskSubsetInnerTime
          <- subsetInnerTime <$> propagateLeafChange clone mempty allTasks currentTaskNb
        relevantTask <- tasks `unsafeIndex` relevantTaskNb
        let
          associatedOtherInnerTime :: EndPoint ( HandedTime oh t )
          associatedOtherInnerTime = pickEndPoint @oh @Inner relevantTask
        when
          -- check that the current task can't be scheduled after / before all the other tasks in the current subset
          ( overloaded excludeCurrentTaskSubsetInnerTime ( pickEndPoint @oh @Inner currentTask ) 
          -- check that this observation imposes a nontrivial constraint on the current task
          && not ( overloaded ( coerce associatedOtherInnerTime :: EndPoint ( HandedTime h t ) ) currentOtherOuterTime )
          )
          do
            let
              subsetText :: Text
              subsetText = foldMap ( \ tk -> "  * \"" <> taskNames Boxed.Vector.! tk <> "\"\n" ) currentSubset'
              constraint :: Constraint t
              constraint = handedTimeConstraint associatedOtherInnerTime
              lastOrFirst, earlierOrLater :: Text
              ( lastOrFirst, earlierOrLater )
                | NotLaterThan _ _ <- constraint
                = ( "last", "finish before" )
                | otherwise
                = ( "first", "start after" )
              reason :: Text
              reason =
                "\"" <> taskNames Boxed.Vector.! currentTaskNb <> "\" cannot be scheduled " <> lastOrFirst <> " among the following tasks:\n" <>
                subsetText <>
                "As a consequence, the task is constrained to " <> earlierOrLater <> "\n\
                \  * " <> Text.pack ( show associatedOtherInnerTime ) <> "\n\n"
            tell 
              ( Constraints
                { constraints    = IntMap.singleton currentTaskNb constraint
                , justifications = reason
                }
              )

      -- Next step of outer loop.
      go ( i + 1 ) j' currentSubset'

    innerLoop
      :: EndPoint ( HandedTime oh t )
      -> Int
      -> [Int]
      -> m ( Int, [Int] )
    innerLoop currentOtherOuterTime j currentSubset = let j' = j + 1 in
      if j' >= nbTasks
      then
        pure ( j, currentSubset )
      else do
      -- Check whether we can add further tasks to the task tree.
        otherTaskNb' <- ( ordered $ pickRanking @oh @Inner rankings ) `unsafeIndex` ( handedIndex @h nbTasks j' )
        otherTask'   <-                                         tasks `unsafeIndex` otherTaskNb'
        if overloaded ( coerce currentOtherOuterTime :: EndPoint ( HandedTime h t ) ) ( pickEndPoint @oh @Inner otherTask' )
        then do
        -- Can add another `j`.
          let
            nodeInfo :: BaseDurationInfo h t
            nodeInfo =
              DurationInfo
                { subsetInnerTime = pickEndPoint @h @Inner otherTask'
                , totalDuration   = taskDuration otherTask'
                }
          void $ propagateLeafChange tree nodeInfo allTasks otherTaskNb'
          innerLoop currentOtherOuterTime j' ( otherTaskNb' : currentSubset )
        else do
          pure ( j, currentSubset )

  -- Start process with first task (ordered by other inner time).
  firstTaskNb <- ( ordered $ pickRanking @oh @Inner rankings ) `unsafeIndex` ( handedIndex @h nbTasks 0 )
  firstTask   <-                                         tasks `unsafeIndex` firstTaskNb
  let
    nodeInfo :: BaseDurationInfo h t
    nodeInfo =
      DurationInfo
        { subsetInnerTime = pickEndPoint @h @Inner firstTask
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
-- The emitted constraints are logged (using the 'MonadWriter' instance),
-- but not applied.
edgeFinding
  :: forall h oh s task t m tvec ivec
  .  ( MonadReader ( Tasks tvec ivec task t ) m
     , MonadWriter ( Constraints t ) m
     , MonadBase (ST s) m
     , Num t, Ord t, Bounded t, Show t
     , ReadableVector m (Task task t) ( tvec (Task task t) )
     , ReadableVector m Int           ( ivec Int )
     , KnownHandedness h oh
     )
  => m ()
edgeFinding = do
  allTasks@( Tasks { taskNames, taskInfos = rankings@(TaskInfos { tasks }) } ) <- ask
  let
    nbTasks :: Int
    nbTasks = Boxed.Vector.length taskNames
  startingTree <- liftBase $ newTree @h @(BaseDurationInfo h t) nbTasks

  -- Start by adding all tasks to the task tree,
  -- in order ( increasing earliest start time / decreasing latest completion time ).
  for_ [ 0 .. ( nbTasks - 1 ) ] \ i -> do
    taskNb <- ( ordered $ pickRanking @h @Outer rankings ) `unsafeIndex` ( handedIndex @h nbTasks i )
    task   <-                                        tasks `unsafeIndex` taskNb
    let
      nodeInfo :: BaseDurationInfo h t
      nodeInfo =
        DurationInfo
          { subsetInnerTime = pickEndPoint @h @Inner task
          , totalDuration   = taskDuration task
          }
    void $ propagateLeafChange startingTree nodeInfo allTasks taskNb
  -- Convert the task tree to a coloured task tree, starting off with no coloured nodes.
  tree <-
    liftBase $ 
      fmapTree
        ( \ durInfo -> mempty { baseDurationInfo = durInfo } )
        startingTree

  -- Edge finding algorithm.
  --
  -- Loop over `j`, reverse ranking by other outer time ( decreasing latest completion time / increasing earliest start time ).

  let
    go :: Int -> Set Int -> m ()
    go j currentTaskSubset = when ( j > 1 ) do
      taskNb <- ( ordered $ pickRanking @oh @Outer rankings ) `unsafeIndex` ( handedIndex @h nbTasks j )
      task   <-                                         tasks `unsafeIndex` taskNb

      -- Set the current task to be coloured in the task tree (normal --> coloured).
      let
        colouredNodeInfo :: DurationExtraInfo h t Int
        colouredNodeInfo =
          DurationExtraInfo
            { baseDurationInfo = mempty -- trivial base task information (coloured task)
            , extraDurationInfo =
              DurationInfo
                { subsetInnerTime = Just $ Arg ( pickEndPoint @h @Inner task ) taskNb
                , totalDuration   = Just $ Arg ( taskDuration task ) taskNb
                }
            }
        j' :: Int
        j' = j - 1
      
      DurationExtraInfo
        { baseDurationInfo  = DurationInfo { subsetInnerTime = currentSubsetInnerTime      }
        , extraDurationInfo = DurationInfo { subsetInnerTime = currentSubsetExtraInnerTime }
        } <- propagateLeafChange tree colouredNodeInfo allTasks taskNb

      nextTaskNb <- ( ordered $ pickRanking @oh @Outer rankings ) `unsafeIndex` ( handedIndex @h nbTasks j' )
      nextTask   <-                                         tasks `unsafeIndex` nextTaskNb
      
      let
        nextOtherOuterTime :: EndPoint ( HandedTime oh t )
        nextOtherOuterTime = pickEndPoint @oh @Outer nextTask

      innerLoop j' ( Set.delete taskNb currentTaskSubset ) nextOtherOuterTime currentSubsetInnerTime currentSubsetExtraInnerTime

    innerLoop
      :: Int
      -> Set Int
      -> EndPoint ( HandedTime oh t )
      -> EndPoint ( HandedTime h t )
      -> Maybe ( Arg ( EndPoint ( HandedTime h t ) ) Int )
      -> m ()
    innerLoop j currentTaskSubset nextOtherOuterTime currentSubsetInnerTime ( Just ( Arg subsetExtraInnerTime blamedTaskNb ) )
      | overloaded subsetExtraInnerTime nextOtherOuterTime
      = do
          -- Entirely remove blamed activity from the task tree (coloured --> removed).
          DurationExtraInfo { extraDurationInfo = DurationInfo { subsetInnerTime = subsetExtraInnerTime' } }
            <- propagateLeafChange tree mempty allTasks blamedTaskNb
          -- Emit induced constraint (if necessary).
          blamedTask <- tasks `unsafeIndex` blamedTaskNb
          let
            blamedOuterTime :: EndPoint ( HandedTime h t )
            blamedOuterTime = pickEndPoint @h @Outer blamedTask
          when ( not $ overloaded blamedOuterTime ( coerce currentSubsetInnerTime :: EndPoint ( HandedTime oh t ) ) ) do
            let
              constraint :: Constraint t
              constraint = handedTimeConstraint currentSubsetInnerTime
              subsetText :: Text
              subsetText = foldMap ( \ tk -> "  * \"" <> taskNames Boxed.Vector.! tk <> "\"\n" ) currentTaskSubset
              afterOrBefore, laterOrEarlier :: Text
              ( afterOrBefore, laterOrEarlier )
                | NotEarlierThan _ _ <- constraint
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
            tell 
              ( Constraints
                { constraints    = IntMap.singleton blamedTaskNb constraint
                , justifications = reason
                }
              )
          -- Continue to see if more activities can be removed.
          innerLoop j currentTaskSubset nextOtherOuterTime currentSubsetInnerTime subsetExtraInnerTime'
    innerLoop j currentTaskSubset _ _ _
      = go j currentTaskSubset

  go ( nbTasks - 1 ) ( Set.fromList [ 0 .. ( nbTasks - 1 ) ] )


-- | Constrain a set of tasks to have a maximum makespan in given intervals (experimental).
--
-- The emitted constraints are logged (using the 'MonadWriter' instance),
-- but not applied.
makespan
  :: forall f1 f2 s task t m tvec ivec
  .  ( MonadReader ( Tasks tvec ivec task t ) m
     , MonadWriter ( Constraints t ) m
     , MonadBase (ST s) m
     , Num t, Ord t, Bounded t, Show t
     , ReadableVector m (Task task t) ( tvec (Task task t) )
     , ReadableVector m Int           ( ivec Int )
     , Foldable f1
     , Foldable f2
     )
  => Text
  -> f1 Int
  -> f2 ( Interval t, Delta t )
  -> m ()
makespan label taskNbs mkspans = do

  allTasks@( Tasks { taskNames, taskInfos = TaskInfos { tasks } } ) <- ask
  let
    nbTasks :: Int
    nbTasks = Boxed.Vector.length taskNames

  -- Compute the estimated ECT and LST of the given subset of tasks.

  -- TODO: here we create full size task trees.
  -- At the cost of recomputing some rankings, we could instead create
  -- task trees the size of the given subset of tasks.
  treeECT <- liftBase $ newTree @Earliest @(BaseDurationInfo Earliest t) nbTasks
  treeLST <- liftBase $ newTree @Latest   @(BaseDurationInfo Latest   t) nbTasks
  ( subsetECT, subsetLST ) <-
    ( `execStateT` ( top, top ) ) $ for_ taskNbs \ taskNb -> do
      task <- lift $ tasks `unsafeIndex` taskNb
      let
        infoECT :: BaseDurationInfo Earliest t
        infoECT =
          DurationInfo
            { subsetInnerTime = pickEndPoint @Earliest @Inner task
            , totalDuration   = taskDuration task
            }
        infoLST :: BaseDurationInfo Latest t
        infoLST =
          DurationInfo
            { subsetInnerTime = pickEndPoint @Latest   @Inner task
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
        latestStart :: EndPoint ( LatestTime t )
        latestStart = cap • ( coerce subsetECT /\ end mkspan )
        outside :: Interval t
        outside = Interval ( start mkspan ) latestStart
        outsides :: Intervals t
        outsides = Intervals ( Seq.singleton outside )
      when ( validInterval outside ) do
        for_ taskNbs \ taskNb -> do
          avail <- taskAvailability <$> tasks `unsafeIndex` taskNb
          let
            removedIntervals :: Intervals t
            removedIntervals = avail /\ outsides
          unless ( null $ intervals removedIntervals ) do
            tell
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
                }
              )
    -- Check whether we need to constrain tasks to not finish near the end of the makespan range,
    -- because the subset must be in progress near the start of the makespan range.
    when ( validInterval $ Interval ( start mkspan ) subsetLST ) do
      let
        earliestEnd :: EndPoint ( EarliestTime t )
        earliestEnd = cap • ( coerce subsetLST /\ start mkspan )
        outside :: Interval t
        outside = Interval earliestEnd ( end mkspan )
        outsides :: Intervals t
        outsides = Intervals ( Seq.singleton outside )
      when ( validInterval outside ) do
        for_ taskNbs \ taskNb -> do
          avail <- taskAvailability <$> tasks `unsafeIndex` taskNb
          let
            removedIntervals :: Intervals t
            removedIntervals = avail /\ outsides
          unless ( null $ intervals removedIntervals ) do
            tell
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
                }
              )
