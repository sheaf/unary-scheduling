{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE UndecidableInstances #-}

module Schedule.Propagators
  ( -- * Propagator framework.
    Propagator(..), basicPropagators
  , coarsen
  , propagateConstraints, propagationLoop
    -- * Constructing the initial 'Modifications' seed for 'propagationLoop'.
  , seedAllOf, seedMatrixWatchers
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
import Data.Maybe
  ( isJust )
import Data.Semigroup
  ( Arg(..) )
import Data.Foldable
  ( for_, find )

-- acts
import Data.Act
  ( Act((•)) )

-- containers
import Data.IntMap.Strict
  ( IntMap )
import qualified Data.IntMap.Strict as IntMap
  ( unionWith, keysSet, filter )
import Data.IntSet
  ( IntSet )
import qualified Data.IntSet as IntSet
  ( fromList, delete, null, empty )
import Data.Sequence
  ( Seq )
import qualified Data.Sequence as Seq
  ( singleton )

-- dependent-map
import qualified Data.Dependent.Map as DMap
  ( fromList, lookup, insert )
import qualified Data.Dependent.Map.Lens as DMap
  ( dmat )

-- dependent-sum
import Data.Dependent.Sum
  ( DSum((:=>)) )

-- generic-lens
import Data.GenericLens.Internal
  ( view, set, over )
import Data.Generics.Product.Fields
  ( field' )

-- lens
import Control.Lens
  ( assign )
import Control.Lens.Fold
  ( forOf_ )
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

-- transformers
import Control.Monad.Trans.Class
  ( lift )

-- vector
import Data.Vector as Boxed.Vector
  ( length )

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
    ( Outside, Inside )
  , HandedTimeConstraint
    ( handedTimeConstraint, handedEndpoint )
  , Constraints(..), Infeasible(..), applyConstraints
  , Justification(..), BoundRule(..), HandedEndpoint(..)
  , BoundMove, Applied(..)
  , tighten, tightenWithPrecedences, tightenBecause
  )
import Schedule.Interval
  ( flipClusivity
  , Endpoint(..)
  , Interval(..)
  , Intervals(..)
  , Measurable(..)
  , pruneShorterThan
  )
import Schedule.Monad
  ( ScheduleMonad, runScheduleMonad
  , constrain
  , SchedulableData
  , TaskUpdates(..)
  , Notifiee(..), Modifications
  , BroadcastTarget(..), broadcastModifications
  )
import Schedule.Monitor
  ( Monitor(..), Monitoring(..), MonitorMode(..) )
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
import Schedule.Trail
  ( Trail )
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
data Propagator task t where
  Propagator
    :: forall ( n :: Type ) ( task :: Type ) ( t :: Type )
    .  { wakeOn        :: Notifiee n
         -- ^ Task modifications this propagator cares about.
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
 :: ( Num t, Measurable t, Bounded t, Show t )
 => Propagator task t
prunePropagator =
  Propagator
    { wakeOn        = Coarse "prune"
    , notifyTarget  = TellEveryoneBut "prune"
    , runPropagator = prune
    }
timetablePropagator =
  Propagator
    { wakeOn        = Coarse "timetable"
    , notifyTarget  = TellEveryone
    , runPropagator = timetable
    }
-- The Θ-tree propagators below read only the earliest/latest /endpoints/ of
-- tasks (via est\/ect\/lst\/lct and durations), never the interior holes of a
-- task's availability. So they wake on endpoint changes only ('Fine'), and sleep
-- through interior-only changes (e.g. a 'timetable'\/'prune' hole removal that
-- leaves est and lct untouched).
overloadPropagator =
  Propagator
    { wakeOn        = Fine "overload"
    , notifyTarget  = TellEveryone
    , runPropagator = overloadCheck
    }
detectablePrecedencesPropagator =
  Propagator
    { wakeOn        = Fine "detectablePrecedences"
    , notifyTarget  = TellEveryone
    , runPropagator = detectablePrecedences @Earliest
    }
detectableSuccedencesPropagator =
  Propagator
    { wakeOn        = Fine "detectableSuccedences"
    , notifyTarget  = TellEveryone
    , runPropagator = detectablePrecedences @Latest
    }
notLastPropagator =
  Propagator
    { wakeOn        = Fine "notLast"
    , notifyTarget  = TellEveryone
    , runPropagator = notExtremal @Earliest
    }
notFirstPropagator =
  Propagator
    { wakeOn        = Fine "notFirst"
    , notifyTarget  = TellEveryone
    , runPropagator = notExtremal @Latest
    }
edgeLastPropagator =
  Propagator
    { wakeOn        = Fine "edgeLast"
    , notifyTarget  = TellEveryone
    , runPropagator = edgeFinding @Earliest
    }
edgeFirstPropagator =
  Propagator
    { wakeOn        = Fine "edgeFirst"
    , notifyTarget  = TellEveryone
    , runPropagator = edgeFinding @Latest
    }
predecessorPropagator =
  Propagator
    { wakeOn        = Coarse "predecessor" -- depends on ordering matrix
    , notifyTarget  = TellEveryone
    , runPropagator = precedenceMatrix @Earliest
    }
successorPropagator =
  Propagator
    { wakeOn        = Coarse "successor" -- depends on ordering matrix
    , notifyTarget  = TellEveryone
    , runPropagator = precedenceMatrix @Latest
    }

-- | List of all propagators, in a convenient order for running all propagation algorithms.
basicPropagators
  :: ( Num t, Measurable t, Bounded t, Show t )
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

-- | The name of a subscription, regardless of its granularity.
notifieeName :: Notifiee n -> Text
notifieeName ( Coarse name ) = name
notifieeName ( Fine   name ) = name

-- | Coarsen a propagator's wake condition: it will then wake on /any/ task
-- modification, not just endpoint changes.
coarsen :: Propagator task t -> Propagator task t
coarsen ( Propagator { wakeOn, notifyTarget, runPropagator } ) =
  Propagator { wakeOn = Coarse ( notifieeName wakeOn ), notifyTarget, runPropagator }

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
  .  ( Num t, Measurable t, Bounded t, Show t, Show task
     , SchedulableData taskData task t
     )
  => taskData
  -> Int
  -> [ Propagator task t ]
  -> ( ImmutableTaskInfos task t, Seq ( Justification t ), Maybe ( Infeasible t ) )
propagateConstraints taskData maxLoopIterations propagators =
  case runScheduleMonad taskData run of
    ( updatedTasks, ( mbInfeasible, Constraints { justifications } ) ) ->
      ( updatedTasks, justifications, either Just ( const Nothing ) mbInfeasible )
  where
    run :: forall s. Trail s task t -> ScheduleMonad s task t ()
    run trail = do
      TaskInfos { taskNames } <- ask
      let allTasks = IntSet.fromList [ 0 .. Boxed.Vector.length taskNames - 1 ]
      -- The non-LCG fixpoint path is never instrumented.
      propagationLoop NoMonitoring maxLoopIterations trail propagators
        ( seedAllOf propagators allTasks )

-- | Seed for 'propagationLoop' that puts the given dirty task set into
-- /every/ propagator subscription.
seedAllOf
  :: [ Propagator task t ]
  -> IntSet
  -> Modifications
seedAllOf propagators dirty = DMap.fromList
  [ case prop of Propagator { wakeOn } -> wakeOn :=> Identity ( fullValue wakeOn dirty )
  | prop <- propagators
  ]

-- | Seed for 'propagationLoop' that wakes /only/ the matrix-watching
-- propagators ('predecessorPropagator', 'successorPropagator') over the
-- given task set.
--
-- Other propagators wake automatically via 'broadcastModifications' if
-- these emit bound-tightening constraints inside the loop.
seedMatrixWatchers :: [ Propagator task t ] -> IntSet -> Modifications
seedMatrixWatchers propagators dirty = DMap.fromList
  [ case prop of
      Propagator { wakeOn } ->
        wakeOn :=> Identity
          ( if notifieeName wakeOn `elem` matrixWatchers
            then fullValue  wakeOn dirty
            else emptyValue wakeOn
              -- NB: these empty values are crucial, as 'broadcastModifications'
              -- can only update subscription keys that are already present.
          )
  | prop <- propagators
  ]
  where
    matrixWatchers :: [ Text ]
    matrixWatchers = [ "predecessor", "successor" ]

{-# INLINABLE propagationLoop #-}
{-# SPECIALISE propagationLoop @MonitoringOff NoMonitoring #-}

-- | Run the given propagators to a fixpoint (event-driven).
propagationLoop
  :: forall mode s task t
  .  ( Num t, Measurable t, Bounded t
     -- debugging
     , Show t, Show task
     , MonitorMode mode
     )
  => Monitor mode s
  -> Int
  -> Trail s task t
  -> [ Propagator task t ]
  -> Modifications          -- ^ initial 'Modifications' used to kick off subscribed propagators
  -> ScheduleMonad s task t ()
propagationLoop mon maxRounds trail propagators seed = do
  modify' ( set ( field' @"tasksModified" ) seed )
  -- Apply any constraints already posted (e.g. by a search decision) before the
  -- first propagator runs, so it sees the tightened domains.
  _ <- applyEmitted TellEveryone
  drive maxRounds
  where

    -- The first propagator with pending work, in list order (so earlier
    -- propagators keep their priority).
    firstReady :: Modifications -> Maybe ( Propagator task t )
    firstReady mods =
      find ( \ ( Propagator { wakeOn } ) -> hasPending wakeOn mods ) propagators

    drive :: Int -> ScheduleMonad s task t ()
    drive rounds
      -- TODO: hitting the round cap returns silently, as if a fixpoint were
      -- reached. Instead we should signal a distinct "GiveUp" value.
      | rounds <= 0
      = pure ()
      | otherwise
      = do
        mods <- view ( field' @"tasksModified" ) <$> get
        case firstReady mods of
          -- No subscription has pending work: fixpoint reached.
          Nothing -> pure ()
          Just ( Propagator { wakeOn, notifyTarget, runPropagator } ) -> do
            runPropagator
            -- Consume this propagator's pending set (local propagators also clear
            -- their own; clearing again here is harmless and covers the globals).
            modify' ( over ( field' @"tasksModified" ) ( clearPending wakeOn ) )
            applied <- applyEmitted notifyTarget
            tickPropagator mon ( notifieeName wakeOn ) applied
            -- Only a round that actually applied constraints counts against the
            -- safety bound, matching the previous loop's iteration counting.
            when applied ( tickRound mon )
            drive ( if applied then rounds - 1 else rounds )

    -- Apply any emitted constraints, broadcasting the resulting task changes to
    -- the subscriptions that should react. Returns whether anything was applied.
    applyEmitted :: BroadcastTarget -> ScheduleMonad s task t Bool
    applyEmitted toNotify = do
      cts <- view ( field' @"taskConstraints" ) <$> get
      if null ( constraints cts )
      then
        pure False
      else do
        applied <- applyConstraints trail cts
        let
          -- How each task's bounds moved (exact vs jumped, or not at all), for
          -- the LCG layer.
          moves :: IntMap ( Maybe BoundMove, Maybe BoundMove )
          moves = fmap ( \ a -> ( estMove a, lctMove a ) ) applied
          -- Whether each bound moved at all, for waking subscriptions.
          bools :: IntMap ( Bool, Bool )
          bools = fmap ( \ ( e, l ) -> ( isJust e, isJust l ) ) moves
          -- Tasks whose interior was carved this pass.
          carved :: IntSet
          carved = IntMap.keysSet ( IntMap.filter wasCarved applied )
        -- NB: this resets 'constraints' but deliberately NOT 'precedences' /
        -- 'boundReasons': the LCG layer ('Schedule.LCG.Theory.runPropagators')
        -- reads the accumulated precedence map and per-bound responsible
        -- subsets at the end of the loop to channel precedences and bound
        -- literals onto the SAT trail. The cost of re-applying the precedences
        -- via 'addIncidentEdges' each round is near-free — the
        -- 'modify'Ordering' equality guard skips (and so does not re-trail)
        -- the idempotent re-adds. TODO: once channeling is the sole matrix
        -- owner ("one matrix owner"), 'applyConstraints' need not touch the
        -- matrix here at all.
        modify'
          -- Reset constraints: they have been applied.
          $ set  ( field' @"taskConstraints" . field' @"constraints" ) mempty
          -- Accumulate how each task's bounds moved (exact vs jumped).
          . over ( field' @"tightenedBounds" ) ( IntMap.unionWith (<>) moves )
          -- Remember which tasks were carved.
          . over ( field' @"carvedTasks" ) ( carved <> )
          -- Broadcast which tasks have been newly modified to the subscriptions
          -- of the propagators that should wake on them.
          . over ( field' @"tasksModified" ) ( broadcastModifications toNotify bools )
        pure True

-- | The \"all tasks pending\" value for a subscription (seeding the initial run).
fullValue :: Notifiee n -> IntSet -> n
fullValue ( Coarse _ ) allTasks = allTasks
fullValue ( Fine   _ ) allTasks = ( allTasks, allTasks )

-- | The empty pending value for a subscription.
emptyValue :: Notifiee n -> n
emptyValue ( Coarse _ ) = IntSet.empty
emptyValue ( Fine   _ ) = ( IntSet.empty, IntSet.empty )

-- | Whether a subscription currently has pending (un-processed) task modifications.
hasPending :: Notifiee n -> Modifications -> Bool
hasPending key mods =
  case DMap.lookup key mods of
    Nothing           -> False
    Just ( Identity v ) -> case key of
      Coarse _ -> not ( IntSet.null v )
      Fine   _ -> case v of ( l, r ) -> not ( IntSet.null l ) || not ( IntSet.null r )

-- | Clear a subscription's pending set.
clearPending :: Notifiee n -> Modifications -> Modifications
clearPending key = DMap.insert key ( Identity ( emptyValue key ) )

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
     , Num t, Measurable t, Show t
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
      constrain $ tighten taskNb ( Inside kept ) $
        SlotsTooShort { task = taskNb, removed }
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
     , Num t, Measurable t, Bounded t, Show t
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
      necessaryInterval = Interval ( flipClusivity ( coerce taskLST ) ) ( flipClusivity ( coerce taskECT ) )
    unless ( isEmpty necessaryInterval ) do
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
            constrain $ tighten otherTaskNb ( Outside necessaryIntervals ) $
              MustBeInProgress
                { duringTask  = taskNb
                , necessary   = necessaryInterval
                , blockedTask = otherTaskNb
                , removed     = removedIntervals
                }

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
     , Num t, Measurable t, Bounded t, Show t
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
      -- Done with the inner loop: report the new earliest/latest time, but only
      -- if it would actually tighten the current outer time (the strict lattice
      -- meet test; see the analogous guards in 'detectablePrecedences' and
      -- 'edgeFinding').
      = when ( ( taskOuterTime /\ limitTime ) /= taskOuterTime ) do
        let
          constraint :: Constraint t
          constraint = handedTimeConstraint limitTime
          subset :: IntSet
          subset = IntSet.fromList subsetTaskNbs
        -- The bound rests on the matrix precedences between 'taskNb' and the
        -- subset; record them as the responsible subset (no new edge is added,
        -- the matrix already holds them).
        constrain $
          tightenBecause taskNb constraint
            ( handedPrecedences @h subset )
            SubsetPrecedence
              { rule          = PrecedenceMatrix
              , task          = taskNb
              , relatedSubset = subset
              , newBound      = handedEndpoint @h limitTime
              }
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
      taskOuterTime = pickEndpoint @h @Outer task
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
     , MonadError ( Infeasible t )  m
     , PrimMonad m, s ~ PrimState m
     , Num t, Measurable t, Bounded t, Show t
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
        -- When the unary resource is overloaded, throw to end propagation.
        when ( overloaded estimatedECT currentLCT ) do
          let
            culprit :: IntSet
            culprit = IntSet.fromList ( taskNb : seenTaskNbs )
          throwError $ Overloaded
            { bindingTask = taskNb
            , bindingLCT  = currentLCT
            , subsetECT   = estimatedECT
            , culprit     = culprit
            }

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
     , Num t, Measurable t, Bounded t, Show t
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
      | i >= nbTasks
      = pure ()
      | otherwise
      = do
        taskNb   <- ( ordered $ view ( _ranking @h @Inner ) allTasks ) `unsafeIndex` ( handedIndex @h nbTasks i )
        currTask <-                                         taskAvails `unsafeIndex` taskNb
        innerLoop taskNb currTask i j js

    innerLoop :: Int -> Task task t -> Int -> Int -> [Int] -> m ()
    innerLoop taskNb currentTask i j otherTaskNbs
      | j >= nbTasks
      = finishOuter taskNb currentTask i j otherTaskNbs
      | otherwise = do
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

      if addNode
      then
        innerLoop   taskNb currentTask i j' otherTaskNbs'
      else
        finishOuter taskNb currentTask i j' otherTaskNbs'

    -- End of the inner loop for the current outer task: emit the detected
    -- precedence (if nontrivial) and go to the next outer loop iteration.
    finishOuter :: Int -> Task task t -> Int -> Int -> [Int] -> m ()
    finishOuter taskNb currentTask i j otherTaskNbs = do
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
        when ( ( currentOuterTime /\ excludeCurrentTaskSubsetInnerTime ) /= currentOuterTime ) do
          let
            constraint :: Constraint t
            constraint = handedTimeConstraint excludeCurrentTaskSubsetInnerTime
            subset :: IntSet
            subset = IntSet.fromList otherTaskNbs
          -- TODO: add precedence to precedence graph to avoid unnecessary duplication of effort.
          constrain $
            tightenWithPrecedences taskNb constraint
              ( handedPrecedences @h subset )
              SubsetPrecedence
                { rule          = DetectablePrecedence
                , task          = taskNb
                , relatedSubset = subset
                , newBound      = handedEndpoint @h excludeCurrentTaskSubsetInnerTime
                }
      -- Continue to next iteration of outer loop.
      go ( i + 1 ) j otherTaskNbs

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
     , Num t, Measurable t, Bounded t, Show t
     , ReadableVector m ( Task task t ) ( bvec ( Task task t ) )
     , ReadableVector m Int             ( uvec Int )
     , KnownHandedness h oh
     , Lattice ( Endpoint ( HandedTime oh t ) )
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
          && ( currentOtherOuterTime /\ associatedOtherInnerTime ) /= currentOtherOuterTime
          )
          do
            let
              constraint :: Constraint t
              constraint = handedTimeConstraint associatedOtherInnerTime
              -- The bound is an energetic consequence of the current subset's
              -- bounds (no precedence edge is implied), so record the subset on
              -- both sides as the responsible set.
              cs :: IntSet
              cs = IntSet.fromList currentSubset'
            constrain $ tightenBecause currentTaskNb constraint ( cs, cs )
              SubsetPrecedence
                { rule          = NotExtremal
                , task          = currentTaskNb
                , relatedSubset = cs
                , newBound      = handedEndpoint @oh associatedOtherInnerTime
                }

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
     , Num t, Measurable t, Bounded t, Show t
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
          -- Ensure this would result in a nontrivial constraint.
          when ( ( blamedOuterTime /\ currentSubsetInnerTime ) /= blamedOuterTime ) do
            let
              constraint :: Constraint t
              constraint = handedTimeConstraint currentSubsetInnerTime
            -- TODO: add precedence to precedence graph to avoid unnecessary duplication of effort.
            constrain $
              tightenWithPrecedences blamedTaskNb constraint
                ( handedPrecedences @h currentTaskSubset )
                SubsetPrecedence
                  { rule          = EdgeFinding
                  , task          = blamedTaskNb
                  , relatedSubset = currentTaskSubset
                  , newBound      = handedEndpoint @h currentSubsetInnerTime
                  }
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
     , Num t, Measurable t, Bounded t, Show t
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
    unless ( isEmpty $ Interval subsetECT ( end mkspan ) ) do
      let
        latestStart :: Endpoint ( LatestTime t )
        latestStart = cap • ( coerce subsetECT /\ end mkspan )
        outside :: Interval t
        outside = Interval ( start mkspan ) latestStart
        outsides :: Intervals t
        outsides = Intervals ( Seq.singleton outside )
      unless ( isEmpty outside ) do
        for_ taskNbs \ taskNb -> do
          avail <- taskAvailability <$> taskAvails `unsafeIndex` taskNb
          let
            removedIntervals :: Intervals t
            removedIntervals = avail /\ outsides
          unless ( null $ intervals removedIntervals ) do
            constrain $ tighten taskNb ( Outside outsides ) $
              MakespanRemoval
                { makespanLabel    = label
                , makespanInterval = mkspan
                , makespanCap      = cap
                , task             = taskNb
                , makespanBound    = LatestBound latestStart
                , removed          = removedIntervals
                }
    -- Check whether we need to constrain tasks to not finish near the end of the makespan range,
    -- because the subset must be in progress near the start of the makespan range.
    unless ( isEmpty $ Interval ( start mkspan ) subsetLST ) do
      let
        earliestEnd :: Endpoint ( EarliestTime t )
        earliestEnd = cap • ( coerce subsetLST /\ start mkspan )
        outside :: Interval t
        outside = Interval earliestEnd ( end mkspan )
        outsides :: Intervals t
        outsides = Intervals ( Seq.singleton outside )
      unless ( isEmpty outside ) do
        for_ taskNbs \ taskNb -> do
          avail <- taskAvailability <$> taskAvails `unsafeIndex` taskNb
          let
            removedIntervals :: Intervals t
            removedIntervals = avail /\ outsides
          unless ( null $ intervals removedIntervals ) do
            constrain $ tighten taskNb ( Outside outsides ) $
              MakespanRemoval
                { makespanLabel    = label
                , makespanInterval = mkspan
                , makespanCap      = cap
                , task             = taskNb
                , makespanBound    = EarliestBound earliestEnd
                , removed          = removedIntervals
                }
{-
TODO: take into account internal fragmentation or un-schedulable gaps in the
makespan calculation.
-}