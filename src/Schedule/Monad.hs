{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

module Schedule.Monad
  ( MonadSchedule
  , ScheduleMonad, runScheduleMonad
  , constrain
  , SchedulableData(..)
  , TaskUpdates(..)
  , Notifiee(..), Modifications
  , BroadcastTarget(..), broadcastModifications
  ) where

-- base
import Control.Category
  ( (>>>) )
import Control.Monad.ST
  ( ST, runST )
import Data.Bifunctor
  ( bimap, second )
import Data.Coerce
  ( coerce )
#ifdef DEBUG
import Data.Foldable
  ( toList )
#endif
import Data.Function
  ( (&) )
import Data.Functor.Identity
  ( Identity(..) )
import Data.Kind
  ( Constraint )
import Data.Type.Equality
  ( (:~:)(..) )
import GHC.Generics
  ( Generic )

-- constraints-extras
import Data.Constraint.Extras.TH
  ( deriveArgDict )

-- containers
import Data.IntMap.Strict
  ( IntMap )
import qualified Data.IntMap.Strict as IntMap
  ( keysSet, filter, unionWith )
import qualified Data.IntSet as IntSet
  ( union )
import Data.IntSet
  ( IntSet )

-- dependent-map
import Data.Dependent.Map
  ( DMap )
import qualified Data.Dependent.Map as DMap
  ( mapWithKey )

-- lens
import Control.Lens
  ( over )

-- generic-lens
import Data.Generics.Product.Fields
  ( field' )

-- mtl
import Control.Monad.Except
  ( MonadError )
import Control.Monad.Reader
  ( MonadReader )
import Control.Monad.State
  ( MonadState, modify' )

-- primitive
import Control.Monad.Primitive
  ( PrimMonad(PrimState) )

-- some
import Data.GADT.Compare
  ( GEq(..), GOrdering(..), GCompare(..) )
import Data.GADT.Show
  ( GShow(..) )

-- text
import Data.Text
  ( Text )

-- transformers
import Control.Monad.Trans.Except
  ( ExceptT, runExceptT )
import Control.Monad.Trans.Reader
  ( ReaderT, runReaderT )
import Control.Monad.Trans.State.Strict
  ( StateT , runStateT )

-- vector
import qualified Data.Vector as Boxed
  ( Vector )
import qualified Data.Vector as Boxed.Vector
  ( length, fromList, unzip, unsafeThaw )

-- unary-scheduling
import Data.Vector.PhaseTransition
  ( Freeze
      ( unsafeFreeze )
  , Thaw
      ( thaw )
  )
import Data.Vector.Ranking
  ( rankOn )
import Schedule.Constraint
  ( Constraints, Infeasible, BoundMove )
import Schedule.Interval
  ( Measurable
#ifdef DEBUG
  , Endpoint(..), Intervals(..)
#endif
  )
import Schedule.Ordering
  ( Order(Unknown), newOrderingMatrix )
import Schedule.Task
  ( Task(..), TaskInfos(..)
  , MutableTaskInfos, ImmutableTaskInfos
  , est, lct, ect, lst
  )
#ifdef DEBUG
import Schedule.Time
  ( Time(..), HandedTime(..), Delta(..) )
#endif
import Schedule.Trail
  ( Trail, newTrail )

-------------------------------------------------------------------------------
-- Schedule monad.

-- | Object which needs to be notified of modifications.
--
-- Either:
--  * coarse notifications: a task has been modified.
--  * fine notifications: a task's left/right endpoint has been modified.
data Notifiee a where
  Coarse :: Text -> Notifiee IntSet
  Fine   :: Text -> Notifiee ( IntSet, IntSet )
deriveArgDict ''Notifiee

data TaskUpdates t
  = TaskUpdates
  { taskConstraints :: !(Constraints t)
  , tasksModified   :: !Modifications
  , -- | Per task, how its earliest start \/ latest completion bound moved as
    -- constraints were applied this pass (exact vs jumped).
    tightenedBounds :: !( IntMap ( Maybe BoundMove, Maybe BoundMove ) )
  , -- | Tasks /carved/ this pass (an 'Schedule.Constraint.Inside'\/
    -- 'Schedule.Constraint.Outside' tightening applied), which may introduce
    -- non-ground interior gaps.
    carvedTasks     :: !IntSet
  }
  deriving stock ( Show, Generic )

instance Measurable t => Semigroup ( TaskUpdates t ) where
  TaskUpdates cts1 mods1 tb1 cv1 <> TaskUpdates cts2 mods2 tb2 cv2 =
    TaskUpdates ( cts1 <> cts2 ) ( mods1 <> mods2 )
      ( IntMap.unionWith (<>) tb1 tb2 )
      ( cv1 <> cv2 )
instance Measurable t => Monoid ( TaskUpdates t ) where
  mempty = TaskUpdates mempty mempty mempty mempty

type ScheduleMonad s task t =
  ( ReaderT ( MutableTaskInfos s task t )
    ( ExceptT ( Infeasible t )
      ( StateT ( TaskUpdates t )
        ( ST s )
      )
    )
  )

type MonadSchedule s task t m =
  ( ( MonadReader ( MutableTaskInfos s task t ) m
    , MonadState  ( TaskUpdates t ) m
    , MonadError  ( Infeasible t ) m
    , PrimMonad m, PrimState m ~ s
    ) :: Constraint
  )

-- | Run a one-shot scheduling computation: thaw a fresh mutable state, run the
-- given action, and freeze the result.
runScheduleMonad
  :: forall task t taskData a
  .  ( Num t, Measurable t, Bounded t
     , SchedulableData taskData task t
     )
  => taskData
  -> ( forall s. Trail s task t -> ScheduleMonad s task t a )
      -- ^ Action to run. Supplied with a fresh 'Trail' for backtracking.
  -> ( ImmutableTaskInfos task t, ( Either ( Infeasible t ) a, Constraints t ) )
runScheduleMonad givenTasks k = runST do
  mutableTaskInfos <- initialTaskData givenTasks
  trail            <- newTrail
  res <- k trail & ( ( `runReaderT` mutableTaskInfos ) >>> runExceptT >>> ( `runStateT` mempty ) )
  finalTaskData <- unsafeFreeze mutableTaskInfos
  pure ( finalTaskData, second taskConstraints res )

constrain :: ( Measurable t, MonadState ( TaskUpdates t ) m ) => Constraints t -> m ()
constrain s = modify' ( over ( field' @"taskConstraints" ) ( <> s ) )

-------------------------------------------------------------------------------
-- Typeclass to abstract over different input data
-- that can be provided to scheduling procedures.

class    ( Num t, Ord t, Bounded t )
      => SchedulableData taskData task t | taskData -> task t
      where
  initialTaskData :: taskData -> ST s ( MutableTaskInfos s task t )

instance ( Num t, Ord t, Bounded t )
      => SchedulableData ( ImmutableTaskInfos task t ) task t
      where
  initialTaskData = thaw

instance ( Num t, Measurable t, Bounded t, Show t )
      => SchedulableData [ ( Task task t, Text ) ] task t
      where
  initialTaskData taskList = do
    let
      numberedTasks :: [ ( Task task t, Int ) ]
      numberedTasks = zipWith ( \ ( t, _ ) i -> ( t, i ) ) taskList [0..]
    let
      immutableTasks :: Boxed.Vector ( Task task t )
      taskNames :: Boxed.Vector Text
      ( immutableTasks, taskNames ) = Boxed.Vector.unzip $ Boxed.Vector.fromList taskList
      n :: Int
      n = Boxed.Vector.length taskNames
#ifdef DEBUG
    assertHeadroom immutableTasks
#endif
    taskAvails <- Boxed.Vector.unsafeThaw immutableTasks
    rankingEST <- rankOn est numberedTasks
    rankingLCT <- rankOn lct numberedTasks
    rankingLST <- rankOn lst numberedTasks
    rankingECT <- rankOn ect numberedTasks
    -- The ordering matrix starts empty; window-implied precedences are
    -- rediscovered on the first propagation, which keeps the matrix in sync.
    orderings  <- newOrderingMatrix n ( \ _ _ -> Unknown )
    pure ( TaskInfos { .. } )

#ifdef DEBUG
-- | Ensure that we aren't going past minBound/maxBound when canonicalising
-- the availabilities of any tasks.
assertHeadroom
  :: forall m task t
  .  ( Monad m, Num t, Measurable t, Bounded t, Show t )
  => Boxed.Vector ( Task task t ) -> m ()
assertHeadroom tasks =
  case filter ( not . Prelude.null . intervals . taskAvailability ) ( toList tasks ) of
    []        -> pure ()
    realTasks
      | maxLct >= maxBound - totalDur || minEst <= minBound + totalDur
      -> error $ unlines
          [ "Task availabilities outside of bounds."
          , "  minBound = " <> show ( minBound :: t )
          , "  maxBound = " <> show ( maxBound :: t )
          , "  min est  = " <> show minEst
          , "  max lct  = " <> show maxLct
          , "  total duration (largest Θ shift) = " <> show totalDur
          ]
      | otherwise
      -> pure ()
      where
        minEst   = minimum ( map ( getTime . handedTime . endpoint . est ) realTasks )
        maxLct   = maximum ( map ( getTime . handedTime . endpoint . lct ) realTasks )
        totalDur = sum     ( map ( getDelta . taskDuration )               realTasks )
#endif

-------------------------------------------------------------------------------
-- Keeping track of stale tasks,
-- that need to be processed again by propagators
-- which operate one task at a time (local propagators).

-- | Keep track of all modifications in a dependent map.
--
-- Each object that needs to be notified has a separate key,
-- with value the set of tasks that we want to notify have since been modified.
type Modifications = DMap Notifiee Identity

data BroadcastTarget
  = TellEveryone
  | TellEveryoneBut Text
  deriving stock ( Show, Eq )

broadcastModifications :: BroadcastTarget -> IntMap ( Bool, Bool ) -> Modifications -> Modifications
broadcastModifications tgt newModifs =
  DMap.mapWithKey \case
    Coarse name
      | TellEveryoneBut name /= tgt
      -- Update even with ( False, False ) keys (i.e. neither left or right adjusted),
      -- as the task can still have been modified without its endpoints changing.
      -> coerce $ IntSet.union ( IntMap.keysSet newModifs )
    Fine name
      | TellEveryoneBut name /= tgt
      -> coerce $ bimap @(,)
            ( IntSet.union ( IntMap.keysSet $ IntMap.filter fst newModifs ) )
            ( IntSet.union ( IntMap.keysSet $ IntMap.filter snd newModifs ) )
    _ -> id

deriving stock instance Show ( Notifiee a )
instance GEq Notifiee where
  geq ( Coarse a ) ( Coarse b )
    | a == b
    = Just Refl
  geq ( Fine a ) ( Fine b )
    | a == b
    = Just Refl
  geq _ _ = Nothing
instance GCompare Notifiee where
  gcompare ( Coarse a ) ( Coarse b ) = case compare a b of
    LT -> GLT
    GT -> GGT
    EQ -> GEQ
  gcompare ( Fine a ) ( Fine b ) = case compare a b of
    LT -> GLT
    GT -> GGT
    EQ -> GEQ
  gcompare ( Coarse _ ) ( Fine _ ) = GLT
  gcompare ( Fine _ ) ( Coarse _ ) = GGT
instance GShow Notifiee where
  gshowsPrec = showsPrec
