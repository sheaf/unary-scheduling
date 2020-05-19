{-# LANGUAGE BlockArguments         #-}
{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE DeriveGeneric          #-}
{-# LANGUAGE DerivingStrategies     #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE RecordWildCards        #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE StandaloneDeriving     #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}

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
import Control.Arrow
  ( second )
import Control.Category
  ( (>>>) )
import Control.Monad.ST
  ( ST, runST )
import Data.Bifunctor
  ( bimap )
import Data.Coerce
  ( coerce )
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

-- bitvec
import Data.Bit
  ( Bit(..) )

-- constraints
import Data.Constraint
  ( Dict(..) )

-- constraints-extras
import Data.Constraint.Extras
  ( ArgDict(..) )

-- containers
import Data.IntMap.Strict
  ( IntMap )
import qualified Data.IntMap.Strict as IntMap
  ( keysSet, filter )
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
  ( length, fromList, (!), unzip, unsafeThaw )

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
  ( Constraints )
import Schedule.Ordering
  ( Order(..), newOrderingMatrix )
import Schedule.Task
  ( Task(..), TaskInfos(..)
  , MutableTaskInfos, ImmutableTaskInfos
  , est, lct, ect, lst
  )
import Schedule.Tree
  ( Propagatable
      ( overloaded )
  )

-------------------------------------------------------------------------------
-- Schedule monad.

data TaskUpdates t
  = TaskUpdates
  { taskConstraints :: !(Constraints t)
  , tasksModified   :: !Modifications
  }
  deriving stock ( Show, Generic )

instance Ord t => Semigroup ( TaskUpdates t ) where
  TaskUpdates cts1 mods1 <> TaskUpdates cts2 mods2 =
    TaskUpdates ( cts1 <> cts2 ) ( mods1 <> mods2 )
instance Ord t => Monoid ( TaskUpdates t ) where
  mempty = TaskUpdates mempty mempty

type ScheduleMonad s task t =
  ( ReaderT ( MutableTaskInfos s task t )
    ( ExceptT Text
      ( StateT ( TaskUpdates t )
        ( ST s )
      )
    )
  )

type MonadSchedule s task t m =
  ( ( MonadReader ( MutableTaskInfos s task t ) m
    , MonadState  ( TaskUpdates t ) m
    , MonadError  Text   m
    , PrimMonad m, PrimState m ~ s
    ) :: Constraint
  )

runScheduleMonad
  :: forall task t taskData a
  .  ( Num t, Ord t, Bounded t
     , SchedulableData taskData task t
     )
  => taskData
  -> ( forall s. ScheduleMonad s task t a )
  -> ( ImmutableTaskInfos task t, ( Either Text a, Constraints t ) )
runScheduleMonad givenTasks ma = runST do
  mutableTaskInfos <- initialTaskData givenTasks
  res <- ma & ( ( `runReaderT` mutableTaskInfos ) >>> runExceptT >>> ( `runStateT` mempty ) )
  finalTaskData <- unsafeFreeze mutableTaskInfos
  pure ( finalTaskData, second taskConstraints res )

constrain :: ( Ord t, MonadState ( TaskUpdates t ) m ) => Constraints t -> m ()
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

instance ( Num t, Ord t, Bounded t )
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

      order :: Int -> Int -> Order
      order i j =
        let
          tk_i, tk_j :: Task task t
          tk_i = immutableTasks Boxed.Vector.! i
          tk_j = immutableTasks Boxed.Vector.! j
        in Order ( Bit ( overloaded ( est tk_j ) ( lst tk_i ) ), Bit ( overloaded ( est tk_i ) ( lst tk_j ) ) )
    taskAvails <- Boxed.Vector.unsafeThaw immutableTasks
    rankingEST <- rankOn est numberedTasks
    rankingLCT <- rankOn lct numberedTasks
    rankingLST <- rankOn lst numberedTasks
    rankingECT <- rankOn ect numberedTasks
    orderings  <- newOrderingMatrix n order
    pure ( TaskInfos { .. } )

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
      -> coerce $ IntSet.union ( IntMap.keysSet $ IntMap.filter ( \case { ( False, False ) -> False; _ -> True } ) newModifs )
    Fine name
      | TellEveryoneBut name /= tgt
      -> coerce $ bimap @(,)
            ( IntSet.union ( IntMap.keysSet $ IntMap.filter fst newModifs ) )
            ( IntSet.union ( IntMap.keysSet $ IntMap.filter snd newModifs ) )
    _ -> id

-- | Object which needs to be notified of modifications.
--
-- Either:
--  * coarse notifications: a task has been modified.
--  * fine notifications: a task's left/right endpoint has been modified.
data Notifiee a where
  Coarse :: Text -> Notifiee IntSet
  Fine   :: Text -> Notifiee ( IntSet, IntSet )
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
instance ArgDict c Notifiee where
  type ConstraintsFor Notifiee c = ( c IntSet, c ( IntSet, IntSet ) )
  argDict ( Coarse _ ) = Dict
  argDict ( Fine   _ ) = Dict
