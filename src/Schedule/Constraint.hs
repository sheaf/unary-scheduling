{-# LANGUAGE BlockArguments      #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE ViewPatterns        #-}

module Schedule.Constraint
  ( Constraint
    ( .. , NotEarlierThan, NotLaterThan, Outside, Inside )
  , HandedTimeConstraint(..)
  , Constraints(..)
  , constrainToBefore, constrainToAfter
  , constrainToInside, constrainToOutside
  , applyConstraint, applyConstraints
  )
  where

-- base
import Control.Monad
  ( when )
import Control.Monad.ST
  ( ST )
import Data.Foldable
  ( traverse_, foldl' )
import GHC.Generics
  ( Generic )

-- containers
import Data.IntMap.Strict
  ( IntMap )
import qualified Data.IntMap.Strict as IntMap
  ( empty, unionWith, foldrWithKey )

-- mtl
import Control.Monad.Reader
  ( MonadReader ( ask ) )

-- text
import Data.Text
  ( Text )

-- transformers-base
import Control.Monad.Base
  ( MonadBase ( liftBase ) )

-- vector
import qualified Data.Vector.Mutable as Boxed.MVector
  ( unsafeRead, unsafeWrite )

-- unary-scheduling
import Data.Lattice
  ( Lattice
      ( (\/), (/\) )
  )
import Data.Vector.Ranking
  ( reorderAfterIncrease, reorderAfterDecrease )
import Schedule.Interval
  ( Clusivity(..), EndPoint(..)
  , Intervals(..)
  , cutBefore, cutAfter, remove
  )
import Schedule.Task
  ( Task(..), Tasks(..), TaskInfos(..)
  , MutableTasks
  , est, lct, lst, ect
  )
import Schedule.Time
  ( Handedness
    ( Earliest, Latest )
  , HandedTime
  , EarliestTime, LatestTime
  )

-------------------------------------------------------------------------------

data Constraint t
  = Constraint
  { notEarlierThan :: Maybe ( EndPoint ( EarliestTime t ) )
  , notLaterThan   :: Maybe ( EndPoint ( LatestTime   t ) )
  , outside        :: Maybe ( Intervals t )
  , inside         :: Maybe ( Intervals t )
  }
  deriving stock ( Show, Generic )

pattern NotEarlierThan :: Ord t => EarliestTime t -> Clusivity -> Constraint t
pattern NotEarlierThan t clu <- ( notEarlierThan -> Just ( EndPoint t clu ) )
  where
    NotEarlierThan t clu = mempty { notEarlierThan = Just ( EndPoint t clu ) }

pattern NotLaterThan :: Ord t => LatestTime t -> Clusivity -> Constraint t
pattern NotLaterThan t clu <- ( notLaterThan -> Just ( EndPoint t clu ) )
  where
    NotLaterThan t clu = mempty { notLaterThan = Just ( EndPoint t clu ) }

pattern Outside :: Ord t => Intervals t -> Constraint t
pattern Outside ivals <- ( outside -> Just ivals )
  where
    Outside ivals = mempty { outside = Just ivals }

pattern Inside :: Ord t => Intervals t -> Constraint t
pattern Inside ivals <- ( inside -> Just ivals )
  where
    Inside ivals = mempty { inside = Just ivals }

instance Ord t => Semigroup ( Constraint t ) where
  Constraint e1 l1 o1 i1 <> Constraint e2 l2 o2 i2 = Constraint e l o i
    where
      e = combine (/\) e1 e2
      l = combine (/\) l1 l2
      o = combine (\/) o1 o2
      i = combine (/\) i1 i2

      combine :: ( a -> a -> a ) -> Maybe a -> Maybe a -> Maybe a
      combine _ Nothing  Nothing  = Nothing
      combine _ (Just a) Nothing  = Just a
      combine _ Nothing  (Just b) = Just b
      combine f (Just a) (Just b) = Just (f a b)

instance Ord t => Monoid ( Constraint t ) where
  mempty = Constraint Nothing Nothing Nothing Nothing

data Constraints t
  = Constraints
  { constraints    :: IntMap ( Constraint t )
  , justifications :: Text
  }
  deriving stock ( Show, Generic )

instance Ord t => Semigroup ( Constraints t ) where
  ( Constraints cts1 logs1 ) <> ( Constraints cts2 logs2 ) =
    Constraints ( IntMap.unionWith (<>) cts1 cts2 ) ( logs1 <> logs2 )
instance Ord t => Monoid ( Constraints t ) where
  mempty = Constraints IntMap.empty mempty

applyConstraints
  :: ( MonadReader ( MutableTasks s task t ) m
     , MonadBase (ST s) m
     , Num t, Ord t, Bounded t
     -- debugging
     , Show t, Show task
     )
  => Constraints t
  -> m ()
applyConstraints = itraverse_ applyConstraint . constraints

applyConstraint
  :: ( MonadReader ( MutableTasks s task t ) m
     , MonadBase (ST s) m
     , Num t, Ord t, Bounded t
     -- debugging
     , Show t, Show task
     )
  => Int
  -> Constraint t
  -> m ()
applyConstraint i ( Constraint { .. } ) = do
  -- apply 'constrain to inside' first (useful in case restriction is not checked)
  traverse_ ( constrainToInside  i ) inside
  traverse_ ( constrainToAfter   i ) notEarlierThan
  traverse_ ( constrainToBefore  i ) notLaterThan
  traverse_ ( constrainToOutside i ) outside


itraverse_ :: Applicative t => ( Int -> v -> t u ) -> IntMap v -> t ()
itraverse_ f = IntMap.foldrWithKey ( \ k a b -> f k a *> b ) ( pure () )

-------------------------------------------------------------------------------

class HandedTimeConstraint (h :: Handedness) where
  -- | Constraint associated to a handed time:
  --   - @Earliest t@ : @NotEarlierThan t@
  --   - @Latest t@ : @NotLaterThan t@.
  handedTimeConstraint :: Ord t => EndPoint (HandedTime h t) -> Constraint t
instance HandedTimeConstraint Earliest where
  handedTimeConstraint ( EndPoint t clu ) = NotEarlierThan t clu
instance HandedTimeConstraint Latest   where
  handedTimeConstraint ( EndPoint t clu ) = NotLaterThan   t clu

-- | Apply the constraint: task must begin after the specified time.
constrainToAfter
  :: ( MonadReader ( MutableTasks s task t ) m
     , MonadBase (ST s) m
     , Num t, Ord t, Bounded t
     )
  => Int
  -> EndPoint ( EarliestTime t ) 
  -> m ()
constrainToAfter taskNo t = do
  Tasks { taskInfos = TaskInfos { tasks, rankingEST, rankingECT } } <- ask
  liftBase do
    task@(Task { taskAvailability }) <- Boxed.MVector.unsafeRead tasks taskNo
    let
      newTaskAvailability = cutBefore t taskAvailability
      newTask = task { taskAvailability = newTaskAvailability }
    Boxed.MVector.unsafeWrite tasks taskNo newTask
    reorderAfterIncrease tasks rankingEST est taskNo
    reorderAfterIncrease tasks rankingECT ect taskNo

-- | Apply the constraint: task must end before the specified time.
constrainToBefore
  :: ( MonadReader ( MutableTasks s task t ) m
     , MonadBase (ST s) m
     , Num t, Ord t, Bounded t
     )
  => Int
  -> EndPoint ( LatestTime t ) 
  -> m ()
constrainToBefore taskNo t = do
  Tasks { taskInfos = TaskInfos { tasks, rankingLCT, rankingLST } } <- ask
  liftBase do
    task@(Task { taskAvailability }) <- Boxed.MVector.unsafeRead tasks taskNo
    let
      newTaskAvailability = cutAfter t taskAvailability
      newTask = task { taskAvailability = newTaskAvailability }
    Boxed.MVector.unsafeWrite tasks taskNo newTask
    reorderAfterDecrease tasks rankingLCT lct taskNo
    reorderAfterDecrease tasks rankingLST lst taskNo

-- | Remove intervals from the domain of availability of a task.
constrainToOutside
  :: ( MonadReader ( MutableTasks s task t ) m
     , MonadBase (ST s) m
     , Num t, Ord t, Bounded t
     )
  => Int
  -> Intervals t
  -> m ()
constrainToOutside taskNo (Intervals ivalsToRemove) = do
  Tasks { taskInfos = TaskInfos { .. } } <- ask
  liftBase do
    task@(Task { taskAvailability }) <- Boxed.MVector.unsafeRead tasks taskNo
    let
      newAvailability = foldl' remove taskAvailability ivalsToRemove
      newTask = task { taskAvailability = newAvailability }
    Boxed.MVector.unsafeWrite tasks taskNo newTask
    when ( est newTask > est task ) do
      reorderAfterIncrease tasks rankingEST est taskNo
      reorderAfterIncrease tasks rankingECT ect taskNo
    when ( lct newTask < lct task ) do
      reorderAfterDecrease tasks rankingLCT lct taskNo
      reorderAfterDecrease tasks rankingLST lst taskNo

-- | Reduce the domain of availability of a task.
constrainToInside
  :: ( MonadReader ( MutableTasks s task t ) m
     , MonadBase (ST s) m
     , Num t, Ord t, Bounded t
     -- debugging
     , Show task, Show t
     )
  => Int
  -> Intervals t
  -> m ()
constrainToInside taskNo shrunkDomain = do
  Tasks { taskInfos = TaskInfos { .. } } <- ask
  liftBase do
    task@( Task { taskAvailability = oldDomain } ) <- Boxed.MVector.unsafeRead tasks taskNo
    let
      newTask = task { taskAvailability = oldDomain /\ shrunkDomain }
    Boxed.MVector.unsafeWrite tasks taskNo newTask
    when ( est newTask > est task ) do
      reorderAfterIncrease tasks rankingEST est taskNo
      reorderAfterIncrease tasks rankingECT ect taskNo
    when ( lct newTask < lct task ) do
      reorderAfterDecrease tasks rankingLCT lct taskNo
      reorderAfterDecrease tasks rankingLST lst taskNo
