{-# LANGUAGE BlockArguments      #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
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
import Data.Foldable
  ( foldl' )
import Data.Maybe
  ( fromMaybe )
import GHC.Generics
  ( Generic )

-- containers
import Data.IntMap.Strict
  ( IntMap )
import qualified Data.IntMap.Strict as IntMap
  ( empty, unionWith, traverseWithKey )

-- mtl
import Control.Monad.Reader
  ( MonadReader ( ask ) )

-- primitive
import Control.Monad.Primitive
  ( PrimMonad(PrimState) )

-- text
import Data.Text
  ( Text )

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
  ( Endpoint(..), Intervals(..)
  , cutBefore, cutAfter, remove
  )
import Schedule.Task
  ( Task(..), TaskInfos(..), MutableTaskInfos
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
  { notEarlierThan :: Maybe ( Endpoint ( EarliestTime t ) )
  , notLaterThan   :: Maybe ( Endpoint ( LatestTime   t ) )
  , outside        :: Maybe ( Intervals t )
  , inside         :: Maybe ( Intervals t )
  }
  deriving stock ( Show, Generic )

pattern NotEarlierThan :: Ord t => Endpoint ( EarliestTime t ) -> Constraint t
pattern NotEarlierThan endpoint <- ( notEarlierThan -> Just endpoint )
  where
    NotEarlierThan endpoint= mempty { notEarlierThan = Just endpoint }

pattern NotLaterThan :: Ord t => Endpoint ( LatestTime t ) -> Constraint t
pattern NotLaterThan endpoint <- ( notLaterThan -> Just endpoint )
  where
    NotLaterThan endpoint = mempty { notLaterThan = Just endpoint }

pattern Outside :: Ord t => Intervals t -> Constraint t
pattern Outside ivals <- ( outside -> Just ivals )
  where
    Outside ivals = mempty { outside = Just ivals }

pattern Inside :: Ord t => Intervals t -> Constraint t
pattern Inside ivals <- ( inside -> Just ivals )
  where
    Inside ivals = mempty { inside = Just ivals }

pattern NoConstraint :: Constraint t
pattern NoConstraint = Constraint Nothing Nothing Nothing Nothing

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
  mempty = NoConstraint

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
  :: ( MonadReader ( MutableTaskInfos s task t ) m
     , PrimMonad m, PrimState m ~ s
     , Num t, Ord t, Bounded t
     -- debugging
     , Show t, Show task
     )
  => Constraints t
  -> m ( IntMap ( Bool, Bool ) )
applyConstraints = IntMap.traverseWithKey applyConstraint . constraints

applyConstraint
  :: ( MonadReader ( MutableTaskInfos s task t )  m
     , PrimMonad m, PrimState m ~ s
     , Num t, Ord t, Bounded t
     -- debugging
     , Show t, Show task
     )
  => Int
  -> Constraint t
  -> m ( Bool, Bool )
applyConstraint _ NoConstraint = pure ( False, False )
applyConstraint i ( Constraint { .. } ) = do
  taskInfos <- ask
  -- apply 'constrain to inside' first (useful in case restriction is not checked)
  ( l1, r1 ) <- fromMaybe ( False, False ) <$> traverse ( constrainToInside  taskInfos i ) inside
  l2         <- fromMaybe False            <$> traverse ( constrainToAfter   taskInfos i ) notEarlierThan
  r2         <- fromMaybe False            <$> traverse ( constrainToBefore  taskInfos i ) notLaterThan
  ( l3, r3 ) <- fromMaybe ( False, False ) <$> traverse ( constrainToOutside taskInfos i ) outside
  pure ( l1 || l2 || l3, r1 || r2 || r3 )

-------------------------------------------------------------------------------

class HandedTimeConstraint (h :: Handedness) where
  -- | Constraint associated to a handed time:
  --   - @Earliest t@ : @NotEarlierThan t@
  --   - @Latest t@ : @NotLaterThan t@.
  handedTimeConstraint :: Ord t => Endpoint (HandedTime h t) -> Constraint t
instance HandedTimeConstraint Earliest where
  handedTimeConstraint endpoint = NotEarlierThan endpoint
instance HandedTimeConstraint Latest   where
  handedTimeConstraint endpoint = NotLaterThan   endpoint

-- | Apply the constraint: task must begin after the specified time.
constrainToAfter
  :: ( Num t, Ord t, Bounded t
     , PrimMonad m, PrimState m ~ s
     )
  => MutableTaskInfos s task t
  -> Int
  -> Endpoint ( EarliestTime t )
  -> m Bool
constrainToAfter ( TaskInfos { taskAvails, rankingEST, rankingECT } ) taskNo t = do
  task@(Task { taskAvailability }) <- Boxed.MVector.unsafeRead taskAvails taskNo
  let
    newTaskAvailability = cutBefore t taskAvailability
    newTask = task { taskAvailability = newTaskAvailability }
  if est newTask > est task
  then do
    Boxed.MVector.unsafeWrite taskAvails taskNo newTask
    reorderAfterIncrease taskAvails rankingEST est taskNo
    reorderAfterIncrease taskAvails rankingECT ect taskNo
    pure True
  else
    pure False

-- | Apply the constraint: task must end before the specified time.
constrainToBefore
  :: ( Num t, Ord t, Bounded t
     , PrimMonad m, PrimState m ~ s
     )
  => MutableTaskInfos s task t
  -> Int
  -> Endpoint ( LatestTime t )
  -> m Bool
constrainToBefore ( TaskInfos { taskAvails, rankingLCT, rankingLST } ) taskNo t = do
  task@(Task { taskAvailability }) <- Boxed.MVector.unsafeRead taskAvails taskNo
  let
    newTaskAvailability = cutAfter t taskAvailability
    newTask = task { taskAvailability = newTaskAvailability }
  if lct newTask < lct task
  then do
    Boxed.MVector.unsafeWrite taskAvails taskNo newTask
    reorderAfterDecrease taskAvails rankingLCT lct taskNo
    reorderAfterDecrease taskAvails rankingLST lst taskNo
    pure True
  else
    pure False

-- | Remove intervals from the domain of availability of a task.
constrainToOutside
  :: ( Num t, Ord t, Bounded t
     , PrimMonad m, PrimState m ~ s
     )
  => MutableTaskInfos s task t
  -> Int
  -> Intervals t
  -> m ( Bool, Bool )
constrainToOutside ( TaskInfos { .. } ) taskNo ( Intervals ivalsToRemove ) = do
  task@(Task { taskAvailability }) <- Boxed.MVector.unsafeRead taskAvails taskNo
  let
    newAvailability = foldl' remove taskAvailability ivalsToRemove
    newTask = task { taskAvailability = newAvailability }
  Boxed.MVector.unsafeWrite taskAvails taskNo newTask
  l <-
    if est newTask > est task
    then do
      reorderAfterIncrease taskAvails rankingEST est taskNo
      reorderAfterIncrease taskAvails rankingECT ect taskNo
      pure True
    else
      pure False
  r <-
    if lct newTask < lct task
    then do
      reorderAfterDecrease taskAvails rankingLCT lct taskNo
      reorderAfterDecrease taskAvails rankingLST lst taskNo
      pure True
    else
      pure False
  pure ( l, r )

-- | Reduce the domain of availability of a task.
constrainToInside
  :: ( Num t, Ord t, Bounded t
     , PrimMonad m, PrimState m ~ s
     )
  => MutableTaskInfos s task t
  -> Int
  -> Intervals t
  -> m ( Bool, Bool )
constrainToInside ( TaskInfos { .. } ) taskNo shrunkDomain = do
  task@( Task { taskAvailability = oldDomain } ) <- Boxed.MVector.unsafeRead taskAvails taskNo
  let
    newTask = task { taskAvailability = oldDomain /\ shrunkDomain }
  Boxed.MVector.unsafeWrite taskAvails taskNo newTask
  l <-
    if est newTask > est task
    then do
      reorderAfterIncrease taskAvails rankingEST est taskNo
      reorderAfterIncrease taskAvails rankingECT ect taskNo
      pure True
    else
      pure False
  r <-
    if lct newTask < lct task
    then do
      reorderAfterDecrease taskAvails rankingLCT lct taskNo
      reorderAfterDecrease taskAvails rankingLST lst taskNo
      pure True
    else
      pure False
  pure ( l, r )
