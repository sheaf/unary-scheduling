{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

module Schedule.Constraint
  ( Constraint
    ( .. , NotEarlierThan, NotLaterThan, Outside, Inside )
  , HandedTimeConstraint(..)
  , Constraints(..)
  , Reason
  , tighten, tightenWithPrecedences, tightenMany
  , constrainToBefore, constrainToAfter
  , constrainToInside, constrainToOutside
  , applyConstraint, applyConstraints
  )
  where

-- base
import Data.Maybe
  ( fromMaybe )
import GHC.Generics
  ( Generic )

-- containers
import Data.IntMap.Strict
  ( IntMap )
import qualified Data.IntMap.Strict as IntMap
  ( empty, singleton, fromList, unionWith, traverseWithKey )
import Data.IntSet
  ( IntSet )

-- lens
import Control.Lens
  ( itraverse_ )

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
  ( unsafeRead )

-- unary-scheduling
import Data.Lattice
  ( Lattice
      ( (\/), (/\) )
  )
import Data.Vector.Ranking
  ( reorderAfterIncrease, reorderAfterDecrease )
import Schedule.Interval
  ( Endpoint(..), Intervals(..), Measurable(..)
  , cutBefore, cutAfter, remove
  )
import Schedule.Ordering
  ( addIncidentEdges )
import Schedule.Task
  ( Task(..), TaskInfos(..), MutableTaskInfos
  , est, lct, lst, ect
  )
import Schedule.Trail
  ( Trail
  , recordSetTask, rankSwapper, orderingCellWriter
  , RankKind(..), RankVec(..)
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
  { notEarlierThan :: !( Maybe ( Endpoint ( EarliestTime t ) ) )
  , notLaterThan   :: !( Maybe ( Endpoint ( LatestTime   t ) ) )
  , outside        :: !( Maybe ( Intervals t ) )
  , inside         :: !( Maybe ( Intervals t ) )
  }
  deriving stock ( Show, Generic )

pattern NotEarlierThan :: Measurable t => Endpoint ( EarliestTime t ) -> Constraint t
pattern NotEarlierThan endpoint <- ( notEarlierThan -> Just endpoint )
  where
    NotEarlierThan endpoint = mempty { notEarlierThan = Just endpoint }

pattern NotLaterThan :: Measurable t => Endpoint ( LatestTime t ) -> Constraint t
pattern NotLaterThan endpoint <- ( notLaterThan -> Just endpoint )
  where
    NotLaterThan endpoint = mempty { notLaterThan = Just endpoint }

pattern Outside :: Measurable t => Intervals t -> Constraint t
pattern Outside ivals <- ( outside -> Just ivals )
  where
    Outside ivals = mempty { outside = Just ivals }

pattern Inside :: Measurable t => Intervals t -> Constraint t
pattern Inside ivals <- ( inside -> Just ivals )
  where
    Inside ivals = mempty { inside = Just ivals }

pattern NoConstraint :: Constraint t
pattern NoConstraint = Constraint Nothing Nothing Nothing Nothing

instance Measurable t => Semigroup ( Constraint t ) where
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

instance Measurable t => Monoid ( Constraint t ) where
  mempty = NoConstraint

data Constraints t
  = Constraints
  { constraints    :: !( IntMap ( Constraint t ) )
  , justifications :: !Text
  , precedences    :: !( IntMap ( IntSet, IntSet ) )
  }
  deriving stock ( Show, Generic )

instance Measurable t => Semigroup ( Constraints t ) where
  ( Constraints cts1 logs1 precs1 ) <> ( Constraints cts2 logs2 precs2 ) =
    Constraints
      ( IntMap.unionWith (<>) cts1 cts2 )
      ( logs1 <> logs2 )
      ( IntMap.unionWith (<>) precs1 precs2 )
instance Measurable t => Monoid ( Constraints t ) where
  mempty = Constraints IntMap.empty mempty mempty

--------------------------------------------------------------------------------
-- Smart constructors for emitting constraints.

-- | A human-readable explanation for an inference.
--
-- TODO: turn into a structured clausal reason for lazy clause generation.
type Reason = Text

-- | Constrain a single task, recording the reason for the inference.
tighten :: Int -> Constraint t -> Reason -> Constraints t
tighten taskNb ct reason =
  Constraints
    { constraints    = IntMap.singleton taskNb ct
    , justifications = reason
    , precedences    = mempty
    }

-- | Like 'tighten', but also records precedence information
-- (the task's new predecessors and successors) for the precedence graph.
tightenWithPrecedences :: Int -> Constraint t -> ( IntSet, IntSet ) -> Reason -> Constraints t
tightenWithPrecedences taskNb ct precs reason =
  Constraints
    { constraints    = IntMap.singleton taskNb ct
    , justifications = reason
    , precedences    = IntMap.singleton taskNb precs
    }

-- | Constrain several tasks at once, with a shared reason and no precedence information.
tightenMany :: [ ( Int, Constraint t ) ] -> Reason -> Constraints t
tightenMany cts reason =
  Constraints
    { constraints    = IntMap.fromList cts
    , justifications = reason
    , precedences    = mempty
    }

--------------------------------------------------------------------------------

applyConstraints
  :: ( MonadReader ( MutableTaskInfos s task t ) m
     , PrimMonad m, PrimState m ~ s
     , Num t, Measurable t, Bounded t
     -- debugging
     , Show t, Show task
     )
  => Trail s task t
  -> Constraints t
  -> m ( IntMap ( Bool, Bool ) )
applyConstraints trail ( Constraints { constraints, precedences } ) = do
  taskInfos@( TaskInfos { orderings } ) <- ask
  itraverse_ ( uncurry . addIncidentEdges ( orderingCellWriter trail taskInfos ) orderings ) precedences
  IntMap.traverseWithKey ( applyConstraint trail taskInfos ) constraints

applyConstraint
  :: ( PrimMonad m, PrimState m ~ s
     , Num t, Measurable t, Bounded t
     -- debugging
     , Show t, Show task
     )
  => Trail s task t
  -> MutableTaskInfos s task t
  -> Int
  -> Constraint t
  -> m ( Bool, Bool )
applyConstraint _ _ _ NoConstraint = pure ( False, False )
applyConstraint trail taskInfos i ( Constraint { .. } ) = do
  -- apply 'constrain to inside' first (useful in case restriction is not checked)
  ( l1, r1 ) <- fromMaybe ( False, False ) <$> traverse ( constrainToInside  trail taskInfos i ) inside
  l2         <- fromMaybe False            <$> traverse ( constrainToAfter   trail taskInfos i ) notEarlierThan
  r2         <- fromMaybe False            <$> traverse ( constrainToBefore  trail taskInfos i ) notLaterThan
  ( l3, r3 ) <- fromMaybe ( False, False ) <$> traverse ( constrainToOutside trail taskInfos i ) outside
  pure ( l1 || l2 || l3, r1 || r2 || r3 )

-------------------------------------------------------------------------------

class HandedTimeConstraint (h :: Handedness) where
  -- | Constraint associated to a handed time:
  --   - @Earliest t@ : @NotEarlierThan t@
  --   - @Latest t@ : @NotLaterThan t@.
  handedTimeConstraint :: Measurable t => Endpoint (HandedTime h t) -> Constraint t
instance HandedTimeConstraint Earliest where
  handedTimeConstraint endpoint = NotEarlierThan endpoint
instance HandedTimeConstraint Latest   where
  handedTimeConstraint endpoint = NotLaterThan   endpoint

-- | Apply the constraint: task must begin after the specified time.
constrainToAfter
  :: ( Num t, Ord t, Bounded t
     , PrimMonad m, PrimState m ~ s
     )
  => Trail s task t
  -> MutableTaskInfos s task t
  -> Int
  -> Endpoint ( EarliestTime t )
  -> m Bool
constrainToAfter trail tis@( TaskInfos { taskAvails, rankingEST, rankingECT } ) taskNo t = do
  task@(Task { taskAvailability }) <- Boxed.MVector.unsafeRead taskAvails taskNo
  let
    newTaskAvailability = cutBefore t taskAvailability
    newTask = task { taskAvailability = newTaskAvailability }
  if est newTask > est task
  then do
    recordSetTask trail tis taskNo newTask
    reorderAfterIncrease ( rankSwapper trail tis ( Ordered ByEST ) ) ( rankSwapper trail tis ( Ranks ByEST ) ) taskAvails rankingEST est taskNo
    reorderAfterIncrease ( rankSwapper trail tis ( Ordered ByECT ) ) ( rankSwapper trail tis ( Ranks ByECT ) ) taskAvails rankingECT ect taskNo
    pure True
  else
    pure False

-- | Apply the constraint: task must end before the specified time.
constrainToBefore
  :: ( Num t, Ord t, Bounded t
     , PrimMonad m, PrimState m ~ s
     )
  => Trail s task t
  -> MutableTaskInfos s task t
  -> Int
  -> Endpoint ( LatestTime t )
  -> m Bool
constrainToBefore trail tis@( TaskInfos { taskAvails, rankingLCT, rankingLST } ) taskNo t = do
  task@(Task { taskAvailability }) <- Boxed.MVector.unsafeRead taskAvails taskNo
  let
    newTaskAvailability = cutAfter t taskAvailability
    newTask = task { taskAvailability = newTaskAvailability }
  if lct newTask < lct task
  then do
    recordSetTask trail tis taskNo newTask
    reorderAfterDecrease ( rankSwapper trail tis ( Ordered ByLCT ) ) ( rankSwapper trail tis ( Ranks ByLCT ) ) taskAvails rankingLCT lct taskNo
    reorderAfterDecrease ( rankSwapper trail tis ( Ordered ByLST ) ) ( rankSwapper trail tis ( Ranks ByLST ) ) taskAvails rankingLST lst taskNo
    pure True
  else
    pure False

-- | Remove intervals from the domain of availability of a task.
constrainToOutside
  :: ( Num t, Ord t, Bounded t
     , PrimMonad m, PrimState m ~ s
     )
  => Trail s task t
  -> MutableTaskInfos s task t
  -> Int
  -> Intervals t
  -> m ( Bool, Bool )
constrainToOutside trail tis@( TaskInfos { .. } ) taskNo ( Intervals ivalsToRemove ) = do
  task@(Task { taskAvailability }) <- Boxed.MVector.unsafeRead taskAvails taskNo
  let
    newAvailability = foldl' remove taskAvailability ivalsToRemove
    newTask = task { taskAvailability = newAvailability }
  recordSetTask trail tis taskNo newTask
  l <-
    if est newTask > est task
    then do
      reorderAfterIncrease ( rankSwapper trail tis ( Ordered ByEST ) ) ( rankSwapper trail tis ( Ranks ByEST ) ) taskAvails rankingEST est taskNo
      reorderAfterIncrease ( rankSwapper trail tis ( Ordered ByECT ) ) ( rankSwapper trail tis ( Ranks ByECT ) ) taskAvails rankingECT ect taskNo
      pure True
    else
      pure False
  r <-
    if lct newTask < lct task
    then do
      reorderAfterDecrease ( rankSwapper trail tis ( Ordered ByLCT ) ) ( rankSwapper trail tis ( Ranks ByLCT ) ) taskAvails rankingLCT lct taskNo
      reorderAfterDecrease ( rankSwapper trail tis ( Ordered ByLST ) ) ( rankSwapper trail tis ( Ranks ByLST ) ) taskAvails rankingLST lst taskNo
      pure True
    else
      pure False
  pure ( l, r )

-- | Reduce the domain of availability of a task.
constrainToInside
  :: ( Num t, Measurable t, Bounded t
     , PrimMonad m, PrimState m ~ s
     )
  => Trail s task t
  -> MutableTaskInfos s task t
  -> Int
  -> Intervals t
  -> m ( Bool, Bool )
constrainToInside trail tis@( TaskInfos { .. } ) taskNo shrunkDomain = do
  task@( Task { taskAvailability = oldDomain } ) <- Boxed.MVector.unsafeRead taskAvails taskNo
  let
    newTask = task { taskAvailability = oldDomain /\ shrunkDomain }
  recordSetTask trail tis taskNo newTask
  l <-
    if est newTask > est task
    then do
      reorderAfterIncrease ( rankSwapper trail tis ( Ordered ByEST ) ) ( rankSwapper trail tis ( Ranks ByEST ) ) taskAvails rankingEST est taskNo
      reorderAfterIncrease ( rankSwapper trail tis ( Ordered ByECT ) ) ( rankSwapper trail tis ( Ranks ByECT ) ) taskAvails rankingECT ect taskNo
      pure True
    else
      pure False
  r <-
    if lct newTask < lct task
    then do
      reorderAfterDecrease ( rankSwapper trail tis ( Ordered ByLCT ) ) ( rankSwapper trail tis ( Ranks ByLCT ) ) taskAvails rankingLCT lct taskNo
      reorderAfterDecrease ( rankSwapper trail tis ( Ordered ByLST ) ) ( rankSwapper trail tis ( Ranks ByLST ) ) taskAvails rankingLST lst taskNo
      pure True
    else
      pure False
  pure ( l, r )
