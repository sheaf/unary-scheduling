{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

module Schedule.Constraint
  ( Constraint
    ( .. , NotEarlierThan, NotLaterThan, Outside, Inside )
  , HandedTimeConstraint(..)
  , Constraints(..)
  , Infeasible(..), renderInfeasible
  , BoundMove(..), boundMoved
  , Applied(..)
  , Reason
  , tighten, tightenWithPrecedences, tightenBecause, tightenMany
  , constrainToBefore, constrainToAfter
  , constrainToInside, constrainToOutside
  , applyConstraint, applyConstraints
  )
  where

-- base
import Control.Monad
  ( when )
import Data.Maybe
  ( fromMaybe, isJust )
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
import Control.Monad.Except
  ( MonadError ( throwError ) )
import Control.Monad.Reader
  ( MonadReader ( ask ) )

-- primitive
import Control.Monad.Primitive
  ( PrimMonad(PrimState) )

-- text
import Data.Text
  ( Text )
import qualified Data.Text as Text
  ( pack )

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
  ( addIncidentEdges, CycleInfo )
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
  , -- | Per task precedences: the new predecessors and successors to add
    -- to the ordering matrix (so the precedence is reflected in the precedence graph).
    precedences    :: !( IntMap ( IntSet, IntSet ) )
  , -- | Per task, the responsible task subset for a bound tightening: the
    -- @(tasks justifying a raised earliest start, tasks justifying a lowered
    -- latest completion)@.
    boundReasons   :: !( IntMap ( IntSet, IntSet ) )
  }
  deriving stock ( Show, Generic )

instance Measurable t => Semigroup ( Constraints t ) where
  ( Constraints cts1 logs1 precs1 brs1 ) <> ( Constraints cts2 logs2 precs2 brs2 ) =
    Constraints
      ( IntMap.unionWith (<>) cts1 cts2 )
      ( logs1 <> logs2 )
      ( IntMap.unionWith (<>) precs1 precs2 )
      ( IntMap.unionWith (<>) brs1  brs2 )
instance Measurable t => Monoid ( Constraints t ) where
  mempty = Constraints IntMap.empty mempty mempty mempty

-- | A reason a scheduling instance was found infeasible during propagation.
data Infeasible t
  = -- | @EmptyDomain i lo hi msg@: task @i@'s window was emptied by bound
    -- tightening. @lo@ is the earliest start and @hi@ the latest completion
    -- the constraint enforced; together they leave no schedulable slot. The
    -- LCG theory cites @i@'s bound atoms at these thresholds.
    EmptyDomain !Int !( Endpoint ( EarliestTime t ) ) !( Endpoint ( LatestTime t ) ) !Text
  | -- | @Overloaded culprit msg@: the @culprit@ subset of tasks cannot all fit
    -- on the unary resource between their collective earliest start and latest
    -- completion.
    Overloaded !IntSet !Text
  | -- | @CycleDetected info msg@: adding a precedence created a cycle in the
    -- ordering matrix.
    CycleDetected !CycleInfo !Text

deriving stock instance Show t => Show ( Infeasible t )

-- | The human-readable rendering carried by an 'Infeasible'.
renderInfeasible :: Infeasible t -> Text
renderInfeasible = \ case
  EmptyDomain   _ _ _ msg -> msg
  Overloaded    _ msg     -> msg
  CycleDetected _ msg     -> msg

-- | How a task's earliest start \/ latest completion moved when a constraint
-- was applied.
--
-- The distinction matters for the LCG bound atoms: an /exact/ move lands the
-- bound exactly on the cut endpoint, so the propagator's antecedents entail it
-- precisely and the bound literal can carry a tight, local reason. A /jumped/
-- move skips over a gap to the next available slot; the antecedents only entail
-- the cut endpoint, with the jump justified by the availability structure (a
-- ground fact for an /instance/ gap, but not for a propagator-carved one — see
-- 'wasCarved').
data BoundMove
  = -- | The bound did not change.
    Unmoved
  | -- | The bound moved exactly onto the cut endpoint.
    MovedExact
  | -- | The bound jumped past the cut endpoint to the next available slot.
    MovedJumped
  deriving stock ( Eq, Show )

-- | Whether the bound moved at all.
boundMoved :: BoundMove -> Bool
boundMoved Unmoved = False
boundMoved _       = True

-- | Combines two moves on the /same/ bound: 'Unmoved' is the identity; two
-- exact moves stay exact (two clean cuts to ever-tighter endpoints); any jump
-- makes the combination a jump (conservative).
instance Semigroup BoundMove where
  Unmoved     <> y           = y
  x           <> Unmoved     = x
  MovedExact  <> MovedExact  = MovedExact
  _           <> _           = MovedJumped

instance Monoid BoundMove where
  mempty = Unmoved

-- | The result of applying a task's accumulated constraint: how each bound
-- moved, and whether the task was /carved/ — i.e. an 'Inside'\/'Outside'
-- tightening was applied, which can introduce interior gaps that are not part
-- of the ground instance structure. A later cut that jumps over such a gap is
-- not soundly explained by the energetic antecedents alone, so the LCG theory
-- falls back to a coarse reason for jumped moves on carved tasks.
data Applied = Applied
  { estMove   :: !BoundMove
  , lctMove   :: !BoundMove
  , wasCarved :: !Bool
  }
  deriving stock Show

--------------------------------------------------------------------------------
-- Smart constructors for emitting constraints.

-- | A human-readable explanation for an inference.
--
-- TODO: turn into a structured clausal reason for lazy clause generation.
type Reason = Text

-- | Constrain a single task, recording the reason for the inference.
--
-- Records no responsible subset, so the LCG theory falls back to a coarse
-- reason for the resulting bound literal. Use 'tightenBecause' (no new edges)
-- or 'tightenWithPrecedences' (new edges) when the subset is known.
tighten :: Int -> Constraint t -> Reason -> Constraints t
tighten taskNb ct reason =
  Constraints
    { constraints    = IntMap.singleton taskNb ct
    , justifications = reason
    , precedences    = mempty
    , boundReasons   = mempty
    }

-- | Like 'tighten', but also adds the task's new predecessors and successors
-- to the precedence graph (and records them as the bound's responsible
-- subset).
tightenWithPrecedences :: Int -> Constraint t -> ( IntSet, IntSet ) -> Reason -> Constraints t
tightenWithPrecedences taskNb ct precs reason =
  Constraints
    { constraints    = IntMap.singleton taskNb ct
    , justifications = reason
    , precedences    = IntMap.singleton taskNb precs
    , boundReasons   = IntMap.singleton taskNb precs
    }

-- | Like 'tighten', but records the responsible task subset for the bound
-- tightening, /without/ adding any precedence edge to the matrix.
--
-- Used by propagators whose inference rests on a subset of tasks that does not
-- correspond to fresh precedence edges (the precedence-matrix and
-- not-first\/not-last propagators).
tightenBecause :: Int -> Constraint t -> ( IntSet, IntSet ) -> Reason -> Constraints t
tightenBecause taskNb ct why reason =
  Constraints
    { constraints    = IntMap.singleton taskNb ct
    , justifications = reason
    , precedences    = mempty
    , boundReasons   = IntMap.singleton taskNb why
    }

-- | Constrain several tasks at once, with a shared reason and no precedence information.
tightenMany :: [ ( Int, Constraint t ) ] -> Reason -> Constraints t
tightenMany cts reason =
  Constraints
    { constraints    = IntMap.fromList cts
    , justifications = reason
    , precedences    = mempty
    , boundReasons   = mempty
    }

--------------------------------------------------------------------------------

applyConstraints
  :: ( MonadReader ( MutableTaskInfos s task t ) m
     , MonadError ( Infeasible t ) m
     , PrimMonad m, PrimState m ~ s
     , Num t, Measurable t, Bounded t
     -- debugging
     , Show t, Show task
     )
  => Trail s task t
  -> Constraints t
  -> m ( IntMap Applied )
applyConstraints trail ( Constraints { constraints, precedences } ) = do
  taskInfos@( TaskInfos { orderings } ) <- ask
  itraverse_ ( uncurry . addIncidentEdges ( orderingCellWriter trail taskInfos ) orderings ) precedences
  IntMap.traverseWithKey ( applyConstraint trail taskInfos ) constraints

applyConstraint
  :: ( MonadError ( Infeasible t ) m
     , PrimMonad m, PrimState m ~ s
     , Num t, Measurable t, Bounded t
     -- debugging
     , Show t, Show task
     )
  => Trail s task t
  -> MutableTaskInfos s task t
  -> Int
  -> Constraint t
  -> m Applied
applyConstraint _ _ _ NoConstraint = pure ( Applied Unmoved Unmoved False )
applyConstraint trail taskInfos@( TaskInfos { taskAvails } ) i ( Constraint { .. } ) = do
  -- The pre-tightening bounds, so an emptied window can report the exact
  -- earliest-start \/ latest-completion the constraint enforced.
  task0 <- Boxed.MVector.unsafeRead taskAvails i
  let est0 = est task0
      lct0 = lct task0
  -- apply 'constrain to inside' first (useful in case restriction is not checked)
  ( l1, r1 ) <- fromMaybe ( False, False ) <$> traverse ( constrainToInside  trail taskInfos i ) inside
  l2         <- fromMaybe Unmoved          <$> traverse ( constrainToAfter   trail taskInfos i ) notEarlierThan
  r2         <- fromMaybe Unmoved          <$> traverse ( constrainToBefore  trail taskInfos i ) notLaterThan
  ( l3, r3 ) <- fromMaybe ( False, False ) <$> traverse ( constrainToOutside trail taskInfos i ) outside
  -- If tightening reduces a task's availability to the empty set, report the
  -- infeasibility immediately instead of letting other propagators spin on
  -- empty domains. Report the enforced earliest-start (@lo@) and
  -- latest-completion (@hi@) bounds, which together leave no slot.
  Task { taskAvailability } <- Boxed.MVector.unsafeRead taskAvails i
  when ( null ( intervals taskAvailability ) ) $
    let lo = maybe est0 ( /\ est0 ) notEarlierThan
        hi = maybe lct0 ( /\ lct0 ) notLaterThan
    in throwError $ EmptyDomain i lo hi $
      "Task #" <> Text.pack ( show i ) <>
      " can no longer be scheduled: its availability has been reduced to the empty set.\n"
  -- 'Inside'\/'Outside' moves are interval surgery (potential gap carving), so
  -- they count as jumps; the lower\/upper cuts carry their own exact\/jumped
  -- status. A task is /carved/ iff an 'Inside'\/'Outside' tightening applied.
  pure Applied
    { estMove   = jumpIf l1 <> l2 <> jumpIf l3
    , lctMove   = jumpIf r1 <> r2 <> jumpIf r3
    , wasCarved = isJust inside || isJust outside
    }
  where
    jumpIf :: Bool -> BoundMove
    jumpIf True  = MovedJumped
    jumpIf False = Unmoved

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
  :: ( Num t, Measurable t, Bounded t
     , PrimMonad m, PrimState m ~ s
     )
  => Trail s task t
  -> MutableTaskInfos s task t
  -> Int
  -> Endpoint ( EarliestTime t )
  -> m BoundMove
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
    -- Exact iff the new earliest start lands on the cut endpoint; otherwise the
    -- cut fell in a gap and the start jumped to the next available slot.
    pure ( if est newTask == canonicalEarliest t then MovedExact else MovedJumped )
  else
    pure Unmoved

-- | Apply the constraint: task must end before the specified time.
constrainToBefore
  :: ( Num t, Measurable t, Bounded t
     , PrimMonad m, PrimState m ~ s
     )
  => Trail s task t
  -> MutableTaskInfos s task t
  -> Int
  -> Endpoint ( LatestTime t )
  -> m BoundMove
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
    -- Exact iff the new latest completion lands on the cut endpoint.
    pure ( if lct newTask == canonicalLatest t then MovedExact else MovedJumped )
  else
    pure Unmoved

-- | Remove intervals from the domain of availability of a task.
constrainToOutside
  :: ( Num t, Measurable t, Bounded t
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
