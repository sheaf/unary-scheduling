{-# LANGUAGE ScopedTypeVariables #-}

module Schedule.Trail
  ( -- * Mutation actions
    Action(..)
  , RankKind(..), RankVec(..)
  , runAction
    -- * Trail
  , Trail
  , newTrail
  , currentMark
  , undoTo
    -- * Trailed mutators
  , recordSetTask
  , rankSwapper
  , orderingCellWriter
  )
  where

-- base
import Control.Monad
  ( when )

-- primitive
import Control.Monad.Primitive
  ( PrimMonad(PrimState) )
import Data.Primitive.MutVar
  ( MutVar, newMutVar, readMutVar, writeMutVar, modifyMutVar' )
import Data.Primitive.PrimVar
  ( PrimVar, newPrimVar, readPrimVar, writePrimVar, modifyPrimVar )

-- vector
import qualified Data.Vector.Mutable as Boxed.MVector
  ( unsafeRead, unsafeWrite )
import qualified Data.Vector.Unboxed.Mutable as Unboxed.MVector
  ( unsafeRead, unsafeWrite, unsafeSwap )

-- unary-scheduling
import Data.Vector.Ranking
  ( Ranking(..) )
import Schedule.Ordering
  ( Order, OrderingMatrix(..) )
import Schedule.Task
  ( Task, TaskInfos(..), MutableTaskInfos )

-------------------------------------------------------------------------------
-- Mutation actions.

-- | Which of the four task rankings an action refers to.
data RankKind = ByEST | ByLCT | ByLST | ByECT
  deriving stock ( Eq, Show )

-- | A single physical permutation vector inside a ranking.
--
-- Each 'Ranking' stores two mutually-inverse permutations, @ordered@ and
-- @ranks@; a reordering step swaps two entries in each.
data RankVec
  = Ordered !RankKind
  | Ranks   !RankKind
  deriving stock ( Eq, Show )

-- | A primitive, reversible mutation of the shared mutable state.
--
-- An 'Action' describes the /forward/ intent. The interpreter 'runAction'
-- performs it and, by reading the previous contents first, returns the 'Action'
-- that undoes it.
data Action task t
  = -- | Overwrite @taskAvails[i]@ with the given task. Inverse restores the
    -- previous task value.
    SetTask  !Int !( Task task t )
  | -- | Swap two positions in a ranking permutation vector. Self-inverse.
    SwapRank !RankVec !Int !Int
  | -- | Overwrite the ordering matrix at the given flat (upper-triangular) cell
    -- index. Inverse restores the previous 'Order'.
    SetOrder !Int !Order

-- | Select the ranking referred to by a 'RankKind'.
rankingOf :: RankKind -> TaskInfos bvec uvec task t -> Ranking ( uvec Int )
rankingOf ByEST = rankingEST
rankingOf ByLCT = rankingLCT
rankingOf ByLST = rankingLST
rankingOf ByECT = rankingECT

-------------------------------------------------------------------------------

-- | Interpreter for 'Action'. Returns the undo action.
runAction
  :: forall m s task t
  .  ( PrimMonad m, PrimState m ~ s )
  => MutableTaskInfos s task t
  -> Action task t
  -> m ( Action task t )
runAction tis = \case
  SetTask i new -> do
    let v = taskAvails tis
    old <- Boxed.MVector.unsafeRead v i
    Boxed.MVector.unsafeWrite v i new
    pure ( SetTask i old )
  SwapRank rv p q -> do
    let v = case rv of
              Ordered k -> ordered ( rankingOf k tis )
              Ranks   k -> ranks   ( rankingOf k tis )
    Unboxed.MVector.unsafeSwap v p q
    -- Swapping the same two positions again restores the original order.
    pure ( SwapRank rv p q )
  SetOrder idx new -> do
    let v = orderingMatrix ( orderings tis )
    old <- Unboxed.MVector.unsafeRead v idx
    Unboxed.MVector.unsafeWrite v idx new
    pure ( SetOrder idx old )

-------------------------------------------------------------------------------
-- Trail.

-- | A trail of inverse mutations, supporting in-place undo to an earlier mark.
data Trail s task t
  = Trail
  { trailUndos :: !( MutVar s [ Action task t ] )
     -- ^ Inverse actions (most recent first).
  , trailDepth :: !( PrimVar s Int )
     -- ^ Number of recorded mutations.
  }

-- | Create a fresh, empty trail.
newTrail :: PrimMonad m => m ( Trail ( PrimState m ) task t )
newTrail = Trail <$> newMutVar [] <*> newPrimVar 0

-- | The current trail depth.
currentMark :: PrimMonad m => Trail ( PrimState m ) task t -> m Int
currentMark = readPrimVar . trailDepth

-- | Apply an action to the shared state and record its inverse for later undo.
record
  :: ( PrimMonad m, PrimState m ~ s )
  => Trail s task t
  -> MutableTaskInfos s task t
  -> Action task t
  -> m ()
record trail tis act = do
  inv <- runAction tis act
  modifyMutVar' ( trailUndos trail ) ( inv : )
  modifyPrimVar ( trailDepth trail ) ( + 1 )

-- | Undo recorded mutations until the trail is back at the given mark.
undoTo
  :: ( PrimMonad m, PrimState m ~ s )
  => Trail s task t
  -> MutableTaskInfos s task t
  -> Int -- ^ target depth
  -> m ()
undoTo trail tis target = go
  where
    go = do
      d <- readPrimVar ( trailDepth trail )
      when ( d > target ) do
        us <- readMutVar ( trailUndos trail )
        case us of
          [] ->
            error "nothing left to undo"
          ( u : rest ) -> do
            _ <- runAction tis u
            writeMutVar ( trailUndos trail ) rest
            writePrimVar ( trailDepth trail ) ( d - 1 )
            go

-------------------------------------------------------------------------------
-- Typed, trailed mutators.

-- | Trailed overwrite of a task's availability cell.
recordSetTask
  :: ( PrimMonad m, PrimState m ~ s )
  => Trail s task t -> MutableTaskInfos s task t -> Int -> Task task t -> m ()
recordSetTask trail tis i task = record trail tis ( SetTask i task )

-- | A trailed swap on a chosen ranking permutation vector.
rankSwapper
  :: ( PrimMonad m, PrimState m ~ s )
  => Trail s task t -> MutableTaskInfos s task t -> RankVec -> Int -> Int -> m ()
rankSwapper trail tis rv p q = record trail tis ( SwapRank rv p q )

-- | A trailed writer for a single ordering-matrix cell (by flat index).
orderingCellWriter
  :: ( PrimMonad m, PrimState m ~ s )
  => Trail s task t -> MutableTaskInfos s task t -> Int -> Order -> m ()
orderingCellWriter trail tis idx ord = record trail tis ( SetOrder idx ord )
