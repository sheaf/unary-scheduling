{-# LANGUAGE MagicHash            #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE UnboxedTuples        #-}

-- | An activity-ordered priority queue over propositional variables.
module SAT.VarOrder
  ( -- * Variable ordering
    VarOrder
  , newVarOrder
  , numVars
  , insertVar
  , insertAuxVar
    -- * Activity
  , bumpActivity
  , decayActivities
  , readActivity
    -- * Decision support
  , extractMaxBy
  , reinsertVar
  )
  where

-- base
import Control.Monad
  ( when )
import Data.Bits
  ( shiftL, shiftR )

-- primitive
import Control.Monad.Primitive
  ( PrimMonad(PrimState) )
import Data.Primitive
  ( Prim(..) )
import Data.Primitive.MutVar
  ( MutVar, newMutVar, readMutVar, modifyMutVar' )

-- memory-arena
import Memory.Growable
  ( Growable )
import qualified Memory.Growable as Growable

-- vector
import qualified Data.Vector.Primitive.Mutable as Primitive
  ( MVector )
import qualified Data.Vector.Unboxed.Mutable as Unboxed
  ( MVector )

-- unary-scheduling
import SAT.Base
  ( Var(..), varIndex )

-------------------------------------------------------------------------------
-- Heap positions.

-- | The position of a variable in the activity heap.
data HeapPos
  = -- | The variable is not currently in the heap.
    --
    -- This is the state of a variable between being popped for a decision
    -- and 'reinsertVar' putting it back on backjump.
    NotInHeap
  | -- | The variable lives at the given zero-based index in the heap.
    InHeap !Int

-- | Packed into a single 'Int'.
instance Prim HeapPos where
  sizeOf# _    = sizeOf#    ( undefined :: Int )
  alignment# _ = alignment# ( undefined :: Int )

  indexByteArray# arr# i# = decodeHeapPos ( indexByteArray# arr# i# )
  readByteArray#  arr# i# s0 =
    case readByteArray# arr# i# s0 of
      (# s1, w #) -> (# s1, decodeHeapPos ( w :: Int ) #)
  writeByteArray# arr# i# hp s0 =
    writeByteArray# arr# i# ( encodeHeapPos hp ) s0

  indexOffAddr# addr# i# = decodeHeapPos ( indexOffAddr# addr# i# )
  readOffAddr#  addr# i# s0 =
    case readOffAddr# addr# i# s0 of
      (# s1, w #) -> (# s1, decodeHeapPos ( w :: Int ) #)
  writeOffAddr# addr# i# hp s0 =
    writeOffAddr# addr# i# ( encodeHeapPos hp ) s0

-- | Internal packing for the 'Prim' 'HeapPos' instance.
encodeHeapPos :: HeapPos -> Int
encodeHeapPos NotInHeap    = -1
encodeHeapPos ( InHeap i ) = i

-- | Inverse of 'encodeHeapPos'.
decodeHeapPos :: Int -> HeapPos
decodeHeapPos i
  | i < 0     = NotInHeap
  | otherwise = InHeap i

-------------------------------------------------------------------------------
-- VarOrder.

-- | An activity-ordered variable priority queue.
data VarOrder s = VarOrder
  { -- | The heap proper: a contiguous packed array of in-heap 'Var's.
    --
    -- Position @0@ is the root (highest-activity variable).
    heap     :: !( Growable Primitive.MVector s Var )
  , -- | Each variable's position in 'heap', or 'NotInHeap' if it has been
    -- popped. Indexed by 'varIndex'.
    heapPos  :: !( Growable Primitive.MVector s HeapPos )
  , -- | Per-variable VSIDS activity scores. Indexed by 'varIndex'.
    activity :: !( Growable Unboxed.MVector s Double )
  , -- | Current activity-bump increment. Decay is implemented by
    -- /inflating/ this value rather than scaling every activity, so most
    -- decays are O(1); a global rescale only happens when an individual
    -- activity would otherwise overflow.
    varInc   :: !( MutVar s Double )
  , -- | Activity decay factor in @(0, 1]@.
    varDecay :: !Double
  }

-- | Allocate an empty 'VarOrder' with the given decay factor.
newVarOrder
  :: PrimMonad m
  => Double  -- ^ activity-decay factor in @(0, 1]@
  -> m ( VarOrder ( PrimState m ) )
newVarOrder decay = do
  hp  <- Growable.new 16
  hps <- Growable.new 16
  act <- Growable.new 16
  vi  <- newMutVar 1
  pure VarOrder
    { heap     = hp
    , heapPos  = hps
    , activity = act
    , varInc   = vi
    , varDecay = decay
    }

-- | Number of variables registered with this 'VarOrder'.
numVars :: PrimMonad m => VarOrder ( PrimState m ) -> m Int
numVars vo = Growable.length ( activity vo )

-- | Allocate a fresh variable with zero activity and append it at the
-- bottom of the heap.
--
-- The newly-minted 'Var' index equals the previous 'numVars'.
insertVar :: PrimMonad m => VarOrder ( PrimState m ) -> m Var
insertVar vo = do
  n <- numVars vo
  let v = Var n
  Growable.push ( activity vo ) 0
  i <- Growable.length ( heap vo )
  Growable.push ( heap vo )    v
  Growable.push ( heapPos vo ) ( InHeap i )
  -- Activity is 0, equal to or below every existing activity, so the new
  -- entry already sits at a valid max-heap leaf; no percolate-up needed.
  pure v

-- | Allocate a fresh variable that is /not/ placed in the activity heap.
--
-- Used for auxiliary variables the search must never branch on (e.g.
-- theory-only bound atoms).
insertAuxVar :: PrimMonad m => VarOrder ( PrimState m ) -> m Var
insertAuxVar vo = do
  n <- numVars vo
  let v = Var n
  Growable.push ( activity vo ) 0
  -- No heap slot: the variable starts (and stays) 'NotInHeap'.
  Growable.push ( heapPos vo ) NotInHeap
  pure v

-- | Read the current VSIDS activity of a variable.
readActivity :: PrimMonad m => VarOrder ( PrimState m ) -> Var -> m Double
readActivity vo v = Growable.read ( activity vo ) ( varIndex v )

-- | Decay all activities by 'varDecay', amortised O(1).
decayActivities :: PrimMonad m => VarOrder ( PrimState m ) -> m ()
decayActivities vo = modifyMutVar' ( varInc vo ) ( / varDecay vo )

-- | Add the current bump increment to a variable's activity and
-- re-percolate it up the heap if it is currently a member.
bumpActivity :: PrimMonad m => VarOrder ( PrimState m ) -> Var -> m ()
bumpActivity vo v = do
  inc <- readMutVar ( varInc vo )
  let vi = varIndex v
  Growable.modify ( activity vo ) ( + inc ) vi
  a <- Growable.read ( activity vo ) vi
  -- Rescale before any single activity threatens to overflow.
  when ( a > 1e100 ) ( rescaleActivities vo )
  hp <- Growable.read ( heapPos vo ) vi
  case hp of
    NotInHeap -> pure ()
    InHeap i  -> percolateUp vo i

-- | Insert a variable that is not currently in the heap, placing it at
-- its activity-determined position.
--
-- Idempotent: a no-op when the variable is already in the heap.
reinsertVar :: PrimMonad m => VarOrder ( PrimState m ) -> Var -> m ()
reinsertVar vo v = do
  let vi = varIndex v
  hp <- Growable.read ( heapPos vo ) vi
  case hp of
    InHeap _  -> pure ()
    NotInHeap -> do
      i <- Growable.length ( heap vo )
      Growable.push  ( heap vo )    v
      Growable.write ( heapPos vo ) vi ( InHeap i )
      percolateUp vo i

-- | Remove and return the highest-activity variable for which the
-- predicate holds, or 'Nothing' if no in-heap variable satisfies it.
--
-- Variables for which the predicate returns 'False' are also removed
-- from the heap and become 'NotInHeap'; use 'reinsertVar' to make
-- them eligible again.
extractMaxBy
  :: forall m
  .  PrimMonad m
  => VarOrder ( PrimState m )
  -> ( Var -> m Bool )
  -> m ( Maybe Var )
extractMaxBy vo accept = go
  where
    go :: m ( Maybe Var )
    go = do
      mb <- popRoot vo
      case mb of
        Nothing -> pure Nothing
        Just v  -> do
          ok <- accept v
          if ok
          then pure ( Just v )
          else go

-- | Remove and return the variable at the root of the heap, leaving it
-- in the 'NotInHeap' state. 'Nothing' iff the heap is empty.
popRoot :: PrimMonad m => VarOrder ( PrimState m ) -> m ( Maybe Var )
popRoot vo = do
  n <- Growable.length ( heap vo )
  if n == 0
  then pure Nothing
  else do
    root <- Growable.read ( heap vo ) 0
    Growable.write ( heapPos vo ) ( varIndex root ) NotInHeap
    let n' = n - 1
    if n' == 0
    then do
      Growable.truncate ( heap vo ) 0
      pure ( Just root )
    else do
      lastV <- Growable.read ( heap vo ) n'
      Growable.write ( heap vo )    0  lastV
      Growable.write ( heapPos vo ) ( varIndex lastV ) ( InHeap 0 )
      Growable.truncate ( heap vo ) n'
      percolateDown vo 0
      pure ( Just root )

-------------------------------------------------------------------------------
-- Heap mechanics (internal)

-- | Rescale every activity (and the bump increment) by @1e-100@ to avoid
-- floating-point overflow. The relative order is preserved exactly, so
-- the heap invariant survives without any swaps.
rescaleActivities :: PrimMonad m => VarOrder ( PrimState m ) -> m ()
rescaleActivities vo = do
  n <- Growable.length ( activity vo )
  let go !i
        | i >= n    = pure ()
        | otherwise = Growable.modify ( activity vo ) ( * 1e-100 ) i *> go ( i + 1 )
  go 0
  modifyMutVar' ( varInc vo ) ( * 1e-100 )

-- | Heap-array index of the parent of position @i@.
parentIx :: Int -> Int
parentIx i = ( i - 1 ) `shiftR` 1

-- | Heap-array index of the left child of position @i@.
leftIx :: Int -> Int
leftIx i = ( i `shiftL` 1 ) + 1

-- | Heap-array index of the right child of position @i@.
rightIx :: Int -> Int
rightIx i = ( i `shiftL` 1 ) + 2

-- | Activity of the variable at the given heap index.
activityAt :: PrimMonad m => VarOrder ( PrimState m ) -> Int -> m Double
activityAt vo i = do
  v <- Growable.read ( heap vo ) i
  Growable.read ( activity vo ) ( varIndex v )

-- | Swap the heap entries at positions @i@ and @j@, keeping each
-- variable's stored 'HeapPos' in sync.
swapHeap :: PrimMonad m => VarOrder ( PrimState m ) -> Int -> Int -> m ()
swapHeap vo i j = do
  vi <- Growable.read ( heap vo ) i
  vj <- Growable.read ( heap vo ) j
  Growable.write ( heap vo )    i  vj
  Growable.write ( heap vo )    j  vi
  Growable.write ( heapPos vo ) ( varIndex vi ) ( InHeap j )
  Growable.write ( heapPos vo ) ( varIndex vj ) ( InHeap i )

-- | Move the entry at position @i@ upwards until its activity does not
-- exceed its parent's.
percolateUp :: PrimMonad m => VarOrder ( PrimState m ) -> Int -> m ()
percolateUp vo = go
  where
    go !i
      | i == 0    = pure ()
      | otherwise = do
          let p = parentIx i
          a_i <- activityAt vo i
          a_p <- activityAt vo p
          if a_i > a_p
          then swapHeap vo i p *> go p
          else pure ()

-- | Move the entry at position @i@ downwards until both its children's
-- activities are no greater than its own.
percolateDown :: PrimMonad m => VarOrder ( PrimState m ) -> Int -> m ()
percolateDown vo i0 = do
  n <- Growable.length ( heap vo )
  let
    go !i = do
      let l = leftIx i
          r = rightIx i
      if l >= n
      then pure ()
      else do
        a_i <- activityAt vo i
        a_l <- activityAt vo l
        ( best, a_best ) <-
          if r >= n
          then pure ( l, a_l )
          else do
            a_r <- activityAt vo r
            pure $ if a_r > a_l then ( r, a_r ) else ( l, a_l )
        if a_best > a_i
        then swapHeap vo i best *> go best
        else pure ()
  go i0
