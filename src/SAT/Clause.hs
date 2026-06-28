{-# LANGUAGE MagicHash            #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE UnboxedTuples        #-}

-- | Clauses, clause references, clause storage, and reasons.
module SAT.Clause
  ( -- * Clauses
    Clause
  , clauseSize
  , clauseLit
  , clauseSwap
  , clauseIsLearnt
  , clauseToList
    -- * Clause storage
  , ClauseStore
  , newClauseStore
  , recordClause
  , recordLearntClause
  , clauseAt
    -- * Clause references
  , ClauseRef(..)
  , FalsifiedClauseRef(..)
    -- * Reasons
  , Reason(..)
  , LazyRef(..)
  , LazyReason(..)
  , forceLazyReasonNow
  )
  where

-- base
import Data.Bits
  ( shiftL, shiftR, (.|.), (.&.) )
import Data.Int
  ( Int32 )

-- memory-arena
import Memory.Arena
  ( Arena, newArena, arenaStorage, allocArray )
import Memory.Prim
  ( IsoPrim(..), As(..) )

-- primitive
import Control.Monad.Primitive
  ( PrimMonad(PrimState) )
import Data.Primitive
  ( Prim, sizeOf )

-- vector
import qualified Data.Vector.Primitive.Mutable as PMV

-- unary-scheduling
import SAT.Base
  ( Lit(..), litIndex
  , LitOfValue(..)
  , FalsifiedLit
  )

-------------------------------------------------------------------------------
-- Clause references.

-- | A reference into a 'ClauseStore'.
newtype ClauseRef = ClauseRef { unCRef :: Int32 }
  deriving stock   Show
  deriving newtype ( Eq, Ord, Prim )

-- | A reference to a clause that is currently falsified: every literal is
-- false under the current assignment.
newtype FalsifiedClauseRef = FalsifiedClauseRef { falsifiedClause :: ClauseRef }
  deriving newtype ( Show, Eq, Ord )

-------------------------------------------------------------------------------
-- Clause storage.

-- | Storage for 'Clause's.
data ClauseStore s = ClauseStore
  { csArena :: !( Arena s )
      -- ^ Underlying storage arena.
  , csView  :: !( PMV.MVector s Int32 )
      -- ^ Element-indexed view of the entire arena as raw 'Int32' data.
      --
      -- Shares the same 'MutableByteArray' as 'csArena'.
  }

-- | Allocate an empty store with the given capacity in bytes.
newClauseStore
  :: PrimMonad m
  => Int -> m ( ClauseStore ( PrimState m ) )
newClauseStore capBytes = do
  let !ali      = sizeOf @Int32 undefined
      !capElems = capBytes `div` ali
  arena <- newArena capBytes ali
  let view = PMV.MVector 0 capElems ( arenaStorage arena )
  pure ( ClauseStore arena view )

-- | Record a fresh (non-learnt) clause and return its reference.
recordClause
  :: PrimMonad m
  => ClauseStore ( PrimState m ) -> [ Lit ] -> m ClauseRef
recordClause store = recordRaw store False

-- | Record a fresh learnt clause and return its reference.
recordLearntClause
  :: PrimMonad m
  => ClauseStore ( PrimState m ) -> [ Lit ] -> m ClauseRef
recordLearntClause store = recordRaw store True

-- | Internal shared helper for 'recordClause'/'recordLearntClause'.
recordRaw
  :: forall m
  .  PrimMonad m
  => ClauseStore ( PrimState m )
  -> Bool -- ^ is this a learnt clause?
  -> [ Lit ]
  -> m ClauseRef
recordRaw store learnt lits = do
  let !n = length lits
  slice <- allocArray @Int32 ( csArena store ) ( n + 1 )
  -- The slice's offset (in elements) is exactly the 'ClauseRef'.
  let PMV.MVector startElem _ _ = slice
  PMV.unsafeWrite slice 0 ( encodeHeader n learnt )
  let writeBody :: Int32 -> [ Lit ] -> m ()
      writeBody !_ [] = pure ()
      writeBody !i ( l : rest ) = do
        PMV.unsafeWrite slice ( fromIntegral $ 1 + i ) ( fromIntegral $ litIndex l )
        writeBody ( i + 1 ) rest
  writeBody 0 lits
  pure ( ClauseRef $ fromIntegral startElem )

-- | Retrieve a 'Clause' given a 'ClauseRef'.
clauseAt
  :: PrimMonad m
  => ClauseStore ( PrimState m ) -> ClauseRef -> m ( Clause ( PrimState m ) )
clauseAt store ( ClauseRef ref ) = do
  hdr <- PMV.unsafeRead ( csView store ) ( fromIntegral ref )
  let ( !sz, !learnt ) = decodeHeader hdr
      body = PMV.unsafeSlice ( fromIntegral $ ref + 1 ) sz ( csView store )
  pure ( Clause body learnt )
  -- NB: this is the only function that knows about the layout
  -- of the clause store header.

-- | Pack a clause's size and learnt-flag into a single header 'Int32':
-- the low bit is the learnt flag, the remaining bits are the size.
encodeHeader :: Int -> Bool -> Int32
encodeHeader sz learnt = ( fromIntegral sz `shiftL` 1 ) .|. ( if learnt then 1 else 0 )

-- | Inverse of 'encodeHeader'.
decodeHeader :: Int32 -> ( Int, Bool )
decodeHeader h = ( fromIntegral ( h `shiftR` 1 ), ( h .&. 1 ) /= 0 )

-------------------------------------------------------------------------------
-- Clauses.

-- | A clause: a disjunction of literals @l0 ∨ l1 ∨ l2 ∨ ...@.
data Clause s = Clause
  { clauseBody   :: {-# UNPACK #-} !( PMV.MVector s Int32 )
  , clauseIsLearnt :: !Bool
  }

-- | The number of literals in a clause.
clauseSize :: Clause s -> Int
clauseSize = PMV.length . clauseBody

-- | Retrieve the literal at the given index of a 'Clause'.
clauseLit :: PrimMonad m => Clause ( PrimState m ) -> Int -> m Lit
clauseLit c i = Lit . fromIntegral <$> PMV.unsafeRead ( clauseBody c ) i

-- | Swap the literals at the given indices of a 'Clause'.
clauseSwap :: PrimMonad m => Clause ( PrimState m ) -> Int -> Int -> m ()
clauseSwap c = PMV.unsafeSwap ( clauseBody c )

-- | Retrieve the literals underlying a clause, in storage order.
clauseToList :: PrimMonad m => Clause ( PrimState m ) -> m [ Lit ]
clauseToList c = go ( clauseSize c - 1 ) []
  where
    v = clauseBody c
    go !i acc
      | i < 0     = pure acc
      | otherwise = do
          l <- PMV.unsafeRead v i
          go ( i - 1 ) ( Lit ( fromIntegral l ) : acc )
{-# WARNING clauseToList "For debugging use only" #-}

-------------------------------------------------------------------------------
-- Reasons.

-- | The reason why a literal was assigned.
data Reason
  -- | The literal is enforced unconditionally at the ground level.
  = RFact
  -- | The literal was assigned by a decision (e.g. during search).
  | RDecision
  -- | The literal was unit-propagated from a binary clause.
  | RBinary !FalsifiedLit -- ^ the other literal of the binary clause
  -- | The literal was unit-propagated by the given clause.
  --
  -- At the moment of propagation, this clause had all other literals false.
  | RClause !ClauseRef
  -- | The Literal was theory-propagated, with the given lazy clausal reason.
  | RLazy !LazyRef

-- | Fit a 'Reason' into an 'Int'.
deriving via ( As Reason Int ) instance Prim Reason
instance IsoPrim Reason Int where
  toPrim   = encodeReason
  fromPrim = decodeReason

-- | Pack a 'Reason' into an 'Int'.
encodeReason :: Reason -> Int
encodeReason = \case
  -- 5 constructors <=> 3 tag bits
  RFact -> 0
  RDecision -> 1
  RBinary ( FalsifiedLit lit ) -> 2 .|. ( fromIntegral ( litIndex lit ) `shiftL` 3 )
  RClause ( ClauseRef ref )    -> 3 .|. ( fromIntegral ref `shiftL` 3 )
  RLazy   ( LazyRef  ref )     -> 4 .|. ( fromIntegral ref `shiftL` 3 )

-- | Inverse of 'encodeReason'.
decodeReason :: Int -> Reason
decodeReason w =
  case w .&. 7 of
    0 -> RFact
    1 -> RDecision
    2 -> RBinary $ FalsifiedLit $ Lit ix
    3 -> RClause $ ClauseRef ix
    4 -> RLazy   $ LazyRef ix
    t -> error $ "decodeReason: invalid reason tag " ++ show t
  where
    ix = fromIntegral w `shiftR` 3

-- | A reference into the solver's lazy-reason table.
newtype LazyRef = LazyRef { unLazyRef :: Int32 }
  deriving stock   Show
  deriving newtype ( Eq, Ord, Prim )

-- | A deferred clause-producing action.
--
-- The closure must be self-contained at the moment it is created: any
-- mutable state it depends on should be captured into the closure so that
-- forcing it later still yields the correct supporting clause.
data LazyReason s =
  -- | A (still unevaluated) lazy reason.
    LazyReason
      ( forall m. ( PrimMonad m, PrimState m ~ s ) => m [ Lit ] )
  -- | The value of an already-forced lazy reason.
  | AlreadyForcedReason [ Lit ]

-- | Force a 'LazyReason' without overwriting the thunk with the value.
--
-- Risks wasting work if the 'LazyReason' is forced again later.
forceLazyReasonNow
  :: forall {s} m
  .  ( PrimMonad m, PrimState m ~ s )
  => LazyReason s -> m [ Lit ]
forceLazyReasonNow = \case
  LazyReason forceIt -> forceIt
  AlreadyForcedReason lits -> pure lits
