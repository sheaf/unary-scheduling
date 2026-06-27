{-# LANGUAGE MagicHash            #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE UnboxedTuples        #-}

-- | Clauses, clause references, clause storage, and reasons.
--
-- A 'ClauseStore' is an arena of clauses. Recording a clause returns a
-- 'ClauseRef' identifying it; 'clauseAt' produces a 'Clause' — a transient,
-- mutable view of that clause's literals — on demand.
module SAT.Clause
  ( -- * Clauses (transient views)
    Clause
  , clauseSize
  , clauseLit
  , clauseSwap
  , isLearnt
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

-- | A reference into a 'ClauseStore' (offset of a clause's header in the
-- store's arena).
newtype ClauseRef = ClauseRef { unCRef :: Int32 }
  deriving stock   Show
  deriving newtype ( Eq, Ord, Prim )

-- | A 'ClauseRef' whose clause is currently /falsified/: every literal is
-- false under the current assignment.
newtype FalsifiedClauseRef = FalsifiedClauseRef { falsifiedClause :: ClauseRef }
  deriving newtype ( Show, Eq, Ord )

-------------------------------------------------------------------------------
-- Clause storage.

-- | An append-only arena of clauses: a recorded clause is never relocated,
-- so its 'ClauseRef' stays valid for the lifetime of the store.
data ClauseStore s = ClauseStore
  { csArena :: !( Arena s )
      -- ^ Bump allocator over the backing 'MutableByteArray'.
  , csView  :: !( PMV.MVector s Int32 )
      -- ^ Element-indexed view of the entire arena as raw 'Int32' data.
      --
      -- Shares the same 'MutableByteArray' as 'csArena'.
  }

-- | Allocate an empty store with the given capacity in bytes.
--
-- Each clause consumes @sizeOf Int32 * (size + 1)@ bytes.
newClauseStore
  :: PrimMonad m
  => Int -> m ( ClauseStore ( PrimState m ) )
newClauseStore capBytes = do
  let !ali      = sizeOf @Int32 undefined
      !capElems = capBytes `div` ali
  arena <- newArena capBytes ali
  let view = PMV.MVector 0 capElems ( arenaStorage arena )
  pure ( ClauseStore arena view )

-- | Append a fresh original (non-learnt) clause and return its reference.
recordClause
  :: PrimMonad m
  => ClauseStore ( PrimState m ) -> [ Lit ] -> m ClauseRef
recordClause store = recordRaw store False

-- | Append a fresh learnt clause and return its reference.
recordLearntClause
  :: PrimMonad m
  => ClauseStore ( PrimState m ) -> [ Lit ] -> m ClauseRef
recordLearntClause store = recordRaw store True

-- | Internal shared helper for  'recordClause' / 'recordLearntClause'.
recordRaw
  :: forall m
  .  PrimMonad m
  => ClauseStore ( PrimState m ) -> Bool -> [ Lit ] -> m ClauseRef
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

-- | Retrieve the 'Clause' from a reference into the clause store.
--
-- Reads see the current state and writes  mutate the store in-place.
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
-- Clauses (transient views).

-- | A view of a clause's literal body together with its learnt flag.
data Clause s = Clause
  { clauseBody   :: {-# UNPACK #-} !( PMV.MVector s Int32 )
  , clauseLearnt :: !Bool
  }

clauseSize :: Clause s -> Int
clauseSize = PMV.length . clauseBody

isLearnt :: Clause s -> Bool
isLearnt = clauseLearnt

clauseLit :: PrimMonad m => Clause ( PrimState m ) -> Int -> m Lit
clauseLit c i = Lit . fromIntegral <$> PMV.unsafeRead ( clauseBody c ) i

clauseSwap :: PrimMonad m => Clause ( PrimState m ) -> Int -> Int -> m ()
clauseSwap c = PMV.unsafeSwap ( clauseBody c )

-- | Snapshot a clause as a list of its current literals (storage order).
--
-- Linear in the clause size; for debugging and oracle comparison only.
clauseToList :: PrimMonad m => Clause ( PrimState m ) -> m [ Lit ]
clauseToList c = go ( clauseSize c - 1 ) []
  where
    v = clauseBody c
    go !i acc
      | i < 0     = pure acc
      | otherwise = do
          l <- PMV.unsafeRead v i
          go ( i - 1 ) ( Lit ( fromIntegral l ) : acc )

-------------------------------------------------------------------------------
-- Reasons.

-- | Why a literal was added to the trail.
data Reason
  -- | Literal enforced unconditionally at the ground level (a unit input
  -- clause, or a unit learnt clause whose backjump level is @0@).
  = RFact
  -- | Literal chosen by the search heuristic (head of a decision level
  -- above the ground level).
  | RDecision
  -- | Literal that was unit-propagated from a binary clause.
  | RBinary !FalsifiedLit -- ^ the "other" literal
  -- | Literal that was unit-propagated from the clause at the given
  -- reference. At the moment of propagation, this clause had all other
  -- literals false.
  | RClause !ClauseRef
  -- | Literal that was theory-propagated, with a deferred clausal reason.
  --
  -- The 'LazyRef' indexes into the solver's lazy-reason table. When 1-UIP
  -- analysis encounters this reason, it forces the corresponding
  -- 'LazyReason' closure to obtain the supporting clause.
  | RLazy !LazyRef

-- | A reference into the solver's lazy-reason table.
newtype LazyRef = LazyRef { unLazyRef :: Int32 }
  deriving stock   Show
  deriving newtype ( Eq, Ord, Prim )

-- | A deferred clause-producing action, attached to a theory-propagated
-- literal as a 'RLazy' reason.
--
-- The closure must be self-contained at the moment it is created: any
-- scheduler state it depends on should be captured into the closure so that
-- forcing it later — after further mutation or backjumping — still yields
-- the correct supporting clause.
--
-- The returned list contains the literals of the supporting clause; the
-- propagated literal may be included since 1-UIP analysis filters out
-- the resolution variable.
data LazyReason s =
  -- | A (still unevaluated) lazy reason.
    LazyReason
      ( forall m. ( PrimMonad m, PrimState m ~ s ) => m [ Lit ] )
  -- | The value of an already-forced lazy reason.
  | AlreadyForcedReason [ Lit ]

-- | Fit a 'Reason' into an 'Int'.
deriving via ( As Reason Int ) instance Prim Reason
instance IsoPrim Reason Int where
  toPrim   = encodeReason
  fromPrim = decodeReason

-- | Internal packing for the 'Prim' 'Reason' instance.
--
-- Five constructors need three tag bits; the remaining 61 bits hold the
-- payload ('Lit' index, 'ClauseRef', or 'LazyRef').
encodeReason :: Reason -> Int
encodeReason = \case
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
    _ -> error "SAT.Clause.decodeReason: invalid reason tag"
  where
    ix = fromIntegral w `shiftR` 3
