{-# LANGUAGE CPP                  #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE UndecidableInstances #-}

module Schedule.Ordering
  ( Order(Order, LessThan, GreaterThan, Unknown, Equal)
  , OrderingMatrix(..), upperTriangular
  , newOrderingMatrix
  , TransitiveClosureScratch, newTransitiveClosureScratch
  , insertEdgeTransitively
  , EdgeOrigin(..), CycleInfo(..)
  , readOrdering
#ifdef VIZ
  , visualiseEdges
#endif
  )
  where

-- base
import Control.Monad
  ( when )
import Data.Bits
  ( shiftR )
import Data.Foldable
  ( for_ )
import Data.Functor
  ( (<&>) )
import GHC.Generics
  ( Generic )

-- bitvec
import Data.Bit
  ( Bit (..) )

-- deepseq
import Control.DeepSeq
  ( NFData )

-- mtl
import Control.Monad.Except
  ( MonadError ( throwError ) )

-- primitive
import Control.Monad.Primitive
  ( PrimMonad(PrimState) )

-- text
import Data.Text
  ( Text )

-- vector
import qualified Data.Vector.Generic as Generic
  ( Vector )
import qualified Data.Vector.Generic as Generic.Vector
import qualified Data.Vector.Generic.Mutable as Generic
  ( MVector )
import qualified Data.Vector.Unboxed as Vector
  ( Unbox )
import qualified Data.Vector.Unboxed as Unboxed
  ( Vector )
import qualified Data.Vector.Unboxed.Mutable as Unboxed
  ( MVector )
import qualified Data.Vector.Unboxed.Mutable as Unboxed.MVector
  ( unsafeNew, unsafeWrite, unsafeRead )

#ifdef VIZ
-- algebraic-graphs
import qualified Algebra.Graph.AdjacencyIntMap as Alga
  ( AdjacencyIntMap, empty, edge, overlay )
import qualified Algebra.Graph.Export.Dot as Alga
  ( exportViaShow )
#endif

-- unary-scheduling
import Data.Lattice
  ( Lattice(..), BoundedLattice(..), Heyting(..) )
import Data.Vector.PhaseTransition
  ( Freeze(..), Thaw(..) )
import Data.Vector.Generic.Index
  ( ReadableVector(unsafeIndex) )

-------------------------------------------------------------------------------

-- | Ordering information (e.g. data for an edge in a directed graph).
newtype Order = Order { getOrder :: ( Bit, Bit ) }
  deriving stock    ( Show, Generic )
  deriving newtype  Eq
  deriving anyclass NFData
  -- Unbox instance defined at the end of this module.

{-# COMPLETE LessThan, GreaterThan, Unknown, Equal #-}
pattern LessThan, GreaterThan, Unknown, Equal :: Order
pattern LessThan    = Order ( Bit True , Bit False )
pattern GreaterThan = Order ( Bit False, Bit True  )
pattern Unknown     = Order ( Bit False, Bit False )
pattern Equal       = Order ( Bit True , Bit True  )

instance Lattice Order where
  Order ( Bit a1, Bit b1 ) \/ Order ( Bit a2, Bit b2 ) = Order ( Bit ( a1 || a2 ), Bit ( b1 || b2 ) )
  Order ( Bit a1, Bit b1 ) /\ Order ( Bit a2, Bit b2 ) = Order ( Bit ( a1 && a2 ), Bit ( b1 && b2 ) )
instance BoundedLattice Order where
  bottom = Order ( Bit False, Bit False )
  top    = Order ( Bit True , Bit True  )
instance Heyting Order where
  negation ( Order ( Bit a, Bit b ) ) = Order ( Bit ( not a ), Bit ( not b ) )

reverseOrder :: Order -> Order
reverseOrder ( Order ( Bit a, Bit b ) ) = Order ( Bit b, Bit a )

-- | Adjacency matrix of a transitively closed directed acyclic graph.
--
-- As self-edges are irrelevant, we only store the above-diagonal entries,
-- each entry containing two bits of data, corresponding to the presence or
-- absence of edges in both directions.
data OrderingMatrix vec = OrderingMatrix
  { dim            :: !Int
  , orderingMatrix :: !( vec Order )
  }
  deriving stock Generic
deriving stock    instance Show   ( vec Order ) => Show   ( OrderingMatrix vec )
deriving anyclass instance NFData ( vec Order ) => NFData ( OrderingMatrix vec )
instance ( PrimMonad m, Freeze m ( mvec Order ) ( vec Order ) ) => Freeze m ( OrderingMatrix mvec ) ( OrderingMatrix vec ) where
  unsafeFreeze ( OrderingMatrix dim mat ) = OrderingMatrix dim <$> unsafeFreeze mat
  freeze       ( OrderingMatrix dim mat ) = OrderingMatrix dim <$> freeze       mat
instance ( PrimMonad m, Thaw   m ( mvec Order ) ( vec Order ) ) => Thaw   m ( OrderingMatrix mvec ) ( OrderingMatrix vec ) where
  unsafeThaw   ( OrderingMatrix dim mat ) = OrderingMatrix dim <$> unsafeThaw   mat
  thaw         ( OrderingMatrix dim mat ) = OrderingMatrix dim <$> thaw         mat

#ifdef VIZ
-- | Return GraphViz code for visualisation of ordering information.
visualiseEdges :: Generic.Vector vec Order => OrderingMatrix vec -> Text
visualiseEdges ( OrderingMatrix { dim, orderingMatrix } )
  = Alga.exportViaShow adjacencyMap
  where
    adjacencyMap :: Alga.AdjacencyIntMap
    adjacencyMap = foldr addEdge Alga.empty [ ( i, j ) | i <- [ 0 .. dim - 1 ], j <- [ i + 1 .. dim - 1 ] ]
    addEdge :: ( Int, Int ) -> Alga.AdjacencyIntMap -> Alga.AdjacencyIntMap
    addEdge ( i, j ) rest = case orderingMatrix Generic.Vector.! ( upperTriangular dim i j ) of
      Unknown     -> rest
      LessThan    -> Alga.edge i j `Alga.overlay` rest
      GreaterThan -> Alga.edge j i `Alga.overlay` rest
      Equal       -> Alga.edge i j `Alga.overlay` Alga.edge j i `Alga.overlay` rest
#endif

-- | Initialise a matrix holding ordering information (similar to an
-- adjacency matrix for a directed graph).
--
-- Number of entries corresponds to the number of above-diagonal cells.
newOrderingMatrix
  :: ( PrimMonad m, PrimState m ~ s )
  => Int -> ( Int -> Int -> Order ) -> m ( OrderingMatrix ( Unboxed.MVector s ) )
newOrderingMatrix dim f = do
  orderingMatrix <- Unboxed.MVector.unsafeNew ( ( dim * ( dim - 1 ) ) `shiftR` 1 )
  for_ [ ( i, j ) | i <- [ 0 .. dim - 1 ], j <- [ i + 1 .. dim - 1 ] ] \ ( i, j ) ->
    Unboxed.MVector.unsafeWrite orderingMatrix ( upperTriangular dim i j ) ( f i j )
  pure ( OrderingMatrix { dim, orderingMatrix } )

-- | Index of above-diagonal cell at row @i@, column @j@ ( @i < j@ ),
-- in upper triangular part of square matrix of dimension @d@ (indexed along rows).
--
-- Illustration for @d = 5@ :
-- @
--     j 0 1 2 3 4
--   i
--   0   . 0 1 2 3
--   1   . . 4 5 6
--   2   . . . 7 8
--   3   . . . . 9
--   4   . . . . .
-- @
upperTriangular :: Int -> Int -> Int -> Int
upperTriangular d i j = j - 1 + i * d - ( ( ( i + 3 ) * i ) `shiftR` 1 )

-- | Mutate ordering matrix, writing the specified edges from vertex @i@ to vertex @j@.
writeOrdering
  :: Monad m
  => ( Int -> Order -> m () ) -- ^ Physical cell write.
  -> OrderingMatrix vec
  -> Order
  -> Int -> Int -> m ()
writeOrdering writeCell ( OrderingMatrix { dim } ) order i j = case compare i j of
  EQ -> pure ()
  LT -> writeCell ( upperTriangular dim i j ) order
  GT -> writeCell ( upperTriangular dim j i ) ( reverseOrder order )

-- | Read ordering matrix for edges from vertex @i@ to vertex @j@.
readOrdering
  :: ( ReadableVector m Order ( vec Order ) )
  => OrderingMatrix vec
  -> Int -> Int
  -> m Order
readOrdering ( OrderingMatrix { dim, orderingMatrix } ) i j = case compare i j of
  EQ -> pure Equal
  LT -> unsafeIndex orderingMatrix ( upperTriangular dim i j )
  GT -> unsafeIndex orderingMatrix ( upperTriangular dim j i ) <&> reverseOrder

-- | Reusable scratch buffer for 'insertEdgeTransitively'.
newtype TransitiveClosureScratch s = TransitiveClosureScratch ( Unboxed.MVector s Int )

newTransitiveClosureScratch
  :: ( PrimMonad m, PrimState m ~ s )
  => Int -- ^ ordering matrix dimension
  -> m ( TransitiveClosureScratch s )
newTransitiveClosureScratch dim =
  TransitiveClosureScratch <$> Unboxed.MVector.unsafeNew dim

-- | Whether a newly-added edge was the directly-inserted edge or was computed by
-- transitive closure.
data EdgeOrigin
  = -- | The directly-inserted edge @u → w@.
    SeedEdge
  | -- | A transitively-derived edge. The carried 'Int' is the witness
    -- vertex @u@ such that the edge follows from @i → u@ and @u → j@.
    DerivedEdge !Int
  deriving stock ( Eq, Show )

-- | A cycle closed by inserting an edge @u → w@ into the precedence graph.
data CycleInfo
  = -- | The inserted edge made vertex @i@ both a predecessor and a successor of
    -- the head @w@: the cycle is @i → w → i@.
    SelfCycle !Int
  | -- | The inserted edge connected @i → j@ while @j → i@ already held: the
    -- cycle is @i → j → i@.
    DoubleCycle !Int !Int
  deriving stock ( Eq, Show )

-- | Whether @i@ precedes @j@, given their stored 'Order' (its first bit).
isBefore :: Order -> Bool
isBefore ( Order ( Bit lt, _ ) ) = lt

-- | Insert a (non-self) edge into a transitively-closed, acyclic ordering matrix.
--
-- Uses Italiano's insertion-only transitive closure algorithm.
insertEdgeTransitively
  :: forall m e s
  .  ( MonadError e m
     , PrimMonad m, s ~ PrimState m
     )
  => TransitiveClosureScratch s           -- ^ scratch space
  -> ( Int -> Order -> m () )             -- ^ trailed physical cell write
  -> ( EdgeOrigin -> Int -> Int -> m () ) -- ^ new-edge notifiy action
  -> ( CycleInfo -> e )                   -- ^ cycle error
  -> OrderingMatrix ( Unboxed.MVector s )
  -> Int -- ^ @u@: tail of the inserted edge (the new predecessor)
  -> Int -- ^ @w@: head of the inserted edge (the new successor)
  -> m ()
insertEdgeTransitively ( TransitiveClosureScratch succBuf ) writeCell onNewEdge cycleError mat@( OrderingMatrix { dim } ) u w = do
  -- This insertion only adds predecessors of 'w', so the successors of 'w' are
  -- fixed: materialise succ(w) = { j : w → j } once and reuse it for every
  -- new predecessor of 'w'.
  nSucc <- collectSuccessors 0 0
  let
    -- Visit every vertex 'i' that newly reaches 'w'.
    visit :: Int -> m ()
    visit i
      | i >= dim  = pure ()
      | i == w    = visit ( i + 1 )
      | otherwise = do
          reachesU <- if i == u then pure True else isBefore <$> readOrdering mat i u
          if not reachesU
          then visit ( i + 1 )
          else do
            iw <- readOrdering mat i w
            if isBefore iw
            -- 'i' already precedes 'w', so the closure already holds every
            -- through-w edge from 'i': nothing new here.
            then visit ( i + 1 )
            else do
              let iw' = iw \/ LessThan
              -- w → i was present, so i → w closes the 2-cycle i ↔ w.
              when ( iw' == Equal ) $ throwError ( cycleError ( SelfCycle i ) )
              writeOrdering writeCell mat iw' i w
              onNewEdge ( if i == u then SeedEdge else DerivedEdge u ) i w
              closeThrough i 0
              visit ( i + 1 )

    -- Close i → j for each successor 'j' of 'w' (the through-w edges i → w → j).
    closeThrough :: Int -> Int -> m ()
    closeThrough i k
      | k >= nSucc = pure ()
      | otherwise  = do
          j  <- Unboxed.MVector.unsafeRead succBuf k
          ij <- readOrdering mat i j
          if isBefore ij
          then closeThrough i ( k + 1 )
          else do
            let ij' = ij \/ LessThan
            -- j → i was present, so i → j closes the 2-cycle i ↔ j.
            when ( ij' == Equal ) $ throwError ( cycleError ( DoubleCycle i j ) )
            writeOrdering writeCell mat ij' i j
            onNewEdge ( DerivedEdge w ) i j
            closeThrough i ( k + 1 )
  visit 0
  where
    -- Fill 'succBuf' with { j : w → j }, returning the count.
    collectSuccessors :: Int -> Int -> m Int
    collectSuccessors j n
      | j >= dim  = pure n
      | j == w    = collectSuccessors ( j + 1 ) n
      | otherwise = do
          o <- readOrdering mat w j
          if isBefore o
          then Unboxed.MVector.unsafeWrite succBuf n j *> collectSuccessors ( j + 1 ) ( n + 1 )
          else collectSuccessors ( j + 1 ) n

-------------------------------------------------------------------------------

newtype instance Unboxed.MVector s Order = MVOrder ( Unboxed.MVector s ( Bit, Bit ) )
newtype instance Unboxed.Vector    Order = VOrder  ( Unboxed.Vector    ( Bit, Bit ) )
deriving newtype instance Generic.MVector Unboxed.MVector Order
deriving newtype instance Generic.Vector Unboxed.Vector Order
deriving newtype instance Vector.Unbox Order
