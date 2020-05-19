{-# LANGUAGE BlockArguments             #-}
{-# LANGUAGE CPP                        #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE NamedFieldPuns             #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE UndecidableInstances       #-}

module Schedule.Ordering
  ( Order(Order, LessThan, GreaterThan, Unknown, Equal)
  , OrderingMatrix(..), upperTriangular
  , newOrderingMatrix, addEdgesTransitively
  , readOrdering
#ifdef VIZ
  , visualiseEdges
#endif
  )
  where

-- base
import Control.Monad
  ( when, unless )
import Data.Bits
  ( shiftR )
import Data.Coerce
  ( coerce )
import Data.Foldable
  ( for_, foldr' )
import Data.Function
  ( (&) )
import Data.Functor
  ( (<&>) )
import Data.Monoid
  ( Any(..) )
import Data.Traversable
  ( for )
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
import qualified Data.Vector.Generic.Mutable as Generic.MVector
import qualified Data.Vector.Unboxed as Vector
  ( Unbox )
import qualified Data.Vector.Unboxed as Unboxed
  ( Vector )
import qualified Data.Vector.Unboxed as Unboxed.Vector
  ( fromList, (!) )
import qualified Data.Vector.Unboxed.Mutable as Unboxed
  ( MVector )
import qualified Data.Vector.Unboxed.Mutable as Unboxed.MVector
  ( unsafeNew, unsafeWrite )

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
-- As self-edges are irrelevant, we only store the above-diagonal entries, each entry containing two bits of data,
-- corresponding to the presence or absence of edges in both directions.
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

-- | Initialise a matrix holding ordering information (similar to an adjacency matrix for a directed graph).
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

-- | Mutate ordering matrix to specify edges from vertex @i@ to vertex @j@.
writeOrdering :: ( PrimMonad m, s ~ PrimState m ) => OrderingMatrix ( Unboxed.MVector s ) -> Order -> Int -> Int -> m ()
writeOrdering ( OrderingMatrix { dim, orderingMatrix } ) order i j = case compare i j of
  EQ -> pure ()
  LT -> Unboxed.MVector.unsafeWrite orderingMatrix ( upperTriangular dim i j ) order
  GT -> Unboxed.MVector.unsafeWrite orderingMatrix ( upperTriangular dim j i ) ( reverseOrder order )

-- | Read stateful ordering matrix for edges from vertex @i@ to vertex @j@.
readOrdering :: ( ReadableVector m Order ( vec Order ) ) => OrderingMatrix vec -> Int -> Int -> m Order
readOrdering ( OrderingMatrix { dim, orderingMatrix } ) i j = case compare i j of
  EQ -> pure Equal
  LT -> unsafeIndex orderingMatrix ( upperTriangular dim i j )
  GT -> unsafeIndex orderingMatrix ( upperTriangular dim j i ) <&> reverseOrder

-- | King–Sagert insertion algorithm: add edges incident to a given vertex, and compute the transitive closure.
addEdgesTransitively
  :: forall m t1 t2 e s
  .  ( Foldable t1, Foldable t2
     , MonadError e m
     , PrimMonad m, s ~ PrimState m
     )
  => ( Int -> Int -> m () ) -- ^ Function to propagate information relative to a new precedence.
  -> ( Either Int ( Int, Int ) -> e ) -- ^ Function to give an error message.
  -> OrderingMatrix ( Unboxed.MVector s )
  -> Int    -- ^ Fixed incidence vertex.
  -> t1 Int -- ^ New predecessors to the given vertex.
  -> t2 Int -- ^ New successors to the given vertex.
  -> m ()
addEdgesTransitively propagateNewEdge errorMessage mat@( OrderingMatrix { dim } ) v befores afters = do
  -- Tally the new connections around vertex 'v': predecessors/successors of 'v' by way of new edges.
  new <- Unboxed.Vector.fromList <$>
    for [ 0 .. dim - 1 ] \ i ->
      if i == v
      then pure Unknown
      else do
        -- New predecessors of 'v' (can reach 'v' from 'i' by making use of a new edge ending at 'v').
        Any bef <- foldMapA ( \ u -> Any . unBit . fst . getOrder <$> readOrdering mat i u ) befores
        -- New successors of 'v' (can readch 'i' from 'v' by making use of a new edge starting at 'v').
        Any aft <- foldMapA ( \ w -> Any . unBit . fst . getOrder <$> readOrdering mat w i ) afters
        let
          res :: Order
          res = Order ( Bit bef, Bit aft )
        when ( res == Equal ) do
          throwError $ errorMessage ( Left i )
        pure res

  -- Add the transitive edges away from 'v'.
  for_ [ ( i, j ) | i <- [ 0 .. dim - 1 ], i /= v, j <- [ i + 1 .. dim - 1 ], j /= v ] \ ( i, j ) -> do
    let
      n_i, n_j :: Order
      n_i = new Unboxed.Vector.! i
      n_j = new Unboxed.Vector.! j & reverseOrder
    unless ( n_i \/ n_j == Unknown ) do
      c_ij <- readOrdering mat i j
      p_i  <- readOrdering mat i v
      p_j  <- readOrdering mat v j
      let
        p_ij :: Order
        p_ij = ( n_i /\ p_i ) \/ ( n_j /\ p_j ) \/ ( n_i /\ n_j )
      unless ( p_ij == Unknown ) do
        let
          res :: Order
          res = c_ij \/ p_ij
        writeOrdering mat res i j
        if res == Equal
        then throwError $ errorMessage ( Right (i, j) )
        else do
          when ( unBit . fst . getOrder $ p_ij ) do
            propagateNewEdge i j
          when ( unBit . snd . getOrder $ p_ij ) do
            propagateNewEdge j i

  -- Add the connections around 'v'.
  for_ [ i | i <- [ 0 .. dim - 1 ], i /= v ] \ i -> do
    let
      n :: Order
      n = new Unboxed.Vector.! i
    unless ( n == Unknown ) do
      c <- readOrdering mat i v
      writeOrdering mat ( c \/ n ) i v
      when ( unBit . fst . getOrder $ n ) do
        propagateNewEdge i v
      when ( unBit . snd . getOrder $ n ) do
        propagateNewEdge v i

-------------------------------------------------------------------------------
-- Writing out 'Unbox' instance for 'Order' by hand to avoid any Template Haskell...

newtype instance Unboxed.MVector s Order = MVOrder ( Unboxed.MVector s ( Bit, Bit ) )
newtype instance Unboxed.Vector    Order = VOrder  ( Unboxed.Vector    ( Bit, Bit ) )

instance Generic.MVector Unboxed.MVector Order where
  basicLength ( MVOrder mv ) = Generic.MVector.basicLength mv
  basicUnsafeSlice i l ( MVOrder mv ) = MVOrder ( Generic.MVector.basicUnsafeSlice i l mv )
  basicOverlaps ( MVOrder mv ) ( MVOrder mw ) = Generic.MVector.basicOverlaps mv mw
  basicUnsafeNew l = MVOrder <$> Generic.MVector.basicUnsafeNew l
  basicInitialize ( MVOrder mv ) = Generic.MVector.basicInitialize mv
  basicUnsafeReplicate i x = MVOrder <$> Generic.MVector.basicUnsafeReplicate i ( coerce x )
  basicUnsafeRead ( MVOrder mv ) i = coerce <$> Generic.MVector.basicUnsafeRead mv i
  basicUnsafeWrite ( MVOrder mv ) i x = Generic.MVector.basicUnsafeWrite mv i ( coerce x )
  basicClear ( MVOrder mv ) = Generic.MVector.basicClear mv
  basicSet ( MVOrder mv ) x = Generic.MVector.basicSet mv ( coerce x )
  basicUnsafeCopy ( MVOrder mv ) ( MVOrder mw ) = Generic.MVector.basicUnsafeCopy mv mw
  basicUnsafeMove ( MVOrder mv ) ( MVOrder mw ) = Generic.MVector.basicUnsafeMove mv mw
  basicUnsafeGrow ( MVOrder mv ) n = MVOrder <$> Generic.MVector.basicUnsafeGrow mv n

instance Generic.Vector Unboxed.Vector Order where
  basicUnsafeFreeze ( MVOrder mv ) = VOrder <$> Generic.Vector.basicUnsafeFreeze mv
  basicUnsafeThaw ( VOrder v ) = MVOrder <$> Generic.Vector.basicUnsafeThaw v
  basicLength ( VOrder v ) = Generic.Vector.basicLength v
  basicUnsafeSlice i l ( VOrder v ) = VOrder ( Generic.Vector.basicUnsafeSlice i l v )
  basicUnsafeIndexM ( VOrder v ) i = coerce <$> Generic.Vector.basicUnsafeIndexM v i
  basicUnsafeCopy ( MVOrder mv ) ( VOrder v ) = Generic.Vector.basicUnsafeCopy mv v
  elemseq ( VOrder v ) x y = Generic.Vector.elemseq v ( coerce x ) y

instance Vector.Unbox Order

-------------------------------------------------------------------------------
-- Utility function only used in this module.

foldMapA :: ( Applicative f, Foldable t, Monoid b ) => ( a -> f b ) -> t a -> f b
foldMapA f = foldr' ( \ a b -> (<>) <$> f a <*> b ) ( pure mempty )
