{-# LANGUAGE CPP                  #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE UndecidableInstances #-}

module Schedule.Ordering
  ( Order(Order, LessThan, GreaterThan, Unknown, Equal)
  , OrderingMatrix(..), upperTriangular
  , newOrderingMatrix
  , addIncidentEdges, addIncidentEdgesTransitively
  , EdgeOrigin(..), CycleInfo(..)
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
  ( for_ )
import Data.Functor
  ( (<&>) )
import Data.Monoid
  ( Any(..), Ap(..) )
import Data.Traversable
  ( for )
import GHC.Generics
  ( Generic )

-- bitvec
import Data.Bit
  ( Bit (..) )

-- containers
import Data.IntSet
  ( IntSet )
import qualified Data.IntSet as IntSet
  ( member, toList )

-- deepseq
import Control.DeepSeq
  ( NFData )

-- lens
import Control.Lens.Fold
  ( foldMapOf, forOf_ )
import qualified Data.IntSet.Lens as IntSet
  ( members )

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

-- | Mutate edge in an ordering matrix.
modify'Ordering
  :: ( PrimMonad m, s ~ PrimState m )
  => ( Int -> Order -> m () ) -- ^ physical cell write
  -> OrderingMatrix ( Unboxed.MVector s ) -> ( Order -> Order ) -> Int -> Int -> m ()
modify'Ordering writeCell mat f i j = do
  o <- readOrdering mat i j
  let
    !o' = f o
  -- Only write when the cell actually changes, to avoid bloating the trail
  -- with no-ops.
  when ( o' /= o ) $
    writeOrdering writeCell mat o' i j

-- | Add edges incident to a given vertex (without computing a transitive closure).
addIncidentEdges
  :: ( PrimMonad m, s ~ PrimState m )
  => ( Int -> Order -> m () ) -- ^ Physical cell write.
  -> OrderingMatrix ( Unboxed.MVector s )
  -> Int    -- ^ Fixed incidence vertex.
  -> IntSet -- ^ New predecessors to the given vertex.
  -> IntSet -- ^ New successors to the given vertex.
  -> m ()
addIncidentEdges writeCell mat v befores afters = do
  forOf_ IntSet.members befores ( modify'Ordering writeCell mat ( GreaterThan \/ ) v )
  forOf_ IntSet.members afters  ( modify'Ordering writeCell mat ( LessThan    \/ ) v )

-- | Whether a new edge was directly asserted (one of the seed edges of the
-- King–Sagert call) or computed by transitive closure.
data EdgeOrigin
  = -- | One of the directly-added edges incident to the central vertex.
    SeedEdge
  | -- | A transitively-derived edge. The carried 'Int' is the witness
    -- vertex @u@ such that the edge follows from @i → u@ and @u → j@.
    DerivedEdge !Int
  deriving stock ( Eq, Show )

-- | A cycle detected during the transitive-closure update.
--
-- All cycles pass through the central vertex @v@ of the call.
data CycleInfo
  = -- | Vertex @i@ became both a predecessor and a successor of @v@: the
    -- cycle is @i → v → i@.
    SelfCycle !Int
  | -- | Vertices @i@ and @j@ became bidirectionally connected via @v@:
    -- the cycle threads @i → v → j → v → i@.
    DoubleCycle !Int !Int
  deriving stock ( Eq, Show )

-- | King–Sagert insertion algorithm: add edges incident to a given vertex,
-- and compute the transitive closure.
addIncidentEdgesTransitively
  :: forall m e s
  .  ( MonadError e m
     , PrimMonad m, s ~ PrimState m
     )
  => ( Int -> Order -> m () )             -- ^ Physical cell write.
  -> ( EdgeOrigin -> Int -> Int -> m () ) -- ^ Propagate a new edge @i → j@.
  -> ( CycleInfo -> e )                   -- ^ Error to raise when a cycle is detected.
  -> OrderingMatrix ( Unboxed.MVector s )
  -> Int    -- ^ Fixed incidence vertex @v@.
  -> IntSet -- ^ New predecessors of @v@.
  -> IntSet -- ^ New successors of @v@.
  -> m ()
addIncidentEdgesTransitively writeCell onNewEdge cycleError mat@( OrderingMatrix { dim } ) v befores afters = do
  -- Step 1: tally the new connections around vertex 'v' (predecessors and
  -- successors reachable through a single new edge incident to 'v').

  -- TODO: allocates a fresh length-'dim' vector on every call (i.e. per
  -- channeled edge). A reusable scratch buffer would avoid the churn.
  new <- Unboxed.Vector.fromList <$>
    for [ 0 .. dim - 1 ] \ i ->
      if i == v
      then pure Unknown
      else getAp do
        let
        -- New predecessors of 'v' (can reach 'v' from 'i' by making use of a new edge ending at 'v').
        Any bef <- foldMapOf IntSet.members ( \ u -> coerce @( m Any ) $ Any . unBit . fst . getOrder <$> readOrdering mat i u ) befores
        -- New successors of 'v' (can readch 'i' from 'v' by making use of a new edge starting at 'v').
        Any aft <- foldMapOf IntSet.members ( \ w -> coerce @( m Any ) $ Any . unBit . fst . getOrder <$> readOrdering mat w i ) afters
        let
          res :: Order
          res = Order ( Bit bef, Bit aft )
        when ( res == Equal ) do
          coerce @( m () ) $ throwError ( cycleError ( SelfCycle i ) )
        pure res

  -- Step 2: add the around-'v' edges to the matrix.
  for_ [ i | i <- [ 0 .. dim - 1 ], i /= v ] \ i -> do
    let
      n :: Order
      n = new Unboxed.Vector.! i
      Order ( Bit bef_i, Bit aft_i ) = n
    unless ( n == Unknown ) do
      c <- readOrdering mat i v
      let
        Order ( Bit c_lt, Bit c_gt ) = c
        !c'                          = c \/ n
      writeOrdering writeCell mat c' i v
      -- A through-'v' cycle: 'i' was already a successor of 'v' and is
      -- now becoming a predecessor (or vice versa).
      when ( c' == Equal ) $
        throwError ( cycleError ( SelfCycle i ) )
      -- Fire 'onNewEdge' for each genuinely-new direction.
      when ( bef_i && not c_lt ) do
        origin <- aroundEdgeOrigin i befores ( \ u -> readOrdering mat i u )
        onNewEdge origin i v
      when ( aft_i && not c_gt ) do
        origin <- aroundEdgeOrigin i afters  ( \ w -> readOrdering mat w i )
        onNewEdge origin v i

  -- Step 3: derive transitive edges.
  for_ [ ( i, j ) | i <- [ 0 .. dim - 1 ], i /= v, j <- [ i + 1 .. dim - 1 ], j /= v ] \ ( i, j ) -> do
    c_ij <- readOrdering mat i j
    Order ( Bit i_lt_v, Bit i_gt_v ) <- readOrdering mat i v
    Order ( Bit v_lt_j, Bit v_gt_j ) <- readOrdering mat v j
    let
      p_ij :: Order
      p_ij = Order ( Bit ( i_lt_v && v_lt_j ), Bit ( v_gt_j && i_gt_v ) )
    unless ( p_ij == Unknown ) do
      let
        Order ( Bit c_lt, Bit c_gt ) = c_ij
        res :: Order
        res = c_ij \/ p_ij
      writeOrdering writeCell mat res i j
      if res == Equal
      then throwError $ cycleError ( DoubleCycle i j )
      else do
        -- Propagate only edges that are genuinely new (not already in 'c_ij').
        when ( i_lt_v && v_lt_j && not c_lt ) do
          onNewEdge ( DerivedEdge v ) i j
        when ( v_gt_j && i_gt_v && not c_gt ) do
          onNewEdge ( DerivedEdge v ) j i

  where
    -- Determine the 'EdgeOrigin' of a phase-2 around-'v' edge with endpoint
    -- @i@: it is 'SeedEdge' iff @i@ is in the input set, and otherwise a
    -- 'DerivedEdge' witnessed by some @u@ in the set with @check u@
    -- returning 'LessThan' (or 'Equal') in its first bit.
    aroundEdgeOrigin :: Int -> IntSet -> ( Int -> m Order ) -> m EdgeOrigin
    aroundEdgeOrigin i inputs check
      | IntSet.member i inputs = pure SeedEdge
      | otherwise              = DerivedEdge <$> findWitness ( IntSet.toList inputs )
      where
        findWitness :: [ Int ] -> m Int
        findWitness [] = error
          "Schedule.Ordering.addIncidentEdgesTransitively: missing witness for derived around-v edge"
        findWitness ( u : us ) = do
          o <- check u
          if unBit ( fst ( getOrder o ) )
          then pure u
          else findWitness us

-------------------------------------------------------------------------------

newtype instance Unboxed.MVector s Order = MVOrder ( Unboxed.MVector s ( Bit, Bit ) )
newtype instance Unboxed.Vector    Order = VOrder  ( Unboxed.Vector    ( Bit, Bit ) )
deriving newtype instance Generic.MVector Unboxed.MVector Order
deriving newtype instance Generic.Vector Unboxed.Vector Order
deriving newtype instance Vector.Unbox Order
