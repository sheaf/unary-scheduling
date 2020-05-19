{-# LANGUAGE AllowAmbiguousTypes        #-}
{-# LANGUAGE BlockArguments             #-}
{-# LANGUAGE CPP                        #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE DuplicateRecordFields      #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE NamedFieldPuns             #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE UndecidableInstances       #-}

module Schedule.Tree
  ( Tree(..), newTree, cloneTree, fmapTree
  , toRoseTree
#ifdef VIZ
  , visualiseTree
#endif
  , Propagatable(..)
  , DurationInfo(..), BaseDurationInfo
  , TTDurationInfo(..), BaseTTDurationInfo
  , DurationExtraInfo(..), TTDurationExtraInfo(..)
  )
  where

-- base
import Data.Bits
  ( Bits
    ( bit, popCount )
  , FiniteBits
    ( finiteBitSize, countLeadingZeros )
  )
import Data.Coerce
  ( coerce )
import Data.Foldable
  ( for_ )
import Data.Functor
  ( (<&>), ($>) )
import Data.Kind
  ( Type )
import Data.Maybe
  ( catMaybes )
import Data.Semigroup
  ( Semigroup
    ( stimes )
  , Arg(..), Max(..), ArgMax
  )

-- acts
import Data.Act
  ( Act(..) )

-- containers
import Data.Set
  ( Set )
import qualified Data.Set as Set
  ( disjoint, empty )
import qualified Data.Tree as Rose
  ( Tree(..) )

-- generic-lens
import Data.GenericLens.Internal
  ( view )

-- primitive
import Control.Monad.Primitive
  ( PrimMonad(PrimState) )

-- vector
import qualified Data.Vector.Mutable as Boxed
  ( MVector )
import qualified Data.Vector.Mutable as Boxed.MVector
  ( length, replicate, unsafeNew, unsafeRead, unsafeWrite, clone )


#ifdef VIZ
-- tree-view
import qualified Data.Tree.View as TreeView
  ( showTree )
#endif

-- unary-scheduling
import Data.Lattice
  ( Lattice((/\)), BoundedLattice(top)
  , TotallyOrderedLattice((/.\))
  )
import Data.Vector.Generic.Index
  ( ReadableVector
    ( unsafeIndex )
  )
import Schedule.Ordering
  ( Order(..) )
import Data.Vector.Ranking
  ( Ranking(..) )
import Schedule.Interval
  ( Endpoint(..), Interval(..), validInterval )
import Schedule.Task
  ( TaskInfos(..)
  , Limit
      ( Outer )
  , PickEndpoint(_ranking)
  )
import Schedule.Time
  ( Delta, Handedness(..), HandedTime(..), OtherHandedness )

---------------------------------------------------------------------------------------------------

-- | Two types of unary scheduling trees:
-- 
--  - Earliest: compute earliest completion time, with leaves sorted by earliest start      time,
--  - Latest  : compute latest   start      time, with leaves sorted by latest   completion time.
newtype Tree ( h :: Handedness ) ( s :: Type ) ( a :: Type ) =
  Tree { treeVector :: Boxed.MVector s a }

{-# SPECIALISE nextPositivePowerOf2 :: Int -> Int #-}
nextPositivePowerOf2 :: forall a. FiniteBits a => a -> a
nextPositivePowerOf2 i
  | popCount i == 1
  = i
  | otherwise
  = bit ( finiteBitSize i - countLeadingZeros i )

-- | Create a new unary scheduling tree with a given number of leaves (one leaf per task).
newTree
  :: forall h a m s
  . ( Monoid a
    , PrimMonad m, PrimState m ~ s
    )
  => Int -> m ( Tree h s a )
newTree nbLeaves = do
  let
    nbNodes :: Int
    nbNodes = 2 * ( nextPositivePowerOf2 nbLeaves ) - 1
  Tree <$> Boxed.MVector.replicate nbNodes mempty

-- | Clone a unary scheduling tree.
cloneTree
  :: ( PrimMonad m, PrimState m ~ s )
  => Tree h s a -> m ( Tree h s a )
cloneTree ( Tree { treeVector } ) = Tree <$> Boxed.MVector.clone treeVector

-- | Map a function over a unary scheduling tree tree.
fmapTree
  :: forall a b h m s
  .  ( PrimMonad m, PrimState m ~ s )
  => ( a -> b ) -> Tree h s a -> m ( Tree h s b )
fmapTree f ( Tree { treeVector = oldTree } ) = do
  let
    lg :: Int
    lg = Boxed.MVector.length oldTree
  newTreeVector <- Boxed.MVector.unsafeNew @_ @b lg
  for_ [ 0 .. lg - 1 ] \ i -> do
    a <- Boxed.MVector.unsafeRead oldTree i
    Boxed.MVector.unsafeWrite newTreeVector i ( f a )
  pure ( Tree { treeVector = newTreeVector } )

-- | Propagate a change from a leaf to the rest of a unary scheduling tree.
--
-- /Warning/: It is not recommended to call this function directly,
-- as the index of a leaf depends on the type of tree.
--
-- The function 'propagateLeafChange' automatically computes the appropriate leaf index.
propagateChangeFromLeaf
  :: forall h a m s
  . ( Show a, Monoid a
    , PrimMonad m, s ~ PrimState m
    )
  => Tree h s a -> a -> Int -> m a
propagateChangeFromLeaf ( Tree { treeVector } ) a leafIndex = case lg of
  0 -> pure a
  1 -> Boxed.MVector.unsafeWrite treeVector leafIndex a $> a
  _ -> Boxed.MVector.unsafeWrite treeVector leafIndex a *> go a ( parentIndex leafIndex )
  where
    lg :: Int
    lg = Boxed.MVector.length treeVector
    go :: a -> ( Int, Side ) -> m a
    go childValue ( nodeIndex, childSide ) = do
      let
        otherChildIndex :: Int
        otherChildIndex = childIndex nodeIndex ( otherSide childSide )
      otherChildValue <- treeVector `Boxed.MVector.unsafeRead` otherChildIndex
      let
        nodeValue :: a
        nodeValue = case childSide of
          LeftChild -> childValue      <> otherChildValue
          _         -> otherChildValue <> childValue
      
      Boxed.MVector.unsafeWrite treeVector nodeIndex nodeValue
      if nodeIndex == 0
      then
        pure nodeValue
      else
        go nodeValue ( parentIndex nodeIndex )

data Side = LeftChild | RightChild
  deriving stock Show

otherSide :: Side -> Side
otherSide LeftChild  = RightChild
otherSide RightChild = LeftChild

parentIndex :: Int -> ( Int, Side )
parentIndex child = ( index, side )
  where
    index :: Int
    index = ( child - 1 ) `div` 2
    side :: Side
    side = if odd child then LeftChild else RightChild

childIndex :: Int -> Side -> Int
childIndex parent LeftChild  = 2 * parent + 1
childIndex parent RightChild = 2 * parent + 2

-- | Convert a task tree into a rose tree (e.g. for displaying purposes).
toRoseTree
  :: forall h a m s
  . ( Eq a, Monoid a
    , PrimMonad m, PrimState m ~ s
    )
  => Tree h s a -> m ( Rose.Tree ( Int, a ) )
toRoseTree ( Tree { treeVector } ) = do
  a <- treeVector `Boxed.MVector.unsafeRead` 0
  mbLeftSubtree  <- go ( childIndex 0 LeftChild  )
  mbRightSubtree <- go ( childIndex 0 RightChild )
  pure ( Rose.Node ( 0, a ) ( catMaybes [ mbLeftSubtree, mbRightSubtree ] ) )
  where
    nbNodes :: Int
    nbNodes = Boxed.MVector.length treeVector
    go :: Int -> m ( Maybe ( Rose.Tree ( Int, a ) ) )
    go i 
      | i >= nbNodes
      = pure Nothing
      | otherwise
      = do
          a <- treeVector `Boxed.MVector.unsafeRead` i
          if a == mempty
          then
            pure Nothing
          else do
            mbLeftSubtree  <- go ( childIndex i LeftChild  )
            mbRightSubtree <- go ( childIndex i RightChild )
            pure ( Just $ Rose.Node ( i, a ) ( catMaybes [ mbLeftSubtree, mbRightSubtree ] ) )

#ifdef VIZ
-- | Visualise a tree using the tree-view package.
visualiseTree
  :: ( Eq a, Monoid a, Show a
     , PrimMonad m, PrimState m ~ s
     )
  => Tree h s a -> m String
visualiseTree tree = TreeView.showTree . fmap show <$> toRoseTree tree
#endif

---------------------------------------------------------------------------------------------------
-- Handedness polymorphism for different kinds of propagatable data.

class Propagatable ( h :: Handedness ) where
  -- | Check whether a resource is overloaded,
  -- i.e. whether the 'Earliest' time exceeds the 'Latest' time.
  overloaded :: Ord t => Endpoint ( HandedTime h t ) -> Endpoint ( HandedTime ( OtherHandedness h ) t ) -> Bool

  -- | Adjusts the index to count from the start (for 'Earliest' handedness) or the end (for 'Latest' handedness).
  handedIndex
    :: Int -- ^ Number of tasks.
    -> Int -- ^ Index to adjust.
    -> Int

  inHandedOrder :: Order -> Bool

  -- | Propagate a change from a leaf to the rest of a unary scheduling tree.
  --
  -- The given index is the task number, from which the leaf index is computed
  -- depending on the handedness of the scheduling tree,
  -- using the relevant task ranking (by earliest start time or latest completion time).
  propagateLeafChange
    :: ( PrimMonad m, s ~ PrimState m
       , Monoid a, Show a
       , ReadableVector m Int (uvec Int)
       )
    => Tree h s a -> a -> TaskInfos bvec uvec task t -> Int -> m a

instance Propagatable Earliest where
  overloaded start end = not $ validInterval ( Interval start end )
  handedIndex _ i = i
  inHandedOrder LessThan = True
  inHandedOrder _        = False
  propagateLeafChange tree@(Tree { treeVector }) val ( TaskInfos { rankingEST = Ranking { ranks } } ) taskIndex = do
    rankEST <- ranks `unsafeIndex` taskIndex
    let
      nbNodes, leafIndex :: Int
      nbNodes = Boxed.MVector.length treeVector
      leafIndex = rankEST + ( nbNodes `div` 2 )
    propagateChangeFromLeaf tree val leafIndex

instance Propagatable Latest where
  overloaded end start = not $ validInterval ( Interval start end )
  handedIndex nbTasks i = nbTasks - 1 - i
  inHandedOrder GreaterThan = True
  inHandedOrder _           = False
  propagateLeafChange tree@(Tree { treeVector }) val taskData taskIndex = do
    rankLCT <- ranks ( view ( _ranking @Latest @Outer ) taskData ) `unsafeIndex` taskIndex
    let
      nbNodes, leafIndex :: Int
      nbNodes = Boxed.MVector.length treeVector
      leafIndex = nbNodes - 1 - rankLCT
    propagateChangeFromLeaf tree val leafIndex

---------------------------------------------------------------------------------------------------
-- Node data that can be propagated through task trees.

-- | Parameter to model both non-coloured and coloured task trees.
data Parameter
  = Normal
  | MaybeLabelled Type

-- | `Apply` type family for higher-kinded data definition.
type family Apply ( p :: Parameter ) ( a :: Type ) :: Type where
  Apply Normal            t = t
  Apply (MaybeLabelled l) t = Maybe (Arg t l)

---------------------------------------------
-- Simple task tree.

-- | Estimation of earliest completion time / latest start time.
data DurationInfo p h t
  = DurationInfo
  { subsetInnerTime :: !(Apply p (Endpoint (HandedTime h t))) -- Estimated earliest completion time / latest start time.
  , totalDuration   :: !(Apply p (Delta t))
  }

type BaseDurationInfo = DurationInfo Normal

deriving stock instance   Eq t         => Eq ( DurationInfo Normal            h t )
deriving stock instance ( Eq t, Eq l ) => Eq ( DurationInfo (MaybeLabelled l) h t )
deriving stock instance ( Show t, Show ( HandedTime h t )         ) => Show ( DurationInfo Normal              h t )
deriving stock instance ( Show t, Show ( HandedTime h t ), Show l ) => Show ( DurationInfo ( MaybeLabelled l ) h t )

---------------------------------------------
-- Task tree with transition times.

-- | Estimation of earliest completion time / latest start time, with added transition times.
-- Assumes there is a fixed transition time between any two distinct transition atoms.
data TTDurationInfo p h t a
  = TTDurationInfo
  { durationInfo    :: !(DurationInfo p h t)
  , transitionAtoms :: !(Set a)
  }

type BaseTTDurationInfo = TTDurationInfo Normal

deriving stock instance ( Eq t, Eq a )       => Eq ( TTDurationInfo Normal            h t a )
deriving stock instance ( Eq t, Eq a, Eq l ) => Eq ( TTDurationInfo (MaybeLabelled l) h t a )
deriving stock instance ( Show t, Show ( HandedTime h t ), Show a         ) => Show ( TTDurationInfo Normal              h t a )
deriving stock instance ( Show t, Show ( HandedTime h t ), Show a, Show l ) => Show ( TTDurationInfo ( MaybeLabelled l ) h t a )

---------------------------------------------
-- Coloured task tree.

-- | Estimate of earliest completion time / latest start time, with extra tasks (coloured tasks).
data DurationExtraInfo h t r
  = DurationExtraInfo
  {  baseDurationInfo :: !(DurationInfo Normal            h t)
  , extraDurationInfo :: !(DurationInfo (MaybeLabelled r) h t)
  }
  deriving stock Eq
deriving stock instance ( Show t, Show (HandedTime h t ), Show r ) => Show ( DurationExtraInfo h t r )

---------------------------------------------
-- Coloured task tree with transition times.

-- | Estimate of earliest completion time / latest start time, with extra tasks and transition times.
data TTDurationExtraInfo h t a r
  = TTDurationExtraInfo
  {  baseTTDurationInfo :: !(TTDurationInfo Normal            h t a)
  , extraTTDurationInfo :: !(TTDurationInfo (MaybeLabelled r) h t a)
  }
  deriving stock Eq
deriving stock instance ( Show t, Show (HandedTime h t ), Show a, Show r ) => Show ( TTDurationExtraInfo h t a r )


---------------------------------------------------------------------------------------------------
-- Methods for propagating the different types of node information defined above.


---------------------------------------------
-- Simple task tree.

instance ( Lattice ( Endpoint ( HandedTime h t ) )
         , Act ( Delta t ) ( HandedTime h t )
         )
      => Semigroup ( DurationInfo Normal h t )
      where
  (<>)
    ( DurationInfo { subsetInnerTime = timeL, totalDuration = durL } )
    ( DurationInfo { subsetInnerTime = timeR, totalDuration = durR } ) 
    = DurationInfo
      { subsetInnerTime = ( durR • timeL ) /\ timeR
      -- ect = max ( ectL + durR ) ectR
      -- lst = min ( lstL - durR ) lstR
      , totalDuration   = durL <> durR
      }

instance ( Num t, BoundedLattice ( Endpoint ( HandedTime h t ) ), Act ( Delta t ) ( HandedTime h t ) )
      => Monoid ( DurationInfo Normal h t )
      where
  mempty = DurationInfo { subsetInnerTime = top, totalDuration = mempty }

---------------------------------------------
-- Task tree with transition times.

class TransitionCost a t where
  transitionCost :: Delta t

minTransitionCost :: forall a t. ( Num t, TransitionCost a t ) => Int -> Delta t
minTransitionCost i
  | i <= 1
  = mempty
  | otherwise
  = stimes ( i - 1 ) ( transitionCost @a )

instance ( Num t, Ord a
         , TransitionCost a t
         , Lattice ( Endpoint ( HandedTime h t ) )
         , Act ( Delta t ) ( HandedTime h t )
         )
      => Semigroup ( TTDurationInfo Normal h t a )
      where
  (<>)
    ( TTDurationInfo
      { durationInfo = DurationInfo { subsetInnerTime = timeL, totalDuration = durL }
      , transitionAtoms = atomsL
      }
    )
    ( TTDurationInfo
      { durationInfo = DurationInfo { subsetInnerTime = timeR, totalDuration = durR }
      , transitionAtoms = atomsR
      }
    ) 
    = TTDurationInfo
      { durationInfo =
        DurationInfo
          { subsetInnerTime = ( ( durR <> minTransitionCost @a nbAtoms ) • timeL ) /\ timeR
          -- ect = max ( ectL + durR + tt ) ectR
          -- lst = min ( lstL - durR - tt ) lstR
          , totalDuration   = durL <> durR
          }
      , transitionAtoms = atomsL <> atomsR
      }
    where
      nbAtoms :: Int
      nbAtoms
        | not ( null atomsL ) && Set.disjoint atomsL atomsR
        = length atomsR + 1
        | otherwise
        = length atomsR

instance ( Num t, Ord a
         , TransitionCost a t
         , BoundedLattice ( Endpoint ( HandedTime h t ) )
         , Act ( Delta t ) ( HandedTime h t )
         )
      => Monoid ( TTDurationInfo Normal h t a )
      where
  mempty = TTDurationInfo { durationInfo = mempty, transitionAtoms = mempty }

---------------------------------------------
-- Coloured task tree.

foldrJusts :: forall a. ( a -> a -> a ) -> [ Maybe a ] -> Maybe a
foldrJusts _ [] = Nothing
foldrJusts f ( Nothing : ms ) = foldrJusts f ms
foldrJusts f ( Just a  : ms ) = Just ( go a ms )
  where
    go :: a -> [ Maybe a ] -> a
    go x [] = x
    go x ( Nothing : ys ) = go x ys
    go x ( Just y  : ys ) = go ( f x y ) ys

instance ( Num t, Ord t
         , TotallyOrderedLattice ( Endpoint ( HandedTime h t ) )
         , Act ( Delta t ) ( HandedTime h t )
         )
      => Semigroup ( DurationExtraInfo h t r )
      where
  (<>)
    ( DurationExtraInfo
      { baseDurationInfo  = baseInfoL@DurationInfo { totalDuration =  baseDurationL, subsetInnerTime =  baseTimeL }
      , extraDurationInfo = mbExtraInfoL
      }
    )
    ( DurationExtraInfo
      { baseDurationInfo  = baseInfoR@DurationInfo { totalDuration =  baseDurationR }
      , extraDurationInfo = mbExtraInfoR
      }
    )
    = DurationExtraInfo
    {  baseDurationInfo = baseInfoL <> baseInfoR
    , extraDurationInfo =
        DurationInfo
          { subsetInnerTime = mbInnerTimeAndResp
          , totalDuration   = mbDurationAndResp
          }
    }
      where
        -- Total duration allowing one extra (coloured) task (responsibility recorded).
        mbDurationAndResp :: Maybe ( Arg ( Delta t ) r )
        mbDurationAndResp =
          foldrJusts ( coerce ( (<>) @( ArgMax ( Delta t ) r ) ) )
            [ totalDuration mbExtraInfoL <&> \ ( Arg extraDurationL extraDurationL_resp ) ->
              Arg ( extraDurationL <>  baseDurationR ) extraDurationL_resp
            , totalDuration mbExtraInfoR <&> \ ( Arg extraDurationR extraDurationR_resp ) ->
              Arg (  baseDurationL <> extraDurationR ) extraDurationR_resp
            ]
        -- Estimated inner time allowing one extra (coloured) task (responsibility recorded).
        mbInnerTimeAndResp :: Maybe ( Arg ( Endpoint ( HandedTime h t ) ) r )
        mbInnerTimeAndResp =
          foldrJusts (/.\)
            [ subsetInnerTime mbExtraInfoR
            , subsetInnerTime mbExtraInfoL <&> \ ( Arg extraInnerL    extraInnerL_resp ) ->
                Arg (  baseDurationR • extraInnerL )    extraInnerL_resp
            , totalDuration   mbExtraInfoR <&> \ ( Arg extraDurationR extraDurationR_resp ) ->
                Arg ( extraDurationR •   baseTimeL ) extraDurationR_resp
            ]
        -- ect* = maximum [ ectR*, ectL* + durR, ectL + durR* ]
        -- lst* = minimum [ lstR*, lstL* - durR, lstL - durR* ]

instance ( Num t, Ord t
         , BoundedLattice ( Endpoint ( HandedTime h t ) )
         , TotallyOrderedLattice ( Endpoint ( HandedTime h t ) )
         , Act ( Delta t ) ( HandedTime h t ) )
      => Monoid ( DurationExtraInfo h t r )
      where
  mempty =
    DurationExtraInfo
      { baseDurationInfo = mempty
      , extraDurationInfo =
        DurationInfo 
          { subsetInnerTime = Nothing
          , totalDuration   = Nothing
          }
      }

---------------------------------------------
-- Coloured task tree with transition times.

instance ( Num t, Ord t, Ord a
         , TransitionCost a t
         , TotallyOrderedLattice ( Endpoint ( HandedTime h t ) )
         , Act ( Delta t ) ( HandedTime h t )
         )
      => Semigroup ( TTDurationExtraInfo h t a r )
      where
  (<>)
    ( TTDurationExtraInfo
      { baseTTDurationInfo = baseInfoL@
          TTDurationInfo
            {    durationInfo = DurationInfo { totalDuration =  baseDurationL, subsetInnerTime =  baseTimeL }
            , transitionAtoms = baseAtomsL
            }
      , extraTTDurationInfo =
          TTDurationInfo
            {    durationInfo = mbExtraInfoL
            , transitionAtoms = extraAtomsL 
            }
      }
    )
    ( TTDurationExtraInfo
      { baseTTDurationInfo = baseInfoR@
          TTDurationInfo
            {    durationInfo = DurationInfo { totalDuration =  baseDurationR }
            , transitionAtoms = baseAtomsR
            }
      , extraTTDurationInfo =
          TTDurationInfo
            {    durationInfo = mbExtraInfoR
            , transitionAtoms = extraAtomsR
            }
      }
    )
    = TTDurationExtraInfo
    {  baseTTDurationInfo = baseInfoL <> baseInfoR
    , extraTTDurationInfo =
      TTDurationInfo
        { durationInfo =
          DurationInfo
            { totalDuration   = mbDurationAndResp
            , subsetInnerTime = mbInnerTimeAndResp
            }
        -- Transition atoms are kept track of differently from the paper:
        -- ONLY grey information is tabulated in this field
        -- for the full estimation of minimum transition times, a calculation is done involving the base transition info too
        , transitionAtoms = extraAtomsL <> extraAtomsR
        }
    }
    where
      mbDurationAndResp :: Maybe ( Arg ( Delta t ) r )
      mbDurationAndResp = 
        foldrJusts ( coerce ( (<>) @( ArgMax ( Delta t ) r ) ) )
          [ totalDuration mbExtraInfoL <&> \ ( Arg extraDurationL extraDurationL_resp ) ->
            Arg ( extraDurationL <>  baseDurationR ) extraDurationL_resp
          , totalDuration mbExtraInfoR <&> \ ( Arg extraDurationR extraDurationR_resp ) ->
            Arg (  baseDurationL <> extraDurationR ) extraDurationR_resp
          ]
      mbInnerTimeAndResp :: Maybe ( Arg ( Endpoint ( HandedTime h t ) ) r )
      mbInnerTimeAndResp =
        foldrJusts (/.\)
          [ subsetInnerTime mbExtraInfoR
          , subsetInnerTime mbExtraInfoL <&> \ ( Arg extraInnerL extraInnerL_resp ) ->
              Arg ( (  baseDurationR <> minTransitionCost @a baseNbAtoms         ) • extraInnerL )    extraInnerL_resp
          , totalDuration   mbExtraInfoR <&> \ ( Arg extraDurationR extraDurationR_resp ) ->
              Arg ( ( extraDurationR <> minTransitionCost @a baseAndExtraNbAtoms ) •   baseTimeL ) extraDurationR_resp
          ]
        -- ect* = maximum [ ectR*, ectL* + durR + tt, ectL + durR* + tt* ]
        -- lst* = minimum [ lstR*, lstL* - durR - tt, lstL - durR* - tt* ]
      nbAtomsR, baseNbAtoms, baseAndExtraNbAtoms :: Int
      nbAtomsR = length baseAtomsR
      ( baseNbAtoms, baseAndExtraNbAtoms ) =
        case
          ( not ( null baseAtomsL ) || Set.disjoint baseAtomsL baseAtomsR
          , Set.disjoint extraAtomsR baseAtomsR
          , Set.disjoint baseAtomsL extraAtomsR
          )
        of
          ( False, False, _     ) -> ( nbAtomsR    , nbAtomsR     )
          ( False, True , _     ) -> ( nbAtomsR    , nbAtomsR + 1 )
          ( True , False, _     ) -> ( nbAtomsR + 1, nbAtomsR + 1 )
          ( True , True , False ) -> ( nbAtomsR + 1, nbAtomsR + 1 )
          ( True , True , True  ) -> ( nbAtomsR + 1, nbAtomsR + 2 )

instance ( Num t, Ord t, Ord a
         , TransitionCost a t
         , BoundedLattice ( Endpoint ( HandedTime h t ) )
         , TotallyOrderedLattice ( Endpoint ( HandedTime h t ) )
         , Act ( Delta t ) ( HandedTime h t )
         )
      => Monoid ( TTDurationExtraInfo h t a r )
      where
  mempty = TTDurationExtraInfo
    { baseTTDurationInfo = mempty
    , extraTTDurationInfo =
      TTDurationInfo
        { durationInfo =
          DurationInfo 
            { subsetInnerTime = Nothing
            , totalDuration   = Nothing
            }
        , transitionAtoms = Set.empty
        }
    }
