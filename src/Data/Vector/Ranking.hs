{-# LANGUAGE ScopedTypeVariables   #-}

module Data.Vector.Ranking
  ( Ranking(..)
  , rankOn
  , reorderAfterIncrease, reorderAfterDecrease
  )
  where

-- base
import Control.Arrow
  ( first )
import Control.Monad
  ( when )
import Data.List
  ( sort )
import GHC.Generics
  ( Generic )

-- deepseq
import Control.DeepSeq
  ( NFData )

-- generic-lens
import Data.Generics.Product.Constraints
  ( HasConstraints
    ( constraints )
  )

-- memory-arena
import Memory.Vector
  ( Freeze(..), Thaw(..) )

-- primitive
import Control.Monad.Primitive
  ( PrimMonad(PrimState) )

-- vector
import qualified Data.Vector.Mutable as Boxed
  ( MVector )
import qualified Data.Vector.Mutable as Boxed.Vector
  ( length, unsafeRead )
import qualified Data.Vector.Unboxed as Unboxed.Vector
  ( fromList, unsafeThaw )
import qualified Data.Vector.Unboxed.Mutable as Unboxed
  ( MVector )
import qualified Data.Vector.Unboxed.Mutable as Unboxed.Vector
  ( unsafeRead )

-------------------------------------------------------------------------------

data Ranking indices
  = Ranking
    { ordered :: !indices
    , ranks   :: !indices
    }
  deriving stock    ( Show, Generic )
  deriving anyclass NFData

instance Freeze m mvec vec => Freeze m ( Ranking mvec ) ( Ranking vec  ) where
  freeze       = constraints @( Freeze m ) freeze
  unsafeFreeze = constraints @( Freeze m ) unsafeFreeze
instance Thaw   m vec mvec => Thaw   m ( Ranking vec  ) ( Ranking mvec ) where
  thaw         = constraints @( Thaw   m ) thaw
  unsafeThaw   = constraints @( Thaw   m ) unsafeThaw

-------------------------------------------------------------------------------

rankOn
  :: ( Ord o, PrimMonad m, PrimState m ~ s )
  => ( a -> o )
  -> [ ( a, Int ) ]
  -> m ( Ranking ( Unboxed.MVector s Int ) )
rankOn f as = do
  let sorted = fmap snd . sort . fmap ( first f ) $ as
  ordered <- Unboxed.Vector.unsafeThaw ( Unboxed.Vector.fromList sorted )
  let ranked = fmap snd . sort $ zip sorted [0..]
  ranks   <- Unboxed.Vector.unsafeThaw ( Unboxed.Vector.fromList ranked )
  pure ( Ranking { ordered, ranks } )

-- | Re-sort a ranking after the key of a single element has increased
-- (resp. decreased), restoring the sorted invariant by adjacent swaps.
reorderAfterIncrease, reorderAfterDecrease
  :: forall m s a o
  .  ( Ord o, PrimMonad m, PrimState m ~ s )
  => ( Int -> Int -> m () ) -- ^ swap two positions in the 'ordered' permutation
  -> ( Int -> Int -> m () ) -- ^ swap two positions in the 'ranks'   permutation
  -> Boxed.MVector s a
  -> Ranking ( Unboxed.MVector s Int )
  -> ( a -> o )
  -> Int
  -> m ()

reorderAfterIncrease swapOrdered swapRanks allTasks ( Ranking { ordered, ranks } ) f i = do
  r <- ranks `Unboxed.Vector.unsafeRead` i
  when ( r + 1 < lg ) do
    o <- f <$> allTasks `Boxed.Vector.unsafeRead` i
    go o r
  where
    lg :: Int
    lg = Boxed.Vector.length allTasks
    go :: o -> Int -> m ()
    go o r = do
      let
        r' = r + 1
      i' <- ordered `Unboxed.Vector.unsafeRead` r'
      o' <- f <$> allTasks `Boxed.Vector.unsafeRead` i'
      when ( o > o' ) do
        swapOrdered r r'
        swapRanks   i i'
        when ( r' + 1 < lg ) do
          go o r'

reorderAfterDecrease swapOrdered swapRanks allTasks ( Ranking { ordered, ranks } ) f i = do
  r <- ranks `Unboxed.Vector.unsafeRead` i
  when ( r > 0 ) do
    o <- f <$> allTasks `Boxed.Vector.unsafeRead` i
    go o r
  where
    go :: o -> Int -> m ()
    go o r = do
      let
        r' = r - 1
      i' <- ordered `Unboxed.Vector.unsafeRead` r'
      o' <- f <$> allTasks `Boxed.Vector.unsafeRead` i'
      when ( o < o' ) do
        swapOrdered r r'
        swapRanks   i i'
        when ( r' > 0 ) do
          go o r'
