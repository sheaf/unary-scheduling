{-# LANGUAGE BlockArguments        #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}

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
import Control.Monad.ST
  ( ST )
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
  ( unsafeRead, unsafeSwap )

-- unary-scheduling
import Data.Vector.PhaseTransition
  ( Freeze(..), Thaw(..) )

-------------------------------------------------------------------------------

data Ranking indices
  = Ranking
    { ordered :: !indices
    , ranks   :: !indices
    }
  deriving stock    ( Show, Generic )
  deriving anyclass NFData

instance Freeze m mvec vec => Freeze m (Ranking mvec) (Ranking vec) where
  freeze       = constraints @( Freeze m ) freeze
  unsafeFreeze = constraints @( Freeze m ) unsafeFreeze
instance Thaw   m vec mvec => Thaw   m (Ranking vec) (Ranking mvec) where
  thaw         = constraints @( Thaw   m ) thaw
  unsafeThaw   = constraints @( Thaw   m ) unsafeThaw

-------------------------------------------------------------------------------

rankOn
  :: ( Ord o )
  => ( a -> o )
  -> [ ( a, Int ) ]
  -> ST s ( Ranking ( Unboxed.MVector s Int ) )
rankOn f as = do
  let sorted = fmap snd . sort . fmap ( first f ) $ as
  ordered <- Unboxed.Vector.unsafeThaw ( Unboxed.Vector.fromList sorted )
  let ranked = fmap snd . sort $ zip sorted [0..]
  ranks   <- Unboxed.Vector.unsafeThaw ( Unboxed.Vector.fromList ranked )
  pure ( Ranking { ordered, ranks } )

reorderAfterIncrease
  :: forall s a o
  .  ( Ord o )
  => Boxed.MVector s a
  -> Ranking ( Unboxed.MVector s Int )
  -> ( a -> o )
  -> Int
  -> ST s ()
reorderAfterIncrease allTasks ( Ranking { ordered, ranks } ) f i = do
  r <- ranks `Unboxed.Vector.unsafeRead` i
  when ( r + 1 < lg ) do
    o <- f <$> allTasks `Boxed.Vector.unsafeRead` i
    go o r
  where
    lg :: Int
    lg = Boxed.Vector.length allTasks
    go :: o -> Int -> ST s ()
    go o r = do
      let
        r' = r + 1
      i' <- ordered `Unboxed.Vector.unsafeRead` r'
      o' <- f <$> allTasks `Boxed.Vector.unsafeRead` i'
      when ( o > o' ) do
        Unboxed.Vector.unsafeSwap ordered r r'
        Unboxed.Vector.unsafeSwap ranks   i i'
        when ( r' + 1 < lg ) do
          go o r'

reorderAfterDecrease
  :: forall s a o
  .  ( Ord o )
  => Boxed.MVector s a
  -> Ranking ( Unboxed.MVector s Int )
  -> ( a -> o )
  -> Int
  -> ST s ()
reorderAfterDecrease allTasks ( Ranking { ordered, ranks } ) f i = do
  r <- ranks `Unboxed.Vector.unsafeRead` i
  when ( r > 0 ) do
    o <- f <$> allTasks `Boxed.Vector.unsafeRead` i
    go o r
  where
    go :: o -> Int -> ST s ()
    go o r = do
      let
        r' = r - 1
      i' <- ordered `Unboxed.Vector.unsafeRead` r'
      o' <- f <$> allTasks `Boxed.Vector.unsafeRead` i'
      when ( o < o' ) do
        Unboxed.Vector.unsafeSwap ordered r r'
        Unboxed.Vector.unsafeSwap ranks   i i'
        when ( r' > 0 ) do
          go o r'
