{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies           #-}

module Data.Vector.Generic.Index
  ( ReadableVector
    ( unsafeIndex )
  )
  where

-- primitive
import Control.Monad.Primitive
  ( PrimMonad
    ( PrimState )
  )

-- vector
import qualified Data.Vector.Generic as Generic
  ( Vector )
import qualified Data.Vector.Generic as Generic.Vector
  ( (!) )
import qualified Data.Vector.Generic.Mutable as Generic
  ( MVector )
import qualified Data.Vector.Generic.Mutable as Generic.MVector
  ( unsafeRead )

-------------------------------------------------------------------------------

class ReadableVector m a vec | vec -> a where
  unsafeIndex :: vec -> Int -> m a

instance {-# OVERLAPPING #-} ( PrimMonad m, s ~ PrimState m, Generic.MVector mvec a )
      => ReadableVector m a ( mvec s a )
      where
  unsafeIndex = Generic.MVector.unsafeRead

instance ( Applicative m, Generic.Vector vec a )
      => ReadableVector m a ( vec a )
      where
  unsafeIndex = ( pure . ) . ( Generic.Vector.! )
