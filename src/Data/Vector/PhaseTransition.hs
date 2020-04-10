{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies           #-}

module Data.Vector.PhaseTransition where

-- primitive
import Control.Monad.Primitive
  ( PrimMonad
    ( PrimState )
  )

-- vector
import qualified Data.Vector.Generic as Generic.Vector
  ( Vector
    ( basicLength, basicUnsafeFreeze, basicUnsafeThaw, basicUnsafeCopy )
  , Mutable
  )
import qualified Data.Vector.Generic.Mutable.Base as Generic.MVector
  ( MVector
     ( basicLength, basicUnsafeNew, basicUnsafeCopy )
  )

-------------------------------------------------------------------------------

class PrimMonad m => Freeze m mut immut where
  freeze       :: mut -> m immut
  unsafeFreeze :: mut -> m immut

class PrimMonad m => Thaw m immut mut where
  thaw       :: immut -> m mut
  unsafeThaw :: immut -> m mut

instance ( PrimMonad m
         , Generic.Vector.Vector vec a
         , s ~ PrimState m
         , mvec ~ Generic.Vector.Mutable vec
         )
      => Freeze m ( mvec s a ) ( vec a )
      where
  unsafeFreeze = Generic.Vector.basicUnsafeFreeze
  freeze mvec = do
    copy <- Generic.MVector.basicUnsafeNew ( Generic.MVector.basicLength mvec )
    Generic.MVector.basicUnsafeCopy copy mvec
    unsafeFreeze copy

instance ( PrimMonad m
         , Generic.Vector.Vector vec a
         , s ~ PrimState m
         , mvec ~ Generic.Vector.Mutable vec
         )
      => Thaw m ( vec a ) ( mvec s a )
      where
  unsafeThaw = Generic.Vector.basicUnsafeThaw
  thaw vec = do
    copy <- Generic.MVector.basicUnsafeNew ( Generic.Vector.basicLength vec )
    Generic.Vector.basicUnsafeCopy copy vec
    pure copy
