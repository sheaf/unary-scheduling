{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeApplications           #-}

module Data.Lattice where

-- base
import Data.Coerce
  ( coerce )
import Data.Semigroup
  ( Arg )

-------------------------------------------------------------------------------

class Lattice t where
  (/\) :: t -> t -> t
  (\/) :: t -> t -> t

class Lattice t => BoundedLattice t where
  bottom :: t
  top    :: t

class BoundedLattice t => Heyting t where
  (==>) :: t -> t -> t
  negation   :: t -> t
  negation t = t ==> bottom

instance Lattice Bool where
  (/\) = (&&)
  (\/) = (||)

instance BoundedLattice Bool where
  bottom = False
  top    = True

instance Heyting Bool where
  a ==> b  = not a || b
  negation = not

instance Lattice b => Lattice ( a -> b ) where
  f \/ g = \ x -> f x \/ g x
  f /\ g = \ x -> f x /\ g x
instance BoundedLattice b => BoundedLattice ( a -> b ) where
  bottom = const bottom
  top    = const top
instance Heyting b => Heyting ( a -> b ) where
  f ==> g = \ x -> f x ==> g x
  negation f = \ x -> negation ( f x )

newtype Meet a = Meet { getMeet :: a }
  deriving stock   Show
  deriving newtype ( Eq, Ord, Bounded )

instance Lattice a => Semigroup ( Meet a ) where
  Meet a <> Meet b = Meet ( a /\ b )

instance BoundedLattice a => Monoid ( Meet a ) where
  mempty = Meet top

newtype Join a = Join { getJoin :: a }
  deriving stock   Show
  deriving newtype ( Eq, Ord, Bounded )

instance Lattice a => Semigroup ( Join a ) where
  Join a <> Join b = Join ( a \/ b )

instance BoundedLattice a => Monoid ( Join a ) where
  mempty = Join top

meet, join :: forall a. BoundedLattice a => [a] -> a
meet = coerce ( mconcat @(Meet a) )
join = coerce ( mconcat @(Join a) )

class Lattice t => TotallyOrderedLattice t where
  (/.\) :: Arg t a -> Arg t a -> Arg t a
  (\./) :: Arg t a -> Arg t a -> Arg t a
