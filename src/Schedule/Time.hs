{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingVia                #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TypeFamilies               #-}

module Schedule.Time
  ( Time(..), Delta(..)
  , Handedness(..), OtherHandedness
  , HandedTime(.., EarliestTime, LatestTime)
  , EarliestTime, LatestTime
  )
  where

-- base
import Data.Monoid
  ( Sum(..) )
import Data.Semigroup
  ( Max(..), Min(..) )
import GHC.Generics
  ( Generic )

-- acts
import Data.Act
  ( Act(..), Torsor )

-- deepseq
import Control.DeepSeq
  ( NFData )

-- groups
import Data.Group
  ( Group(..) )

-------------------------------------------------------------------------------

newtype Time t = Time { getTime :: t }
  deriving stock   Show
  deriving newtype ( Eq, Ord, Enum, Bounded, NFData )
  deriving ( Act ( Delta t ), Torsor ( Delta t ) )
    via ( Delta t )

newtype Delta t = Delta { getDelta :: t }
  deriving stock    Show
  deriving newtype ( Eq, Ord, NFData )
  deriving ( Semigroup, Monoid, Group )
    via ( Sum t )

data Handedness = Earliest | Latest
  deriving stock    ( Show, Generic )
  deriving anyclass NFData

type family OtherHandedness ( h :: Handedness ) :: Handedness where
  OtherHandedness Earliest = Latest
  OtherHandedness Latest   = Earliest

-- | Earliest time or latest time.
newtype HandedTime ( h :: Handedness ) t = HandedTime { handedTime :: Time t }
  deriving newtype ( Eq, Ord, Bounded, NFData )

instance Show t => Show ( HandedTime Earliest t ) where
  show ( EarliestTime t ) = "EarliestTime " <> show t
instance Show t => Show ( HandedTime Latest t ) where
  show ( LatestTime   t ) = "LatestTime "   <> show t

type EarliestTime = HandedTime Earliest
type LatestTime   = HandedTime Latest
{-# COMPLETE EarliestTime #-}
pattern EarliestTime :: Time t -> HandedTime Earliest t
pattern EarliestTime t = HandedTime t
{-# COMPLETE LatestTime   #-}
pattern LatestTime   :: Time t -> HandedTime Latest   t
pattern LatestTime   t = HandedTime t

deriving via ( Max t ) instance   Ord t              => Semigroup ( HandedTime Earliest t )
deriving via ( Max t ) instance ( Ord t, Bounded t ) => Monoid    ( HandedTime Earliest t )
deriving via ( Min t ) instance   Ord t              => Semigroup ( HandedTime Latest   t )
deriving via ( Min t ) instance ( Ord t, Bounded t ) => Monoid    ( HandedTime Latest   t )

instance Num t => Act ( Delta t ) ( HandedTime Earliest t ) where
  delta • EarliestTime t = EarliestTime ( delta • t )
instance Num t => Act ( Delta t ) ( HandedTime Latest t ) where
  delta • LatestTime   t = LatestTime ( invert delta • t )

{-
class KnownHandedness ( h :: Handedness ) where
  handedness :: Handedness
instance KnownHandedness Earliest where
  handedness = Earliest
instance KnownHandedness Latest where
  handedness = Latest
-}