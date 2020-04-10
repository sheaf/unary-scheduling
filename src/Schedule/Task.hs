{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TypeApplications      #-}

module Schedule.Task
  ( Task(..), Tasks(..)
  , Ranking(..), TaskInfos(..)
  , MutableTasks, ImmutableTasks
  , est, lct, lst, ect
  , freezeTaskInfos, unsafeFreezeTaskInfos
  , thawTaskInfos, unsafeThawTaskInfos
  , Limit(..), PickEndPoint(..)
  ) where

-- base
import Control.Monad.ST
  ( ST )
import GHC.Generics
  ( Generic )

-- acts
import Data.Act
  ( Act(..) )

-- containers
import Data.Sequence
  ( Seq
    ( (:<|), (:|>) )
  )

-- generic-lens
import Data.Generics.Product.Constraints
  ( HasConstraints
    ( constraints )
  )

-- text
import Data.Text
  ( Text )

-- vector
import qualified Data.Vector as Boxed
  ( Vector )
import Data.Vector.Generic
  ( Mutable )
import qualified Data.Vector.Generic as Generic.Vector
  ( Vector )
import qualified Data.Vector.Mutable as Boxed
  ( MVector )
import qualified Data.Vector.Unboxed as Unboxed
  ( Vector )
import qualified Data.Vector.Unboxed.Mutable as Unboxed
  ( MVector )

-- unary-scheduling
import Data.Lattice
  ( BoundedLattice(bottom) )
import Data.Vector.PhaseTransition
  ( Freeze
     ( freeze, unsafeFreeze )
  , Thaw
     ( thaw, unsafeThaw )
  )
import Data.Vector.Ranking
  ( Ranking(..) )
import Schedule.Interval
  ( EndPoint(..), Interval(..)
  , Intervals
    ( Intervals )
  )
import Schedule.Time
  ( Delta
  , Handedness(Earliest, Latest)
  , HandedTime
  , EarliestTime, LatestTime
  )

-------------------------------------------------------------------------------

data Task task t
  = Task
  { taskAvailability :: !(Intervals t)
  , taskDuration     :: !(Delta t)
  , taskInfo         :: !task
  }
  deriving stock ( Show, Eq )

data Tasks tvec ivec task t
  = Tasks
    { taskNames :: Boxed.Vector Text
    , taskInfos :: TaskInfos ( tvec (Task task t) ) ( ivec Int )
    }
  deriving stock Generic

deriving stock instance
    ( Show task, Show t, Show (tvec (Task task t)), Show ( ivec Int ) )
  => Show ( Tasks tvec ivec task t )

{-
instance ( Show task, Show t ) => Show ( Tasks Boxed.Vector ivec task t ) where
  show ( Tasks { taskNames, taskInfos } ) = foldMap showTask [ 0 .. nbTasks - 1 ]
    where
      nbTasks :: Int
      nbTasks = Boxed.Vector.length taskNames
      showTask :: Int -> String
      showTask i =
        "Task named " <> Text.unpack ( taskNames Boxed.Vector.! i ) <> ":\n"
        <> show ( tasks taskInfos Boxed.Vector.! i ) <> "\n"
-}

data TaskInfos tasks indices = TaskInfos
  { tasks      :: !tasks             -- tasks
  , rankingEST :: !(Ranking indices) -- task rankings according to earliest start      time
  , rankingLCT :: !(Ranking indices) -- task rankings according to latest   completion time
  , rankingLST :: !(Ranking indices) -- task rankings according to latest   start      time
  , rankingECT :: !(Ranking indices) -- task rankings according to earliest completion time
  }
  deriving stock ( Show, Generic )

type MutableTasks s = Tasks ( Boxed.MVector s ) ( Unboxed.MVector s ) 
type ImmutableTasks = Tasks   Boxed.Vector        Unboxed.Vector

-- | Earliest start time.
est :: ( Ord t, Bounded t ) => Task task t -> EndPoint (EarliestTime t)
est ( Task { taskAvailability = Intervals ( ival :<| _ ) } ) = start ival
est _                                                        = bottom

-- | Latest completion time.
lct :: ( Ord t, Bounded t ) => Task task t -> EndPoint (LatestTime t)
lct ( Task { taskAvailability = Intervals ( _ :|> ival ) } ) = end ival
lct _                                                        = bottom

-- | Latest start time.
lst :: ( Num t, Ord t, Bounded t ) => Task task t -> EndPoint (LatestTime t)
lst ( task@( Task { taskDuration = delta } ) ) = delta • lct task -- recall: action of delta on 'LatestTime' involves an inversion

-- | Earliest completion time.
ect :: ( Num t, Ord t, Bounded t ) => Task task t -> EndPoint (EarliestTime t)
ect ( task@( Task { taskDuration = delta } ) ) = delta • est task

freezeTaskInfos, unsafeFreezeTaskInfos
  :: forall s task i tvec ivec
  .  ( Generic.Vector.Vector tvec task, Generic.Vector.Vector ivec i )
  => TaskInfos ( Mutable tvec s task ) ( Mutable ivec s i )
  -> ST s ( TaskInfos ( tvec task ) ( ivec i ) )
freezeTaskInfos       = constraints @( Freeze (ST s) ) freeze
unsafeFreezeTaskInfos = constraints @( Freeze (ST s) ) unsafeFreeze

thawTaskInfos, unsafeThawTaskInfos
  :: forall s task i tvec ivec
  .  ( Generic.Vector.Vector tvec task, Generic.Vector.Vector ivec i )
  => TaskInfos ( tvec task ) ( ivec i )
  -> ST s ( TaskInfos ( Mutable tvec s task ) ( Mutable ivec s i ) )
thawTaskInfos       = constraints @( Thaw (ST s) ) thaw
unsafeThawTaskInfos = constraints @( Thaw (ST s) ) unsafeThaw

-------------------------------------------------------------------------------

data Limit = Outer | Inner
  deriving stock Show

class PickEndPoint ( h :: Handedness ) ( e :: Limit ) where
  pickEndPoint :: ( Num t, Ord t, Bounded t ) => Task task t -> EndPoint (HandedTime h t)
  pickRanking  :: TaskInfos tasks indices -> Ranking indices

instance PickEndPoint Earliest Outer where
  pickEndPoint = est
  pickRanking  = rankingEST
instance PickEndPoint Earliest Inner where
  pickEndPoint = ect
  pickRanking  = rankingECT
instance PickEndPoint Latest   Outer where
  pickEndPoint = lct
  pickRanking  = rankingLCT
instance PickEndPoint Latest   Inner where
  pickEndPoint = lst
  pickRanking  = rankingLST
