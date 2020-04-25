{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MonoLocalBinds        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}

module Schedule.Task
  ( Task(..), Tasks(..)
  , summariseTasks
  , Ranking(..), TaskInfos(..)
  , MutableTasks, ImmutableTasks
  , est, lct, lst, ect
  , Limit(..), PickEndPoint(..)
  ) where

-- base
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

-- deepseq
import Control.DeepSeq
  ( NFData )

-- generic-lens
import Data.Generics.Product.Constraints
  ( HasConstraints
    ( constraints )
  )

-- primitive
import Control.Monad.Primitive
  ( PrimMonad
    ( PrimState )
  )

-- text
import Data.Text
  ( Text )
import qualified Data.Text as Text
  ( pack )

-- vector
import qualified Data.Vector as Boxed
  ( Vector )
import qualified Data.Vector as Boxed.Vector
  ( length, (!) )
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
import Schedule.Ordering
  ( Order, OrderingMatrix )
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
  deriving stock    ( Show, Eq, Generic )
  deriving anyclass NFData

-- | Earliest start time.
est :: ( Ord t, Bounded t ) => Task task t -> EndPoint ( EarliestTime t )
est ( Task { taskAvailability = Intervals ( ival :<| _ ) } ) = start ival
est _                                                        = bottom

-- | Latest completion time.
lct :: ( Ord t, Bounded t ) => Task task t -> EndPoint ( LatestTime t )
lct ( Task { taskAvailability = Intervals ( _ :|> ival ) } ) = end ival
lct _                                                        = bottom

-- | Latest start time.
lst :: ( Num t, Ord t, Bounded t ) => Task task t -> EndPoint ( LatestTime t )
lst ( task@( Task { taskDuration = delta } ) ) = delta • lct task -- recall: action of delta on 'LatestTime' involves an inversion

-- | Earliest completion time.
ect :: ( Num t, Ord t, Bounded t ) => Task task t -> EndPoint ( EarliestTime t )
ect ( task@( Task { taskDuration = delta } ) ) = delta • est task

data Tasks tvec ivec task t
  = Tasks
    { taskNames :: Boxed.Vector Text
    , taskInfos :: TaskInfos ( tvec (Task task t) ) ivec
    }
  deriving stock Generic

deriving stock instance
    ( Show task, Show t, Show (tvec (Task task t)), Show ( ivec Int ), Show ( OrderingMatrix ivec ) )
  => Show ( Tasks tvec ivec task t )
deriving anyclass instance
    ( NFData ( tvec ( Task task t ) ), NFData ( ivec Int ), NFData ( ivec Order ) )
  => NFData ( Tasks tvec ivec task t )

-- | Quick summary of all the tasks' start and end times.
summariseTasks
  :: forall task t ivec
  .  ( Show task, Show t, Ord t, Bounded t )
  => Tasks Boxed.Vector ivec task t
  -> Text
summariseTasks ( Tasks { taskNames, taskInfos = TaskInfos { tasks } } ) =
  foldMap summariseTask [ 0 .. nbTasks - 1 ]
    where
      nbTasks :: Int
      nbTasks = Boxed.Vector.length taskNames
      summariseTask :: Int -> Text
      summariseTask i =
        let
          task :: Task task t
          task = tasks Boxed.Vector.! i
        in
          "Task named " <> taskNames Boxed.Vector.! i <> ":\n"
          <> Text.pack ( show $ est task ) <> " --- " <> Text.pack ( show $ lct task ) <> "\n"


type MutableTasks s = Tasks ( Boxed.MVector s ) ( Unboxed.MVector s ) 
type ImmutableTasks = Tasks   Boxed.Vector        Unboxed.Vector

data TaskInfos tasks ivec = TaskInfos
  { tasks      :: !tasks                 -- tasks
  , rankingEST :: !(Ranking (ivec Int))  -- task rankings according to earliest start      time
  , rankingLCT :: !(Ranking (ivec Int))  -- task rankings according to latest   completion time
  , rankingLST :: !(Ranking (ivec Int))  -- task rankings according to latest   start      time
  , rankingECT :: !(Ranking (ivec Int))  -- task rankings according to earliest completion time
  , orderings  :: !(OrderingMatrix ivec) -- precedence graph information
  }
  deriving stock    Generic
deriving stock    instance ( Show tasks, Show ( ivec Int ), Show ( OrderingMatrix ivec ) ) => Show ( TaskInfos tasks ivec )
deriving anyclass instance ( NFData tasks, NFData ( ivec Int ), NFData ( ivec Order ) ) => NFData ( TaskInfos tasks ivec )

instance ( PrimMonad m, s ~ PrimState m
         , Generic.Vector.Vector tvec task, Generic.Vector.Vector ivec Int, Generic.Vector.Vector ivec Order
         , mtvec ~ Mutable tvec
         , mivec ~ Mutable ivec
         )
  => Freeze m ( TaskInfos ( mtvec s task ) ( mivec s ) ) ( TaskInfos ( tvec task ) ivec )
  where
  freeze       = constraints @( Freeze m ) freeze
  unsafeFreeze = constraints @( Freeze m ) unsafeFreeze

instance ( PrimMonad m, s ~ PrimState m
         , Generic.Vector.Vector tvec task, Generic.Vector.Vector ivec Int, Generic.Vector.Vector ivec Order
         , mtvec ~ Mutable tvec
         , mivec ~ Mutable ivec
         )
  => Thaw m ( TaskInfos ( tvec task ) ivec ) ( TaskInfos ( mtvec s task ) ( mivec s ) )
  where
  thaw       = constraints @( Thaw m ) thaw
  unsafeThaw = constraints @( Thaw m ) unsafeThaw

-------------------------------------------------------------------------------

data Limit = Outer | Inner
  deriving stock Show

class PickEndPoint ( h :: Handedness ) ( e :: Limit ) where
  pickEndPoint :: ( Num t, Ord t, Bounded t ) => Task task t -> EndPoint (HandedTime h t)
  pickRanking  :: TaskInfos tasks ivec -> Ranking ( ivec Int )

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
