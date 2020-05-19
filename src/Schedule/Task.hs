{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE DeriveAnyClass         #-}
{-# LANGUAGE DeriveGeneric          #-}
{-# LANGUAGE DerivingStrategies     #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE QuantifiedConstraints  #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE StandaloneDeriving     #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
 
module Schedule.Task
  ( Task(..)
  , TaskInfos(..)
  , MutableTaskInfos, ImmutableTaskInfos
  , summariseTasks
  , est, lct, lst, ect
  , Limit(..), PickEndpoint(..)
  ) where

-- base
import GHC.Generics
  ( Generic )
import GHC.TypeLits
  ( Symbol )

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
import Data.GenericLens.Internal
  ( Lens' )
import Data.Generics.Product.Constraints
  ( HasConstraints
      ( constraints )
  )
import Data.Generics.Product.Fields
  ( HasField'
      ( field' )
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
import qualified Data.Vector.Generic as Generic.Vector
  ( Mutable )
import qualified Data.Vector.Mutable as Boxed
  ( MVector )
import qualified Data.Vector.Unboxed as Vector
  ( Unbox )
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
  ( Endpoint(..), Interval(..)
  , Intervals
    ( Intervals )
  )
import Schedule.Ordering
  ( OrderingMatrix )
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
est :: ( Ord t, Bounded t ) => Task task t -> Endpoint ( EarliestTime t )
est ( Task { taskAvailability = Intervals ( ival :<| _ ) } ) = start ival
est _                                                        = bottom

-- | Latest completion time.
lct :: ( Ord t, Bounded t ) => Task task t -> Endpoint ( LatestTime t )
lct ( Task { taskAvailability = Intervals ( _ :|> ival ) } ) = end ival
lct _                                                        = bottom

-- | Latest start time.
lst :: ( Num t, Ord t, Bounded t ) => Task task t -> Endpoint ( LatestTime t )
lst ( task@( Task { taskDuration = delta } ) ) = delta • lct task -- recall: action of delta on 'LatestTime' involves an inversion

-- | Earliest completion time.
ect :: ( Num t, Ord t, Bounded t ) => Task task t -> Endpoint ( EarliestTime t )
ect ( task@( Task { taskDuration = delta } ) ) = delta • est task

-- | Quick summary of all the tasks' start and end times.
summariseTasks
  :: forall task t
  .  ( Show task, Show t, Ord t, Bounded t )
  => Boxed.Vector Text
  -> Boxed.Vector ( Task task t )
  -> Text
summariseTasks names tasks =
  foldMap summariseTask [ 0 .. nbTasks - 1 ]
    where
      nbTasks :: Int
      nbTasks = Boxed.Vector.length names
      summariseTask :: Int -> Text
      summariseTask i =
        let
          task :: Task task t
          task = tasks Boxed.Vector.! i
        in
          "Task named " <> names Boxed.Vector.! i <> ":\n"
          <> Text.pack ( show $ est task ) <> " --- " <> Text.pack ( show $ lct task ) <> "\n"

-------------------------------------------------------------------------------

data Limit = Outer | Inner
  deriving stock Show

class PickEndpoint ( h :: Handedness ) ( e :: Limit ) where

  type EndpointRanking h e :: Symbol

  pickEndpoint
    :: ( Num t, Ord t, Bounded t )
    => Task task t
    -> Endpoint ( HandedTime h t )

  _ranking
    :: forall task t bvec uvec
    .  Lens' ( TaskInfos bvec uvec task t ) ( Ranking ( uvec Int ) )

instance PickEndpoint  Earliest Outer where
  type EndpointRanking Earliest Outer = "rankingEST"
  pickEndpoint = est
  _ranking = field' @"rankingEST"
instance PickEndpoint  Earliest Inner where
  type EndpointRanking Earliest Inner = "rankingECT"
  pickEndpoint = ect
  _ranking = field' @"rankingECT"
instance PickEndpoint  Latest   Outer where
  type EndpointRanking Latest   Outer = "rankingLCT"
  pickEndpoint = lct
  _ranking = field' @"rankingLCT"
instance PickEndpoint  Latest   Inner where
  type EndpointRanking Latest   Inner = "rankingLST"
  pickEndpoint = lst
  _ranking = field' @"rankingLST"

-------------------------------------------------------------------------------
-- Tasks, together with additional information such as rankings,
-- for efficient propagation algorithms.

data TaskInfos bvec uvec task t =
  TaskInfos
    { taskNames  :: !(Boxed.Vector Text)   -- ^ Task names.
    , taskAvails :: !(bvec (Task task t))  -- ^ Task availabilities.
    , rankingEST :: !(Ranking (uvec Int))  -- ^ Task rankings according to earliest start      time.
    , rankingLCT :: !(Ranking (uvec Int))  -- ^ Task rankings according to latest   completion time.
    , rankingLST :: !(Ranking (uvec Int))  -- ^ Task rankings according to latest   start      time.
    , rankingECT :: !(Ranking (uvec Int))  -- ^ Task rankings according to earliest completion time.
    , orderings  :: !(OrderingMatrix uvec) -- ^ Precedence graph information.
    }
  deriving stock Generic

deriving stock instance
    ( Show task, Show t
    , forall a.   Show a                   => Show ( bvec a )
    , forall a. ( Show a, Vector.Unbox a ) => Show ( uvec a )
    )
  => Show ( TaskInfos bvec uvec task t )
deriving anyclass instance
    ( NFData task, NFData t
    , forall a.   NFData a                   => NFData ( bvec a )
    , forall a. ( NFData a, Vector.Unbox a ) => NFData ( uvec a )
    )
  => NFData ( TaskInfos bvec uvec task t )

type MutableTaskInfos s =
  TaskInfos
    (   Boxed.MVector s )
    ( Unboxed.MVector s )
type ImmutableTaskInfos =
  TaskInfos
      Boxed.Vector
    Unboxed.Vector

instance {-# OVERLAPPING #-}
     ( PrimMonad m, s ~ PrimState m
     , bvec ~   Boxed.Vector
     , uvec ~ Unboxed.Vector
     , mbvec ~ Generic.Vector.Mutable bvec
     , muvec ~ Generic.Vector.Mutable uvec
     )
  => Freeze m ( TaskInfos ( mbvec s ) ( muvec s ) task t ) ( TaskInfos bvec uvec task t )
  where
  freeze       = constraints @( Freeze m ) freeze
  unsafeFreeze = constraints @( Freeze m ) unsafeFreeze

instance {-# OVERLAPPING #-}
     ( PrimMonad m, s ~ PrimState m
     , bvec ~   Boxed.Vector
     , uvec ~ Unboxed.Vector
     , mbvec ~ Generic.Vector.Mutable bvec
     , muvec ~ Generic.Vector.Mutable uvec
     )
  => Thaw m
        ( TaskInfos bvec uvec task t )
        ( TaskInfos ( mbvec s ) ( muvec s ) task t ) 
  where
  thaw       = constraints @( Thaw m ) thaw
  unsafeThaw = constraints @( Thaw m ) unsafeThaw
