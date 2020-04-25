{-# LANGUAGE BlockArguments         #-}
{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE RecordWildCards        #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeSynonymInstances   #-}

module Schedule.Monad
  ( MonadSchedule
  , ScheduleMonad, runScheduleMonad
  , SchedulableData
  ) where

-- base
import Control.Category
  ( (>>>) )
import Control.Monad.ST
  ( ST, runST )
import Data.Function
  ( (&) )
import Data.Kind
  ( Constraint )

-- bitvec
import Data.Bit
  ( Bit (..) )

-- generic-lens
import Data.Generics.Product.Fields
  ( field )

-- mtl
import Control.Monad.Except
  ( MonadError )
import Control.Monad.Reader
  ( MonadReader )
import Control.Monad.State
  ( MonadState )

-- text
import Data.Text
  ( Text )

-- transformers
import Control.Monad.Trans.Except
  ( ExceptT, runExceptT )
import Control.Monad.Trans.Reader
  ( ReaderT, runReaderT )
import Control.Monad.Trans.State.Strict
  ( StateT , runStateT )

-- transformers-base
import Control.Monad.Base
  ( MonadBase )

-- vector
import qualified Data.Vector as Boxed
  ( Vector )
import qualified Data.Vector as Boxed.Vector
  ( (!), fromList, length, unzip, unsafeThaw )

-- unary-scheduling
import Data.Vector.PhaseTransition
  ( thaw, unsafeFreeze )
import Data.Vector.Ranking
  ( rankOn )
import Schedule.Constraint
  ( Constraints )
import Schedule.Ordering
  ( Order(..), newOrderingMatrix )
import Schedule.Task
  ( Task(..), Tasks(..), TaskInfos(..)
  , MutableTasks, ImmutableTasks
  , est, lct, lst, ect
  )
import Schedule.Tree
  ( Propagatable ( overloaded ) )

-------------------------------------------------------------------------------

type ScheduleMonad s task t =
  ( ReaderT ( MutableTasks s task t )
    ( ExceptT Text
      ( StateT ( Constraints t )
        ( ST s )
      )
    )
  )

type MonadSchedule s task t m =
  ( ( MonadReader ( MutableTasks s task t ) m
    , MonadState  ( Constraints t ) m
    , MonadError  Text m
    , MonadBase (ST s) m
    ) :: Constraint
  )

class    ( Num t, Ord t, Bounded t )
      => SchedulableData taskData task t | taskData -> task t
      where
  initialTaskData :: taskData -> ST s ( MutableTasks s task t )

instance ( Num t, Ord t, Bounded t )
      => SchedulableData ( ImmutableTasks task t ) task t
      where
  initialTaskData = field @"taskInfos" thaw

instance ( Num t, Ord t, Bounded t )
      => SchedulableData [ ( Task task t, Text ) ] task t
      where
  initialTaskData taskList = do
    let
      numberedTasks :: [ ( Task task t, Int ) ]
      numberedTasks = zipWith ( \ ( t, _ ) i -> ( t, i ) ) taskList [0..]
    let
      immutableTasks :: Boxed.Vector ( Task task t )
      taskNames :: Boxed.Vector Text
      ( immutableTasks, taskNames ) = Boxed.Vector.unzip $ Boxed.Vector.fromList taskList
      n :: Int
      n = Boxed.Vector.length taskNames

      order :: Int -> Int -> Order
      order i j =
        let
          tk_i, tk_j :: Task task t
          tk_i = immutableTasks Boxed.Vector.! i
          tk_j = immutableTasks Boxed.Vector.! j
        in Order ( Bit ( overloaded ( est tk_j ) ( lst tk_i ) ), Bit ( overloaded ( est tk_i ) ( lst tk_j ) ) )
    tasks <- Boxed.Vector.unsafeThaw immutableTasks
    rankingEST <- rankOn est numberedTasks
    rankingLCT <- rankOn lct numberedTasks
    rankingLST <- rankOn lst numberedTasks
    rankingECT <- rankOn ect numberedTasks
    orderings  <- newOrderingMatrix n order
    let
      taskInfos = TaskInfos {..}
    pure ( Tasks { .. } )

runScheduleMonad
  :: forall task t taskData a
  .  ( Num t, Ord t, Bounded t
     , SchedulableData taskData task t
     )
  => taskData
  -> ( forall s. ScheduleMonad s task t a )
  -> ( ImmutableTasks task t, ( Either Text a, Constraints t ) )
runScheduleMonad givenTasks ma = runST do
  mutableTaskData <- initialTaskData givenTasks
  res <- ma & ( ( `runReaderT` mutableTaskData ) >>> runExceptT >>> ( `runStateT` mempty ) )
  finalTaskData <- field @"taskInfos" unsafeFreeze mutableTaskData
  pure ( finalTaskData, res )
