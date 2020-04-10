{-# LANGUAGE BlockArguments      #-}
{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

module Schedule.Monad
  ( MonadSchedule
  , ScheduleMonad, runScheduleMonad
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

-- generic-lens
import Data.Generics.Product.Fields
  ( field )

-- mtl
import Control.Monad.Except
  ( MonadError )
import Control.Monad.Reader
  ( MonadReader )
import Control.Monad.Writer
  ( MonadWriter )

-- text
import Data.Text
  ( Text )

-- transformers
import Control.Monad.Trans.Except
  ( ExceptT, runExceptT )
import Control.Monad.Trans.Reader
  ( ReaderT, runReaderT )
import Control.Monad.Trans.Writer.CPS
  ( WriterT, runWriterT )

-- transformers-base
import Control.Monad.Base
  ( MonadBase )

-- vector
import qualified Data.Vector as Boxed.Vector
  ( fromList, unzip, unsafeThaw )

-- unary-scheduling
import Data.Vector.Ranking
  ( rankOn )
import Schedule.Constraint
  ( Constraints )
import Schedule.Task
  ( Task(..), Tasks(..), TaskInfos(..)
  , MutableTasks, ImmutableTasks
  , thawTaskInfos, unsafeFreezeTaskInfos
  , est, lct, lst, ect
  )

-------------------------------------------------------------------------------

type ScheduleMonad s task t =
  ( ReaderT ( MutableTasks s task t )
    ( ExceptT Text
      ( WriterT ( Constraints t )
        ( ST s )
      )
    )
  )

type MonadSchedule s task t m =
  ( ( MonadReader ( MutableTasks s task t ) m
    , MonadWriter ( Constraints t ) m
    , MonadError  Text m
    , MonadBase (ST s) m
    ) :: Constraint
  )

runScheduleMonad
  :: forall task t a
  .  ( Num t, Ord t, Bounded t )
  => ( Either [ ( Task task t, Text ) ] ( ImmutableTasks task t ) )
  -> ( forall s. ScheduleMonad s task t a )
  -> ( ImmutableTasks task t, ( Either Text a, Constraints t ) )
runScheduleMonad givenTasks ma = runST do

  mutableTaskData <- case givenTasks of
    Left taskList -> do
      let
        numberedTasks :: [ ( Task task t, Int ) ]
        numberedTasks = zipWith ( \ ( t, _ ) i -> ( t, i ) ) taskList [0..]
      let ( immutableTasks, taskNames ) = Boxed.Vector.unzip $ Boxed.Vector.fromList taskList
      tasks <- Boxed.Vector.unsafeThaw immutableTasks
      rankingEST <- rankOn est numberedTasks
      rankingLCT <- rankOn lct numberedTasks
      rankingLST <- rankOn lst numberedTasks
      rankingECT <- rankOn ect numberedTasks
      let
        taskInfos = TaskInfos {..}
      pure ( Tasks { .. } )
    Right immutableTaskData ->
      field @"taskInfos" thawTaskInfos immutableTaskData

  res <- ma & ( ( `runReaderT` mutableTaskData ) >>> runExceptT >>> runWriterT )
  finalTaskData <- field @"taskInfos" unsafeFreezeTaskInfos mutableTaskData
  pure ( finalTaskData, res )
