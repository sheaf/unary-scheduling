{-# LANGUAGE BlockArguments      #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

module Schedule.Search where

-- base
import Control.Monad.ST
  ( ST )
import Data.Functor.Const
  ( Const(..) )
import Data.Functor.Identity
  ( Identity(..) )
import Data.List
  ( insert, sort )
import Data.Maybe
  ( mapMaybe, listToMaybe )
import Data.Monoid
  ( Sum(..) )
import Data.Semigroup
  ( Arg(..) )
import GHC.Generics
  ( Generic )

-- acts
import Data.Act
  ( Torsor((-->)) )

-- deepseq
import Control.DeepSeq
  ( NFData )

-- generic-lens
import Data.Generics.Product.Fields
  ( field' )
import Data.GenericLens.Internal
  ( over )

-- mtl
import Control.Monad.Except
  ( MonadError )
import Control.Monad.Reader
  ( MonadReader, ask )
import Control.Monad.State.Strict
  ( MonadState, get, put, modify' )

-- text
import Data.Text
  ( Text )

-- transformers
import Control.Monad.Trans.State.Strict
  ( execState )

-- transformers-base
import Control.Monad.Base
  ( MonadBase ( liftBase ) )

-- vector
import qualified Data.Vector as Boxed
  ( Vector )
import qualified Data.Vector as Boxed.Vector
  ( (!) )
import qualified Data.Vector.Unboxed as Unboxed
  ( Vector )
import qualified Data.Vector.Unboxed as Unboxed.Vector
  ( (!), foldr )

-- unary-scheduling
import Data.Vector.Generic.Index
  ( unsafeIndex )
import Schedule.Constraint
  ( constrainToBefore, constrainToAfter )
import Schedule.Interval
  ( EndPoint(..) )
import Schedule.Monad
  ( runScheduleMonad )
import Schedule.Ordering
  ( Order(..)
  , OrderingMatrix(..), upperTriangular
  , addEdgesTransitively
  )
import Schedule.Propagators
  ( Propagator, propagationLoop )
import Schedule.Task
  ( Task, Tasks(..), TaskInfos(..), MutableTasks, ImmutableTasks
  , est, ect, lst, lct
  )
import Schedule.Time
  ( HandedTime(..), Delta(..) )

import Debug.Trace

-------------------------------------------------------------------------------

data SearchDecision
  = TryLT
  | TryGT
  deriving stock    ( Show, Generic )
  deriving anyclass NFData

data SearchData task t
  = SearchData
  { searchTasks    :: !(ImmutableTasks task t)
  , searchDecision :: !( Int, Int )
  }
  deriving stock ( Show, Generic )

data SearchState task t
  = SearchState
  { pastDecisions       :: [ SearchData task t ]
  , solutions           :: [ Arg Double ( ImmutableTasks task t ) ]
  , totalSolutionsFound :: !Int
  , totalDecisionsTaken :: !Int
  }
  deriving stock ( Show, Generic )

search
  :: forall task t
  .  ( Num t, Ord t, Enum t, Bounded t
     , NFData t, NFData task
     , Show t, Show task
     )
  => ( ImmutableTasks task t -> Double )
  -> Int
  -> [ Propagator task t ]
  -> ImmutableTasks task t
  -> SearchState task t
search cost maxSolutions propagators = ( `execState` initialState ) . findNextSearchStart
  where

    initialState :: SearchState task t
    initialState = SearchState
      { pastDecisions = []
      , solutions = []
      , totalSolutionsFound = 0
      , totalDecisionsTaken = 0
      }

    -- Search for the next precedence decision that can be taken.
    findNextSearchStart :: MonadState ( SearchState task t ) m => ImmutableTasks task t -> m ()
    findNextSearchStart currentTasks@( Tasks { taskInfos } ) =
      case nextLikeliestPrecedence ( tasks taskInfos ) ( orderings taskInfos ) of
        -- No further decisions to make: make a note of the solution found and then backtrack to keep searching.
        Nothing -> do
          SearchState { totalSolutionsFound } <- get
          modify'
            $ over ( field' @"solutions" )
                ( trace ( "found solution #" <> show ( totalSolutionsFound + 1 ) <> "\n" )
                $ insertSolution maxSolutions currentTasks ( cost currentTasks )
                )
          backtrack
        -- A further search decision can be made:
        --  - make a search decision and compute its effect,
        --  - if the search can continue, add the decisions to the search state to enable backtracking.
        -- Choose the @ < @ decision first, as @ > @ is chosen only after backtracking.
        Just ( i, j ) -> decide TryLT i j currentTasks

    -- Take a decision: add a precedence, and if there were other choices that could have been made,
    -- add a point to backtrack to so that the search can continue with the other decisions.
    decide :: MonadState ( SearchState task t ) m => SearchDecision -> Int -> Int -> ImmutableTasks task t -> m ()
    decide decToTry i j currentTasks = do

      next <- case decToTry of
        TryLT -> do
          let
            -- We are always trying @ T_i < T_j @ before @ T_i > T_j @.
            -- Hence, if we are currently trying @ < @, then provide a backtracking point for @ > @.
            backtrackPoint :: SearchData task t
            backtrackPoint = SearchData { searchTasks = currentTasks, searchDecision = ( i, j ) }
          modify'
            $ over ( field' @"pastDecisions" ) ( backtrackPoint : )
            . over ( field' @"totalDecisionsTaken" ) ( + 1 )
          pure $ runScheduleMonad currentTasks ( addEdge i j *> propagationLoop 1000 propagators )
        TryGT -> do
          -- Don't provide a backtracking point:
          -- at this stage we should have already tried @ T_i < T_j @.
          modify'
            $ over ( field' @"totalDecisionsTaken" ) ( + 1 )
          pure $ runScheduleMonad currentTasks ( addEdge j i *> propagationLoop 1000 propagators )
      case next of
        -- No results possible: record the (partial) solution, then backtrack.
        ( _, ( Left _err, _ ) ) -> do
          let
            remainingUnknowns :: Int
            remainingUnknowns
              = getSum
              . Unboxed.Vector.foldr ( (<>) . ( \case { Unknown -> 1 ; _ -> 0 } ) ) mempty
              $ ( orderingMatrix . orderings . taskInfos $ currentTasks )
          --pastDecs <- ( map searchDecision . pastDecisions ) <$> get
          --modify'
          --  $ over ( field' @"solutions" )
          --      ( insertSolution maxSolutions currentTasks ( Right ( Arg remainingUnknowns pastDecs ) ) )
          backtrack
        -- Search can continue: keep going.
        ( newTaskData, _ ) ->
          findNextSearchStart newTaskData

    backtrack :: MonadState ( SearchState task t ) m => m ()
    backtrack = do
      oldSearchState@( SearchState { pastDecisions = decs } ) <- get
      case decs of
        -- Nothing to backtrack to: finish.
        [] -> pure ()
        -- Found a point to backtrack to.
        ( SearchData { searchTasks, searchDecision = ( i, j ) } : prevDecs ) -> do
          put ( oldSearchState { pastDecisions = prevDecs } )
          -- Try the @ T_i > T_j @ precedence now (the search should have already tried the other decision).
          decide TryGT i j searchTasks

-- | Insert a solution, bumping off old too-costly solutions if we exceeding the maximum number of solutions.
insertSolution :: Ord cost => Int -> sol -> cost -> [ Arg cost sol ] -> [ Arg cost sol ]
insertSolution maxSolutions currentSolution currentCost
  = take maxSolutions
  . insert ( Arg currentCost currentSolution )


-- | Obtain the indices for the most likely unknown precedence.
nextLikeliestPrecedence
  :: forall task t
  .  ( Num t, Ord t, Bounded t )
  =>  Boxed.Vector ( Task task t )
  -> OrderingMatrix Unboxed.Vector
  -> Maybe ( Int, Int )
nextLikeliestPrecedence allTasks ( OrderingMatrix { dim, orderingMatrix } )
  = fmap ( \ ( Arg _ v ) -> v )
  . listToMaybe
  . sort
  . mapMaybe
    ( \ ( i, j ) -> case orderingMatrix Unboxed.Vector.! ( upperTriangular dim i j ) of
        Unknown -> Just $ Arg ( likelihood i j ) ( i, j )
        _       -> Nothing
    )
  $ [ ( i, j ) | i <- [ 0 .. dim - 1 ], j <- [ i + 1 .. dim - 1 ] ]
  where
    likelihood :: Int -> Int -> Delta t
    likelihood i j =
      let
        tk_i, tk_j :: Task task t
        tk_i = allTasks Boxed.Vector.! i
        tk_j = allTasks Boxed.Vector.! j
      in
        min
          ( handedTime ( endPoint ( lst tk_j ) ) --> handedTime ( endPoint ( lct tk_i ) ) )
          ( handedTime ( endPoint ( est tk_j ) ) --> handedTime ( endPoint ( ect tk_i ) ) )

-- | Add a precedence in the ordering matrix,
-- inducing precedence constraints on all resulting transitive edges.
addEdge
  :: forall m task t s
  .  ( MonadReader ( MutableTasks s task t ) m
     , MonadBase ( ST s ) m
     , MonadError Text m
     , Num t, Ord t, Bounded t
     )
  => Int
  -> Int
  -> m ()
addEdge start end = do
  Tasks { taskNames, taskInfos = TaskInfos { tasks, orderings } } <- ask

  let
    addEdges :: m ()
    addEdges =
      addEdgesTransitively
        propagateNewEdge errorMessage
        orderings
        end ( Identity start ) ( Const () )

    propagateNewEdge :: Int -> Int -> m ()
    propagateNewEdge i j = do
      tk_i <- liftBase $ tasks `unsafeIndex` i
      tk_j <- liftBase $ tasks `unsafeIndex` j
      constrainToBefore i ( lst tk_j )
      constrainToAfter  j ( ect tk_i )

    errorMessage :: Either Int ( Int, Int ) -> Text
    errorMessage ( Left i ) =
      "Cycle involving \"" <> taskNames Boxed.Vector.! i <> "\" detected after adding the precedence:\n" <>
      "  - \"" <> taskNames Boxed.Vector.! start <> "\"\n\
      \  before\n\
      \  - \"" <> taskNames Boxed.Vector.! end <> "\"\n\n"
    errorMessage ( Right ( i, j ) ) =
      "Cycle between \"" <> taskNames Boxed.Vector.! i <> "\" and \"" <>
      taskNames Boxed.Vector.! j <> "\" detected after adding the precedence:\n" <>
      "  - \"" <> taskNames Boxed.Vector.! start <> "\"\n\
      \  before\n\
      \  - \"" <> taskNames Boxed.Vector.! end <> "\"\n\n"

  addEdges
