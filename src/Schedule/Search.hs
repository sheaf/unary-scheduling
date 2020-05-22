
{-# LANGUAGE BlockArguments        #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}

module Schedule.Search where

-- base
import Data.List
  ( insert, sort )
import Data.Maybe
  ( mapMaybe, listToMaybe )
import Data.Semigroup
  ( Arg(..), Sum(..) )
import GHC.Generics
  ( Generic )

-- acts
import Data.Act
  ( Torsor((-->)) )

-- containers
import qualified Data.IntMap as IntMap
  ( fromList )
import qualified Data.IntSet as IntSet
  ( singleton )

-- deepseq
import Control.DeepSeq
  ( NFData )

-- lens
import Control.Lens
  ( modifying )

-- generic-lens
import Data.Generics.Product.Fields
  ( field' )
import Data.GenericLens.Internal
  ( over )

-- mtl
import Control.Monad.Reader
  ( ask )
import Control.Monad.State.Strict
  ( MonadState, get, put, modify' )

-- text
import Data.Text
  ( Text )

-- transformers
import Control.Monad.Trans.State.Strict
  ( execState )

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
  ( Constraints(..), Constraint(..) )
import Schedule.Interval
  ( Endpoint(..) )
import Schedule.Monad
  ( MonadSchedule
  , runScheduleMonad, constrain
  )
import Schedule.Ordering
  ( Order(..)
  , OrderingMatrix(..), upperTriangular
  , addIncidentEdgesTransitively
  )
import Schedule.Propagators
  ( Propagator, propagationLoop )
import Schedule.Task
  ( Task, TaskInfos(..), ImmutableTaskInfos
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
  { searchTasks    :: !( ImmutableTaskInfos task t )
  , searchDecision :: !( Int, Int )
  }
  deriving stock    ( Show, Generic )
  deriving anyclass NFData

data SolutionCost
  = FullSolution    Double
  | PartialSolution Int
  deriving stock    ( Eq, Ord, Show, Generic )
  deriving anyclass NFData

data SearchState task t
  = SearchState
  { pastDecisions       :: [ SearchData task t ]
  , solutions           :: [ Arg SolutionCost ( ImmutableTaskInfos task t ) ]
  , totalSolutionsFound :: !Int
  , totalDecisionsTaken :: !Int
  }
  deriving stock    ( Show, Generic )
  deriving anyclass NFData

search
  :: forall task t
  .  ( Num t, Ord t, Enum t, Bounded t
     , NFData t, NFData task
     , Show t, Show task
     )
  => ( ImmutableTaskInfos task t -> Double )
  -> Int
  -> [ Propagator task t ]
  -> ImmutableTaskInfos task t
  -> SearchState task t
search cost maxSolutions propagators = ( `execState` initialState ) . findNextSearchStart
  where

    initialState :: SearchState task t
    initialState = SearchState
      { pastDecisions       = []
      , solutions           = []
      , totalSolutionsFound = 0
      , totalDecisionsTaken = 0
      }

    -- Find the precedence which would incur the largest adjustment in availability for the two tasks involved.
    likelihood :: Task task t -> Task task t -> Delta t
    likelihood tk tk' = min ( totalCut tk tk' ) ( totalCut tk' tk )
      where
        totalCut :: Task task t -> Task task t -> Delta t
        totalCut tk_i tk_j =
          max mempty ( handedTime ( endpoint ( lst tk_j ) ) --> handedTime ( endpoint ( lct tk_i ) ) )
          <>
          max mempty ( handedTime ( endpoint ( est tk_j ) ) --> handedTime ( endpoint ( ect tk_i ) ) )

    -- Search for the next precedence decision that can be taken.
    findNextSearchStart :: MonadState ( SearchState task t ) m => ImmutableTaskInfos task t -> m ()
    findNextSearchStart taskInfos@( TaskInfos { taskAvails, orderings } )  =
      case nextLikeliestPrecedence likelihood taskAvails orderings of
        -- No further decisions to make: make a note of the solution found and then backtrack to keep searching.
        Nothing -> do
          SearchState { totalSolutionsFound } <- get
          modify'
            $ over ( field' @"solutions" )
                ( trace ( "found solution #" <> show ( totalSolutionsFound + 1 ) <> "\n" )
                $ insertSolution maxSolutions taskInfos ( FullSolution $ cost taskInfos )
                )
          backtrack
        -- A further search decision can be made:
        --  - make a search decision and compute its effect,
        --  - if the search can continue, add the decisions to the search state to enable backtracking.
        -- Choose the @ < @ decision first, as @ > @ is chosen only after backtracking.
        Just ( i, j ) -> decide TryLT i j taskInfos

    -- Take a decision: add a precedence, and if there were other choices that could have been made,
    -- add a point to backtrack to so that the search can continue with the other decisions.
    decide :: MonadState ( SearchState task t ) m => SearchDecision -> Int -> Int -> ImmutableTaskInfos task t -> m ()
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
        -- No results possible: backtrack.
        ( _, ( Left _err, _ ) ) -> do
          let
            remainingUnknowns :: Int
            remainingUnknowns
              = getSum
              . Unboxed.Vector.foldr ( (<>) . ( \case { Unknown -> 1 ; _ -> 0 } ) ) mempty
              $ ( orderingMatrix . orderings $ currentTasks )
          --pastDecs <- ( map searchDecision . pastDecisions ) <$> get
          modify'
            $ over ( field' @"solutions" )
                ( insertSolution maxSolutions currentTasks ( PartialSolution $ remainingUnknowns ) )
          --trace ( "backtracking from depth " <> show ( length pastDecs ) <> "\n" )
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
  :: forall task t o
  .  ( Num t, Ord t, Bounded t
     , Ord o
     )
  => ( Task task t -> Task task t -> o )
  -> Boxed.Vector ( Task task t )
  -> OrderingMatrix Unboxed.Vector
  -> Maybe ( Int, Int )
nextLikeliestPrecedence likelihood allTasks ( OrderingMatrix { dim, orderingMatrix } ) 
  = fmap ( \ ( Arg _ v ) -> v )
  . listToMaybe
  . sort
  . mapMaybe
    ( \ ( i, j ) -> case orderingMatrix Unboxed.Vector.! ( upperTriangular dim i j ) of
        Unknown -> 
          let
            tk_i, tk_j :: Task task t
            tk_i = allTasks Boxed.Vector.! i
            tk_j = allTasks Boxed.Vector.! j 
          in
            Just $ Arg ( likelihood tk_i tk_j ) ( i, j )
        _ -> Nothing
    )
  $ [ ( i, j ) | i <- [ 0 .. dim - 1 ], j <- [ i + 1 .. dim - 1 ] ]

-- | Add a precedence in the ordering matrix,
-- inducing precedence constraints on all resulting transitive edges.
addEdge
  :: forall m task t s
  .  ( MonadSchedule s task t m
     , Num t, Ord t, Bounded t
     )
  => Int
  -> Int
  -> m ()
addEdge start end = do
  TaskInfos { taskNames, taskAvails, orderings } <- ask

  modifying ( field' @"taskConstraints" . field' @"justifications" )
    ( <> 
      "Search decision has introduced the precedence:\n\
      \\"" <> taskNames Boxed.Vector.! start <> "\" < \"" <> taskNames Boxed.Vector.! end <> "\n\n"
    )

  let
    addEdges :: m ()
    addEdges =
      addIncidentEdgesTransitively
        propagateNewEdge errorMessage
        orderings
        end ( IntSet.singleton start ) ( mempty )

    propagateNewEdge :: Int -> Int -> m ()
    propagateNewEdge i j = do
      tk_i <- taskAvails `unsafeIndex` i
      tk_j <- taskAvails `unsafeIndex` j
      constrain
        ( Constraints
          { constraints
              = IntMap.fromList
              [ ( i, NotLaterThan   $ lst tk_j )
              , ( j, NotEarlierThan $ ect tk_i )
              ]
          , justifications = ""
          , precedences = mempty -- precedences are added by the 'addIncidentEdgesTransitively' function
          }
        )

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
