
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Schedule.Search where

-- base
import Control.Monad
  ( when )
import Control.Monad.ST
  ( ST, runST )
import Data.Ord
  ( Down(..) )
import Data.Semigroup
  ( Arg(..) )
import GHC.Generics
  ( Generic )

-- acts
import Data.Act
  ( Torsor((-->)) )

-- containers
import qualified Data.IntSet as IntSet
  ( singleton )
import Data.Sequence
  ( Seq(..) )
import qualified Data.Sequence as Seq
  ( singleton, length )

-- deepseq
import Control.DeepSeq
  ( NFData )

-- lens
import Control.Lens
  ( modifying )

-- generic-lens
import Data.Generics.Product.Fields
  ( field' )

-- primitive
import Data.Primitive.MutVar
  ( newMutVar, readMutVar, writeMutVar, modifyMutVar' )

-- text
import Data.Text
  ( Text )

-- transformers
import Control.Monad.Reader
  ( ask )
import Control.Monad.Trans.Reader
  ( runReaderT )
import Control.Monad.Trans.Except
  ( runExceptT )
import Control.Monad.Trans.State.Strict
  ( runStateT )

-- vector
import qualified Data.Vector as Boxed.Vector
  ( (!) )
import qualified Data.Vector.Mutable as Boxed.MVector
  ( unsafeRead )
import qualified Data.Vector.Unboxed.Mutable as Unboxed.MVector
  ( unsafeRead )

-- unary-scheduling
import qualified Data.Sequence.Insert as Seq
  ( insertIntoSorted )
import Data.Vector.Generic.Index
  ( unsafeIndex )
import Data.Vector.PhaseTransition
  ( Freeze(freeze), Thaw(thaw) )
import Schedule.Constraint
  ( Constraint(..), tightenMany )
import Schedule.Contention
  ( contentionScore )
import Schedule.Interval
  ( Endpoint(..), Measurable )
import Schedule.Monad
  ( MonadSchedule
  , constrain
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
  , est, ect, lct, lst
  )
import Schedule.Time
  ( Delta(..), HandedTime(..) )
import Schedule.Trail
  ( Trail, newTrail, currentMark, undoTo
  , orderingCellWriter
  )

import Debug.Trace
  ( traceM )

-------------------------------------------------------------------------------

-- | How the search chooses the next pair of tasks whose precedence to branch on.
data BranchHeuristic
  = Contention
    -- ^ Branch on the pair of tasks with peak joint contention
  | WindowCut
    -- ^ Branch on the pair of tasks whose least disruptive ordering shrinks the task windows most
  deriving stock ( Show, Eq )

data SolutionCost
  = FullSolution    Double
  | PartialSolution Int
  deriving stock    ( Eq, Ord, Show, Generic )
  deriving anyclass NFData

-- | Search state.
data SearchState task t
  = SearchState
  { solutions           :: Seq ( Arg ( Down SolutionCost ) ( ImmutableTaskInfos task t ) )
  , totalSolutionsFound :: !Int
  , totalDecisionsTaken :: !Int

    -- Debug instrumentation (TODO: split this off)
  , openDepth           :: !Int -- ^ current number of open backtrack points (decision-stack depth)
  , maxOpenDepth        :: !Int -- ^ largest decision-stack depth reached so far
  , totalBacktracks     :: !Int -- ^ number of times the search has backtracked
  }
  deriving stock    ( Show, Generic )
  deriving anyclass NFData

-- | A backtracking choice point.
--
-- Records the trail mark of the /parent/ state and the precedence pair @(i,j)@
-- whose @ T_j < T_i @ alternative is still to be explored (the @ T_i < T_j @
-- alternative having been tried first).
data Frame = Frame !Int !Int !Int

-- | How often (counted in decisions) the search emits a progress trace.
-- Set to @0@ to disable progress tracing.
traceEvery :: Int
traceEvery = 1000

-- | One-line summary of the best solution cost found so far (for logging).
bestCostSummary :: Seq ( Arg ( Down SolutionCost ) x ) -> String
bestCostSummary ( _ :|> Arg ( Down c ) _ ) = show c
bestCostSummary _                          = "none"

-- | Chronological backtracking search over task precedences, using one shared
-- mutable state with in-place undo.
search
  :: forall task t
  .  ( Num t, Measurable t, Real t, Enum t, Bounded t
     , NFData t, NFData task
     , Show t, Show task
     )
  => ( ImmutableTaskInfos task t -> Double )
  -> BranchHeuristic
  -> Int
  -> [ Propagator task t ]
  -> ImmutableTaskInfos task t
  -> SearchState task t
search cost branchHeuristic maxSolutions propagators initialTasks = runST \ @s -> do
  let
    initialState :: SearchState task t
    initialState = SearchState
      { solutions           = Empty
      , totalSolutionsFound = 0
      , totalDecisionsTaken = 0
      , openDepth           = 0
      , maxOpenDepth        = 0
      , totalBacktracks     = 0
      }
  tis    <- thaw initialTasks
  trail  <- newTrail
  stRef  <- newMutVar initialState
  stkRef <- newMutVar @_ @[ Frame ] []

  -- Pick the next undecided precedence to branch on.
  let
    pickWith
      :: forall o
      .  Ord o
      => ( Task task t -> Task task t -> o )
      -> ST s ( Maybe ( Int, Int ) )
    pickWith likelihood = loop 0 1 Nothing
      where
        OrderingMatrix { dim, orderingMatrix = mat } = orderings tis
        tasks = taskAvails tis
        loop :: Int -> Int -> Maybe ( Arg o ( Int, Int ) ) -> ST s ( Maybe ( Int, Int ) )
        loop i j best
          | i >= dim  = pure ( fmap ( \ ( Arg _ ij ) -> ij ) best )
          | j >= dim  = loop ( i + 1 ) ( i + 2 ) best
          | otherwise = do
              o <- Unboxed.MVector.unsafeRead mat ( upperTriangular dim i j )
              best' <- case o of
                Unknown -> do
                  tk_i <- Boxed.MVector.unsafeRead tasks i
                  tk_j <- Boxed.MVector.unsafeRead tasks j
                  let cand = Arg ( likelihood tk_i tk_j ) ( i, j )
                  -- 'Arg' compares on the score only; ties keep the earlier
                  -- (smaller-index) pair, matching the previous selection order.
                  pure $ Just $ maybe cand ( max cand ) best
                _ -> pure best
              loop i ( j + 1 ) best'

  let
    maxIter :: Int
    maxIter = 1000

    windowCut :: Task task t -> Task task t -> Delta t
    windowCut tk tk' = min ( totalCut tk tk' ) ( totalCut tk' tk )
      where
        totalCut :: Task task t -> Task task t -> Delta t
        totalCut tk_i tk_j =
          max mempty ( handedTime ( endpoint ( lst tk_j ) ) --> handedTime ( endpoint ( lct tk_i ) ) )
          <>
          max mempty ( handedTime ( endpoint ( est tk_j ) ) --> handedTime ( endpoint ( ect tk_i ) ) )

    nextPrecedenceM :: ST s ( Maybe ( Int, Int ) )
    nextPrecedenceM = case branchHeuristic of
      Contention -> pickWith @Double      contentionScore
      WindowCut  -> pickWith @( Delta t ) windowCut

    -- Count remaining undecided precedences (for the partial-solution cost).
    remainingUnknownsM :: ST s Int
    remainingUnknownsM = countFrom 0 0
      where
        OrderingMatrix { dim, orderingMatrix = mat } = orderings tis
        n = ( dim * ( dim - 1 ) ) `div` 2
        countFrom k acc
          | k >= n    = pure acc
          | otherwise = do
              o <- Unboxed.MVector.unsafeRead mat k
              countFrom ( k + 1 ) ( if o == Unknown then acc + 1 else acc )

    -- Apply a precedence @ T_a < T_b @ and propagate.
    -- Returns @Left@ on conflict; mutations remain on the trail, to be
    -- undone by backtracking.
    stepNode :: Int -> Int -> ST s ( Either Text () )
    stepNode a b = do
      ( res, _ ) <-
        runStateT
          ( runExceptT
            ( runReaderT
                ( addEdge trail a b *> propagationLoop maxIter trail propagators )
                tis
            )
          )
          mempty
      pure res

    logProgress :: ST s ()
    logProgress = do
      st <- readMutVar stRef
      when ( traceEvery > 0 && totalDecisionsTaken st `mod` traceEvery == 0 ) $
        traceM $ "[search] decisions=" <> show ( totalDecisionsTaken st )
              <> " openDepth="    <> show ( openDepth st )
              <> " maxOpenDepth=" <> show ( maxOpenDepth st )
              <> " solutionsFound=" <> show ( totalSolutionsFound st )
              <> " backtracks="   <> show ( totalBacktracks st )
              <> " best="         <> bestCostSummary ( solutions st )

    -- Would a solution of the given cost actually be kept?
    wouldInsert :: SolutionCost -> Seq ( Arg ( Down SolutionCost ) ( ImmutableTaskInfos task t ) ) -> Bool
    wouldInsert curCost sols = case sols of
      Empty -> maxSolutions > 0
      ( Arg ( Down worstCost ) _ :<| _ ) ->
        Seq.length sols < maxSolutions || curCost < worstCost

    recordFull :: ST s ()
    recordFull = do
      st   <- readMutVar stRef
      snap <- freeze tis
      let c = FullSolution ( cost snap )
      traceM ( "found solution #" <> show ( totalSolutionsFound st + 1 ) )
      writeMutVar stRef
        st { solutions = insertSolution maxSolutions snap c ( solutions st ) }

    recordPartial :: ST s ()
    recordPartial = do
      st        <- readMutVar stRef
      remaining <- remainingUnknownsM
      let c = PartialSolution remaining
      when ( wouldInsert c ( solutions st ) ) do
        snap <- freeze tis
        writeMutVar stRef
          st { solutions = insertSolution maxSolutions snap c ( solutions st ) }

    -- Find the next decision from the current (live) state.
    findNext :: ST s ()
    findNext = do
      logProgress
      mb <- nextPrecedenceM
      case mb of
        -- No undecided precedence left: a full solution. Record it and
        -- backtrack to keep searching for cheaper solutions.
        Nothing -> recordFull *> backtrack
        -- Branch: try @ T_i < T_j @ first, pushing a choice point for the
        -- @ T_j < T_i @ alternative.
        Just ( i, j ) -> do
          m <- currentMark trail
          modifyMutVar' stkRef ( Frame m i j : )
          modifyMutVar' stRef \ st ->
            st { totalDecisionsTaken = totalDecisionsTaken st + 1
               , openDepth           = openDepth st + 1
               , maxOpenDepth        = max ( maxOpenDepth st ) ( openDepth st + 1 )
               }
          res <- stepNode i j
          case res of
            Left  _ -> failBranch m
            Right _ -> findNext

    -- Pop a choice point and try its second (@ T_j < T_i @) alternative.
    backtrack :: ST s ()
    backtrack = do
      stk <- readMutVar stkRef
      case stk of
        [] -> pure ()
        ( Frame m i j : rest ) -> do
          writeMutVar stkRef rest
          modifyMutVar' stRef \ st ->
            st { openDepth       = openDepth st - 1
               , totalBacktracks = totalBacktracks st + 1
               }
          undoTo trail tis m
          modifyMutVar' stRef \ st ->
            st { totalDecisionsTaken = totalDecisionsTaken st + 1 }
          res <- stepNode j i
          case res of
            Left  _ -> failBranch m
            Right _ -> findNext

    -- A branch failed: restore the parent state, record it as a partial
    -- solution, and continue backtracking.
    failBranch :: Int -> ST s ()
    failBranch m = do
      undoTo trail tis m
      recordPartial
      backtrack

  findNext
  readMutVar stRef

-- | Insert a solution, bumping off old too-costly solutions if we exceed the maximum number of solutions.
insertSolution :: Ord cost => Int -> sol -> cost -> Seq ( Arg ( Down cost ) sol ) -> Seq ( Arg ( Down cost ) sol )
insertSolution maxSolutions currentSolution currentCost Empty
  | maxSolutions > 0
  = Seq.singleton ( Arg ( Down currentCost ) currentSolution )
  | otherwise
  = Empty
insertSolution maxSolutions currentSolution currentCost prevSols@( Arg ( Down worstCost ) worstSol :<| otherSols )
  | currentCost >= worstCost
  = if Seq.length prevSols >= maxSolutions
    then prevSols
    else Arg ( Down currentCost ) currentSolution :<| prevSols
  | otherwise
  = let
      sols = Seq.insertIntoSorted ( Arg ( Down currentCost ) currentSolution ) otherSols
    in
      if Seq.length prevSols >= maxSolutions
      then sols
      else ( Arg ( Down worstCost ) worstSol ) :<| sols

-- | Add a precedence in the ordering matrix,
-- inducing precedence constraints on all resulting transitive edges.
addEdge
  :: forall m task t s
  .  ( MonadSchedule s task t m
     , Num t, Measurable t, Bounded t
     )
  => Trail s task t
  -> Int
  -> Int
  -> m ()
addEdge trail start end = do
  tis@( TaskInfos { taskNames, taskAvails, orderings } ) <- ask

  modifying ( field' @"taskConstraints" . field' @"justifications" )
    ( <>
      "Search decision has introduced the precedence:\n\
      \\"" <> taskNames Boxed.Vector.! start <> "\" < \"" <> taskNames Boxed.Vector.! end <> "\n\n"
    )

  let
    addEdges :: m ()
    addEdges =
      addIncidentEdgesTransitively
        ( orderingCellWriter trail tis )
        propagateNewEdge errorMessage
        orderings
        end ( IntSet.singleton start ) ( mempty )

    propagateNewEdge :: Int -> Int -> m ()
    propagateNewEdge i j = do
      tk_i <- taskAvails `unsafeIndex` i
      tk_j <- taskAvails `unsafeIndex` j
      constrain $
        tightenMany
          -- NB: precedences are added by the 'addIncidentEdgesTransitively' function
          [ ( i, NotLaterThan   $ lst tk_j )
          , ( j, NotEarlierThan $ ect tk_i )
          ]
          ""

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
