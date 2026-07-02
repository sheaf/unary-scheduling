{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

-- | A Z3-backed oracle for unary-scheduling.
module Schedule.Z3
  ( -- * Unary scheduling Z3 encoding
    intervalIntBounds
  , buildUnaryModel
    -- * Feasibility oracle
  , z3Feasible
    -- ** Shared-environment feasibility (amortised setup)
  , Z3Feasibility(..)
  , newZ3Env, z3FeasibleIn
    -- * Differential validation
  , Z3Verdict(..)
  , verifyAgainstZ3
    -- * Frustration-minimising reference solver
  , unaryScheduleZ3
  )
  where

-- base
import Control.Monad
  ( when )
import Data.Coerce
  ( Coercible, coerce )
import Data.Foldable
  ( for_, toList )
import Data.List
  ( sortOn )
import Data.Maybe
  ( catMaybes )
import Data.Traversable
  ( for )

-- mtl
import Control.Monad.Reader
  ( ask )

-- containers
import Data.Set
  ( Set )

-- containers
import qualified Data.IntSet as IntSet
  ( fromList )

-- text
import Data.Text
  ( Text )

-- vector
import qualified Data.Vector as Boxed.Vector
  ( (!), length )

-- z3
import Z3.Monad
  ( Z3 )
import qualified Z3.Monad as Z3

-- unary-scheduling
import Schedule.Constraint
  ( Infeasible, renderInfeasible )
import Schedule.Interval
  ( Endpoint(..), Interval(..), Intervals(..), Measurable, intervalIntBounds )
import Schedule.Monad
  ( runScheduleMonad, SchedulableData )
import Schedule.Monitor
  ( Monitor(..) )
import Schedule.Ordering
  ( Order(Unknown), readOrdering, newTransitiveClosureScratch )
import Schedule.Precedence
  ( addEdge )
import Schedule.Propagators
  ( Propagator, propagationLoop, seedAllOf, matrixChanneller )
import Schedule.Task
  ( Task(..), TaskInfos(..), ImmutableTaskInfos, est, lst )
import Schedule.Time
  ( Delta(..), Time(..), HandedTime(..) )

--------------------------------------------------------------------------------
-- Encoding.

-- | Build a unary-scheduling model: one integer start-time variable per task,
-- constrained to lie within its availability, plus a pairwise non-overlap
-- (disjunctive) constraint enforcing the unary resource.
--
-- Returns each task's @(index, startVar, durationVar)@ in input order.
buildUnaryModel
  :: forall task t
  .  Coercible t Int
  => [ Task task t ]
  -> Z3 [ ( Int, Z3.AST, Z3.AST ) ]
buildUnaryModel tasks = do
  ts <- for ( zip [ 0 :: Int .. ] tasks ) \ ( taskNb, Task { taskAvailability, taskDuration } ) -> do
    t <- Z3.mkFreshIntVar ( show taskNb )
    d <- Z3.mkIntNum ( coerce taskDuration :: Int )
    withinIvals <-
      for ( intervals taskAvailability ) \ ival -> do
        let ( s', e' ) = intervalIntBounds ival
        start_t <- Z3.mkIntNum   s'
        end_t   <- Z3.mkIntNum ( e' - coerce taskDuration )
        startsAfter <- Z3.mkGe t start_t
        endsBefore  <- Z3.mkLe t end_t
        Z3.mkAnd [ startsAfter, endsBefore ]
    -- The task must be scheduled within one of its availability intervals.
    Z3.assert =<< Z3.mkOr ( toList withinIvals )
    pure ( taskNb, t, d )
  -- Unary resource: for every pair of tasks, one must finish before the other starts.
  let
    taskPairs :: [ ( ( Z3.AST, Z3.AST ), ( Z3.AST, Z3.AST ) ) ]
    taskPairs = [ ( ( t1, d1 ), ( t2, d2 ) ) | ( nb1, t1, d1 ) <- ts, ( nb2, t2, d2 ) <- ts, nb2 > nb1 ]
  for_ taskPairs \ ( ( t1, d1 ), ( t2, d2 ) ) -> do
    before <- ( `Z3.mkLe` t2 ) =<< Z3.mkAdd [ t1, d1 ]
    after  <- ( `Z3.mkLe` t1 ) =<< Z3.mkAdd [ t2, d2 ]
    Z3.assert =<< Z3.mkOr [ before, after ]
  pure ts

--------------------------------------------------------------------------------
-- Feasibility oracle.

-- | Decide feasibility of the unary scheduling problem with Z3 (no objective),
-- returning the start times (aligned with input order) of some feasible schedule,
-- or 'Nothing' if the instance is infeasible.
z3Feasible
  :: forall task t
  .  Coercible t Int
  => [ Task task t ]
  -> IO ( Maybe [ Integer ] )
z3Feasible tasks = snd <$> Z3.evalZ3 ( z3FeasibleQuery tasks )

-- | The feasibility query as a reusable 'Z3' action: build the model, check it,
-- and read back the start times. Factored out of 'z3Feasible' so a single
-- environment can drive many checks (see 'z3FeasibleIn').
--
-- The 'Z3.Result' is returned alongside the start times so callers can tell a
-- timeout apart from infeasibility.
--
-- We do /not/ use 'Z3.withModel' here: it fetches the model on any non-'Z3.Unsat'
-- result, which throws \"there is no current model\" on the 'Z3.Undef' produced
-- by a timeout. We instead read the model only when the check returns 'Z3.Sat'.
z3FeasibleQuery
  :: forall task t
  .  Coercible t Int
  => [ Task task t ]
  -> Z3 ( Z3.Result, Maybe [ Integer ] )
z3FeasibleQuery tasks = do
  ts <- buildUnaryModel tasks
  res <- Z3.check
  ( res, ) <$>
    case res of
      Z3.Sat -> do
        -- Only use 'getModel' when there is a model.
        model    <- Z3.solverGetModel
        mbStarts <- mapM ( Z3.evalInt model . ( \ ( _, t, _ ) -> t ) ) ts
        pure $ sequence mbStarts
      Z3.Unsat -> pure Nothing
      Z3.Undef -> pure Nothing

-- | The outcome of a single shared-environment feasibility check
-- (see 'z3FeasibleIn').
data Z3Feasibility
  = Z3TimedOut
    -- ^ the solver hit the timeout
  | Z3Decided !( Maybe [ Integer ] )
    -- ^ the solver decided: @Just starts@ for a feasible schedule, @Nothing@ if
    -- infeasible
  deriving stock ( Eq, Show )

-- | Create a fresh Z3 environment that can be re-used across many
-- feasability checks, in order to amortise the setup cost.
newZ3Env
  :: Int -- ^ timeout (in milliseconds)
  -> IO Z3.Z3Env
newZ3Env timeoutMillis =
  Z3.newEnv Nothing ( Z3.stdOpts <> Z3.opt "timeout" timeoutMillis )

-- | Run a single feasibility given a Z3 environment.
--
-- The check runs under 'Z3.local', so its assertions are popped afterwards and
-- the environment is left clean for the next check.
z3FeasibleIn
  :: forall task t
  .  Coercible t Int
  => Z3.Z3Env
  -> [ Task task t ]
  -> IO Z3Feasibility
z3FeasibleIn env tasks = do
  ( res, mbModel ) <- Z3.evalZ3WithEnv ( Z3.local ( z3FeasibleQuery tasks ) ) env
  pure $ case res of
    Z3.Undef -> Z3TimedOut
    Z3.Sat   -> Z3Decided mbModel
    Z3.Unsat -> Z3Decided mbModel

--------------------------------------------------------------------------------
-- Differential validation.

-- | The outcome of cross-checking native propagation against the Z3 oracle on a
-- single instance.
data Z3Verdict
  = Z3Infeasible
    -- ^ Z3 found no feasible schedule
  | NativeRejected !Text
    -- ^ Native propagation threw on Z3's precedence chain: a Z3-feasible schedule
    -- was rejected (unsoundness in propagation)
  | NativePruned ![ Int ]
    -- ^ Native propagation pushed these tasks' Z3 start times outside their
    -- @[est, lst]@ window (unsoundness in propagation)
  | Consistent ![ Integer ]
  deriving stock ( Eq, Show )

-- | Cross-check native propagation against Z3 on a single instance.
verifyAgainstZ3
  :: forall task t
  .  ( Num t, Measurable t, Bounded t, Show t, Show task
     , Coercible t Int
     , SchedulableData [ ( Task task t, Text ) ] task t
     )
  => [ Propagator task t ]
  -> [ ( Task task t, Text ) ]
  -> IO Z3Verdict
verifyAgainstZ3 propagators namedTasks = do
  mbStarts <- z3Feasible ( map fst namedTasks )
  pure $ case mbStarts of
    Nothing     -> Z3Infeasible
    Just starts ->
      let
        -- Z3's task order, as consecutive precedences (the transitive closure
        -- fills in the rest).
        chain :: [ ( Int, Int ) ]
        chain =
          let order = map snd ( sortOn fst ( zip starts [ 0 :: Int .. ] ) )
          in  zip order ( drop 1 order )
        ti  :: ImmutableTaskInfos task t
        res :: Either ( Infeasible t ) ()
        ( ti, ( res, _ ) ) =
          runScheduleMonad namedTasks \ trail -> do
            -- Only post precedences that aren't already determined, as the
            -- ordering matrix implementation doesn't deal with redundant edges.
            TaskInfos { orderings, taskNames } <- ask
            for_ chain \ ( a, b ) -> do
              o <- readOrdering orderings a b
              when ( o == Unknown ) ( addEdge trail a b )
            let nbTasks  = Boxed.Vector.length taskNames
                allTasks = IntSet.fromList [ 0 .. nbTasks - 1 ]
            scratch <- newTransitiveClosureScratch nbTasks
            propagationLoop NoMonitoring 1000 trail propagators
              ( matrixChanneller trail scratch ) ( seedAllOf propagators allTasks )
        -- Tasks whose Z3 start time no longer lies within the tightened window.
        violators :: [ Int ]
        violators =
          [ i
          | ( i, s ) <- zip [ 0 :: Int .. ] starts
          , let task = taskAvails ti Boxed.Vector.! i
                st   = coerce ( fromInteger s :: Int ) :: t
                estV = getTime ( handedTime ( endpoint ( est task ) ) )
                lstV = getTime ( handedTime ( endpoint ( lst task ) ) )
          , null ( intervals ( taskAvailability task ) ) || st < estV || st > lstV
          ]
      in case res of
           Left err -> NativeRejected ( renderInfeasible ( taskNames ti ) err )
           Right ()
             | not ( null violators ) -> NativePruned violators
             | otherwise              -> Consistent starts

--------------------------------------------------------------------------------
-- Frustration-minimising reference solver.

-- | Find a frustration-minimising schedule using Z3.
unaryScheduleZ3
  :: forall t staff
  .  ( Ord staff, Coercible t Int )
  => [ Task ( Set staff ) t ]
  -> [ ( staff, [ ( Interval t, Int ) ] ) ]
  -> IO ( Maybe [ Integer ] )
unaryScheduleZ3 tasks frustrationRanges = do
  ( startTimes, _res ) <- Z3.evalZ3 do
    ts <- buildUnaryModel tasks

    -- Compute sum of squared frustrations per staff member.
    memberFrusts <- for frustrationRanges \ ( staff, ranges ) -> do
      let
        staffMemberTasks :: [ ( Z3.AST, Z3.AST ) ]
        staffMemberTasks = map ( ( \ ( _, t, d ) -> ( t, d ) ) . fst ) . filter ( ( staff `elem` ) . taskInfo . snd ) $ zip ts tasks
      frusts <- for ranges \ ( range, multiplier ) -> do
        frust <- linearFrustration staffMemberTasks range
        mult  <- Z3.mkIntNum multiplier
        Z3.mkMul [ frust, mult ]
      linearFrust <- Z3.mkAdd frusts
      Z3.mkMul [ linearFrust, linearFrust ]

    totalFrust <- Z3.mkAdd memberFrusts
    _frustVal <- Z3.optimizeMinimize totalFrust
    optRes <- Z3.optimizeCheck []

    ( _res, val :: Maybe [ Integer ] ) <- Z3.withModel \ model ->
      catMaybes <$> mapM ( Z3.evalInt model . ( \ ( _, t, _ ) -> t ) ) ts
    pure ( val, optRes )
  pure startTimes

linearFrustration :: Coercible t Int => [ ( Z3.AST, Z3.AST ) ] -> Interval t -> Z3 Z3.AST
linearFrustration startTimesAndDurations ival = do
  let ( s', e' ) = intervalIntBounds ival
  range_start <- Z3.mkIntNum s'
  range_end   <- Z3.mkIntNum e'
  computeFrustrationBetween ( range_start, range_end ) startTimesAndDurations

computeFrustrationBetween :: ( Z3.AST, Z3.AST ) -> [ ( Z3.AST, Z3.AST ) ] -> Z3 Z3.AST
computeFrustrationBetween ( range_start, range_end ) tasks = do
  initial_min <- Z3.mkIntNum (  1073741824 :: Int ) --   2 ^ 30
  initial_max <- Z3.mkIntNum ( -1073741824 :: Int ) -- - 2 ^ 30
  zero        <- Z3.mkIntNum (           0 :: Int ) -- (so that initial_max - initial_min doesn't overflow the 31 available bits)
  total <- go initial_min initial_max zero tasks
  total_isPos <- Z3.mkGe total zero
  Z3.mkIte total_isPos total zero
  where
    go :: Z3.AST -> Z3.AST -> Z3.AST -> [ ( Z3.AST, Z3.AST ) ] -> Z3 Z3.AST
    go rolling_min rolling_max rolling_dur [] = Z3.mkSub [ rolling_max, rolling_min, rolling_dur ]
    go rolling_min rolling_max rolling_dur ( ( t, d ) : as ) = do
      after_range_start <- Z3.mkGe t range_start
      before_range_end  <- Z3.mkLe t range_end
      isRelevant <- Z3.mkAnd [ after_range_start, before_range_end ]
      smaller_than_rolling_min <- ( \ better -> Z3.mkAnd [ isRelevant, better ] ) =<< Z3.mkLt t rolling_min
      larger_than_rolling_max  <- ( \ better -> Z3.mkAnd [ isRelevant, better ] ) =<< Z3.mkGt t rolling_max
      with_added_dur <- Z3.mkAdd [ rolling_dur, d ]
      new_min <- Z3.mkIte smaller_than_rolling_min t rolling_min
      new_max <- Z3.mkIte larger_than_rolling_max  t rolling_max
      new_dur <- Z3.mkIte isRelevant with_added_dur rolling_dur
      go new_min new_max new_dur as
