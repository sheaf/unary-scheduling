{-# LANGUAGE ScopedTypeVariables #-}

-- | A Z3-backed oracle for unary-scheduling.
module Schedule.Z3
  ( -- * Unary scheduling Z3 encoding
    intervalIntBounds
  , buildUnaryModel
    -- * Feasibility oracle
  , z3Feasible
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
import Schedule.Interval
  ( Clusivity(..), Endpoint(..), Interval(..), Intervals(..), Measurable )
import Schedule.Monad
  ( runScheduleMonad, SchedulableData )
import Schedule.Monitor
  ( Monitor(..) )
import Schedule.Ordering
  ( Order(Unknown), readOrdering )
import Schedule.Precedence
  ( addEdge )
import Schedule.Propagators
  ( Propagator, propagationLoop, seedAllOf )
import Schedule.Task
  ( Task(..), TaskInfos(..), ImmutableTaskInfos, est, lst )
import Schedule.Time
  ( Delta(..), Time(..), HandedTime(..) )

--------------------------------------------------------------------------------
-- Encoding.

-- | Normalise an interval to half-open integer bounds @[s, e)@.
--
-- A task starting at slot @t@ with duration @d@ occupies slots
-- @[t, t + d)@; the per-task Z3 constraint is therefore
-- @s ≤ t ∧ t + d ≤ e@, with both inequalities applied to the
-- half-open bounds returned here.
intervalIntBounds :: Coercible t Int => Interval t -> ( Int, Int )
intervalIntBounds ( Interval ( Endpoint ( EarliestTime ( Time s ) ) clu_s ) ( Endpoint ( LatestTime ( Time e ) ) clu_e ) ) =
  ( case clu_s of { Exclusive -> coerce s + 1; _ -> coerce s }
  , case clu_e of { Inclusive -> coerce e + 1; _ -> coerce e }
  )

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
z3Feasible tasks = Z3.evalZ3 do
  ts <- buildUnaryModel tasks
  ( _res, mbStarts ) <- Z3.withModel \ model ->
    mapM ( Z3.evalInt model . ( \ ( _, t, _ ) -> t ) ) ts
  pure ( sequence =<< mbStarts )

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
        res :: Either Text ()
        ( ti, ( res, _ ) ) =
          runScheduleMonad namedTasks \ trail -> do
            -- Only post precedences that aren't already determined, as the
            -- ordering matrix implementation doesn't deal with redundant edges.
            TaskInfos { orderings, taskNames } <- ask
            for_ chain \ ( a, b ) -> do
              o <- readOrdering orderings a b
              when ( o == Unknown ) ( addEdge trail a b )
            let allTasks = IntSet.fromList [ 0 .. Boxed.Vector.length taskNames - 1 ]
            propagationLoop NoMonitoring 1000 trail propagators ( seedAllOf propagators allTasks )
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
           Left err -> NativeRejected err
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
