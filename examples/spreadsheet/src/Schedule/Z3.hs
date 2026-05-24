{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Schedule.Z3 where

-- base
import Data.Coerce
  ( Coercible, coerce )
import Data.Foldable
  ( for_, toList )
import Data.Maybe
  ( catMaybes )
import Data.Traversable
  ( for )

-- containers
import Data.Set
  ( Set )
import qualified Data.Set as Set
  ( )

-- z3
import Z3.Monad
  ( Z3 )
import qualified Z3.Monad as Z3

-- unary-scheduling
import Schedule.Interval
  ( Clusivity(..), Endpoint(..), Interval(..), Intervals(..) )
import Schedule.Task
  ( Task(..) )
import Schedule.Time
  ( Delta(..), Time(..), HandedTime(..) )

--------------------------------------------------------------------------------

-- | Convert an interval's endpoints to the inclusive integer range @[s', e']@
-- that Z3 reasons about.
intervalIntBounds :: Coercible t Int => Interval t -> ( Int, Int )
intervalIntBounds ( Interval ( Endpoint ( EarliestTime ( Time s ) ) clu_s ) ( Endpoint ( LatestTime ( Time e ) ) clu_e ) ) =
  ( case clu_s of { Exclusive -> coerce s + 1; _ -> coerce s }
  , case clu_e of { Exclusive -> coerce e - 1; _ -> coerce e }
  )

-- | Build a unary-scheduling model: one integer start-time variable per
-- task, constrained to lie within its availability, plus a pairwise non-overlap
-- (disjunctive) constraint enforcing the unary resource.
--
-- Returns each task's @(index, startVar, durationVar)@ in input order.
buildUnaryModel
  :: forall t staff
  .  Coercible t Int
  => [ Task ( Set staff ) t ]
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


-- | Decide feasibility of the unary scheduling problem with Z3 (no objective).
unaryScheduleFeasibleZ3
  :: forall t staff
  .  Coercible t Int
  => [ Task ( Set staff ) t ]
  -> IO ( Maybe [ Integer ] )
unaryScheduleFeasibleZ3 tasks = Z3.evalZ3 do
  ts <- buildUnaryModel tasks
  -- Check satisfiability and read back the start times (aligned with input order),
  -- or 'Nothing' if unsat or any variable is unevaluated.
  ( _res, mbStarts ) <- Z3.withModel \ model ->
    mapM ( Z3.evalInt model . ( \ ( _, t, _ ) -> t ) ) ts
  pure ( sequence =<< mbStarts )


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
