{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE ScopedTypeVariables         #-}

-- | Property-based differential testing against Z3.
module Schedule.Z3.Test ( tests ) where

-- containers
import qualified Data.Sequence as Seq
  ( fromList )

-- text
import Data.Text
  ( Text )
import qualified Data.Text as Text
  ( pack, unpack )

-- base
import Control.Monad
  ( when )
import Data.Coerce
  ( Coercible )
import Data.Foldable
  ( toList )

-- hedgehog
import Hedgehog
  ( Gen, Property, PropertyT
  , (===)
  , annotate, annotateShow, evalIO, failure, forAll, property, success, withTests
  )
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

-- tasty
import Test.Tasty
  ( TestTree, testGroup )
import Test.Tasty.Hedgehog
  ( testPropertyNamed )

-- unary-scheduling
import Schedule.Interval
  ( Clusivity(..), Endpoint(..), Interval(..), Intervals(..), Measurable(..), mkIntervals )
import Schedule.LCG.Search
  ( SearchResult(..), defaultSearchOptions, lcgSearch )
import Schedule.Monad
  ( SchedulableData )
import Schedule.Monitor
  ( Monitoring(..) )
import Schedule.Propagators
  ( Propagator, basicPropagators, coarsen, propagateConstraints
  , prunePropagator, timetablePropagator, overloadPropagator
  , detectablePrecedencesPropagator, detectableSuccedencesPropagator
  , notLastPropagator, notFirstPropagator
  , edgeLastPropagator, edgeFirstPropagator
  , predecessorPropagator, successorPropagator
  )
import Schedule.Task
  ( Task(..), TaskInfos(..), ImmutableTaskInfos )
import Schedule.Time
  ( Delta(..), Time(..), HandedTime(..) )

-- z3-oracle
import Schedule.Z3
  ( Z3Verdict(..), verifyAgainstZ3, intervalIntBounds, z3Feasible )

--------------------------------------------------------------------------------
-- A small, bounded time type so generated instances stay cheap for Z3.

newtype TestTime = TestTime Int
  deriving newtype ( Eq, Ord, Num, Real, Measurable )

instance Bounded TestTime where
  minBound = TestTime 0
  maxBound = TestTime horizon

instance Show TestTime where
  show ( TestTime t ) = show t

-- | The scheduling horizon: all generated times lie in @[0, horizon]@.
horizon :: Int
horizon = 32

type TestTask = Task () TestTime

--------------------------------------------------------------------------------
-- Generators.

-- | Generate a (non-empty) interval.
genInterval :: Gen ( Interval TestTime )
genInterval = Gen.filter ( not . isEmpty ) do
  a     <- Gen.int ( Range.linear 0 horizon )
  b     <- Gen.int ( Range.linear 0 horizon )
  s_clu <- Gen.element [ Exclusive, Inclusive ]
  e_clu <- Gen.element [ Exclusive, Inclusive ]
  let lo = min a b
      hi = max a b
  pure $
    Interval
      ( Endpoint ( EarliestTime ( Time ( TestTime lo ) ) ) s_clu )
      ( Endpoint ( LatestTime   ( Time ( TestTime hi ) ) ) e_clu )

genTask :: Gen TestTask
genTask = do
  dur   <- Gen.int ( Range.linear 1 ( horizon `div` 8 ) )
  -- At least one availability interval, so the task is not trivially unschedulable.
  ivals <- Gen.list ( Range.linear 1 3 ) genInterval
  pure
    Task
      { taskAvailability = mkIntervals ( Seq.fromList ivals )
      , taskDuration     = Delta ( TestTime dur )
      , taskInfo         = ()
      }

genInstance :: Gen [ ( TestTask, Text ) ]
genInstance = do
  tasks <- Gen.list ( Range.linear 1 5 ) genTask
  pure $ zipWith ( \ i task -> ( task, "task" <> Text.pack ( show i ) ) ) [ 0 :: Int .. ] tasks

--------------------------------------------------------------------------------
-- A structured regression fixture (needs a longer horizon than 'TestTime').

newtype RehTime = RehTime Int
  deriving newtype ( Eq, Ord, Num, Real, Measurable )

instance Bounded RehTime where
  minBound = RehTime 0
  maxBound = RehTime 128

instance Show RehTime where
  show ( RehTime t ) = show t

-- | A concrete tight multi-day rehearsal.
--
-- Serves as a regression test for an ordering matrix double-write bug.
rehearsalRegressionInstance :: [ ( Task () RehTime, Text ) ]
rehearsalRegressionInstance =
  zipWith ( \ i ( dur, wins ) -> ( mkTask dur wins, "song" <> Text.pack ( show i ) ) )
    [ 0 :: Int .. ]
    [ ( 6, [ (18,34), (36,52), (72,88) ] )
    , ( 7, [ (0,16), (18,34), (36,52), (72,88) ] )
    , ( 7, [ (0,16), (36,52) ] )
    , ( 8, [ (54,70) ] )
    , ( 2, [ (18,34), (36,52), (72,88) ] )
    , ( 6, [ (0,16), (54,70) ] )
    , ( 2, [ (72,88) ] )
    , ( 4, [ (0,16), (54,70) ] )
    , ( 2, [ (0,16), (36,52) ] )
    , ( 1, [ (0,16) ] )
    , ( 3, [ (0,16), (54,70), (72,88) ] )
    , ( 3, [ (0,16), (36,52), (54,70), (72,88) ] )
    , ( 1, [ (36,52), (54,70), (72,88) ] )
    , ( 2, [ (72,88) ] )
    , ( 5, [ (72,88) ] )
    , ( 2, [ (0,16), (18,34), (36,52) ] )
    , ( 7, [ (36,52), (72,88) ] )
    , ( 8, [ (18,34), (72,88) ] )
    , ( 4, [ (18,34) ] )
    , ( 5, [ (36,52) ] )
    ]
  where
    mkTask :: Int -> [ ( Int, Int ) ] -> Task () RehTime
    mkTask dur wins =
      Task
        { taskAvailability = mkIntervals ( Seq.fromList ( map window wins ) )
        , taskDuration     = Delta ( RehTime dur )
        , taskInfo         = ()
        }
    window :: ( Int, Int ) -> Interval RehTime
    window ( lo, hi ) =
      Interval
        ( Endpoint ( EarliestTime ( Time ( RehTime lo ) ) ) Inclusive )
        ( Endpoint ( LatestTime   ( Time ( RehTime hi ) ) ) Inclusive )

--------------------------------------------------------------------------------
-- Properties.

-- | Check that the LCG search verdict (using the given propagators) agrees with
-- Z3's feasibility verdict on the given instance.
lcgVerdictMatchesZ3
  :: forall task t
  .  ( Real t, Num t, Measurable t, Bounded t, Show t, Show task
     , Coercible t Int
     , SchedulableData [ ( Task task t, Text ) ] task t
     )
  => [ Propagator task t ]
  -> [ ( Task task t, Text ) ]
  -> PropertyT IO ()
lcgVerdictMatchesZ3 props named = do
  mbStarts <- evalIO ( z3Feasible ( map fst named ) )
  let res = lcgSearch @MonitoringOff defaultSearchOptions props named
  case ( solution res, mbStarts ) of
    ( Right _, Just _ )    -> success
    ( Left _,  Nothing )   -> success
    ( Right _, Nothing )   -> do
      annotate "LCG returned a solution but Z3 reports infeasibility."
      failure
    ( Left err, Just sts ) -> do
      annotate "LCG returned infeasible but Z3 found a schedule:"
      annotateShow sts
      annotate ( Text.unpack err )
      failure

prop_rehearsal_regression :: Property
prop_rehearsal_regression = withTests 1 $ property $
  lcgVerdictMatchesZ3 basicPropagators rehearsalRegressionInstance

baseOnlyProps :: ( Num t, Measurable t, Bounded t, Show t ) => [ Propagator task t ]
baseOnlyProps =
  [ prunePropagator, timetablePropagator, overloadPropagator
  , predecessorPropagator, successorPropagator
  ]

prop_lcg_base_only_matches_z3 :: Property
prop_lcg_base_only_matches_z3 = withTests 2000 $ property do
  namedTasks <- forAll genInstance
  lcgVerdictMatchesZ3 baseOnlyProps namedTasks

prop_rehearsal_base_only :: Property
prop_rehearsal_base_only = withTests 1 $ property $
  lcgVerdictMatchesZ3 baseOnlyProps rehearsalRegressionInstance

prop_propagation_sound_vs_z3 :: Property
prop_propagation_sound_vs_z3 = withTests 1000 $ property do
  namedTasks <- forAll genInstance
  verdict    <- evalIO ( verifyAgainstZ3 basicPropagators namedTasks )
  case verdict of
    Z3Infeasible       -> success
    Consistent _       -> success
    NativeRejected err -> do
      annotate ( "rejected a Z3-feasible schedule:\n" <> Text.unpack err )
      failure
    NativePruned bad   -> do
      annotate "pruned the Z3 start of these task indices:"
      annotateShow bad
      failure

-- | Canonical availabilities.
canonicalAvails :: ImmutableTaskInfos () TestTime -> [ [ ( Int, Int ) ] ]
canonicalAvails ti =
  [ map intervalIntBounds ( toList ( intervals ( taskAvailability tk ) ) )
  | tk <- toList ( taskAvails ti )
  ]

-- | A propagation result must be a fixpoint: re-propagating it with the
-- conservative coarse waking (which runs every propagator) must not tighten
-- anything further.
reachesFixpoint :: [ Propagator () TestTime ] -> Property
reachesFixpoint propagators = withTests 1000 $ property do
  namedTasks <- forAll genInstance
  let ( ti, _, err ) = propagateConstraints namedTasks 1000 propagators
  when ( null err ) do
    -- Re-saturate from the result, conservatively (coarse runs every propagator).
    let ( reTi, _, reErr ) = propagateConstraints ti 1000 ( map coarsen basicPropagators )
    -- Re-propagation must not newly discover infeasibility...
    reErr === Nothing
    -- ...nor tighten any domain.
    canonicalAvails ti === canonicalAvails reTi

-- | Order-independence (confluence) check for a propagator list: fine-grained
-- and coarse waking must reach the same (canonical) fixpoint.
confluentOn :: [ Propagator () TestTime ] -> Property
confluentOn props = withTests 1000 $ property do
  namedTasks <- forAll genInstance
  let
    ( a, _, ea ) = propagateConstraints namedTasks 1000 props
    ( b, _, eb ) = propagateConstraints namedTasks 1000 ( map coarsen props )
  null ea === null eb
  when ( null ea && null eb ) do
    canonicalAvails a === canonicalAvails b

-- | The LCG search's verdict (feasible / infeasible) must agree with Z3's
-- on every instance.
prop_lcg_matches_z3 :: Property
prop_lcg_matches_z3 = withTests 1000 $ property do
  namedTasks <- forAll genInstance
  lcgVerdictMatchesZ3 basicPropagators namedTasks

-- Various subsets of propagators tested separately.
coreProps, withDetectableProps, withEdgeProps, withoutMatrixProps
  :: [ Propagator () TestTime ]
coreProps =
  [ prunePropagator, timetablePropagator, overloadPropagator ]
withDetectableProps =
  coreProps ++ [ detectablePrecedencesPropagator, detectableSuccedencesPropagator ]
withEdgeProps =
  coreProps ++ [ edgeLastPropagator, edgeFirstPropagator ]
-- everything except the precedence-matrix propagators (the matrix is still
-- written by detectable/edge-finding, just never read back)
withoutMatrixProps =
  [ prunePropagator, timetablePropagator, overloadPropagator
  , detectablePrecedencesPropagator, detectableSuccedencesPropagator
  , notLastPropagator, notFirstPropagator
  , edgeLastPropagator, edgeFirstPropagator
  ]

tests :: TestTree
tests = testGroup "Differential tests"
  [ testPropertyNamed
      "sound w.r.t. Z3 feasible schedules"
      "prop_propagation_sound_vs_z3"
      prop_propagation_sound_vs_z3
  , testPropertyNamed
      "coarse propagation reaches a fixpoint (event queue does not stop early)"
      "prop_coarse_reaches_fixpoint"
      ( reachesFixpoint ( map coarsen basicPropagators ) )
  , testPropertyNamed
      "fine-grained waking reaches a fixpoint (no under-waking)"
      "prop_fine_reaches_fixpoint"
      ( reachesFixpoint basicPropagators )
  , testGroup "confluence"
      [ testPropertyNamed "core (prune+timetable+overload)" "confluent_core"       ( confluentOn coreProps )
      , testPropertyNamed "core + detectable precedences"   "confluent_detectable" ( confluentOn withDetectableProps )
      , testPropertyNamed "core + edge finding"             "confluent_edge"       ( confluentOn withEdgeProps )
      , testPropertyNamed "all but the precedence matrix"   "confluent_no_matrix"  ( confluentOn withoutMatrixProps )
      , testPropertyNamed "all propagators (full set)"      "confluent_full"       ( confluentOn basicPropagators )
      ]
  , testPropertyNamed
      "LCG search verdict matches Z3"
      "prop_lcg_matches_z3"
      prop_lcg_matches_z3
  , testPropertyNamed
      "LCG vs Z3: tight rehearsal instance"
      "prop_rehearsal_regression"
      prop_rehearsal_regression
  , testGroup "verdict invariant under propagator subset"
      [ testPropertyNamed
          "base-only (prune+timetable+overload+matrix) verdict matches Z3"
          "prop_lcg_base_only_matches_z3"
          prop_lcg_base_only_matches_z3
      , testPropertyNamed
          "base-only vs Z3: tight rehearsal instance"
          "prop_rehearsal_base_only"
          prop_rehearsal_base_only
      ]
  ]
