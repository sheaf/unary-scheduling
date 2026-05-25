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

-- hedgehog
import Hedgehog
  ( Gen, Property
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
  ( Clusivity(..), Endpoint(..), Interval(..), Measurable(..), mkIntervals )
import Schedule.Propagators
  ( basicPropagators )
import Schedule.Task
  ( Task(..) )
import Schedule.Time
  ( Delta(..), Time(..), HandedTime(..) )

-- z3-oracle
import Schedule.Z3
  ( Z3Verdict(..), verifyAgainstZ3 )

--------------------------------------------------------------------------------
-- A small, bounded time type so generated instances stay cheap for Z3.

newtype TestTime = TestTime Int
  deriving newtype ( Eq, Ord, Num, Measurable )

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

-- | Generate a non-empty interval. Empty intervals (e.g. @[5,5)@, or @(5,6)@ which
-- holds no integer) would be silently dropped by 'mkIntervals', skewing the
-- generated task-count distribution, so we reject them up front.
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
-- Properties.

prop_propagation_sound_vs_z3 :: Property
prop_propagation_sound_vs_z3 = withTests 100 $ property do
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

tests :: TestTree
tests = testGroup "Z3 differential tests"
  [ testPropertyNamed
      "sound w.r.t. Z3 feasible schedules"
      "prop_propagation_sound_vs_z3"
      prop_propagation_sound_vs_z3
  ]
