{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE TypeApplications           #-}

module Schedule.Test ( tests ) where

-- containers
import qualified Data.Sequence as Seq
  ( fromList )

-- tasty
import Test.Tasty
  ( TestTree, testGroup )
import Test.Tasty.HUnit
  ( Assertion, testCase, assertBool, assertFailure, (@?=) )

-- text
import Data.Text
  ( Text )
import qualified Data.Text as Text
  ( unpack )

-- vector
import qualified Data.Vector as Boxed
  ( Vector )
import qualified Data.Vector as Boxed.Vector
  ( fromList, (!) )

-- unary-scheduling
import Schedule.Interval
  ( Interval(..), Intervals(..), Endpoint(..), Measurable(..), inside )
import Schedule.Propagators
import Schedule.Task
  ( Task(..), TaskInfos(..), est, lct )
import Schedule.Time
  ( Time(..), Delta(..), HandedTime(..) )

-------------------------------------------------------------------------------
-- Notion of time used for the tests.

-- Time of day in minutes.
newtype Minutes = Minutes { minutes :: Int }
  deriving newtype ( Eq, Ord, Measurable, Num )
instance Bounded Minutes where
  minBound = 0
  maxBound = 24 * 60
instance Show Minutes where
  show ( Minutes m ) = show hrs <> "h" <> show mins
    where
      (hrs, mins) = m `divMod` 60

h :: Int -> Int -> Minutes
h hrs mins = Minutes ( 60 * hrs + mins )

type TimeOfDayTask = Task () Minutes

timeOfDayTask :: Minutes -> [ ( Minutes, Minutes ) ] -> TimeOfDayTask
timeOfDayTask delta ivals =
  Task
    { taskAvailability = Intervals ( Seq.fromList $ map ( \ ( s, e ) -> Time s :<=..< Time e ) ivals )
    , taskDuration     = Delta delta
    , taskInfo         = ()
    }

-------------------------------------------------------------------------------
-- Test 'pruneIntervals' propagator.

prunePropagators :: [ Propagator () Minutes ]
prunePropagators = [ prunePropagator ]

pruneTasks :: [ ( TimeOfDayTask, Text ) ]
pruneTasks =
  [ ( task1, "#1 (no prune 1)")
  , ( task2, "#1 (no prune 2)" )
  , ( task3, "#2 (partially prune)" )
  , ( task4, "#3 (fully prune)" )
  ]
  where
    task1 = timeOfDayTask ( Minutes 30 ) []
    task2 = timeOfDayTask ( Minutes 15 ) [ ( 07 `h` 00, 08 `h` 00 ), ( 10 `h` 00, 12 `h` 00 ) ]
    task3 = timeOfDayTask ( Minutes 30 ) [ ( 08 `h` 00, 09 `h` 00 ), ( 11 `h` 00, 11 `h` 15 ), ( 11 `h` 20, 11 `h` 30 ) ]
    task4 = timeOfDayTask ( Minutes 60 ) [ ( 09 `h` 15, 10 `h` 00 ), ( 14 `h` 00, 14 `h` 30 ) ]

expectedPruneTasks :: [ TimeOfDayTask ]
expectedPruneTasks =
  [ timeOfDayTask ( Minutes 30 ) []
  , timeOfDayTask ( Minutes 15 ) [ ( 07 `h` 00, 08 `h` 00 ), ( 10 `h` 00, 12 `h` 00 ) ]
  , timeOfDayTask ( Minutes 30 ) [ ( 08 `h` 00, 09 `h` 00 ) ]
  , timeOfDayTask ( Minutes 60 ) []
  ]

-------------------------------------------------------------------------------
-- Test 'overloadCheck'.

overloadPropagators :: [ Propagator () Minutes ]
overloadPropagators = [ overloadPropagator ]

overloadTasks1 :: [ ( TimeOfDayTask, Text ) ]
overloadTasks1 = [ ( task, "#1 (overloaded)" ) ]
  where
    task = timeOfDayTask ( Minutes 30 ) [ ]

overloadTasks2 :: [ ( TimeOfDayTask, Text ) ]
overloadTasks2 = [ ( task, "#1 (overloaded)" ) ]
  where
    task = timeOfDayTask ( Minutes 30 ) [ ( 05 `h` 00, 05 `h` 15 ) ]

overloadTasks3 :: [ ( TimeOfDayTask, Text ) ]
overloadTasks3 = [ ( task1, "#1" ), ( task2, "#2"), ( task3, "#3" ) ]
  where
    task1 = timeOfDayTask ( Minutes 5 ) [ ( 00 `h` 00, 00 `h` 13 ) ]
    task2 = timeOfDayTask ( Minutes 5 ) [ ( 00 `h` 01, 00 `h` 14 ) ]
    task3 = timeOfDayTask ( Minutes 6 ) [ ( 00 `h` 00, 00 `h` 13 ) ]

overloadTasks4 :: [ ( TimeOfDayTask, Text ) ]
overloadTasks4 = [ ( task, "#1 (not overloaded)" ) ]
  where
    task = timeOfDayTask ( Minutes 30 ) [ ( 04 `h` 00, 04 `h` 30 ) ]

-------------------------------------------------------------------------------
-- Test 'timetable' propagator.

timetablePropagators :: [ Propagator () Minutes ]
timetablePropagators = [ timetablePropagator ]

timetableTasks :: [ ( TimeOfDayTask, Text ) ]
timetableTasks =
  [ ( task1, "#1 (necessary component)" )
  , ( task2, "#2 (unaffected)" )
  , ( task3, "#3 (overlaps with necessary component)" )
  ]
  where
    task1 = timeOfDayTask ( Minutes 60 ) [ ( 07 `h` 15, 08 `h` 45 ) ] -- must run between 7h45 and 8h15
    task2 = timeOfDayTask ( Minutes 15 ) [ ( 11 `h` 15, 12 `h` 00 ) ]
    task3 = timeOfDayTask ( Minutes 30 ) [ ( 06 `h` 15, 07 `h` 00 ), ( 08 `h` 00, 11 `h` 00 ) ]

-------------------------------------------------------------------------------
-- Test detectable precedences.

detectableSuccedencesPropagators :: [ Propagator () Minutes ]
detectableSuccedencesPropagators = [ detectablePrecedencesPropagator ]

-- | Expect constraint: task #3 must be last, and thus start no earlier than 00h10.
succedenceTasks :: [ ( TimeOfDayTask, Text ) ]
succedenceTasks = [ ( task1, "#1" ), ( task2, "#2"), ( task3, "#3 (last)" ) ]
  where
    task1 = timeOfDayTask ( Minutes 5 ) [ ( 00 `h` 00, 00 `h` 13 ) ]
    task2 = timeOfDayTask ( Minutes 5 ) [ ( 00 `h` 01, 00 `h` 14 ) ]
    task3 = timeOfDayTask ( Minutes 3 ) [ ( 00 `h` 07, 00 `h` 17 ) ]

detectablePrecedencesPropagators :: [ Propagator () Minutes ]
detectablePrecedencesPropagators = [ detectableSuccedencesPropagator ]

-- | Expect constraint: task #3 must be first, and thus end no later than 00h07.
precedenceTasks :: [ ( TimeOfDayTask, Text ) ]
precedenceTasks = [ ( task1, "#1" ), ( task2, "#2"), ( task3, "#3 (first)" ) ]
  where
    task1 = timeOfDayTask ( Minutes 5 ) [ ( 00 `h` 04, 00 `h` 17 ) ]
    task2 = timeOfDayTask ( Minutes 5 ) [ ( 00 `h` 03, 00 `h` 16 ) ]
    task3 = timeOfDayTask ( Minutes 3 ) [ ( 00 `h` 00, 00 `h` 10 ) ]

-------------------------------------------------------------------------------
-- Test 'notExtremal' propagators.

notLastPropagators :: [ Propagator () Minutes ]
notLastPropagators = [ notLastPropagator ]

-- | Expect constraint: task #3 must not be last, and thus finish no later than 00h17.
notLastTasks :: [ ( TimeOfDayTask, Text ) ]
notLastTasks = [ ( task1, "#1" ), ( task2, "#2"), ( task3, "#3 (not last)" ) ]
  where
    task1 = timeOfDayTask ( Minutes 11 ) [ ( 00 `h` 00, 00 `h` 25 ) ]
    task2 = timeOfDayTask ( Minutes 10 ) [ ( 00 `h` 01, 00 `h` 27 ) ]
    task3 = timeOfDayTask ( Minutes 2  ) [ ( 00 `h` 04, 00 `h` 20 ) ]

notFirstPropagators :: [ Propagator () Minutes ]
notFirstPropagators = [ notFirstPropagator ]

-- | Expect constraint: task #3 must not be first, and thus start no earlier than 00h10.
notFirstTasks :: [ ( TimeOfDayTask, Text ) ]
notFirstTasks = [ ( task1, "#1" ), ( task2, "#2"), ( task3, "#3 (not first)" ) ]
  where
    task1 = timeOfDayTask ( Minutes 11 ) [ ( 00 `h` 02, 00 `h` 27 ) ]
    task2 = timeOfDayTask ( Minutes 10 ) [ ( 00 `h` 00, 00 `h` 26 ) ]
    task3 = timeOfDayTask ( Minutes 2  ) [ ( 00 `h` 07, 00 `h` 23 ) ]

-------------------------------------------------------------------------------
-- Test 'edgeFinding' propagators.

edgeLastPropagators :: [ Propagator () Minutes ]
edgeLastPropagators = [ edgeLastPropagator ]

-- | Expect constraint: task #1 must be last, and thus start after 00h18.
edgeLastTasks1 :: [ ( TimeOfDayTask, Text ) ]
edgeLastTasks1 = [ ( task1, "#1 (last)" ), ( task2, "#2"), ( task3, "#3"), ( task4, "#4") ]
  where
    task1 = timeOfDayTask ( Minutes 4 ) [ ( 00 `h` 04, 00 `h` 30 ) ]
    task2 = timeOfDayTask ( Minutes 3 ) [ ( 00 `h` 05, 00 `h` 13 ) ]
    task3 = timeOfDayTask ( Minutes 3 ) [ ( 00 `h` 05, 00 `h` 13 ) ]
    task4 = timeOfDayTask ( Minutes 5 ) [ ( 00 `h` 13, 00 `h` 18 ) ]

-- | Expect no new constraints.
edgeLastTasks2 :: [ ( TimeOfDayTask, Text ) ]
edgeLastTasks2 = [ ( task1, "#1 (last)" ), ( task2, "#2"), ( task3, "#3"), ( task4, "#4") ]
  where
    task1 = timeOfDayTask ( Minutes 4 ) [ ( 00 `h` 19, 00 `h` 30 ) ]
    task2 = timeOfDayTask ( Minutes 3 ) [ ( 00 `h` 05, 00 `h` 13 ) ]
    task3 = timeOfDayTask ( Minutes 3 ) [ ( 00 `h` 05, 00 `h` 13 ) ]
    task4 = timeOfDayTask ( Minutes 5 ) [ ( 00 `h` 13, 00 `h` 18 ) ]

edgeFirstPropagators :: [ Propagator () Minutes ]
edgeFirstPropagators = [ edgeFirstPropagator ]

-- | Expect constraint: task #1 must be last, and thus start after 00h18.
edgeFirstTasks1 :: [ ( TimeOfDayTask, Text ) ]
edgeFirstTasks1 = [ ( task1, "#1 (first)" ), ( task2, "#2"), ( task3, "#3"), ( task4, "#4") ]
  where
    task1 = timeOfDayTask ( Minutes 4 ) [ ( 00 `h`  0, 00 `h` 26 ) ]
    task2 = timeOfDayTask ( Minutes 3 ) [ ( 00 `h` 17, 00 `h` 25 ) ]
    task3 = timeOfDayTask ( Minutes 3 ) [ ( 00 `h` 17, 00 `h` 25 ) ]
    task4 = timeOfDayTask ( Minutes 5 ) [ ( 00 `h` 12, 00 `h` 17 ) ]

-------------------------------------------------------------------------------
-- Test tree.

tests :: TestTree
tests = testGroup "Schedule.Propagators"
  [ testGroup "prune"
      [ testCase "removes slots too short for the task" $
          case runProp pruneTasks prunePropagators of
            Left err     -> assertFailure ( Text.unpack err )
            Right avails -> avails @?= Boxed.Vector.fromList expectedPruneTasks
      ]
  , testGroup "overload check"
      [ testCase "empty availability overloads"            $ assertOverloaded    overloadTasks1
      , testCase "task longer than its slot overloads"     $ assertOverloaded    overloadTasks2
      , testCase "three competing tasks overload"          $ assertOverloaded    overloadTasks3
      , testCase "task fitting its slot does not overload" $ assertNotOverloaded overloadTasks4
      ]
  , testGroup "timetable"
      [ testCase "necessary component removed from the overlapping task" $
          case runProp timetableTasks timetablePropagators of
            Left err     -> assertFailure ( Text.unpack err )
            Right avails -> do
              let task3 = avails Boxed.Vector.! 2
              assertBool "08h00 (within #1's necessary component) should be removed from #3"
                ( not ( inside ( Time ( 8 `h` 0 ) ) ( taskAvailability task3 ) ) )
              assertBool "06h30 (outside the component) should be retained on #3"
                ( inside ( Time ( 6 `h` 30 ) ) ( taskAvailability task3 ) )
      ]
  , testGroup "detectable precedences"
      [ testCase "#3 must succede the others (est = 00h10)" $ assertEstAt succedenceTasks detectableSuccedencesPropagators 2 10
      , testCase "#3 must precede the others (lct = 00h07)" $ assertLctAt precedenceTasks detectablePrecedencesPropagators 2 07
      ]
  , testGroup "not first / not last"
      [ testCase "#3 cannot be last (lct = 00h17)"  $ assertLctAt notLastTasks  notLastPropagators  2 17
      , testCase "#3 cannot be first (est = 00h10)" $ assertEstAt notFirstTasks notFirstPropagators 2 10
      ]
  , testGroup "edge finding"
      [ testCase "#1 must be last (est = 00h18)"          $ assertEstAt edgeLastTasks1  edgeLastPropagators  0 18
      , testCase "no new constraint when #1 already fits" $ assertEstAt edgeLastTasks2  edgeLastPropagators  0 19
      , testCase "#1 must be first (lct = 00h12)"         $ assertLctAt edgeFirstTasks1 edgeFirstPropagators 0 12
      ]
  ]

-------------------------------------------------------------------------------
-- Helpers.

-- | Run propagation to a fixpoint, returning the final task availabilities,
-- or the overload error if the resource proved unschedulable.
runProp
  :: [ ( TimeOfDayTask, Text ) ]
  -> [ Propagator () Minutes ]
  -> Either Text ( Boxed.Vector TimeOfDayTask )
runProp tasks props =
  case propagateConstraints tasks 10 props of
    ( _,   _, Just err ) -> Left err
    ( end, _, Nothing  ) -> Right ( taskAvails end )

-- | Earliest start time / latest completion time of a task, as a raw minute count.
estMin, lctMin :: TimeOfDayTask -> Int
estMin = minutes . getTime . handedTime . endpoint . est
lctMin = minutes . getTime . handedTime . endpoint . lct

-- | Assert the earliest start time of the task at the given index after propagation.
assertEstAt :: [ ( TimeOfDayTask, Text ) ] -> [ Propagator () Minutes ] -> Int -> Int -> Assertion
assertEstAt tasks props idx expected =
  case runProp tasks props of
    Left err     -> assertFailure ( "unexpected overload:\n" <> Text.unpack err )
    Right avails -> estMin ( avails Boxed.Vector.! idx ) @?= expected

-- | Assert the latest completion time of the task at the given index after propagation.
assertLctAt :: [ ( TimeOfDayTask, Text ) ] -> [ Propagator () Minutes ] -> Int -> Int -> Assertion
assertLctAt tasks props idx expected =
  case runProp tasks props of
    Left err     -> assertFailure ( "unexpected overload:\n" <> Text.unpack err )
    Right avails -> lctMin ( avails Boxed.Vector.! idx ) @?= expected

-- | Assert that the unary resource is overloaded.
assertOverloaded :: [ ( TimeOfDayTask, Text ) ] -> Assertion
assertOverloaded tasks =
  case runProp tasks overloadPropagators of
    Left _  -> pure ()
    Right _ -> assertFailure "expected the resource to be overloaded, but propagation succeeded"

-- | Assert that the unary resource is not overloaded.
assertNotOverloaded :: [ ( TimeOfDayTask, Text ) ] -> Assertion
assertNotOverloaded tasks =
  case runProp tasks overloadPropagators of
    Left err -> assertFailure ( "expected no overload, but got:\n" <> Text.unpack err )
    Right _  -> pure ()
