{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE TypeApplications           #-}

module Schedule.Test where

-- containers
import qualified Data.Sequence as Seq
  ( fromList )

-- text
import Data.Text
  ( Text )
import qualified Data.Text as Text

-- vector
import qualified Data.Vector as Boxed.Vector
  ( fromList )

-- unary-scheduling
import Schedule.Interval
  ( Interval(..), Intervals(..) )
import Schedule.Propagators
import Schedule.Task
  ( Task(..), TaskInfos(..) )
import Schedule.Time
  ( Time(..), Delta(..) )

-------------------------------------------------------------------------------
-- Notion of time used for the tests.

-- Time of day in minutes.
newtype Minutes = Minutes { minutes :: Int }
  deriving newtype ( Eq, Ord, Num )
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
    { taskAvailability = Intervals ( Seq.fromList $ map ( \ ( s, e ) -> Time s :<=..<= Time e ) ivals )
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

testPrune :: Either Text ()
testPrune = case mbExceptText of
  Just err
    -> Left err
  _ 
    | taskAvails endTasks /= Boxed.Vector.fromList expectedTasks
    -> Left ( "expected:\n" <> Text.pack ( show expectedTasks ) <> "\nactual:\n" <> Text.pack ( show ( taskAvails endTasks ) ) )
  _ -> Right ()
  where
    ( endTasks, _endText, mbExceptText ) = propagateConstraints pruneTasks 10 prunePropagators
    expectedTasks :: [ TimeOfDayTask ]
    expectedTasks =
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
