{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

-- | Scheduling instance generators and pure solver runners for the
-- unary-scheduling benchmarks, with no dependency on @tasty@, @tasty-bench@,
-- or the Z3 oracle.
module Schedule.Bench.Instances
  ( -- * Time and instance types
    BenchTime(..), BenchTask, Instance
    -- * Runners
  , LCGOutcome(..), runLCG
  , PropOutcome(..), runPropOnly
    -- * Instance families
  , fullTask
  , randomInstanceAtUtilisation
  , overloadedInstance
  , twoSegmentInstance
  , tightCliqueInstance
  , chainedWindowInstance
  , chainedOverloadedInstance
  )
  where

-- base
import GHC.Generics
  ( Generic )

-- containers
import qualified Data.Sequence as Seq
  ( fromList )

-- deepseq
import Control.DeepSeq
  ( NFData )

-- random
import System.Random
  ( StdGen, mkStdGen, randomR, randomRs )

-- text
import Data.Text
  ( Text )
import qualified Data.Text as Text
  ( pack )

-- unary-scheduling
import Schedule.Interval
  ( Clusivity(..), Endpoint(..), Interval(..)
  , Measurable, mkIntervals
  )
import Schedule.LCG.Search
  ( SearchResult, defaultSearchOptions, lcgSearch )
import Schedule.Monitor
  ( Monitoring(..) )
import Schedule.Propagators
  ( basicPropagators, propagateConstraints )
import Schedule.Task
  ( ImmutableTaskInfos, Task(..) )
import Schedule.Time
  ( Delta(..), Time(..), HandedTime(..) )

-------------------------------------------------------------------------------
-- A small, bounded time type matching the test suite.

newtype BenchTime = BenchTime Int
  deriving newtype ( Eq, Ord, Num, Measurable, NFData )

instance Show BenchTime where
  show ( BenchTime t ) = show t

instance Bounded BenchTime where
  minBound = BenchTime 0
  maxBound = BenchTime 100000

type BenchTask = Task () BenchTime
type Instance  = [ ( BenchTask, Text ) ]

-------------------------------------------------------------------------------
-- The solvers under test (sans Z3, which lives in "Schedule.Bench").

-- | Wrapper to give 'NFData' to the search result.
newtype LCGOutcome = LCGOutcome
  ( SearchResult () BenchTime )
  deriving newtype NFData
  deriving stock   Generic

runLCG :: Instance -> LCGOutcome
runLCG inst = LCGOutcome ( lcgSearch @MonitoringOff defaultSearchOptions basicPropagators inst )

-- | The propagator fixpoint with no SAT search on top.
--
-- We force the final 'ImmutableTaskInfos' and the @Maybe Text@ error
-- channel, so the work is comparable to forcing 'LCGOutcome'.
data PropOutcome = PropOutcome
  !( ImmutableTaskInfos () BenchTime )
  !( Maybe Text )
  deriving stock    Generic
  deriving anyclass NFData

runPropOnly :: Instance -> PropOutcome
runPropOnly inst =
  case propagateConstraints inst 1000 basicPropagators of
    ( ti, _, mbErr ) -> PropOutcome ti mbErr

-------------------------------------------------------------------------------
-- Instance generators.

-- | Make a simple task with one availability interval @[0, horizon]@ and
-- the given duration.
fullTask :: Int -> Int -> Text -> ( BenchTask, Text )
fullTask horizon dur name =
  ( Task
      { taskAvailability = mkIntervals
          ( Seq.fromList
            [ Interval
              ( Endpoint ( EarliestTime ( Time ( BenchTime 0 ) ) ) Inclusive )
              ( Endpoint ( LatestTime   ( Time ( BenchTime horizon ) ) ) Inclusive )
            ]
          )
      , taskDuration     = Delta ( BenchTime dur )
      , taskInfo         = ()
      }
  , name
  )

-- | @n@ tasks sharing the single window @[0, horizon]@, with random durations
-- in @[1, maxDur]@, where the horizon is sized from the /realised/ total
-- demand so the resource runs at the requested @utilisation@ (= demand /
-- capacity).
randomInstanceAtUtilisation
  :: Double  -- ^ target utilisation, in @(0, 1]@ for a feasible instance
  -> Int     -- ^ number of tasks
  -> Int     -- ^ maximum task duration
  -> Int     -- ^ PRNG seed
  -> Instance
randomInstanceAtUtilisation utilisation n maxDur seed =
  [ fullTask horizon d ( Text.pack ( "t" ++ show k ) )
  | ( k, d ) <- zip [ 0 .. ] durations
  ]
  where
    durations :: [ Int ]
    durations = take n ( randomRs ( 1, maxDur ) ( mkStdGen seed ) )
    -- Size the window from the realised demand. 'max maxDur' keeps every
    -- individual task fitting even in degenerate (tiny-@n@) cases.
    horizon :: Int
    horizon = max maxDur ( ceiling ( fromIntegral ( sum durations ) / utilisation ) )

-- | An instance that's deliberately overloaded: @n@ tasks each of
-- duration @dur@ over a window of @floor (n * dur / 2)@ — total demand
-- twice the capacity, so the propagators or search must report infeasibility.
overloadedInstance :: Int -> Int -> Instance
overloadedInstance n dur =
  [ fullTask horizon dur ( Text.pack ( "ov" ++ show k ) )
  | k <- [ 0 .. n - 1 ]
  ]
  where
    horizon = ( n * dur ) `div` 2

-- | A two-segment instance: @n@ tasks each with two availability windows,
-- forcing the search to commit to which window each task lands in.
twoSegmentInstance :: Int -> Int -> Int
                   -> Int -> Instance
twoSegmentInstance n horizon gap dur =
  [ ( Task
        { taskAvailability = mkIntervals
            ( Seq.fromList
              [ Interval
                ( Endpoint ( EarliestTime ( Time ( BenchTime 0 ) ) ) Inclusive )
                ( Endpoint ( LatestTime   ( Time ( BenchTime horizon ) ) ) Inclusive )
              , Interval
                ( Endpoint ( EarliestTime ( Time ( BenchTime ( horizon + gap ) ) ) ) Inclusive )
                ( Endpoint ( LatestTime   ( Time ( BenchTime ( 2 * horizon + gap ) ) ) ) Inclusive )
              ]
            )
        , taskDuration     = Delta ( BenchTime dur )
        , taskInfo         = ()
        }
    , Text.pack ( "ts" ++ show k )
    )
  | k <- [ 0 .. n - 1 ]
  ]

-- | A /tight disjunctive clique/: @n@ duration-@d@ tasks, all sharing the
-- single window @[0, n·d)@. Total demand equals capacity, so every feasible
-- schedule is a permutation. Stresses pure precedence branching with no
-- helpful bound-tightening to fall back on.
tightCliqueInstance :: Int -> Int -> Instance
tightCliqueInstance n d =
  [ fullTask ( n * d ) d ( Text.pack ( "c" ++ show k ) )
  | k <- [ 0 .. n - 1 ]
  ]

-- | A /chained-window/ instance: task @k@ has the single availability
-- window @[k, k + window]@. Each task individually has @window@-many slots
-- of choice, but adjacent tasks compete for overlapping slots, forcing the
-- search to commit to an ordering.
--
-- For @window = 2@ and duration 1, this is the rolling-window analogue
-- of @n@-pigeon-into-@n+1@-holes: feasible (exactly @n+1@ solutions)
-- but requires actual SAT-side decisions.
chainedWindowInstance :: Int -> Int -> Int -> Instance
chainedWindowInstance n window dur =
  [ ( Task
        { taskAvailability = mkIntervals
            ( Seq.fromList
              [ Interval
                ( Endpoint ( EarliestTime ( Time ( BenchTime k ) ) ) Inclusive )
                ( Endpoint ( LatestTime   ( Time ( BenchTime ( k + window ) ) ) ) Inclusive )
              ]
            )
        , taskDuration     = Delta ( BenchTime dur )
        , taskInfo         = ()
        }
    , Text.pack ( "cw" ++ show k )
    )
  | k <- [ 0 .. n - 1 ]
  ]

-- | Same shape as 'chainedWindowInstance' but with an extra task that
-- pushes total demand past capacity; intended as a /structured/
-- infeasibility (each task individually fits, but the global schedule
-- cannot be completed).
chainedOverloadedInstance :: Int -> Int -> Int -> Instance
chainedOverloadedInstance n window dur =
  chainedWindowInstance n window dur
  ++
  -- One extra task in the middle of the window.
  [ fullTask ( n + window ) dur ( Text.pack ( "cw-extra" ) ) ]
