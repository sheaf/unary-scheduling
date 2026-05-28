{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Benchmarks for the LCG search over the unary-scheduling problem.
module Schedule.Bench
  ( benchmarks )
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
  ( StdGen, mkStdGen, randomR )

-- tasty
import Test.Tasty
  ( localOption )

-- tasty-bench
import Test.Tasty.Bench
  ( Benchmark, RelStDev(..), bgroup, bench, env, whnf )

-- text
import Data.Text
  ( Text )
import qualified Data.Text as Text
  ( pack )

-- unary-scheduling
import Schedule.Interval
  ( Clusivity(..), Endpoint(..), Interval(..), Intervals(..)
  , Measurable, mkIntervals
  )
import Schedule.LCG.Search
  ( SearchResult, defaultSearchOptions, lcgSearch )
import Schedule.Propagators
  ( basicPropagators )
import Schedule.Task
  ( Task(..) )
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

-- | Wrapper to give 'NFData' to the search result without exposing
-- the inner generics.
newtype SearchOutcome = SearchOutcome
  ( SearchResult () BenchTime )
  deriving newtype NFData
  deriving stock   Generic

-- | Run 'lcgSearch' with default options and basic propagators.
runLCG :: Instance -> SearchOutcome
runLCG inst = SearchOutcome ( lcgSearch defaultSearchOptions basicPropagators inst )

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

-- | Generate @n@ tasks, each available over @[0, horizon]@ with uniform
-- random durations in @[1, maxDur]@.
randomFullInstance :: Int -> Int -> Int -> Int -> Instance
randomFullInstance n horizon maxDur seed = build ( mkStdGen seed ) 0
  where
    build :: StdGen -> Int -> Instance
    build _ k | k >= n = []
    build g k =
      let ( d, g' ) = randomR ( 1, maxDur ) g
      in  fullTask horizon d ( Text.pack ( "t" ++ show k ) ) : build g' ( k + 1 )

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

-------------------------------------------------------------------------------
-- Suite.

benchmarks :: [ Benchmark ]
benchmarks =
  map ( localOption ( RelStDev 0.2 ) )
  [ bgroup "tight feasible (n tasks of duration d, horizon ≈ n·d)"
      [ envBench n d ( randomFullInstance n ( n * d ) d 42 )
      | ( n, d ) <- [ ( 4, 3 ), ( 6, 3 ), ( 8, 3 ) ]
      ]
  , bgroup "slack feasible (horizon = 4 · n · d, plenty of room)"
      [ envBench n d ( randomFullInstance n ( 4 * n * d ) d 42 )
      | ( n, d ) <- [ ( 4, 3 ), ( 6, 3 ), ( 8, 3 ) ]
      ]
  , bgroup "infeasible (total demand twice the horizon)"
      [ envBench n d ( overloadedInstance n d )
      | ( n, d ) <- [ ( 4, 3 ), ( 6, 3 ), ( 8, 3 ) ]
      ]
  , bgroup "two-segment availability (forces window-commitment branches)"
      [ env ( pure ( twoSegmentInstance n h 2 d ) ) \ inst ->
          bench
            ( "n=" ++ show n ++ " win=" ++ show h ++ " dur=" ++ show d )
            ( whnf runLCG inst )
      | ( n, h, d ) <- [ ( 4, 8, 2 ), ( 6, 12, 2 ) ]
      ]
  ]
  where
    envBench n d gen =
      env ( pure gen ) \ inst ->
        bench
          ( "n=" ++ show n ++ " dur=" ++ show d )
          ( whnf runLCG inst )
