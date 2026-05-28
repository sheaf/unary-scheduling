{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Benchmarks for the unary-scheduling solvers.
--
-- For each instance family we report three timings on the same instance:
--
--  * /LCG/         — the full 'lcgSearch' (BCP + theory propagation + 1-UIP).
--  * /propagators/ — 'propagateConstraints' alone, no SAT search.
--  * /Z3/          — 'z3Feasible' as an external oracle.
--
-- The ratio @LCG / propagators@ quantifies how much we are paying for the
-- SAT integration on instances the propagators alone can fully decide;
-- the ratio @LCG / Z3@ is the north-star comparison against an industrial
-- solver. See @bench/SAT/Bench.hs@ for the SAT-core-only counterpart.
module Schedule.Bench
  ( benchmarks )
  where

-- base
import Data.Maybe
  ( isJust )
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
  ( localOption, mkTimeout )

-- tasty-bench
import Test.Tasty.Bench
  ( Benchmark, RelStDev(..), bgroup, bench, env, whnf, nfIO )

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
import Schedule.Propagators
  ( basicPropagators, propagateConstraints )
import Schedule.Task
  ( ImmutableTaskInfos, Task(..) )
import Schedule.Time
  ( Delta(..), Time(..), HandedTime(..) )

-- z3-oracle
import Schedule.Z3
  ( z3Feasible )

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
-- The three solvers under test.

-- | Wrapper to give 'NFData' to the search result.
newtype LCGOutcome = LCGOutcome
  ( SearchResult () BenchTime )
  deriving newtype NFData
  deriving stock   Generic

runLCG :: Instance -> LCGOutcome
runLCG inst = LCGOutcome ( lcgSearch defaultSearchOptions basicPropagators inst )

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

-- | Z3 feasibility check (no objective). Returns 'True' iff Z3 reports a
-- satisfying schedule exists; the actual start times are forced but
-- discarded by 'isJust' to match the bool-valued verdict.
runZ3 :: Instance -> IO Bool
runZ3 inst = isJust <$> z3Feasible ( map fst inst )

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

-------------------------------------------------------------------------------
-- Suite.

-- | Three benchmarks (LCG, propagators only, Z3) sharing one cached
-- instance, presented as a labelled group.
triple :: String -> Instance -> Benchmark
triple label inst =
  env ( pure inst ) \ i ->
    bgroup label
      [ bench "LCG"         ( whnf runLCG i )
      , bench "propagators" ( whnf runPropOnly i )
      , bench "Z3"          ( nfIO ( runZ3 i ) )
      ]

benchmarks :: [ Benchmark ]
benchmarks =
  -- tolerate higher variance to avoid tests taking too long
  map ( localOption ( RelStDev 0.1 ) . localOption ( mkTimeout 5_000_000 ) )
  [ bgroup "tight feasible (horizon ≈ n·d)"
      [ triple ( "n=" ++ show n ++ " d=" ++ show d )
               ( randomFullInstance n ( n * d ) d 42 )
      | ( n, d ) <- [ ( 4, 3 ), ( 6, 3 ), ( 8, 3 ), ( 12, 3 ), ( 16, 3 ) ]
      ]
  , bgroup "slack feasible (horizon = 4·n·d)"
      [ triple ( "n=" ++ show n ++ " d=" ++ show d )
               ( randomFullInstance n ( 4 * n * d ) d 42 )
      | ( n, d ) <- [ ( 4, 3 ), ( 6, 3 ), ( 8, 3 ), ( 12, 3 ), ( 16, 3 ) ]
      ]
  , bgroup "infeasible (demand twice the horizon)"
      [ triple ( "n=" ++ show n ++ " d=" ++ show d )
               ( overloadedInstance n d )
      | ( n, d ) <- [ ( 4, 3 ), ( 6, 3 ), ( 8, 3 ), ( 12, 3 ), ( 16, 3 ) ]
      ]
  , bgroup "two-segment availability"
      [ triple ( "n=" ++ show n ++ " win=" ++ show h ++ " d=" ++ show d )
               ( twoSegmentInstance n h 2 d )
      | ( n, h, d ) <- [ ( 4, 8, 2 ), ( 6, 12, 2 ), ( 8, 16, 2 ) ]
      ]
  , bgroup "tight clique (n duration-d tasks, horizon n·d)"
      [ triple ( "n=" ++ show n ++ " d=" ++ show d )
               ( tightCliqueInstance n d )
      | ( n, d ) <- [ ( 4, 2 ), ( 6, 2 ), ( 8, 2 ), ( 12, 2 ) ]
      ]
  , bgroup "chained window (each task k in [k, k+w])"
      [ triple ( "n=" ++ show n ++ " w=" ++ show w )
               ( chainedWindowInstance n w 1 )
      | ( n, w ) <- [ ( 4, 2 ), ( 6, 2 ), ( 8, 2 ), ( 12, 2 ) ]
      ]
  , bgroup "chained-window + extra task (structured infeasibility)"
      [ triple ( "n=" ++ show n ++ " w=" ++ show w )
               ( chainedOverloadedInstance n w 1 )
      | ( n, w ) <- [ ( 4, 2 ), ( 6, 2 ), ( 8, 2 ) ]
      ]
  ]
