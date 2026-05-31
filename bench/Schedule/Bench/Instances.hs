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
  , windowedTask
  , randomWindowedInstance
  , rehearsalInstance
  , overloadedInstance
  , tightCliqueInstance
  , intervalPigeonholeInstance
  , infeasibleRehearsalInstance
  )
  where

-- base
import Data.List
  ( sortOn )
import GHC.Generics
  ( Generic )

-- containers
import Data.IntMap.Strict
  ( IntMap )
import qualified Data.IntMap.Strict as IntMap
  ( fromList, elems, (!) )
import qualified Data.Sequence as Seq
  ( fromList )

-- deepseq
import Control.DeepSeq
  ( NFData )

-- random
import System.Random
  ( mkStdGen, randomRs, split )

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

-- | A task with a single availability window @[release, deadline]@ and the
-- given duration.
windowedTask
  :: Int   -- ^ release time (window start)
  -> Int   -- ^ deadline (window end)
  -> Int   -- ^ duration
  -> Text  -- ^ name
  -> ( BenchTask, Text )
windowedTask release deadline dur name =
  ( Task
      { taskAvailability = mkIntervals
          ( Seq.fromList
            [ Interval
              ( Endpoint ( EarliestTime ( Time ( BenchTime release ) ) ) Inclusive )
              ( Endpoint ( LatestTime   ( Time ( BenchTime deadline ) ) ) Inclusive )
            ]
          )
      , taskDuration     = Delta ( BenchTime dur )
      , taskInfo         = ()
      }
  , name
  )

-- | Make a simple task with one availability interval @[0, horizon]@ and
-- the given duration.
fullTask :: Int -> Int -> Text -> ( BenchTask, Text )
fullTask horizon = windowedTask 0 horizon

-- | A feasible instance with /heterogeneous, overlapping/ availability windows.
randomWindowedInstance
  :: Double  -- ^ target utilisation, in @(0, 1]@
  -> Int     -- ^ window slack: max extra room added to each side of a task's window
  -> Int     -- ^ number of tasks
  -> Int     -- ^ maximum task duration
  -> Int     -- ^ PRNG seed
  -> Instance
randomWindowedInstance utilisation windowSlack n maxDur seed =
  -- Emit tasks in id order @0 .. n-1@ (so the id is the list position, and thus
  -- the SAT variable index), each with the window around its planted slot.
  [ windowedTask
      ( max 0       ( startOf t - lo ) )
      ( min horizon ( startOf t + durOf t + hi ) )
      ( durOf t )
      ( Text.pack ( "w" ++ show t ) )
  | ( t, ( lo, hi ) ) <- zip [ 0 .. n - 1 ] winSlacks
  ]
  where
    ( gDur, g1 )   = split ( mkStdGen seed )
    ( gKey, gWin ) = split g1

    -- Random duration per task id.
    durs :: IntMap Int
    durs = IntMap.fromList ( zip [ 0 .. ] ( take n ( randomRs ( 1, maxDur ) gDur ) ) )
    durOf :: Int -> Int
    durOf t = durs IntMap.! t

    total, horizon, gap :: Int
    total   = sum ( IntMap.elems durs )
    horizon = max maxDur ( ceiling ( fromIntegral total / utilisation ) )
    -- Distribute the free space as a uniform gap between planted slots.
    gap     = ( horizon - total ) `div` n

    -- Randomise the layout to avoid the solver being able to luck out.
    layout :: [ Int ]
    layout = map snd ( sortOn fst ( zip keys [ 0 .. n - 1 ] ) )
      where keys = take n ( randomRs ( 0 :: Int, 1_000_000_000 ) gKey )

    -- Planted (non-overlapping) start of each task, following the layout order.
    starts :: IntMap Int
    starts = IntMap.fromList ( go 0 layout )
      where
        go _   []         = []
        go acc ( i : is ) = ( i, acc ) : go ( acc + durOf i + gap ) is
    startOf :: Int -> Int
    startOf t = starts IntMap.! t

    -- Per-task @(beforeSlack, afterSlack)@, consumed two at a time.
    winSlacks :: [ ( Int, Int ) ]
    winSlacks = take n ( pairUp ( randomRs ( 0, windowSlack ) gWin ) )
    pairUp :: [ Int ] -> [ ( Int, Int ) ]
    pairUp ( a : b : rest ) = ( a, b ) : pairUp rest
    pairUp _                = []

-- | A multi-day /rehearsal/ instance (simulacrum of realistic use case).
rehearsalInstance
  :: Double  -- ^ utilisation: total demand / total day capacity, in @(0, 1]@
  -> Double  -- ^ per-(song, day) availability probability, in @(0, 1]@
  -> Int     -- ^ number of days
  -> Int     -- ^ number of songs
  -> Int     -- ^ maximum rehearsal duration
  -> Int     -- ^ PRNG seed
  -> Instance
rehearsalInstance utilisation availProb numDays numSongs maxDur seed =
  [ multiDayTask ( songDays k ) dayLen dayGap ( durOf k ) ( Text.pack ( "song" ++ show k ) )
  | k <- [ 0 .. numSongs - 1 ]
  ]
  where
    ( gDur, gAvail ) = split ( mkStdGen seed )

    durs :: IntMap Int
    durs  = IntMap.fromList ( zip [ 0 .. ] ( take numSongs ( randomRs ( 1, maxDur ) gDur ) ) )
    durOf :: Int -> Int
    durOf k = durs IntMap.! k

    -- Size a day so the whole schedule runs at the target utilisation; a single
    -- carved boundary slot between days stops a rehearsal straddling the
    -- boundary (one contiguous task cannot skip the missing slot).
    total, dayLen, dayGap :: Int
    total  = sum ( IntMap.elems durs )
    dayLen = max maxDur ( ceiling ( fromIntegral total / ( fromIntegral numDays * utilisation ) ) )
    dayGap = 1

    -- Per-(song, day) availability draws, chunked @numDays@ per song.
    availDraws :: [ Double ]
    availDraws = take ( numSongs * numDays ) ( randomRs ( 0, 1 ) gAvail )
    songDays :: Int -> [ Int ]
    songDays k =
      let mask = take numDays ( drop ( k * numDays ) availDraws )
          ds   = [ d | ( d, p ) <- zip [ 0 .. ] mask, p < availProb ]
      in if null ds then [ k `mod` numDays ] else ds

-- | A task available on each of the given @days@. Day @d@ is the @dayLen@-slot
-- window @[d * (dayLen + dayGap), d * (dayLen + dayGap) + dayLen - 1]@, so
-- consecutive days are separated by @dayGap@ unoccupiable boundary slots.
multiDayTask :: [ Int ] -> Int -> Int -> Int -> Text -> ( BenchTask, Text )
multiDayTask days dayLen dayGap dur name =
  ( Task
      { taskAvailability = mkIntervals ( Seq.fromList ( map dayWindow days ) )
      , taskDuration     = Delta ( BenchTime dur )
      , taskInfo         = ()
      }
  , name
  )
  where
    dayWindow :: Int -> Interval BenchTime
    dayWindow d =
      let start = d * ( dayLen + dayGap )
      in Interval
           ( Endpoint ( EarliestTime ( Time ( BenchTime start ) ) ) Inclusive )
           ( Endpoint ( LatestTime   ( Time ( BenchTime ( start + dayLen - 1 ) ) ) ) Inclusive )

-- | Difficult infeasible instance that requires search.
intervalPigeonholeInstance
  :: Int   -- ^ number of slots @m@ (the instance has @m + 1@ tasks)
  -> Int   -- ^ task\/slot duration
  -> Instance
intervalPigeonholeInstance numSlots dur =
  [ ( Task
        { taskAvailability =
            mkIntervals ( Seq.fromList [ slot j | j <- [ 0 .. numSlots - 1 ] ] )
        , taskDuration     = Delta ( BenchTime dur )
        , taskInfo         = ()
        }
    , Text.pack ( "ph" ++ show k )
    )
  | k <- [ 0 .. numSlots ]
  ]
  where
    -- Slot @j@ is the window @[2·j·dur, 2·j·dur + dur]@: just wide enough for one
    -- duration-@dur@ task, pinned to start at its left edge.
    slot :: Int -> Interval BenchTime
    slot j =
      let lo = 2 * j * dur
      in Interval
           ( Endpoint ( EarliestTime ( Time ( BenchTime lo ) ) )           Inclusive )
           ( Endpoint ( LatestTime   ( Time ( BenchTime ( lo + dur ) ) ) ) Inclusive )

-- | A multi-day rehearsal that is infeasible but that requires genuine search
-- to prove so.
infeasibleRehearsalInstance
  :: Int   -- ^ number of copies of the five-song fragmentation gadget (@>= 1@)
  -> Instance
infeasibleRehearsalInstance numCopies =
  [ multiDayTask [ 0 .. numBins - 1 ] dayLen dayGap sz
      ( Text.pack ( "bp" ++ show c ++ "_" ++ show sz ) )
  | c  <- [ 0 .. numCopies - 1 ]
  , sz <- itemSizes
  ]
  where
    itemSizes :: [ Int ]
    itemSizes = [ 8, 7, 6, 5, 4 ]   -- per copy: total 30, but needs four length-10 days
    numBins, dayLen, dayGap :: Int
    numBins = 3 * numCopies
    dayLen  = 10
    dayGap  = 10                    -- >= dayLen: convex envelope dwarfs windowed capacity

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

-- | A /tight disjunctive clique/: @n@ duration-@d@ tasks, all sharing the
-- single window @[0, n·d)@. Total demand equals capacity, so every feasible
-- schedule is a permutation. Stresses pure precedence branching with no
-- helpful bound-tightening to fall back on.
tightCliqueInstance :: Int -> Int -> Instance
tightCliqueInstance n d =
  [ fullTask ( n * d ) d ( Text.pack ( "c" ++ show k ) )
  | k <- [ 0 .. n - 1 ]
  ]

