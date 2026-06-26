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
    -- * Instance families
  , fullTask
  , windowedTask
  , randomWindowedInstance
  , rehearsalInstance
  , overloadedInstance
  , tightCliqueInstance
  , intervalPigeonholeInstance
  , infeasibleRehearsalInstance
  , fragmentationInstance
  , phaseTransitionInstance
  , phaseTransitionAt
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
  ( SplitGen(splitGen), mkStdGen, randomRs )

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
  ( basicPropagators )
import Schedule.Task
  ( Task(..) )
import Schedule.Time
  ( Delta(..), Time(..), HandedTime(..) )

-------------------------------------------------------------------------------
-- A small, bounded time type matching the test suite.

newtype BenchTime = BenchTime Int
  deriving newtype ( Eq, Ord, Num, Real, Measurable, NFData )

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
    ( gDur, g1 )   = splitGen ( mkStdGen seed )
    ( gKey, gWin ) = splitGen g1

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
    ( gDur, gAvail ) = splitGen ( mkStdGen seed )

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

-- | A bin-packing fragmentation instance: the given /item sizes/ must each be
-- placed whole into one of @numBins@ length-10 days (a task cannot straddle a
-- day boundary), and no two items may overlap within a day. Infeasible exactly
-- when the multiset of items does not pack into the days. The wide inter-day gap
-- (@dayGap >= dayLen@) keeps the convex envelope loose, so global energetic
-- overload never fires and the infeasibility can only be found by search.
--
-- The item sizes are arbitrary, so heterogeneous (non-symmetric) infeasible
-- instances are expressible — see 'infeasibleRehearsalInstance' for the
-- symmetric copy-of-a-gadget special case.
fragmentationInstance
  :: [ Int ]   -- ^ item sizes
  -> Int       -- ^ number of length-10 days (bins)
  -> Instance
fragmentationInstance itemSizes numBins =
  [ multiDayTask [ 0 .. numBins - 1 ] dayLen dayGap sz
      ( Text.pack ( "frag" ++ show idx ++ "_" ++ show sz ) )
  | ( idx, sz ) <- zip [ 0 :: Int .. ] itemSizes
  ]
  where
    dayLen, dayGap :: Int
    dayLen = 10
    dayGap = 10   -- >= dayLen: convex envelope dwarfs windowed capacity

-- | A multi-day rehearsal that is infeasible but that requires genuine search
-- to prove so: @numCopies@ symmetric copies of the five-song fragmentation
-- gadget @[8,7,6,5,4]@ (total 30 per copy, needing four length-10 days) sharing
-- @3 * numCopies@ days.
infeasibleRehearsalInstance
  :: Int   -- ^ number of copies of the five-song fragmentation gadget (@>= 1@)
  -> Instance
infeasibleRehearsalInstance numCopies =
  fragmentationInstance
    ( concat ( replicate numCopies [ 8, 7, 6, 5, 4 ] ) )
    ( 3 * numCopies )

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

-- | A random single-machine instance from the /solvability phase-transition/
-- model of Wang, O'Gorman, Tran, Rieffel, Frank & Do, \"An Investigation of
-- Phase Transitions in Single-Machine Scheduling Problems\" (ICAPS 2017).
--
-- Each of @n@ jobs gets:
--
--   * a processing time drawn uniformly from the /two-element coprime set/
--     @{pₛ, pₗ}@ (the paper uses e.g. @{3,19}@ or @{7,11}@; coprimality and a
--     moderate ratio are deliberate, to avoid accidentally-easy instances);
--   * a window length @w ~ U[pₗ + 1, wMax]@ (so every job fits its own window,
--     but tightly — infeasibility can only come from the no-overlap interaction);
--   * a release @r ~ U[0, T − w]@, giving the availability window @[r, r + w]@.
--
-- @T@ (horizon) and @wMax@ (max window length) are the two order parameters; see
-- 'phaseTransitionAt' for the paper's normalised @(T/(n·p̄), wMax/T)@ coordinates.
phaseTransitionInstance
  :: ( Int, Int )  -- ^ processing-time pair @(pₛ, pₗ)@, @pₛ < pₗ@, coprime
  -> Int           -- ^ number of jobs @n@
  -> Int           -- ^ horizon @T@
  -> Int           -- ^ maximum window length @wMax@ (clamped to @[pₗ+1, T]@)
  -> Int           -- ^ PRNG seed
  -> Instance
phaseTransitionInstance ( pSmall, pLarge ) n horizon wMaxArg seed =
  [ windowedTask r ( r + w ) p ( Text.pack ( "pt" ++ show k ) )
  | ( k, p, w, u ) <- zip4 [ 0 :: Int .. ] procs windows releaseDraws
  , let r = floor ( u * fromIntegral ( max 0 ( horizon - w ) ) )
  ]
  where
    -- Window lengths are bounded below by pₗ+1 (every job fits) and above by the
    -- horizon (so a release in [0, T-w] always exists).
    wMax :: Int
    wMax = max ( pLarge + 1 ) ( min horizon wMaxArg )

    ( gProc, g1 )       = splitGen ( mkStdGen seed )
    ( gWindow, gRelease ) = splitGen g1

    -- p ~ U{pₛ, pₗ}; w ~ U[pₗ+1, wMax]; release fraction u ~ U[0,1) (scaled per
    -- job to its own [0, T-w] range, since the range depends on w).
    procs :: [ Int ]
    procs = take n ( map ( \ b -> if b == ( 0 :: Int ) then pSmall else pLarge )
                         ( randomRs ( 0, 1 ) gProc ) )
    windows :: [ Int ]
    windows = take n ( randomRs ( pLarge + 1, wMax ) gWindow )
    releaseDraws :: [ Double ]
    releaseDraws = take n ( randomRs ( 0, 0.999999 ) gRelease )

    zip4 :: [ a ] -> [ b ] -> [ c ] -> [ d ] -> [ ( a, b, c, d ) ]
    zip4 ( a : as ) ( b : bs ) ( c : cs ) ( d : ds ) = ( a, b, c, d ) : zip4 as bs cs ds
    zip4 _ _ _ _ = []

-- | Build a 'phaseTransitionInstance' from the paper's /normalised/ order
-- parameters, so a benchmark can place an instance directly relative to the
-- solvability frontier (the hyperbola @T/(n·p̄) = a₀/(wMax/T) + c₀@):
--
--   * @ratioT = T / (n · p̄)@ — the horizon as a multiple of the expected total
--     work (@p̄ = (pₛ + pₗ)/2@). @≈1@ is tight (little room); @>1@ is loose.
--   * @ratioW = wMax / T@ — window length relative to the horizon. Small means
--     tight windows (a sharper transition); large means loose windows.
phaseTransitionAt
  :: ( Int, Int )  -- ^ @(pₛ, pₗ)@
  -> Int           -- ^ @n@
  -> Double        -- ^ @ratioT = T/(n·p̄)@
  -> Double        -- ^ @ratioW = wMax/T@
  -> Int           -- ^ seed
  -> Instance
phaseTransitionAt p@( pSmall, pLarge ) n ratioT ratioW seed =
  phaseTransitionInstance p n horizon wMax seed
  where
    pBar :: Double
    pBar    = fromIntegral ( pSmall + pLarge ) / 2
    horizon = round ( ratioT * fromIntegral n * pBar )
    wMax    = round ( ratioW * fromIntegral horizon )

