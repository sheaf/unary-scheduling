-- | Monitoring instrumentation.
module Schedule.Monitor
  ( -- * Instrumentation mode
    Monitoring(..)
  , MonitorMode(..)
  , Monitor(..)
    -- * Report
  , MonitorReport(..)
  , emptyReport
  , renderReport
  )
  where

-- base
import Data.Kind
  ( Type, Constraint )
import Data.List
  ( sortOn )
import Data.Word
  ( Word64 )
import GHC.Clock
  ( getMonotonicTimeNSec )
import GHC.Generics
  ( Generic )
import Text.Printf
  ( printf )

-- containers
import Data.Map.Strict
  ( Map )
import qualified Data.Map.Strict as Map

-- deepseq
import Control.DeepSeq
  ( NFData )

-- primitive
import Control.Monad.Primitive
  ( PrimMonad(PrimState), unsafeIOToPrim )
import Data.Primitive.MutVar
  ( MutVar, newMutVar, readMutVar, modifyMutVar' )

-- text
import Data.Text
  ( Text )
import qualified Data.Text as Text

-------------------------------------------------------------------------------
-- Mode tags.

data Monitoring
  -- | Instrumentation disabled.
  = MonitoringOff
  -- | Instrumentation enabled.
  | MonitoringOn

-------------------------------------------------------------------------------
-- The monitor class.

-- | Operations a search uses to record what it did.
type MonitorMode :: Monitoring -> Constraint
class MonitorMode mode where
  -- | The per-run mutable state of a monitor.
  data Monitor mode :: Type -> Type

  -- | Allocate a fresh monitor.
  newMonitor :: PrimMonad m => m ( Monitor mode ( PrimState m ) )

  -- | Record one invocation of the named propagator. The 'Bool' says whether
  -- that invocation was /productive/ (emitted at least one applied constraint).
  tickPropagator :: PrimMonad m => Monitor mode ( PrimState m ) -> Text -> Bool -> m ()

  -- | Run a propagator action, accumulating its wall-clock time against the
  -- named propagator.
  withPropagatorTiming :: PrimMonad m => Monitor mode ( PrimState m ) -> Text -> m a -> m a

  -- | Like 'withPropagatorTiming', but accumulates against a named /search phase/
  -- to localise where search time goes. A name of the form @\"parent\/child\"@
  -- marks a sub-phase nested inside @parent@'s timed region (its time is included
  -- in the parent); see the 'phaseTime' field doc for how that must be read.
  withPhaseTiming :: PrimMonad m => Monitor mode ( PrimState m ) -> Text -> m a -> m a

  -- | Record one productive round of the propagation fixpoint loop.
  tickRound :: PrimMonad m => Monitor mode ( PrimState m ) -> m ()

  -- | Record one @channelLit@ call (one precedence literal drained into the
  -- ordering matrix).
  tickChannelCall :: PrimMonad m => Monitor mode ( PrimState m ) -> m ()

  -- | Record @n@ transitively-derived edges asserted as theory propagations.
  tickDerivedEdges :: PrimMonad m => Monitor mode ( PrimState m ) -> Int -> m ()

  -- | Record one theory conflict by its textual label.
  tickConflict :: PrimMonad m => Monitor mode ( PrimState m ) -> Text -> m ()

  -- | Record the length (number of literals) of a materialised reason clause.
  recordReasonLen :: PrimMonad m => Monitor mode ( PrimState m ) -> Int -> m ()

  -- | Record that one lazy reason was recorded: a theory propagation above the
  -- ground level whose explanation is deferred ('SAT.Solver.recordLazyReason').
  tickLazyRecord :: PrimMonad m => Monitor mode ( PrimState m ) -> m ()

  -- | Record one force of a recorded lazy reason during conflict analysis; the
  -- 'Int' is the number of literals the forced reason produced.
  tickLazyForce
    :: PrimMonad m
    => Monitor mode ( PrimState m ) -> Int -> m ()

  -- | Snapshot the accumulated counters into an immutable 'MonitorReport'.
  readReport :: PrimMonad m => Monitor mode ( PrimState m ) -> m MonitorReport

instance MonitorMode MonitoringOff where
  data Monitor MonitoringOff s = NoMonitoring
  newMonitor = pure NoMonitoring
  {-# INLINE newMonitor #-}
  tickPropagator     _ _ _ = pure ()
  {-# INLINE tickPropagator #-}
  withPropagatorTiming _ _ act = act
  {-# INLINE withPropagatorTiming #-}
  withPhaseTiming    _ _ act = act
  {-# INLINE withPhaseTiming #-}
  tickRound          _     = pure ()
  {-# INLINE tickRound #-}
  tickChannelCall    _     = pure ()
  {-# INLINE tickChannelCall #-}
  tickDerivedEdges   _ _   = pure ()
  {-# INLINE tickDerivedEdges #-}
  tickConflict       _ _   = pure ()
  {-# INLINE tickConflict #-}
  recordReasonLen    _ _   = pure ()
  {-# INLINE recordReasonLen #-}
  tickLazyRecord     _     = pure ()
  {-# INLINE tickLazyRecord #-}
  tickLazyForce      _ _   = pure ()
  {-# INLINE tickLazyForce #-}
  readReport         _     = pure emptyReport
  {-# INLINE readReport #-}

instance MonitorMode MonitoringOn where
  data Monitor MonitoringOn s = Monitor
    { onPerProp         :: !( MutVar s ( Map Text ( Int, Int ) ) )
    , onPerPropTime     :: !( MutVar s ( Map Text Word64 ) )
    , onPhaseTime       :: !( MutVar s ( Map Text Word64 ) )
    , onRounds          :: !( MutVar s Int )
    , onChannelCalls    :: !( MutVar s Int )
    , onDerivedEdges    :: !( MutVar s Int )
    , onConflicts       :: !( MutVar s ( Map Text Int ) )
    , onReasonCount     :: !( MutVar s Int )
    , onReasonTotalLen  :: !( MutVar s Int )
    , onReasonMaxLen    :: !( MutVar s Int )
    , onLazyRecorded    :: !( MutVar s Int )
    , onLazyForced      :: !( MutVar s Int )
    , onLazyForceLits   :: !( MutVar s Int )
    }
  newMonitor =
    Monitor
      <$> newMutVar Map.empty
      <*> newMutVar Map.empty
      <*> newMutVar Map.empty
      <*> newMutVar 0
      <*> newMutVar 0
      <*> newMutVar 0
      <*> newMutVar Map.empty
      <*> newMutVar 0
      <*> newMutVar 0
      <*> newMutVar 0
      <*> newMutVar 0
      <*> newMutVar 0
      <*> newMutVar 0
  tickPropagator mon name productive =
    modifyMutVar' ( onPerProp mon )
      ( Map.insertWith (addPair) name ( 1, if productive then 1 else 0 ) )
    where
      addPair :: ( Int, Int ) -> ( Int, Int ) -> ( Int, Int )
      addPair ( i1, p1 ) ( i2, p2 ) = ( i1 + i2, p1 + p2 )
  withPropagatorTiming mon name act = do
    t0  <- unsafeIOToPrim getMonotonicTimeNSec
    res <- act
    t1  <- unsafeIOToPrim getMonotonicTimeNSec
    modifyMutVar' ( onPerPropTime mon ) ( Map.insertWith (+) name ( t1 - t0 ) )
    pure res
  withPhaseTiming mon name act = do
    t0  <- unsafeIOToPrim getMonotonicTimeNSec
    res <- act
    t1  <- unsafeIOToPrim getMonotonicTimeNSec
    modifyMutVar' ( onPhaseTime mon ) ( Map.insertWith (+) name ( t1 - t0 ) )
    pure res
  tickRound          mon   = modifyMutVar' ( onRounds mon )          ( + 1 )
  tickChannelCall    mon   = modifyMutVar' ( onChannelCalls mon )    ( + 1 )
  tickDerivedEdges   mon n = modifyMutVar' ( onDerivedEdges mon )    ( + n )
  tickConflict mon label =
    modifyMutVar' ( onConflicts mon )
      ( Map.insertWith (+) label 1 )
  recordReasonLen    mon n = do
    modifyMutVar' ( onReasonCount mon )    ( + 1 )
    modifyMutVar' ( onReasonTotalLen mon ) ( + n )
    modifyMutVar' ( onReasonMaxLen mon )   ( max n )
  tickLazyRecord mon = modifyMutVar' ( onLazyRecorded mon ) ( + 1 )
  tickLazyForce mon n = do
    modifyMutVar' ( onLazyForced   mon ) ( + 1 )
    modifyMutVar' ( onLazyForceLits mon ) ( + n )
  readReport mon =
    MonitorReport
      <$> readMutVar ( onPerProp mon )
      <*> readMutVar ( onPerPropTime mon )
      <*> readMutVar ( onPhaseTime mon )
      <*> readMutVar ( onRounds mon )
      <*> readMutVar ( onChannelCalls mon )
      <*> readMutVar ( onDerivedEdges mon )
      <*> readMutVar ( onConflicts mon )
      <*> readMutVar ( onReasonCount mon )
      <*> readMutVar ( onReasonTotalLen mon )
      <*> readMutVar ( onReasonMaxLen mon )
      <*> readMutVar ( onLazyRecorded mon )
      <*> readMutVar ( onLazyForced mon )
      <*> readMutVar ( onLazyForceLits mon )

-------------------------------------------------------------------------------
-- Report.

-- | An immutable snapshot of the monitor counters.
data MonitorReport = MonitorReport
  { -- | Per-propagator @(invocations, productive invocations)@, keyed by the
    -- propagator's subscription name.
    perPropagator   :: !( Map Text ( Int, Int ) )
  , -- | Per-propagator cumulative wall-clock time (nanoseconds), keyed by the
    -- propagator's subscription name.
    perPropagatorTime :: !( Map Text Word64 )
  , -- | Per-search-phase cumulative wall-clock time (nanoseconds).
    --
    -- Remarks:
    --
    --   1. A key of the form @\"parent\/child\"@ is a /sub-phase/ whose time
    --      is /already included/ in its parent's total.
    --
    --   2. Instrumentation adds a cost, so it can over-inflate sub-phases.
    phaseTime       :: !( Map Text Word64 )
  , -- | Productive rounds of the propagation fixpoint loop.
    rounds          :: !Int
  , -- | Precedence literals drained into the ordering matrix.
    channelCalls    :: !Int
  , -- | Transitively-derived edges asserted as theory propagations.
    derivedEdges    :: !Int
  , -- | Theory conflicts broken down by source label.
    conflictBreakdown :: !( Map Text Int )
  , -- | Number of reason clauses whose length was recorded (the
    -- eagerly-materialised theory-conflict clauses).
    reasonCount     :: !Int
  , -- | Sum of recorded reason-clause lengths (for the mean).
    reasonTotalLen  :: !Int
  , -- | Largest recorded reason-clause length.
    reasonMaxLen    :: !Int
  , -- | Lazy reasons recorded (deferred theory propagations above the ground
    -- level). The denominator for lazy-reason utilisation.
    lazyRecorded    :: !Int
  , -- | Lazy reasons forced during conflict analysis. @lazyForced \/
    -- lazyRecorded@ is the utilisation. Memoisation in 'SAT.Solver.forceLazy'
    -- means each distinct reason is forced (and so counted) at most once.
    lazyForced      :: !Int
  , -- | Total literals across all forced reasons (mean length is
    -- @lazyForceLits \/ lazyForced@).
    lazyForceLits   :: !Int
  }
  deriving stock    ( Show, Generic )
  deriving anyclass NFData

-- | The all-zero report.
emptyReport :: MonitorReport
emptyReport = MonitorReport
  { perPropagator     = Map.empty
  , perPropagatorTime = Map.empty
  , phaseTime         = Map.empty
  , rounds            = 0
  , channelCalls      = 0
  , derivedEdges      = 0
  , conflictBreakdown = Map.empty
  , reasonCount       = 0
  , reasonTotalLen    = 0
  , reasonMaxLen      = 0
  , lazyRecorded      = 0
  , lazyForced        = 0
  , lazyForceLits     = 0
  }

-- | A human-readable multi-line rendering of a 'MonitorReport'.
renderReport :: MonitorReport -> String
renderReport r = unlines $
  [ "theory:"
  , line "rounds"           ( rounds r )
  , line "channel calls"    ( channelCalls r )
  , line "derived edges"    ( derivedEdges r )
  , printf "  %-22s count=%d  mean=%.1f  max=%d"
      ( "reason lengths" :: String )
      ( reasonCount r )
      ( meanLen :: Double )
      ( reasonMaxLen r )
  , "lazy reasons:"
  , line "recorded"          ( lazyRecorded r )
  , line "forced"            ( lazyForced r )
  , printf "  %-22s %.1f%%  |  %.1f mean lits/force"
      ( "utilisation" :: String )
      ( utilisation :: Double ) ( meanForceLen :: Double )
  , "conflicts by source:"
  ] ++ conflictLines ++
  [ "search phases (total ms & sub-phase breakdown):"
  ] ++ phaseLines ++
  [ "per-propagator (invocations / productive / total ms):"
  ] ++ propLines
  where
    line :: String -> Int -> String
    line name n = printf "  %-22s %d" name n
    -- Phases are rendered as a one-level tree: a key @\"parent/child\"@ is a
    -- sub-phase whose time is included in @parent@.
    phaseLines
      | Map.null ( phaseTime r ) = [ "  (none)" ]
      | otherwise = concatMap renderTop topSorted
      where
        ms :: Word64 -> Double
        ms ns = fromIntegral ns / 1e6
        split :: Text -> ( Maybe Text, Text )
        split k = case Text.breakOn "/" k of
          ( top, rest )
            | Text.null rest -> ( Nothing, top )
            | otherwise      -> ( Just top, Text.drop 1 rest )
        entries   = Map.toList ( phaseTime r )
        topSorted =
          sortOn ( negate . snd ) [ ( name, v ) | ( k, v ) <- entries, ( Nothing, name ) <- [ split k ] ]
        childrenOf p =
          sortOn ( negate . snd )
            [ ( child, v ) | ( k, v ) <- entries, ( Just par, child ) <- [ split k ], par == p ]
        phaseRow :: String -> Word64 -> String
        phaseRow nm t = printf "  %-26s %8.2f" nm ( ms t )
        renderTop ( name, total ) =
          let kids = childrenOf name
          in  phaseRow ( Text.unpack name ) total
              :  [ phaseRow ( "  - " ++ Text.unpack cn ) cv | ( cn, cv ) <- kids ]
              ++ [ phaseRow "  - (others) " ( total - sum ( map snd kids ) )
                 | not ( null kids ) ]
    conflictLines
      | Map.null ( conflictBreakdown r ) = [ "  (none)" ]
      | otherwise =
          [ printf "  %-22s %d" ( Text.unpack label ) count
          | ( label, count ) <- Map.toList ( conflictBreakdown r )
          ]
    meanLen
      | reasonCount r == 0 = 0
      | otherwise          = fromIntegral ( reasonTotalLen r ) / fromIntegral ( reasonCount r )
    safeRatio :: Int -> Int -> Double
    safeRatio _ 0 = 0
    safeRatio a b = fromIntegral a / fromIntegral b
    utilisation  = 100 * safeRatio ( lazyForced r )    ( lazyRecorded r )
    meanForceLen = safeRatio ( lazyForceLits r ) ( lazyForced r )
    propLines
      | Map.null ( perPropagator r ) = [ "  (none)" ]
      | otherwise =
          [ printf "  %-22s %5d / %5d (%5.1f%%) / %5.2f" ( Text.unpack name ) inv prod prodPct
              ( fromIntegral ( Map.findWithDefault 0 name ( perPropagatorTime r ) ) / 1e6 :: Double )
          -- Most-time-consuming first.
          | ( name, ( inv, prod ) ) <-
              sortOn ( negate . flip ( Map.findWithDefault 0 ) ( perPropagatorTime r ) . fst )
                ( Map.toList ( perPropagator r ) )
          , let prodPct :: Double
                prodPct = 100 * fromIntegral prod / fromIntegral inv
          ]
