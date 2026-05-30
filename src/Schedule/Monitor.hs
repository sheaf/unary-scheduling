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
  ( PrimMonad(PrimState) )
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

  -- | Record one productive round of the propagation fixpoint loop.
  tickRound :: PrimMonad m => Monitor mode ( PrimState m ) -> m ()

  -- | Record one @channelLit@ call (one precedence literal drained into the
  -- ordering matrix).
  tickChannelCall :: PrimMonad m => Monitor mode ( PrimState m ) -> m ()

  -- | Record @n@ transitively-derived edges asserted as theory propagations.
  tickDerivedEdges :: PrimMonad m => Monitor mode ( PrimState m ) -> Int -> m ()

  -- | Record one theory conflict: its @label@ (source) and whether it was
  -- explained by a /tight/ local reason ('True') or a coarse trail snapshot
  -- ('False').
  tickConflict :: PrimMonad m => Monitor mode ( PrimState m ) -> Text -> Bool -> m ()

  -- | Record the length (number of literals) of a materialised reason clause.
  recordReasonLen :: PrimMonad m => Monitor mode ( PrimState m ) -> Int -> m ()

  -- | Snapshot the accumulated counters into an immutable 'MonitorReport'.
  readReport :: PrimMonad m => Monitor mode ( PrimState m ) -> m MonitorReport

instance MonitorMode MonitoringOff where
  data Monitor MonitoringOff s = NoMonitoring
  newMonitor = pure NoMonitoring
  {-# INLINE newMonitor #-}
  tickPropagator     _ _ _ = pure ()
  {-# INLINE tickPropagator #-}
  tickRound          _     = pure ()
  {-# INLINE tickRound #-}
  tickChannelCall    _     = pure ()
  {-# INLINE tickChannelCall #-}
  tickDerivedEdges   _ _   = pure ()
  {-# INLINE tickDerivedEdges #-}
  tickConflict       _ _ _ = pure ()
  {-# INLINE tickConflict #-}
  recordReasonLen    _ _   = pure ()
  {-# INLINE recordReasonLen #-}
  readReport         _     = pure emptyReport
  {-# INLINE readReport #-}

instance MonitorMode MonitoringOn where
  data Monitor MonitoringOn s = Monitor
    { onPerProp         :: !( MutVar s ( Map Text ( Int, Int ) ) )
    , onRounds          :: !( MutVar s Int )
    , onChannelCalls    :: !( MutVar s Int )
    , onDerivedEdges    :: !( MutVar s Int )
    , onConflicts       :: !( MutVar s ( Map Text ( Int, Int ) ) )
    , onReasonCount     :: !( MutVar s Int )
    , onReasonTotalLen  :: !( MutVar s Int )
    , onReasonMaxLen    :: !( MutVar s Int )
    }
  newMonitor =
    Monitor
      <$> newMutVar Map.empty
      <*> newMutVar 0
      <*> newMutVar 0
      <*> newMutVar 0
      <*> newMutVar Map.empty
      <*> newMutVar 0
      <*> newMutVar 0
      <*> newMutVar 0
  tickPropagator mon name productive =
    modifyMutVar' ( onPerProp mon )
      ( Map.insertWith addPair name ( 1, if productive then 1 else 0 ) )
    where
      addPair ( i1, p1 ) ( i2, p2 ) = ( i1 + i2, p1 + p2 )
  tickRound          mon   = modifyMutVar' ( onRounds mon )          ( + 1 )
  tickChannelCall    mon   = modifyMutVar' ( onChannelCalls mon )    ( + 1 )
  tickDerivedEdges   mon n = modifyMutVar' ( onDerivedEdges mon )    ( + n )
  tickConflict mon label tight =
    modifyMutVar' ( onConflicts mon )
      ( Map.insertWith addPair label ( if tight then ( 1, 0 ) else ( 0, 1 ) ) )
    where
      addPair ( t1, c1 ) ( t2, c2 ) = ( t1 + t2, c1 + c2 )
  recordReasonLen    mon n = do
    modifyMutVar' ( onReasonCount mon )    ( + 1 )
    modifyMutVar' ( onReasonTotalLen mon ) ( + n )
    modifyMutVar' ( onReasonMaxLen mon )   ( max n )
  readReport mon =
    MonitorReport
      <$> readMutVar ( onPerProp mon )
      <*> readMutVar ( onRounds mon )
      <*> readMutVar ( onChannelCalls mon )
      <*> readMutVar ( onDerivedEdges mon )
      <*> readMutVar ( onConflicts mon )
      <*> readMutVar ( onReasonCount mon )
      <*> readMutVar ( onReasonTotalLen mon )
      <*> readMutVar ( onReasonMaxLen mon )

-------------------------------------------------------------------------------
-- Report.

-- | An immutable snapshot of the monitor counters.
data MonitorReport = MonitorReport
  { -- | Per-propagator @(invocations, productive invocations)@, keyed by the
    -- propagator's subscription name.
    perPropagator   :: !( Map Text ( Int, Int ) )
  , -- | Productive rounds of the propagation fixpoint loop.
    rounds          :: !Int
  , -- | Precedence literals drained into the ordering matrix.
    channelCalls    :: !Int
  , -- | Transitively-derived edges asserted as theory propagations.
    derivedEdges    :: !Int
  , -- | Theory conflicts broken down by source label, each as
    -- @(tight, coarse)@ counts (tight = locally explained, coarse =
    -- snapshot-explained).
    conflictBreakdown :: !( Map Text ( Int, Int ) )
  , -- | Number of reason clauses whose length was recorded.
    --
    -- Currently this counts eagerly-materialised theory-conflict clauses;
    -- lazily-built propagation reasons are only measured if forced, which would
    -- require a hook at the force site in @SAT.Solver.walkUIP@ (not yet wired).
    reasonCount     :: !Int
  , -- | Sum of recorded reason-clause lengths (for the mean).
    reasonTotalLen  :: !Int
  , -- | Largest recorded reason-clause length.
    reasonMaxLen    :: !Int
  }
  deriving stock    ( Show, Generic )
  deriving anyclass NFData

-- | The all-zero report.
emptyReport :: MonitorReport
emptyReport = MonitorReport
  { perPropagator   = Map.empty
  , rounds          = 0
  , channelCalls    = 0
  , derivedEdges      = 0
  , conflictBreakdown = Map.empty
  , reasonCount     = 0
  , reasonTotalLen  = 0
  , reasonMaxLen    = 0
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
  , "conflicts by source (tight / coarse):"
  ] ++ conflictLines ++
  [ "per-propagator (invocations / productive):"
  ] ++ propLines
  where
    line :: String -> Int -> String
    line name n = printf "  %-22s %d" name n
    conflictLines
      | Map.null ( conflictBreakdown r ) = [ "  (none)" ]
      | otherwise =
          [ printf "  %-22s %d / %d" ( Text.unpack label ) tight coarse
          | ( label, ( tight, coarse ) ) <- Map.toList ( conflictBreakdown r )
          ]
    meanLen
      | reasonCount r == 0 = 0
      | otherwise          = fromIntegral ( reasonTotalLen r ) / fromIntegral ( reasonCount r )
    propLines
      | Map.null ( perPropagator r ) = [ "  (none)" ]
      | otherwise =
          [ printf "  %-22s %d / %d" ( Text.unpack name ) inv prod
          -- Most-invoked first.
          | ( name, ( inv, prod ) ) <- sortOn ( negate . fst . snd ) ( Map.toList ( perPropagator r ) )
          ]
