{-# LANGUAGE CPP                  #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE UndecidableInstances #-}

-- | A minimal Clause-Driven Conflict Learning core.
--
-- The search loop is the standard MiniSat skeleton:
--
--   * decide a literal using VSIDS plus saved-phase,
--   * BCP with two-literal watches on the trail until either a falsified
--     clause is found or no further propagation is possible,
--   * on a conflict, run 1-UIP conflict analysis to produce an asserting
--     learnt clause, backjump, and resume.
--
-- A Luby schedule throttles restarts.
--
-- = Known limitations
--
--
--   * /No learnt-clause minimisation./ 'analyse' returns the 1-UIP clause
--     as produced by resolution, without recursive or local self-subsumption
--     (Sörensson \& Biere 2009).
--
--   * /No learnt-clause deletion or DB reduction./ The learnt-clause set
--     grows monotonically.
--
--   * /No LBD (Literal Block Distance) score, no per-clause activity./
--
--   * /No hyper-binary resolution, no on-the-fly subsumption./ Input
--     clauses are normalised only per-clause (duplicates, tautology,
--     level-0 satisfaction); no cross-clause preprocessing happens.
--
--   * /Coarse conflict budget./ 'optConflictBudget' is a single global
--     count with no per-restart accounting and no time-based fallback.
--
-- = References
--
--   * Eén, Sörensson (2003), /An Extensible SAT-solver/ (MiniSat).
--   * Marques-Silva, Sakallah (1996), /GRASP/.
--   * Moskewicz et al. (2001), /Chaff/.
--   * Pipatsrisawat, Darwiche (2007), /A Lightweight Component Caching Scheme/
--     (phase saving).
--   * Sörensson, Biere (2009), /Minimizing Learned Clauses/.
--   * Audemard, Simon (2009), /Predicting Learnt Clauses Quality in Modern
--     SAT Solvers/ (LBD).
module SAT.Solver
  ( -- * Solver
    Solver
  , newSolver
    -- * Building the problem
  , newVar
  , newAuxVar
  , addClause
  , addBinaryLemma
  , PostResult(..)
  , numVariables
    -- * Solving
  , Verdict(..)
  , solve
  , solveWith
  , SolverOptions(..)
  , defaultOptions
    -- * Inspection
  , Assignment
  , assignmentValue
  , getModel
  , valueOf
  , numConflicts
  , numDecisions
  , numLearnts

    -- * Lower-level driver primitives
    --
    -- These primitives expose the inner step interface of the search loop,
    -- intended for theory-driven (DPLL(T)) consumers that need to interleave
    -- propagation and decisions with their own theory.
  , DecisionLevel(GroundLevel, ..)
  , TrailPos(..)
  , Conflict(..)
  , currentLevel
  , levelOfAssignedVar
  , dumpSolverState
  , trailSize
  , trailAt
  , litValue
  , decide
  , decideVar
  , propagate
  , analyse
  , cancelUntil
  , pushNewLevel
  , enqueueUndef
  , countDecision
  , tryEnqueue
  , installLearnt
  , resolveConflict
  , recordLazyReason
  , recordTheoryClause
  , ClauseRef(..)
  , isOk
  , markFalse
  , bumpVarActivity
  )
  where

-- base
import Control.Monad
  ( when )
import Data.Bits
  ( (.&.), (.|.), unsafeShiftL )
import Data.Foldable
  ( for_ )
import Data.List
  ( intercalate )
import Data.Word
  ( Word64 )

-- bitvec
import Data.Bit
  ( Bit(..) )

-- containers
import Data.IntMap.Strict
  ( IntMap )
import qualified Data.IntMap.Strict as IntMap
  ( empty, insert, lookup )

-- primitive
import Control.Monad.Primitive
  ( PrimMonad(PrimState) )
import Data.Primitive
  ( Prim(..) )
import Data.Primitive.MutVar
  ( MutVar, newMutVar, readMutVar, writeMutVar, modifyMutVar' )

-- ghc-prim
import GHC.Exts
  ( (+#), (*#) )

-- memory-arena
import Memory.Growable
  ( Growable )
import qualified Memory.Growable as Growable

-- vector
import qualified Data.Vector.Generic as Generic
  ( Vector )
import qualified Data.Vector.Generic.Mutable as Generic
  ( MVector )
import qualified Data.Vector.Mutable as Boxed
  ( MVector )
import qualified Data.Vector.Primitive.Mutable as Primitive
  ( MVector )
import qualified Data.Vector.Unboxed as Vector
  ( Unbox )
import qualified Data.Vector.Unboxed as Unboxed
  ( Vector )
import qualified Data.Vector.Unboxed.Mutable as Unboxed
  ( MVector )

-- unary-scheduling
import SAT.Base
  ( Var(..), varIndex
  , Polarity(..), polarityValue
  , Lit, litIndex, mkLit, litVar, litPolarity, negateLit
  , LBool(..)
  , litValueFromVar
  )
import SAT.Clause
  ( Clause, clauseSize, clauseLit, clauseSwap
  , ClauseRef(..)
  , ClauseStore, newClauseStore
  )
import qualified SAT.Clause as Clause
  ( Reason(..), LazyReason(..), LazyRef(..)
  , clauseAt, recordClause, recordLearntClause
  , forceLazyReason
  )
import qualified SAT.Restart as Restart
  ( luby )
import SAT.VarOrder
  ( VarOrder, newVarOrder )
import qualified SAT.VarOrder as VarOrder
  ( insertVar, insertAuxVar, reinsertVar
  , bumpActivity, decayActivities, extractMaxBy
  )

-------------------------------------------------------------------------------
-- Decision levels.

-- | A position in the decision stack.
newtype DecisionLevel = DecisionLevel { unDecisionLevel :: Int }
  deriving stock   Show
  deriving newtype ( Eq, Ord, Prim )

newtype instance Unboxed.MVector s DecisionLevel = MVDecisionLevel ( Unboxed.MVector s Int )
newtype instance Unboxed.Vector    DecisionLevel = VDecisionLevel  ( Unboxed.Vector    Int )
deriving newtype instance Generic.MVector Unboxed.MVector DecisionLevel
deriving newtype instance Generic.Vector  Unboxed.Vector  DecisionLevel
deriving newtype instance Vector.Unbox DecisionLevel

-- | Ground level, for facts enforced unconditionally by the input clauses.
pattern GroundLevel :: DecisionLevel
pattern GroundLevel = DecisionLevel 0

-- | Level for unassigned variables (used as a sentinel value).
pattern UnassignedLevel :: DecisionLevel
pattern UnassignedLevel = DecisionLevel -1

-- | Hash a decision level into one of 64 buckets as a single-bit mask. The OR
-- of these over a clause's literals over-approximates its set of decision
-- levels, letting 'minimiseLearnt' reject a self-subsumption candidate cheaply:
-- a reason literal whose level-bit is absent from the clause mask cannot be
-- covered. Hash collisions only make the test more conservative, never unsound.
abstractLevel :: DecisionLevel -> Word64
abstractLevel ( DecisionLevel l ) = 1 `unsafeShiftL` ( l .&. 63 )

-------------------------------------------------------------------------------
-- Trail positions.

-- | A position on the assignment trail: an index in the range
-- @[0, trailSize)@.
--
-- Also used to express the trail's length / the "one past the last assignment"
-- anchor of a decision level.
newtype TrailPos = TrailPos { unTrailPos :: Int }
  deriving stock   Show
  deriving newtype ( Eq, Ord, Num )

newtype instance Unboxed.MVector s TrailPos = MVTrailPos ( Unboxed.MVector s Int )
newtype instance Unboxed.Vector    TrailPos = VTrailPos  ( Unboxed.Vector    Int )
deriving newtype instance Generic.MVector Unboxed.MVector TrailPos
deriving newtype instance Generic.Vector  Unboxed.Vector  TrailPos
deriving newtype instance Vector.Unbox TrailPos

-------------------------------------------------------------------------------
-- Watchers and conflicts.

-- | A single entry on a literal's watch list.
data Watcher
  = -- | A binary clause: the other literal of the clause is stored inline.
    WBinary !Lit
  | -- | A long clause (size @>= 3@), together with a /blocker/: a literal
    -- whose current truth lets BCP skip fetching the clause altogether.
    WLong !ClauseRef !Lit

-- | A 'Watcher' is encoded in two adjacent 'Int's: a 'ClauseRef' followed by a 'Lit'.
instance Prim Watcher where
  sizeOf# _ = sizeOf# ( undefined :: ClauseRef ) +# sizeOf# ( undefined :: Lit )
  alignment# _ = alignment# ( undefined :: ClauseRef )

  indexByteArray# arr# i# =
    let !cr  = indexByteArray# arr# ( i# *# 2# )      :: ClauseRef
        !lit = indexByteArray# arr# ( i# *# 2# +# 1# ) :: Lit
    in decodeWatcher cr lit
  readByteArray# arr# i# s0 =
    case readByteArray# arr# ( i# *# 2# ) s0 of
      (# s1, cr #) ->
        case readByteArray# arr# ( i# *# 2# +# 1# ) s1 of
          (# s2, lit #) -> (# s2, decodeWatcher ( cr :: ClauseRef ) ( lit :: Lit ) #)
  writeByteArray# arr# i# w s0 =
    case w of
      WBinary lit ->
        case writeByteArray# arr# ( i# *# 2# ) ( ClauseRef -1 ) s0 of
          s1 -> writeByteArray# arr# ( i# *# 2# +# 1# ) lit s1
      WLong cref lit ->
        case writeByteArray# arr# ( i# *# 2# ) cref s0 of
          s1 -> writeByteArray# arr# ( i# *# 2# +# 1# ) lit s1

  indexOffAddr# addr# i# =
    let !cr  = indexOffAddr# addr# ( i# *# 2# )      :: ClauseRef
        !lit = indexOffAddr# addr# ( i# *# 2# +# 1# ) :: Lit
    in decodeWatcher cr lit
  readOffAddr# addr# i# s0 =
    case readOffAddr# addr# ( i# *# 2# ) s0 of
      (# s1, cr #) ->
        case readOffAddr# addr# ( i# *# 2# +# 1# ) s1 of
          (# s2, lit #) -> (# s2, decodeWatcher ( cr :: ClauseRef ) ( lit :: Lit ) #)
  writeOffAddr# addr# i# w s0 =
    case w of
      WBinary lit ->
        case writeOffAddr# addr# ( i# *# 2# ) ( ClauseRef -1 ) s0 of
          s1 -> writeOffAddr# addr# ( i# *# 2# +# 1# ) lit s1
      WLong cref lit ->
        case writeOffAddr# addr# ( i# *# 2# ) cref s0 of
          s1 -> writeOffAddr# addr# ( i# *# 2# +# 1# ) lit s1

-- | Internal round-trip helper for the 'Prim' 'Watcher' instance.
decodeWatcher :: ClauseRef -> Lit -> Watcher
decodeWatcher cref lit
  | unCRef cref < 0 = WBinary lit
  | otherwise       = WLong cref lit

-- | The source of a Binary Constrait Propagation (BCP) conflict.
data Conflict
  = ConflictClause !ClauseRef
  | ConflictBinary !Lit !Lit

-------------------------------------------------------------------------------
-- Solver state.

-- | Tunable knobs.
data SolverOptions = SolverOptions
  { -- | VSIDS activity decay factor in @(0, 1]@.
    --
    -- Smaller values fade older bumps faster.
    optVarDecay       :: !Double
  , -- | Base unit of conflicts per restart cycle: the @k@-th window allows
    -- @optRestartUnit * luby k@ conflicts before a restart.
    optRestartUnit    :: !Int
  , -- | Hard ceiling on the total number of conflicts before the search
    -- gives up and reports 'Unknown'. @0@ disables the budget.
    optConflictBudget :: !Int
  }

defaultOptions :: SolverOptions
defaultOptions = SolverOptions
  { optVarDecay       = 0.95
  , optRestartUnit    = 100
  , optConflictBudget = 0
  }

-- | The mutable state of a running CDCL search.
data Solver s = Solver
  { -- | Lifted-boolean assignment, indexed by 'varIndex'.
    assigns   :: !( Growable Unboxed.MVector s LBool )
  , -- | Decision level at which each variable was assigned.
    level     :: !( Growable Unboxed.MVector s DecisionLevel )
  , -- | Reason for each variable's current assignment.
    reason    :: !( Growable Primitive.MVector s Clause.Reason )
  , -- | Polarity at which each variable was last assigned (used for phase
    -- saving on the next decision).
    --
    -- Defaults to 'Positive' for variables that have never been assigned.
    phase     :: !( Growable Unboxed.MVector s Polarity )
  , -- | Whether each variable is a /decision/ variable, i.e. eligible to be
    -- branched on by 'decide'. Indexed by 'varIndex'.
    decidable :: !( Growable Unboxed.MVector s Bit )
  , -- | Activity-ordered priority queue over variables (also owns the
    -- VSIDS activity scores, current bump increment, and decay factor).
    --
    -- Replaces the linear-scan decision heuristic with an O(log /n/) pop.
    varOrder  :: !( VarOrder s )
  , -- | Transient per-variable marker used by 1-UIP analysis.
    --
    -- Always @False@ outside of an 'analyse' call.
    seen      :: !( Growable Unboxed.MVector s Bit )
  , -- | Transient per-literal marker used by 'preprocessClause' to detect
    -- duplicate literals and tautologies in O(1) per literal.
    --
    -- Indexed by 'litIndex' (so two bits per variable: one per polarity).
    --
    -- Always @False@ outside of a 'preprocessClause' call.
    seenLit   :: !( Growable Unboxed.MVector s Bit )
  , -- | Per-literal watch lists, indexed by 'litIndex' and sized to
    -- @2 * numVars@. @watches[p]@ holds every watcher whose clause has
    -- @negateLit p@ as a watched literal, so that enqueueing @p@ wakes
    -- those clauses.
    watches   :: !( Growable Boxed.MVector s ( Growable Primitive.MVector s Watcher ) )
  , -- | Assigned literals (in chronological order).
    trail     :: !( Growable Unboxed.MVector s Lit )
  , -- | Trail position at which each decision level begins, indexed by
    -- decision level minus one (level @k+1@ starts at @trailLim[k]@).
    trailLim  :: !( Growable Unboxed.MVector s TrailPos )
  , -- | Next trail position for Boolean Constraint Propagation.
    qhead     :: !( MutVar s TrailPos )
  , -- | Storage for long clauses (size @>= 3@).
    clauseStore :: !( ClauseStore s )
  , -- | References of all learnt clauses (kept separate from input
    -- clauses so a future deletion policy can target only learnt material).
    learnts   :: !( Growable Primitive.MVector s ClauseRef )
  , -- | Lazy-reason closures attached to theory-propagated literals via
    -- 'Clause.RLazy'. Indexed by 'Clause.LazyRef'. Forced by 'walkUIP' when
    -- 1-UIP analysis crosses a theory-propagated literal.
    lazyReasons :: !( Growable Boxed.MVector s ( Clause.LazyReason s ) )
  , -- | Total conflicts encountered.
    confCount :: !( MutVar s Int )
  , -- | Total decisions taken.
    decCount  :: !( MutVar s Int )
  , -- | Flips to 'False' as soon as a top-level inconsistency is detected;
    -- from then on the solver is permanently UNSAT.
    okFlag    :: !( MutVar s Bool )

    -- Conflict-analysis scratch space, reused across every 'analyse' call
    -- so the inner loop never has to allocate fresh accumulators.
  , -- | Number of seen literals at the current decision level still on the
    -- implication path, decremented by each resolution step.
    analyzePathC      :: !( MutVar s Int )
  , -- | Variable indices that 'analyse' has marked in 'seen'; walked to
    -- clear the markers at the end of the call.
    analyzeTouched    :: !( Growable Primitive.MVector s Int )
  , -- | Literals at strictly lower decision levels collected during
    -- analysis; together with 'analyzeOtherLevels' these form the body of
    -- the learnt clause (the asserting literal is prepended afterwards).
    analyzeOtherLits  :: !( Growable Primitive.MVector s Lit )
  , -- | Levels matching 'analyzeOtherLits' in lockstep, used to find the
    -- second-watch literal and the backjump level.
    analyzeOtherLevels :: !( Growable Primitive.MVector s DecisionLevel )
  , -- | Transient per-variable marker used by learnt-clause minimisation: a
    -- variable proven /not/ self-subsumed (so its literal cannot be dropped).
    -- Memoises failed redundancy checks so the recursion does not re-explore a
    -- subtree. Always @False@ outside a 'minimiseLearnt' call.
    --
    -- The dual \"proven redundant\" state reuses the 'seen' marker (which also
    -- marks clause membership): both make the redundancy check treat a variable
    -- as covered, so they need not be distinguished.
    minFailed          :: !( Growable Unboxed.MVector s Bit )
  , -- | Variables whose 'minFailed' marker was set during minimisation; walked
    -- to clear those markers at the end of the call.
    minFailedTouched   :: !( Growable Primitive.MVector s Int )
  }

-------------------------------------------------------------------------------
-- Construction.

newSolver :: PrimMonad m => m ( Solver ( PrimState m ) )
newSolver = do
  asg   <- Growable.new 16
  lvl   <- Growable.new 16
  rsn   <- Growable.new 16
  phs   <- Growable.new 16
  dec   <- Growable.new 16
  vo    <- newVarOrder 0.95
  sen   <- Growable.new 16
  senL  <- Growable.new 32
  wts   <- Growable.new 32
  trl   <- Growable.new 16
  tlm   <- Growable.new 4
  lns   <- Growable.new 16
  qh    <- newMutVar 0
  cc    <- newMutVar 0
  dc    <- newMutVar 0
  ok    <- newMutVar True
  -- Scratch space for 'analyse'.
  -- Reset at the start of each 'analyse' call and grown on demand.
  apc   <- newMutVar 0
  ato   <- Growable.new 32
  aol   <- Growable.new 16
  aolv  <- Growable.new 16
  mf    <- Growable.new 16
  mft   <- Growable.new 16
  -- TODO: expose the clause-store capacity via 'SolverOptions'. The
  -- default is a compromise (small enough to be cheap to preallocate,
  -- large enough that typical problems do not run out before we implement
  -- learnt-clause deletion + compaction).
  cstore <- newClauseStore defaultStoreCapacityLits
  lzs    <- Growable.new 4
  pure Solver
    { assigns            = asg
    , level              = lvl
    , reason             = rsn
    , phase              = phs
    , decidable          = dec
    , varOrder           = vo
    , seen               = sen
    , seenLit            = senL
    , watches            = wts
    , trail              = trl
    , trailLim           = tlm
    , qhead              = qh
    , clauseStore        = cstore
    , learnts            = lns
    , lazyReasons        = lzs
    , confCount          = cc
    , decCount           = dc
    , okFlag             = ok
    , analyzePathC       = apc
    , analyzeTouched     = ato
    , analyzeOtherLits   = aol
    , analyzeOtherLevels = aolv
    , minFailed          = mf
    , minFailedTouched   = mft
    }
  where

    defaultStoreCapacityLits :: Int
    defaultStoreCapacityLits = ( 1024 * 1024 * 1024 ) `div` 8

numVariables :: PrimMonad m => Solver ( PrimState m ) -> m Int
numVariables s = Growable.length ( assigns s )

-- | Allocate a fresh /decision/ variable. All per-variable and per-literal
-- tables grow to accommodate it; the new variable is initially unassigned
-- with zero activity and no saved phase. It is registered at the bottom of
-- the activity heap and is eligible to be branched on by 'decide'.
-- | Add one activity bump to a variable (and re-heapify it). Exposed so a
-- theory can bias the decision order towards variables it considers
-- structurally important — e.g. the day-assignment bound atoms of the
-- scheduler, which we want decided before the within-day sequencing.
bumpVarActivity :: PrimMonad m => Solver ( PrimState m ) -> Var -> m ()
bumpVarActivity s = VarOrder.bumpActivity ( varOrder s )

newVar :: PrimMonad m => Solver ( PrimState m ) -> m Var
newVar s = newVarWith s True

-- | Allocate a fresh /auxiliary/ (non-decision) variable.
--
-- Identical to 'newVar' except that the variable is kept out of the activity
-- heap and flagged non-decidable: 'decide' never branches on it and
-- 'cancelUntil' never returns it to the heap.
newAuxVar :: PrimMonad m => Solver ( PrimState m ) -> m Var
newAuxVar s = newVarWith s False

-- | Shared allocator for 'newVar' / 'newAuxVar'.
newVarWith :: PrimMonad m => Solver ( PrimState m ) -> Bool -> m Var
newVarWith s isDecision = do
  v <- ( if isDecision then VarOrder.insertVar else VarOrder.insertAuxVar )
         ( varOrder s )
  Growable.push ( assigns s )   LUndef
  Growable.push ( level s )     UnassignedLevel
  Growable.push ( reason s )    Clause.RDecision
  Growable.push ( phase s )     Positive
  Growable.push ( decidable s ) ( Bit isDecision )
  Growable.push ( seen s )      ( Bit False )
  Growable.push ( minFailed s ) ( Bit False )
  -- Two seenLit slots per variable (one per polarity).
  Growable.push ( seenLit s ) ( Bit False )
  Growable.push ( seenLit s ) ( Bit False )
  -- Two fresh empty watch lists per variable (one for each polarity).
  posWs <- Growable.new initialWatchListCapacity
  negWs <- Growable.new initialWatchListCapacity
  Growable.push ( watches s ) posWs
  Growable.push ( watches s ) negWs
  pure v
  where
    initialWatchListCapacity :: Int
    initialWatchListCapacity = 4

-------------------------------------------------------------------------------
-- Lookups.

-- | The lifted-boolean value currently assigned to a variable.
valueOf
  :: PrimMonad m
  => Solver ( PrimState m ) -> Var -> m LBool
valueOf s v = Growable.read ( assigns s ) ( varIndex v )

-- | The lifted-boolean value of a literal under the current assignment.
litValue
  :: PrimMonad m
  => Solver ( PrimState m ) -> Lit -> m LBool
litValue s l = litValueFromVar l <$> valueOf s ( litVar l )

-- | The decision level we are currently exploring.
currentLevel :: PrimMonad m => Solver ( PrimState m ) -> m DecisionLevel
currentLevel s = DecisionLevel <$> Growable.length ( trailLim s )

-- | The decision level at which the given variable was assigned.
--
-- Precondition: the variable must currently be assigned.
levelOfAssignedVar
  :: PrimMonad m
  => Solver ( PrimState m ) -> Var -> m DecisionLevel
levelOfAssignedVar s v = do
  lvl <- Growable.read ( level s ) ( varIndex v )
  case lvl of
    UnassignedLevel -> do
      dump <- dumpSolverState s
      error $ "SAT.Solver.levelOfAssignedVar: unassigned variable "
           ++ show v ++ "\n" ++ dump
    _ -> return lvl

-- | Render a snapshot of the trail (lits, levels, reasons) and the
-- current decision-level stack, for inclusion in panic messages.
dumpSolverState
  :: forall m
  .  PrimMonad m
  => Solver ( PrimState m ) -> m String
dumpSolverState s = do
  TrailPos sz       <- trailSize s
  DecisionLevel cur <- currentLevel s
  nLim              <- Growable.length ( trailLim s )
  let
    readLim :: Int -> m Int
    readLim k = do TrailPos p <- Growable.read ( trailLim s ) k; pure p
    showLits :: Int -> m [ String ]
    showLits k
      | k >= sz   = pure []
      | otherwise = do
          l   <- Growable.read ( trail s ) k
          lvl <- Growable.read ( level s ) ( varIndex ( litVar l ) )
          val <- Growable.read ( assigns s ) ( varIndex ( litVar l ) )
          rsn <- Growable.read ( reason s ) ( varIndex ( litVar l ) )
          rest <- showLits ( k + 1 )
          pure ( ( "  [" ++ show k ++ "] " ++ show l
                 ++ "  lvl=" ++ ( case lvl of UnassignedLevel -> "UNASSIGNED"; DecisionLevel d -> show d )
                 ++ "  assign=" ++ show val
                 ++ "  reason=" ++ showReason rsn ) : rest )
    limLine :: Int -> m [ String ]
    limLine k
      | k >= nLim = pure []
      | otherwise = do
          p <- readLim k
          rest <- limLine ( k + 1 )
          pure ( ( show ( k + 1 ) ++ "->" ++ show p ) : rest )
  trailLines <- showLits 0
  lims       <- limLine 0
  pure $ "  trailSize=" ++ show sz ++ " currentLevel=" ++ show cur
      ++ "  trailLim=[" ++ intercalate "," lims ++ "]\n"
      ++ "  trail:\n" ++ unlines trailLines

showReason :: Clause.Reason -> String
showReason Clause.RFact         = "RFact"
showReason Clause.RDecision     = "RDecision"
showReason ( Clause.RBinary l ) = "RBinary " ++ show l
showReason ( Clause.RClause r ) = "RClause " ++ show r
showReason ( Clause.RLazy l )   = "RLazy " ++ show l

-- | Render a conflict source (for panic messages).
describeConflict
  :: forall m
  .  PrimMonad m
  => Solver ( PrimState m ) -> Conflict -> m String
describeConflict s = \case
    ConflictClause cref -> do
      c <- clauseAt s cref
      let n = clauseSize c
          go :: Int -> m [ String ]
          go k
            | k >= n    = pure []
            | otherwise = do
                l    <- clauseLit c k
                line <- describeLit l
                rest <- go ( k + 1 )
                pure ( line : rest )
      ls <- go 0
      pure $ "ConflictClause " ++ show cref ++ " (size=" ++ show n ++ "):\n"
          ++ unlines ls
    ConflictBinary l1 l2 -> do
      d1 <- describeLit l1
      d2 <- describeLit l2
      pure $ "ConflictBinary:\n" ++ unlines [ d1, d2 ]
  where
    describeLit :: Lit -> m String
    describeLit l = do
      let vi = varIndex ( litVar l )
      val <- Growable.read ( assigns s ) vi
      lvl <- Growable.read ( level s )   vi
      rsn <- Growable.read ( reason s )  vi
      pure $ "    " ++ show l
          ++ "  assign=" ++ show val
          ++ "  lvl=" ++ ( case lvl of UnassignedLevel -> "UNASSIGNED"; DecisionLevel d -> show d )
          ++ "  reason=" ++ showReason rsn

trailSize :: PrimMonad m => Solver ( PrimState m ) -> m TrailPos
trailSize s = TrailPos <$> Growable.length ( trail s )

numConflicts, numDecisions :: PrimMonad m => Solver ( PrimState m ) -> m Int
numConflicts = readMutVar . confCount
numDecisions = readMutVar . decCount

numLearnts :: PrimMonad m => Solver ( PrimState m ) -> m Int
numLearnts = Growable.length . learnts

-- | Look up a clause by its reference. Precondition: the reference came
-- from a previous 'recordClause' on this solver.
--
-- This is a thin wrapper around 'Clause.clauseAt' that drops the
-- 'clauseStore' indirection at call sites.
clauseAt
  :: PrimMonad m
  => Solver ( PrimState m ) -> ClauseRef -> m ( Clause ( PrimState m ) )
clauseAt s = Clause.clauseAt ( clauseStore s )

-- | Build a fresh long clause in the store and return both its reference
-- and a view over it. Does not attach watches.
recordClause
  :: PrimMonad m
  => Solver ( PrimState m ) -> Bool -> [ Lit ] -> m ( ClauseRef, Clause ( PrimState m ) )
recordClause s learnt ls = do
  ref <- ( if learnt then Clause.recordLearntClause else Clause.recordClause )
           ( clauseStore s ) ls
  c <- Clause.clauseAt ( clauseStore s ) ref
  pure ( ref, c )

-------------------------------------------------------------------------------
-- Assignment.

-- | Internal helper: write a variable's value, level, and reason, and
-- append the literal to the trail.
performAssignment
  :: PrimMonad m
  => Solver ( PrimState m ) -> Lit -> Clause.Reason -> m ()
performAssignment s l rsn = do
  let vi  = varIndex ( litVar l )
      val = polarityValue ( litPolarity l )
  lvl <- currentLevel s
  Growable.write ( assigns s ) vi val
  Growable.write ( level s )   vi lvl
  Growable.write  ( reason s )  vi rsn
  Growable.push  ( trail s )   l

-- | Assign a literal at the current decision level.
--
-- Precondition: the literal's variable is currently unassigned.
enqueueUndef
  :: PrimMonad m
  => Solver ( PrimState m ) -> Lit -> Clause.Reason -> m ()
enqueueUndef s l rsn = do
  cur <- valueOf s ( litVar l )
  case cur of
    LUndef -> performAssignment s l rsn
    _      -> error "SAT.Solver.enqueueUndef: variable already assigned"

-- | Attempt to assign a literal whose variable may already be set.
--
-- Returns 'False' iff the literal already evaluates to false under the
-- current assignment (a conflict); 'True' both when the literal was
-- already true (idempotent) and when the assignment succeeded.
--
-- Used for input unit clauses, which may contradict previously-posted
-- level-0 facts.
tryEnqueue
  :: PrimMonad m
  => Solver ( PrimState m ) -> Lit -> Clause.Reason -> m Bool
tryEnqueue s l rsn = do
  let val = polarityValue ( litPolarity l )
  cur <- valueOf s ( litVar l )
  case cur of
    LUndef -> performAssignment s l rsn *> pure True
    _      -> pure ( cur == val )

-------------------------------------------------------------------------------
-- Clause attachment and input.

-- | Append a watcher to the watch list of the given literal.
pushWatcher
  :: PrimMonad m
  => Solver ( PrimState m ) -> Lit -> Watcher -> m ()
pushWatcher s l w = do
  inner <- Growable.read ( watches s ) ( litIndex l )
  Growable.push inner w

-- | Register a binary clause @[l, m]@ inline on both watch lists. No
-- 'Clause' is allocated; the pair of watcher entries IS the clause.
attachBinary
  :: PrimMonad m
  => Solver ( PrimState m ) -> Lit -> Lit -> m ()
attachBinary s l m = do
  pushWatcher s ( negateLit l ) ( WBinary m )
  pushWatcher s ( negateLit m ) ( WBinary l )

-- | Register a long clause (size @>= 3@) on the watch lists of its first
-- two literals, using the other watched literal as the blocker hint.
attachLong
  :: PrimMonad m
  => Solver ( PrimState m ) -> ClauseRef -> Clause ( PrimState m ) -> m ()
attachLong s cref c
  | clauseSize c < 3
  = error $ "attachLong: expected clause of size >= 3, got " ++ show ( clauseSize c )
  | otherwise = do
      l0 <- clauseLit c 0
      l1 <- clauseLit c 1
      pushWatcher s ( negateLit l0 ) ( WLong cref l1 )
      pushWatcher s ( negateLit l1 ) ( WLong cref l0 )

-- | The outcome of posting an input clause.
data PostResult
  = -- | The clause was stored and attached to the solver.
    Posted
  | -- | The clause was not stored, because redundant.
    --
    -- The clause might be a literal-level tautology such as @x ∨ ¬x@,
    -- or already satisfied by a level-0 fact.
    Tautology
  | -- | The clause cannot be satisfied, because either:
    --
    --  - it is the empty clause
    --  - it contradicts an existing level-0 fact
    --  - propagation from a unit clause produced a conflict.
    InstantUnsat
  deriving stock ( Eq, Show )

-- | Post an input clause to the solver. Duplicate literals and clauses
-- already satisfied by level-0 facts are normalised away.
addClause
  :: PrimMonad m
  => Solver ( PrimState m ) -> [ Lit ] -> m PostResult
addClause s ls0 = do
  ok <- readMutVar ( okFlag s )
  if not ok then pure InstantUnsat
  else do
    mb <- preprocessClause s ls0
    case mb of
      Nothing -> pure Tautology
      Just [] -> markFalse s >> pure InstantUnsat
      Just [ l ] -> do
        e <- tryEnqueue s l Clause.RFact
        if e
        then do
          conf <- propagate s
          case conf of
            Just _  -> markFalse s >> pure InstantUnsat
            Nothing -> pure Posted
        else markFalse s >> pure InstantUnsat
      Just [ l, m ] -> do
        attachBinary s l m
        pure Posted
      Just ls -> do
        ( cref, c ) <- recordClause s False ls
        attachLong s cref c
        pure Posted

-- | Attach a binary clause @[l, m]@ to the watch lists mid-search, /without/
-- the unit-collapse and level-0 normalisation of 'addClause'.
--
-- 'addClause' is meant for input clauses posted at the ground level: when
-- normalisation reduces a clause to a unit it enqueues the survivor as an
-- 'RFact', which is only sound at the ground level. A binary clause generated
-- lazily during the search — a theory lemma such as bound-atom monotonicity —
-- must therefore be attached directly: were it left to 'addClause', a literal
-- already false at the ground level would collapse it to a unit and enqueue an
-- 'RFact' at the /current/ level, which later trips conflict analysis.
--
-- The caller must guarantee at least one literal is currently unassigned (true
-- when one of them is a freshly created variable), so the clause is never
-- already falsified at attach time; any later violation is caught by the watch
-- on the second literal.
addBinaryLemma
  :: PrimMonad m
  => Solver ( PrimState m ) -> Lit -> Lit -> m ()
addBinaryLemma s l m = do
  ok <- readMutVar ( okFlag s )
  when ok ( attachBinary s l m )

markFalse :: PrimMonad m => Solver ( PrimState m ) -> m ()
markFalse s = writeMutVar ( okFlag s ) False

-- | Normalise an input clause: drop duplicate literals, detect tautology,
-- drop literals already known false at level @0@, and report 'Nothing' if
-- any literal is already true at level @0@ (so the clause is trivially
-- satisfied).
preprocessClause
  :: forall m
  .  PrimMonad m
  => Solver ( PrimState m )
  -> [ Lit ]
  -> m ( Maybe [ Lit ] )
preprocessClause s ls0 = do
  result <- go [] ls0
  -- Clear any markers we may have set during the pass. Re-walking 'ls0' is
  -- safe: positions that were never marked are already 'Bit False', so the
  -- redundant writes are no-ops. This avoids keeping a separate touched-list
  -- accumulator alongside the kept-literals one.
  for_ ls0 \ l -> Growable.write ( seenLit s ) ( litIndex l ) ( Bit False )
  pure result
  where
    go :: [ Lit ] -> [ Lit ] -> m ( Maybe [ Lit ] )
    go !keep [] = pure ( Just ( reverse keep ) )
    go keep ( l : rest ) = do
      let li = litIndex l
          ni = litIndex ( negateLit l )
      Bit seenOpp <- Growable.read ( seenLit s ) ni
      if seenOpp
      then pure Nothing   -- tautology: the negation is already in the clause
      else do
        Bit seenSelf <- Growable.read ( seenLit s ) li
        if seenSelf
        then go keep rest   -- duplicate literal
        else do
          v <- valueOf s ( litVar l )
          let keepIt = do
                Growable.write ( seenLit s ) li ( Bit True )
                go ( l : keep ) rest
          case litValueFromVar l v of
            LUndef -> keepIt
            here -> do
              atGround <- ( GroundLevel == ) <$> levelOfAssignedVar s ( litVar l )
              case ( here, atGround ) of
                ( LTrue,  True ) -> pure Nothing
                ( LFalse, True ) -> go keep rest
                _                -> keepIt

-------------------------------------------------------------------------------
-- Boolean Constraint Propagation.

-- | Run BCP from the current trail tail until either no further propagation
-- is possible or a falsified clause is encountered.
propagate
  :: forall m
  .  PrimMonad m
  => Solver ( PrimState m ) -> m ( Maybe Conflict )
propagate s = loop
  where
    loop :: m ( Maybe Conflict )
    loop = do
      q  <- readMutVar ( qhead s )
      sz <- trailSize s
      if q >= sz
      then pure Nothing
      else do
        p <- Growable.read ( trail s ) ( unTrailPos q )
        writeMutVar ( qhead s ) ( q + 1 )
        mbConf <- propagateLit s p
        case mbConf of
          Just c  -> pure ( Just c )
          Nothing -> loop

-- | Outcome of revisiting a long-clause watcher.
data WatchOutcome
  = -- | The clause's watch was re-routed to a non-false literal; the
    -- watcher is no longer on the current watch list.
    WatchReplaced
  | -- | The watcher stays on the current watch list, with the given new
    -- blocker. Use this both when the other watched lit is already true
    -- (clause satisfied) and when the clause has just been unit-propagated.
    WatchKept !Lit
  | -- | All literals are false: the clause is the conflict. The new
    -- blocker should still be recorded so that subsequent BCP visits
    -- after a backjump see an up-to-date entry.
    WatchConflict !Lit

-- | Process every watcher on @watches[litIndex p]@ — these are clauses for
-- which @negateLit p@ is a watched literal, which has just become false.
--
-- Iterates with a read/write index pair so that watchers we keep are
-- compacted in place; watchers we move to a different watch list (via the
-- watch dance) are dropped from this list.
propagateLit
  :: forall m
  .  PrimMonad m
  => Solver ( PrimState m ) -> Lit -> m ( Maybe Conflict )
propagateLit s p = do
  ws <- Growable.read ( watches s ) ( litIndex p )
  total <- Growable.length ws
  loop ws total 0 0
  where
    falseLit :: Lit
    falseLit = negateLit p

    loop
      :: Growable Primitive.MVector ( PrimState m ) Watcher
      -> Int -> Int -> Int
      -> m ( Maybe Conflict )
    loop ws total !ri !wi
      | ri >= total = do
          Growable.truncate ws wi
          pure Nothing
      | otherwise = do
          w <- Growable.read ws ri
          case w of
            WBinary other -> do
              -- Binary watcher: clause memory is never touched.
              v <- litValue s other
              Growable.write ws wi w
              case v of
                LTrue  -> loop ws total ( ri + 1 ) ( wi + 1 )
                LUndef -> do
                  enqueueUndef s other ( Clause.RBinary p )
                  loop ws total ( ri + 1 ) ( wi + 1 )
                LFalse -> do
                  -- Restore unprocessed remainder so the watch invariant
                  -- holds when the search later backjumps and re-runs BCP.
                  compactRest ws total ( ri + 1 ) ( wi + 1 )
                  pure ( Just ( ConflictBinary falseLit other ) )
            WLong cref blocker -> do
              -- Try the blocker shortcut before fetching the clause.
              bv <- litValue s blocker
              if bv == LTrue
              then do
                Growable.write ws wi w
                loop ws total ( ri + 1 ) ( wi + 1 )
              else do
                c <- clauseAt s cref
                r <- handleWatched s cref falseLit c
                case r of
                  WatchReplaced -> loop ws total ( ri + 1 ) wi
                  WatchKept newBlocker -> do
                    Growable.write ws wi ( WLong cref newBlocker )
                    loop ws total ( ri + 1 ) ( wi + 1 )
                  WatchConflict newBlocker -> do
                    Growable.write ws wi ( WLong cref newBlocker )
                    compactRest ws total ( ri + 1 ) ( wi + 1 )
                    pure ( Just ( ConflictClause cref ) )

    -- Slide the unprocessed tail of the watch list down to writeIdx and
    -- truncate; called after surfacing a conflict.
    compactRest
      :: Growable Primitive.MVector ( PrimState m ) Watcher
      -> Int -> Int -> Int -> m ()
    compactRest ws total !ri !wi
      | ri >= total = Growable.truncate ws wi
      | otherwise = do
          w <- Growable.read ws ri
          Growable.write ws wi w
          compactRest ws total ( ri + 1 ) ( wi + 1 )

handleWatched
  :: forall m
  .  PrimMonad m
  => Solver ( PrimState m )
  -> ClauseRef                   -- ^ reference to the same clause; used for the new watch and the reason
  -> Lit                    -- ^ the watched literal that just became false
  -> Clause ( PrimState m )
  -> m WatchOutcome
handleWatched s cref falseLit c = do
  -- Normalise so 'falseLit' sits at position 1 and the other watched
  -- literal at position 0.
  c0 <- clauseLit c 0
  when ( c0 == falseLit ) ( clauseSwap c 0 1 )
  other <- clauseLit c 0
  otherV <- litValue s other
  case otherV of
    LTrue -> pure ( WatchKept other )
    _ -> do
      mb <- findNonFalseFrom s c 2
      case mb of
        Just ( i, newWatched ) -> do
          clauseSwap c 1 i
          -- The clause now watches 'other' at position 0 and 'newWatched'
          -- at position 1. Register it on the new watch list with 'other'
          -- as the blocker.
          pushWatcher s ( negateLit newWatched ) ( WLong cref other )
          pure WatchReplaced
        Nothing ->
          case otherV of
            LFalse -> pure ( WatchConflict other )
            LUndef -> do
              enqueueUndef s other ( Clause.RClause cref )
              pure ( WatchKept other )

-- | Scan a clause from position @start@ onwards for the first literal that
-- is not currently false, returning its position and value.
findNonFalseFrom
  :: forall m
  .  PrimMonad m
  => Solver ( PrimState m )
  -> Clause ( PrimState m )
  -> Int
  -> m ( Maybe ( Int, Lit ) )
findNonFalseFrom s c start = go start
  where
    n :: Int
    n = clauseSize c
    go :: Int -> m ( Maybe ( Int, Lit ) )
    go !i
      | i >= n = pure Nothing
      | otherwise = do
          l <- clauseLit c i
          v <- litValue s l
          if v == LFalse
          then go ( i + 1 )
          else pure ( Just ( i, l ) )

-------------------------------------------------------------------------------
-- Conflict analysis (1-UIP).

-- | Resolve the conflict clause backwards through the implication graph
-- until exactly one literal of the current decision level remains. That
-- literal is the first unique implication point; its negation is the
-- asserting literal of the learnt clause.
--
-- The returned learnt clause has the asserting literal first and the
-- highest-level remaining literal second, so that the clause is immediately
-- unit and watchable as soon as we backjump to the second component of the
-- return value.
analyse
  :: forall m
  .  PrimMonad m
  => Solver ( PrimState m )
  -> Conflict
  -> m ( [ Lit ], DecisionLevel )
analyse s conflict0 = do
  curLevel <- currentLevel s
  -- Reset the per-call scratch buffers. They are owned by the solver, so
  -- 'analyse' never needs to allocate fresh accumulators.
  writeMutVar ( analyzePathC s ) 0
  Growable.truncate ( analyzeTouched s )     0
  Growable.truncate ( analyzeOtherLits s )   0
  Growable.truncate ( analyzeOtherLevels s ) 0
  let
    -- Mark a variable as seen and remember it for batch-clearance.
    markSeen :: Int -> m ()
    markSeen vi = do
      Growable.write ( seen s ) vi ( Bit True )
      Growable.push ( analyzeTouched s ) vi

    -- Process a single literal during analysis, skipping the resolution
    -- variable @skipVi@ (@-1@ on the very first pass). Each
    -- previously-unseen literal at a non-zero level is either tallied on
    -- the path counter (if at the current level) or pushed onto the
    -- learnt-clause scratch buffers (if at a strictly lower level).
    visitLit :: Int -> Lit -> m ()
    visitLit skipVi l = do
      let vi = varIndex ( litVar l )
      Bit marker <- Growable.read ( seen s ) vi
      if marker || vi == skipVi
      then pure ()
      else do
        lvl <- levelOfAssignedVar s ( litVar l )
        if lvl <= GroundLevel
        then pure ()
        else do
          VarOrder.bumpActivity ( varOrder s ) ( Var vi )
          markSeen vi
          if lvl >= curLevel
          then modifyMutVar' ( analyzePathC s ) ( + 1 )
          else do
            Growable.push ( analyzeOtherLits   s ) l
            Growable.push ( analyzeOtherLevels s ) lvl

    -- Walk a long-clause reason, deferring per-literal work to 'visitLit'.
    visit :: Int -> Clause ( PrimState m ) -> m ()
    visit skipVi c = do
      let n = clauseSize c
          loopK !k
            | k >= n = pure ()
            | otherwise = do
                l <- clauseLit c k
                visitLit skipVi l
                loopK ( k + 1 )
      loopK 0

  -- Seed analysis from the conflict source.
  case conflict0 of
    ConflictClause cref -> do
      c <- clauseAt s cref
      visit ( -1 ) c
    ConflictBinary l1 l2 -> do
      visitLit ( -1 ) l1
      visitLit ( -1 ) l2

  -- BCP only fires this analysis when the conflict was produced at the
  -- current level, so the conflict source must mention at least one
  -- literal at 'curLevel'. Failing this points at a BCP / level-bookkeeping
  -- bug; panic loudly rather than walking the trail past its head.
  postVisitPC <- readMutVar ( analyzePathC s )
  when ( postVisitPC == 0 ) $ do
    conflictDesc <- describeConflict s conflict0
    stateDump    <- dumpSolverState s
    error $ unlines
      [ "SAT.Solver.analyse: conflict at level > 0 has no current-level literals."
      , "  currentLevel=" ++ show ( unDecisionLevel curLevel )
      , "  conflict source:"
      , conflictDesc
      , stateDump
      ]

  initTrail <- trailSize s
  uipLit <- walkUIP s visit visitLit ( initTrail - 1 )

  -- Drop self-subsumed body literals while 'seen' still marks the body. This
  -- runs before the clause is built, so 'pickSecondWatch' sees the shorter body.
  minimiseLearnt s

  -- Clear the 'seen' bits we set during this analysis (including variables
  -- 'minimiseLearnt' additionally marked while memoising proven-redundant ones).
  do
    touchedN <- Growable.length ( analyzeTouched s )
    let clearLoop !i
          | i >= touchedN = pure ()
          | otherwise = do
              vi <- Growable.read ( analyzeTouched s ) i
              Growable.write ( seen s ) vi ( Bit False )
              clearLoop ( i + 1 )
    clearLoop 0

  let asserting = negateLit uipLit
  ( mbSecond, restLits, bjLevel ) <-
    pickSecondWatch ( analyzeOtherLits s ) ( analyzeOtherLevels s )
  let learnt = case mbSecond of
        Nothing    -> [ asserting ]
        Just secnd -> asserting : secnd : restLits
  pure ( learnt, bjLevel )

-- | Recursive learnt-clause minimisation (self-subsumption; Sörensson \& Biere
-- 2009). A body literal of the learnt clause is /redundant/ when its negation is
-- already implied by the rest of the clause — i.e. every other literal of its
-- reason is at the ground level, in the clause, or itself recursively redundant.
-- Dropping all such literals leaves a logically-equivalent, typically much
-- shorter clause (often roughly halved).
--
-- Precondition: 'seen' is set exactly for the body-literal variables (the state
-- 'walkUIP' leaves behind). A variable proven redundant is additionally marked
-- 'seen' (memoising success — harmlessly extending clause membership for the
-- recursive check) and appended to 'analyzeTouched' so the caller clears it; a
-- variable proven irredundant is marked 'minFailed', cleared before returning.
minimiseLearnt
  :: forall m
  .  PrimMonad m
  => Solver ( PrimState m ) -> m ()
minimiseLearnt s = do
  Growable.truncate ( minFailedTouched s ) 0
  n <- Growable.length ( analyzeOtherLits s )
  -- The set of decision levels present in the body, hashed into a 64-bit mask
  -- ('abstractLevel'). A literal can only be self-subsumed if every other
  -- literal of its reason resolves into a level already in the clause; a reason
  -- literal whose level is absent from this mask is therefore not coverable, and
  -- the redundancy check fails fast without forcing the (possibly large, coarse)
  -- reason. (MiniSat's abstraction-levels optimisation; conservative under hash
  -- collisions, never unsound.)
  abstraction <- collectAbstraction n
  let
    -- Walk the body buffer, dropping redundant literals and compacting both
    -- buffers in lockstep (read index @ri@, write index @wi@).
    compact :: Int -> Int -> m ()
    compact !ri !wi
      | ri >= n = do
          Growable.truncate ( analyzeOtherLits s )   wi
          Growable.truncate ( analyzeOtherLevels s ) wi
      | otherwise = do
          l   <- Growable.read ( analyzeOtherLits s ) ri
          red <- reasonRedundant abstraction ( varIndex ( litVar l ) )
          if red
          then compact ( ri + 1 ) wi
          else do
            when ( wi /= ri ) do
              lvl <- Growable.read ( analyzeOtherLevels s ) ri
              Growable.write ( analyzeOtherLits s )   wi l
              Growable.write ( analyzeOtherLevels s ) wi lvl
            compact ( ri + 1 ) ( wi + 1 )
  compact 0 0
  clearFailed
  where
    -- OR together the abstraction bits of every body literal's level.
    collectAbstraction :: Int -> m Word64
    collectAbstraction n = go 0 0
      where
        go !i !acc
          | i >= n    = pure acc
          | otherwise = do
              lvl <- Growable.read ( analyzeOtherLevels s ) i
              go ( i + 1 ) ( acc .|. abstractLevel lvl )
    -- A variable's assignment is self-subsumed iff its reason exists and every
    -- /other/ literal of that reason is covered. A decision (no reason) is not.
    reasonRedundant :: Word64 -> Int -> m Bool
    reasonRedundant abstraction vi = do
      rsn <- Growable.read ( reason s ) vi
      case rsn of
        Clause.RDecision     -> pure False
        Clause.RFact         -> pure True   -- a ground fact is unconditionally true
        Clause.RBinary other -> covered abstraction other
        Clause.RClause cref  -> clauseOthersCovered abstraction cref vi
        Clause.RLazy lref    -> forceLazy s lref >>= othersCovered abstraction vi

    -- Whether reason-literal @q@ is covered: at the ground level, already a
    -- clause (or proven-redundant) variable, or recursively self-subsumed.
    -- Memoises both outcomes (success via 'seen', failure via 'minFailed'). A
    -- literal whose level is absent from the clause's @abstraction@ mask cannot
    -- be covered, so it fails fast without forcing its reason.
    covered :: Word64 -> Lit -> m Bool
    covered abstraction q = do
      let vq = varIndex ( litVar q )
      lvl <- levelOfAssignedVar s ( litVar q )
      if lvl <= GroundLevel
      then pure True
      else do
        Bit isSeen <- Growable.read ( seen s ) vq
        if isSeen
        then pure True
        else do
          Bit isFailed <- Growable.read ( minFailed s ) vq
          if isFailed
          then pure False
          else if abstractLevel lvl .&. abstraction == 0
          then markFailed vq
          else do
            ok <- reasonRedundant abstraction vq
            if ok
            then do
              Growable.write ( seen s ) vq ( Bit True )
              Growable.push  ( analyzeTouched s ) vq
              pure True
            else markFailed vq

    markFailed :: Int -> m Bool
    markFailed vq = do
      Growable.write ( minFailed s ) vq ( Bit True )
      Growable.push  ( minFailedTouched s ) vq
      pure False

    -- Every literal of the reason clause other than the resolved variable @vi@.
    clauseOthersCovered :: Word64 -> ClauseRef -> Int -> m Bool
    clauseOthersCovered abstraction cref vi = do
      c <- clauseAt s cref
      let sz = clauseSize c
          go !k
            | k >= sz   = pure True
            | otherwise = do
                l <- clauseLit c k
                if varIndex ( litVar l ) == vi
                then go ( k + 1 )
                else do
                  cov <- covered abstraction l
                  if cov then go ( k + 1 ) else pure False
      go 0

    othersCovered :: Word64 -> Int -> [ Lit ] -> m Bool
    othersCovered abstraction vi = go
      where
        go [] = pure True
        go ( l : ls )
          | varIndex ( litVar l ) == vi = go ls
          | otherwise = do
              cov <- covered abstraction l
              if cov then go ls else pure False

    clearFailed :: m ()
    clearFailed = do
      k <- Growable.length ( minFailedTouched s )
      let loop !i
            | i >= k = pure ()
            | otherwise = do
                vi <- Growable.read ( minFailedTouched s ) i
                Growable.write ( minFailed s ) vi ( Bit False )
                loop ( i + 1 )
      loop 0

-- | Walk backwards along the trail at the current level, popping seen
-- variables and resolving against their reason clauses, until a single
-- current-level literal remains. That literal is the 1-UIP.
walkUIP
  :: forall m
  .  PrimMonad m
  => Solver ( PrimState m )
  -> ( Int -> Clause ( PrimState m ) -> m () )
  -> ( Int -> Lit -> m () )
  -> TrailPos
  -> m Lit
walkUIP s visit visitLit ( TrailPos start ) = go start
  where
    go :: Int -> m Lit
    go !idx
      | idx < 0 = error "SAT.Solver.analyse: trail underflow during UIP scan"
      | otherwise = do
          lit <- Growable.read ( trail s ) idx
          let vi = varIndex ( litVar lit )
          Bit marker <- Growable.read ( seen s ) vi
          if not marker
          then go ( idx - 1 )
          else do
            modifyMutVar' ( analyzePathC s ) ( subtract 1 )
            Growable.write ( seen s ) vi ( Bit False )
            pc <- readMutVar ( analyzePathC s )
            if pc == 0
            then pure lit
            else do
              rsn <- Growable.read ( reason s ) vi
              case rsn of
                Clause.RDecision ->
                  error "SAT.Solver.analyse: decision encountered before UIP"
                Clause.RFact ->
                  error "SAT.Solver.analyse: ground-level fact reached during UIP scan"
                Clause.RBinary other -> do
                  -- A binary reason [lit, other] resolves on 'lit'; only
                  -- 'other' needs to be visited (the polarity of 'lit'
                  -- itself is the resolution variable, filtered via 'vi').
                  visitLit vi other
                  go ( idx - 1 )
                Clause.RClause cref -> do
                  c' <- clauseAt s cref
                  visit vi c'
                  go ( idx - 1 )
                Clause.RLazy lref -> do
                  -- Theory-propagated literal: force the deferred reason
                  -- closure to recover the supporting clause's literals.
                  ls <- forceLazy s lref
                  visitLits vi ls
                  go ( idx - 1 )

    visitLits :: Int -> [ Lit ] -> m ()
    visitLits skipVi = mapM_ ( visitLit skipVi )

-- | Pick the highest-level literal from the analyse-side scratch buffers;
-- it becomes the learnt clause's second watch and its level the backjump
-- level. The remaining literals (excluding the chosen one) are returned
-- in storage order. The backjump level is 'GroundLevel' when there are no
-- lower-level lits.
pickSecondWatch
  :: forall m
  .  PrimMonad m
  => Growable Primitive.MVector ( PrimState m ) Lit
  -> Growable Primitive.MVector ( PrimState m ) DecisionLevel
  -> m ( Maybe Lit, [ Lit ], DecisionLevel )
pickSecondWatch litsBuf lvlsBuf = do
  n <- Growable.length litsBuf
  if n == 0
  then pure ( Nothing, [], GroundLevel )
  else do
    -- Scan once for the index of the maximum-level entry.
    let findMax :: Int -> Int -> DecisionLevel -> m ( Int, DecisionLevel )
        findMax !i !bestI !bestL
          | i >= n = pure ( bestI, bestL )
          | otherwise = do
              l <- Growable.read lvlsBuf i
              if l > bestL
              then findMax ( i + 1 ) i l
              else findMax ( i + 1 ) bestI bestL
    headLvl <- Growable.read lvlsBuf 0
    ( bestI, bestL ) <- findMax 1 0 headLvl
    bestLit <- Growable.read litsBuf bestI
    -- Build the rest of the clause body (the lits other than 'bestLit'),
    -- in storage order, by walking the buffer right-to-left and consing.
    let buildRest :: Int -> [ Lit ] -> m [ Lit ]
        buildRest !i !acc
          | i < 0       = pure acc
          | i == bestI  = buildRest ( i - 1 ) acc
          | otherwise = do
              l <- Growable.read litsBuf i
              buildRest ( i - 1 ) ( l : acc )
    rest <- buildRest ( n - 1 ) []
    pure ( Just bestLit, rest, bestL )

-------------------------------------------------------------------------------
-- Backjump.

-- | Undo all assignments above the given decision level. If the target is
-- already at or above the current level, this is a no-op.
cancelUntil
  :: forall m
  .  PrimMonad m
  => Solver ( PrimState m ) -> DecisionLevel -> m ()
cancelUntil s tgtLevel@( DecisionLevel tgt ) = do
  cur <- currentLevel s
  when ( cur > tgtLevel ) do
    TrailPos sz  <- trailSize s
    lim@( TrailPos limI ) <- Growable.read ( trailLim s ) tgt
    let
      undo :: Int -> m ()
      undo !i
        | i < limI  = pure ()
        | otherwise = do
            lit <- Growable.read ( trail s ) i
            let v  = litVar lit
                vi = varIndex v
            -- The lit on the trail was the asserted-true literal, so its
            -- polarity is exactly the polarity we want to save for the
            -- next decision touching this variable.
            Growable.write ( phase s )   vi ( litPolarity lit )
            Growable.write ( assigns s ) vi LUndef
            Growable.write ( level s )   vi UnassignedLevel
            Growable.write ( reason s )  vi Clause.RDecision
            -- A decision variable is unassigned again, so it must be in the
            -- heap to be eligible for future decisions; 'reinsertVar' is a
            -- no-op if it was already there (i.e. it was propagated, not
            -- popped). Auxiliary (non-decision) variables are deliberately
            -- never returned to the heap.
            Bit dec <- Growable.read ( decidable s ) vi
            when dec ( VarOrder.reinsertVar ( varOrder s ) v )
            undo ( i - 1 )
    undo ( sz - 1 )
    Growable.truncate ( trail s )    limI
    Growable.truncate ( trailLim s ) tgt
    writeMutVar ( qhead s )    lim

-------------------------------------------------------------------------------
-- Decisions.

-- | Pick the unassigned variable with the highest VSIDS activity, returning
-- the literal with the saved phase (defaulting to positive when no phase
-- has been saved). Returns 'Nothing' once every variable is assigned.
--
-- O(log /n/) per call in the amortised case.
decide
  :: forall m
  .  PrimMonad m
  => Solver ( PrimState m ) -> m ( Maybe Lit )
decide s = do
  mbV <- VarOrder.extractMaxBy ( varOrder s ) isUnassigned
  case mbV of
    Nothing -> pure Nothing
    Just v  -> do
      modifyMutVar' ( decCount s ) ( + 1 )
      pol <- Growable.read ( phase s ) ( varIndex v )
      pure ( Just ( mkLit v pol ) )
  where
    isUnassigned :: Var -> m Bool
    isUnassigned v = ( LUndef == ) <$> valueOf s v

-- | Branch on a /specific/ variable, returning the literal with its saved phase
-- (defaulting to positive). 'Nothing' if the variable is already assigned.
--
-- Unlike 'decide', this neither consults the VSIDS heap nor counts the decision
-- (the caller is expected to count it via 'countDecision'), so a theory
-- heuristic can propose any variable — e.g. one chosen by conflict-ordering —
-- while still honouring phase saving. The variable need not be removed from the
-- VSIDS heap: 'decide' filters out already-assigned variables, and 'cancelUntil'
-- reinserts it once it becomes unassigned again.
decideVar
  :: forall m
  .  PrimMonad m
  => Solver ( PrimState m ) -> Var -> m ( Maybe Lit )
decideVar s v = do
  val <- valueOf s v
  case val of
    LUndef -> do
      pol <- Growable.read ( phase s ) ( varIndex v )
      pure ( Just ( mkLit v pol ) )
    _ -> pure Nothing

-------------------------------------------------------------------------------
-- Search driver.

-- | The outcome of a 'solve' call.
data Verdict
  = -- | A satisfying assignment exists; call 'getModel' to extract it.
    Sat
  | -- | The problem is unsatisfiable.
    Unsat
  | -- | The conflict budget was exhausted before a verdict was reached.
    Unknown
  deriving stock ( Eq, Show )

-- | Outcome of one Luby restart window.
data StepResult
  = Solved !Verdict
  | Restart

solve
  :: PrimMonad m
  => Solver ( PrimState m ) -> m Verdict
solve = solveWith defaultOptions

solveWith
  :: forall m
  .  PrimMonad m
  => SolverOptions -> Solver ( PrimState m ) -> m Verdict
solveWith opts s = do
  ok <- readMutVar ( okFlag s )
  if not ok then pure Unsat
  else do
    cancelUntil s GroundLevel
    mbConf <- propagate s
    case mbConf of
      Just _  -> markFalse s *> pure Unsat
      Nothing -> driveRestarts 1
  where
    driveRestarts :: Int -> m Verdict
    driveRestarts !k = do
      let confLimit = optRestartUnit opts * Restart.luby k
      res <- searchWindow confLimit
      case res of
        Solved v -> pure v
        Restart  -> do
          cancelUntil s GroundLevel
          driveRestarts ( k + 1 )

    searchWindow :: Int -> m StepResult
    searchWindow !limit = step 0
      where
        step :: Int -> m StepResult
        step !confs = do
          mbConf <- propagate s
          case mbConf of
            Just c -> do
              lvl <- currentLevel s
              if lvl == GroundLevel
              then markFalse s *> pure ( Solved Unsat )
              else do
                -- Count, analyse, backjump, install, decay.
                -- No theory backjump hook needed for the plain SAT loop.
                resolveConflict s c ( \ _bj -> pure () )
                budget <- checkBudget
                if budget == Just Unknown
                then pure ( Solved Unknown )
                else if confs + 1 >= limit
                then pure Restart
                else step ( confs + 1 )
            Nothing -> do
              mbLit <- decide s
              case mbLit of
                Nothing -> pure ( Solved Sat )
                Just lit -> do
                  pushNewLevel s
                  enqueueUndef s lit Clause.RDecision
                  step confs

        checkBudget :: m ( Maybe Verdict )
        checkBudget
          | optConflictBudget opts <= 0 = pure Nothing
          | otherwise = do
              n <- readMutVar ( confCount s )
              pure $ if n >= optConflictBudget opts then Just Unknown else Nothing

-------------------------------------------------------------------------------
-- Driver primitives.
--
-- The functions below carve up the inner step of 'solveWith' into discrete
-- pieces, exposed for DPLL(T) consumers that interleave theory work with
-- the SAT search.

-- | Open a fresh decision level by marking the current trail size as the
-- start of the new level. The next 'enqueueUndef' call will be the head
-- of the new level (typically a decision).
pushNewLevel
  :: PrimMonad m
  => Solver ( PrimState m ) -> m ()
pushNewLevel s = do
  n <- trailSize s
  Growable.push ( trailLim s ) n

-- | Record a branching decision taken /outside/ 'decide' — e.g. a literal
-- proposed by a DPLL(T) theory's own decision heuristic — so that
-- 'numDecisions' counts the full search-tree size, not just VSIDS branches.
countDecision
  :: PrimMonad m
  => Solver ( PrimState m ) -> m ()
countDecision s = modifyMutVar' ( decCount s ) ( + 1 )

-- | Install a learnt clause and unit-assert its asserting literal.
--
-- The clause must be non-empty and unit at the current decision level
-- (i.e. its asserting literal is currently unassigned and every other
-- literal is currently false at strictly lower levels).
--
-- Returns silently for the unit and ground-level cases; in particular,
-- passing the empty clause marks the solver as permanently UNSAT.
installLearnt
  :: PrimMonad m
  => Solver ( PrimState m ) -> [ Lit ] -> m ()
installLearnt s = \case
  [] -> markFalse s
  [ l ] -> enqueueUndef s l Clause.RFact
  [ l, m ] -> do
    attachBinary s l m
    enqueueUndef s l ( Clause.RBinary m )
  ls@( l : _ ) -> do
    ( cref, c ) <- recordClause s True ls
    Growable.push ( learnts s ) cref
    attachLong s cref c
    enqueueUndef s l ( Clause.RClause cref )

-- | Resolve a non-ground conflict.
--
-- Precondition: the conflict is at a decision level strictly above
-- 'GroundLevel'; a ground-level conflict is terminal UNSAT and must be
-- handled by the caller via 'markFalse'.
--
-- Consequently, 'numConflicts' counts only resolved above-ground conflicts.
resolveConflict
  :: PrimMonad m
  => Solver ( PrimState m )
  -> Conflict
  -> ( DecisionLevel -> m () )
       -- ^ post-backjump hook, run after 'cancelUntil' and before
       -- 'installLearnt'; given the backjump level
  -> m ()
resolveConflict s c onBackjump = do
  modifyMutVar' ( confCount s ) ( + 1 )
  ( learnt, bj ) <- analyse s c
  cancelUntil s bj
  onBackjump bj
  installLearnt s learnt
  VarOrder.decayActivities ( varOrder s )

-- | Whether the solver is still consistent (i.e. has not detected a
-- ground-level inconsistency).
isOk :: PrimMonad m => Solver ( PrimState m ) -> m Bool
isOk = readMutVar . okFlag

-- | Read the literal at a trail position. Precondition: the position is
-- in @[0, trailSize)@.
trailAt
  :: PrimMonad m
  => Solver ( PrimState m ) -> TrailPos -> m Lit
trailAt s ( TrailPos i ) = Growable.read ( trail s ) i

-- | Stash a lazy-reason closure in the solver and return its handle.
--
-- The closure can later be attached to a theory-propagated literal as a
-- 'Clause.RLazy' reason. It is forced only if 1-UIP analysis crosses the
-- literal.
recordLazyReason
  :: PrimMonad m
  => Solver ( PrimState m ) -> Clause.LazyReason ( PrimState m ) -> m Clause.LazyRef
recordLazyReason s lazy = do
  i <- Growable.length ( lazyReasons s )
  Growable.push ( lazyReasons s ) lazy
  pure ( Clause.LazyRef i )

-- | Force a previously-recorded 'Clause.LazyReason' to obtain its supporting
-- clause's literals.
forceLazy
  :: PrimMonad m
  => Solver ( PrimState m ) -> Clause.LazyRef -> m [ Lit ]
forceLazy s ( Clause.LazyRef i ) = do
#ifdef DEBUG
  n <- Growable.length ( lazyReasons s )
  when ( i < 0 || i >= n ) $
    error $ "SAT.Solver.forceLazy: out-of-range LazyRef=" ++ show i
         ++ " lazyReasons.length=" ++ show n
#endif
  lazy <- Growable.read ( lazyReasons s ) i
  Clause.forceLazyReason lazy

-- | Record a long (size @≥ 3@) theory-supplied clause in the clause store
-- without attaching watchers.
--
-- Intended for materialising a theory conflict so that 'analyse' can read
-- it via 'clauseAt'. Theory conflict clauses are consumed once by 1-UIP
-- and never need to participate in BCP, so they do not need to be in any
-- watch list. (The /learnt/ clause that 1-UIP produces from analysis is
-- attached normally via 'installLearnt'.)
recordTheoryClause
  :: PrimMonad m
  => Solver ( PrimState m ) -> [ Lit ] -> m ClauseRef
recordTheoryClause s ls = fst <$> recordClause s False ls
  -- TODO: these clauses are stored permanently, never reclaimed.

-------------------------------------------------------------------------------
-- Assignments.

-- | A snapshot of the solver's variable assignment.
--
-- Only variables with a definite value are present; unassigned variables
-- are absent and surface as 'LUndef' via 'assignmentValue'.
newtype Assignment = Assignment ( IntMap Bool )
  deriving stock Show

-- | The lifted-boolean value of a variable under the assignment.
assignmentValue :: Var -> Assignment -> LBool
assignmentValue ( Var v ) ( Assignment m ) =
  case IntMap.lookup v m of
    Just True  -> LTrue
    Just False -> LFalse
    Nothing    -> LUndef

-- | Take a snapshot of the solver's current assignment.
--
-- Most relevant after 'solve' has returned 'Sat' to get the full assignment,
-- but calling it in any other state is well defined and returns the
-- partial assignment at that point.
--
-- TODO: this walks every variable; it would be cheaper to walk the trail
-- (whose length is the number of /assigned/ variables) when the caller
-- only cares about assigned values. (Negligible for one-shot use.)
getModel
  :: forall m
  .  PrimMonad m
  => Solver ( PrimState m ) -> m Assignment
getModel s = do
  n <- numVariables s
  let
    collect :: Int -> IntMap Bool -> m ( IntMap Bool )
    collect !i !acc
      | i < 0     = pure acc
      | otherwise = do
          val <- valueOf s ( Var i )
          let !acc' = case val of
                LTrue  -> IntMap.insert i True  acc
                LFalse -> IntMap.insert i False acc
                LUndef -> acc
          collect ( i - 1 ) acc'
  Assignment <$> collect ( n - 1 ) IntMap.empty
