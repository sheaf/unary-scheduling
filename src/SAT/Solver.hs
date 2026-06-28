{-# LANGUAGE CPP                  #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE UndecidableInstances #-}

-- | A Conflict Driven Clause Learning (CDCL) SAT solver, inspired by MiniSat.
--
-- The module plays two roles:
--
--   * a self-contained solver ('solve'/'solveWith')
--   * a set of lower-level primitives that expose each step of the loop
--     ('decide', 'propagate', 'analyse', 'cancelUntil', 'installLearnt') so
--     that a DPLL(T) theory can interleave its own propagation and decisions.
--
-- The loop is the standard CDCL skeleton:
--
--  - the search decides on the value of a literal,
--  - the value is propagated by two-watched-literal BCP until a clause is
--    falsified or no unit propagation remains
--  - on conflict, we learn an asserting clause by 1-UIP analysis, backjump,
--    and resume the search.
module SAT.Solver
  ( -- * Solver
    SolverState, Assignments
  , solverAssignments
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
  , defaultSolverOptions
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
  , dumpAssignments
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
  , getLazyReason
  , forceLazyReason
  , recordTheoryClause
  , recordFalsifiedClause
  , ClauseRef(..)
  , FalsifiedClauseRef(..)
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
import Data.Int
  ( Int32 )
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
  ( Prim )
import Data.Primitive.MutVar
  ( MutVar, newMutVar, readMutVar, writeMutVar, modifyMutVar' )

-- memory-arena
import Memory.Growable
  ( Growable )
import qualified Memory.Growable as Growable
import Memory.Prim
  ( IsoPrim(..), As(..), P2(..) )

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
  , Lit(..), litIndex, mkLit, litVar, litPolarity, negateLit
  , Ł3(..)
  , litValueFromVarValue
  , LitOfValue(..), FalsifiedLit
  )
import SAT.Clause
  ( Clause, clauseSize, clauseSwap
  , clauseLit
  , ClauseRef(..)
  , FalsifiedClauseRef(..)
  , ClauseStore, newClauseStore
  )
import qualified SAT.Clause as Clause
  ( Reason(..), LazyReason(..), LazyRef(..)
  , clauseAt, recordClause, recordLearntClause
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

-- | Hash a decision level into one of 64 buckets as a single-bit mask.
hashDecisionLevel :: DecisionLevel -> Word64
hashDecisionLevel ( DecisionLevel l ) = 1 `unsafeShiftL` ( l .&. 63 )

-------------------------------------------------------------------------------
-- Trail positions.

-- | A position on the assignment trail: an index in the range @[0, trailSize)@.
newtype TrailPos = TrailPos { unTrailPos :: Int32 }
  deriving stock   Show
  deriving newtype ( Eq, Ord, Num )

-- | Watermarks needed to restore an 'AssignmentTrail' on backjump.
data LevelStart = LevelStart
  { levelTrailPos  :: !TrailPos
    -- ^ 'entries' length when the level started
    --
    -- This is also where Boolean Constraint Propagation resumes, i.e.
    -- the 'trailHead' to restore on backjump.
  , levelLazyCount :: !Int32
    -- ^ 'lazyReasons' length when the level opened
  }
  deriving stock Show

-- | Fit a 'LevelStart' into two 'Int32's.
deriving via ( As LevelStart ( P2 Int32 ) ) instance Prim LevelStart
instance IsoPrim LevelStart ( P2 Int32 ) where
  toPrim ( LevelStart ( TrailPos i ) j ) = P2 i j
  fromPrim ( P2 i j ) = LevelStart ( TrailPos i ) j

-- | Assigned literals in chronological order, with the per-level bookkeeping
-- needed to backtrack.
data AssignmentTrail s = AssignmentTrail
  { entries     :: !( Growable Primitive.MVector s Lit )
    -- ^ Assigned literals, in chronological assignment order.
  , levelStarts :: !( Growable Primitive.MVector s LevelStart )
    -- ^ Per-level watermarks, indexed by decision level minus one (level @k+1@
    -- opens at @levelStarts[k]@).
  , trailHead   :: !( MutVar s TrailPos )
    -- ^ Next trail position for Boolean Constraint Propagation.
  , lazyReasons :: !( Growable Boxed.MVector s ( Clause.LazyReason s ) )
    -- ^ Lazy-reason closures attached to theory-propagated literals via
    -- 'Clause.RLazy', indexed by 'Clause.LazyRef'.
  }

-- | Create a new (empty) assignment trail.
newAssignmentTrail :: PrimMonad m => m ( AssignmentTrail ( PrimState m ) )
newAssignmentTrail = do
  entries     <- Growable.new 16
  levelStarts <- Growable.new 4
  trailHead   <- newMutVar 0
  lazyReasons <- Growable.new 4
  pure $ AssignmentTrail { .. }

-------------------------------------------------------------------------------
-- Watchers and conflicts.

-- | A single entry on a literal's watch list.
data Watcher
  = -- | A binary clause, storing the "other literal" of the clause.
    WBinary !Lit
  | -- | A long clause (size @>= 3@).
    WLong
      !ClauseRef
      !Lit
        -- ^ Blocker: literal whose current assignment allows BCP to skip
        -- fetching the clause altogether.

-- | Encode a 'Watcher' into two 'Int32's.
deriving via ( As Watcher ( P2 Int32 ) ) instance Prim Watcher
instance IsoPrim Watcher ( P2 Int32 ) where
  toPrim = \case
    WBinary ( Lit lit )                -> P2 -1 lit
    WLong ( ClauseRef cr ) ( Lit lit ) -> P2 cr lit
  fromPrim ( P2 cref lit )
    | cref < 0  = WBinary ( Lit lit )
    | otherwise = WLong ( ClauseRef cref ) ( Lit lit )

-- | The source of a Binary Constraint Propagation (BCP) conflict.
data Conflict
  = ConflictClause !FalsifiedClauseRef
  | ConflictBinary !FalsifiedLit !FalsifiedLit

-------------------------------------------------------------------------------
-- Solver state.

-- | The mutable state of a running CDCL search.
data SolverState s = SolverState
  { -- | Flips to 'False' as soon as a top-level inconsistency is detected;
    -- from then on the solver is permanently UNSAT.
    okFlag    :: !( MutVar s Bool )

    -- | Variable assignments and related metadata.
  , solverAssignments :: !( Assignments s )

  , -- | Clause database.
    clauseDB  :: !( ClauseDB s )

    -- | Activity-ordered variable priority queue.
  , varOrder  :: !( VarOrder s )

    -- | Transient per-literal marker.
    --
    -- Used by 'preprocessClause' to detect duplicate literals and tautologies,
    -- and by 'binarySubsume' for O(1) learnt-clause membership tests.
    --
    -- Always @False@ outside of those calls.
  , seenLit   :: !( Growable Unboxed.MVector s Bit )

    -- | Conflict-analysis and learnt-clause-minimisation state.
  , analysisState :: !( AnalysisState s )

    -- | Search statistics and instrumentation counters.
  , stats     :: !( Statistics s )
  }

-- | Tunable parameters for the solver.
data SolverOptions = SolverOptions
  { -- | VSIDS activity decay factor in @(0, 1]@.
    --
    -- Smaller values fade older bumps faster.
    optVarDecay       :: !Double
  , -- | Base unit of conflicts per restart cycle: the @k@-th window allows
    -- @optRestartUnit * luby k@ conflicts before a restart.
    optRestartUnit    :: !Int
  , -- | Hard ceiling on the cumulative number of conflicts across the whole
    -- 'solveWith' call, tested once per resolved conflict; when reached, the
    -- search gives up and reports 'Unknown'. @0@ disables the budget.
    optConflictBudget :: !Int
  }

defaultSolverOptions :: SolverOptions
defaultSolverOptions = SolverOptions
  { optVarDecay       = 0.95
  , optRestartUnit    = 100
  , optConflictBudget = 0
  }

-- | State for 1-UIP conflict analysis and learnt clause minimisation.
data AnalysisState s = AnalysisState
  { -- | Number of seen literals at the current decision level still on the
    -- implication path (decremented by each resolution step).
    analysePathC      :: !( MutVar s Int )
  , -- | Transient per-variable marker tracking membership of the
    -- clause in progress, used by 1-UIP analysis and by learnt-clause
    -- minimisation.
    --
    -- Always @False@ outside of an 'analyse' call.
    seen              :: !( Growable Unboxed.MVector s Bit )
  , -- | Variable indices that 'analyse' has marked in 'seen'; walked to
    -- clear the markers at the end of the call.
    analyseTouched    :: !( Growable Primitive.MVector s Int )
  , -- | Literals at strictly lower decision levels collected during
    -- analysis; together with 'analyseOtherLevels' these form the body of
    -- the learnt clause (the asserting literal is prepended afterwards).
    analyseOtherLits  :: !( Growable Primitive.MVector s Lit )
  , -- | Levels matching 'analyseOtherLits' in lockstep, used to find the
    -- second-watch literal and the backjump level.
    analyseOtherLevels :: !( Growable Primitive.MVector s DecisionLevel )
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

-- | The clause database: long clause storage, learnt clauses, and the
-- per-literal watch lists.
data ClauseDB s = ClauseDB
  { -- | Storage for long clauses (size @>= 3@).
    clauseStore :: !( ClauseStore s )
  , -- | References of all learnt clauses.
    --
    -- Tracked separately from the input clauses so the two sets can be managed
    -- independently.
    learnts   :: !( Growable Primitive.MVector s ClauseRef )
  , -- | Per-literal watch lists, indexed by 'litIndex' and sized to
    -- @2 * numVars@.
    --
    -- @watches[p]@ holds every watcher whose clause has @negateLit p@ as a
    -- watched literal, so that enqueueing @p@ wakes those clauses.
    watches   :: !( Growable Boxed.MVector s ( Growable Primitive.MVector s Watcher ) )
  }

-- | Search statistics that the search logic depends on (restart scheduling).
--
-- Pure instrumentation lives in 'Schedule.Monitor.Monitor', not here.
data Statistics s = Statistics
  { -- | Total conflicts encountered.
    confCount :: !( MutVar s Int )
  , -- | Total decisions taken.
    decCount  :: !( MutVar s Int )
  }

-- | Variable assignments and related metadata.
data Assignments s =
  Assignments
   { -- | Variable assignments, indexed by 'varIndex'.
     assignments :: !( Growable Unboxed.MVector s Ł3 )
     -- | Polarity at which each variable was last assigned (used for phase
     -- saving on the next decision).
     --
     -- Defaults to 'Positive' for variables that have never been assigned.
   , phase     :: !( Growable Unboxed.MVector s Polarity )
     -- | Per-variable reason and decision level.
   , varData   :: !( VarData s )
   , -- | Whether each variable is a decision variable, i.e. eligible to be
     -- branched on by 'decide'. Indexed by 'varIndex'.
     decidable :: !( Growable Unboxed.MVector s Bit )
     -- | The assignment trail, with the per-level bookkeeping needed for backjumping.
   , trail     :: !( AssignmentTrail s )
   }

-- | Metadata about a variable assignment.
data VarData s = VarData
  { -- | Decision level at which each variable was assigned.
    level  :: !( Growable Unboxed.MVector s DecisionLevel )
  , -- | Reason for each variable's current assignment.
    reason :: !( Growable Primitive.MVector s Clause.Reason )
  }

-------------------------------------------------------------------------------
-- Construction.

newSolver :: PrimMonad m => m ( SolverState ( PrimState m ) )
newSolver = do
  solverAssignments <- newSolverAssignments
  varOrder          <- newVarOrder 0.95
  seenLit           <- Growable.new 32
  clauseDB          <- newClauseDB
  stats             <- newStatistics
  okFlag            <- newMutVar True
  analysisState     <- newAnalysisState
  pure $ SolverState { .. }

newSolverAssignments :: PrimMonad m => m ( Assignments ( PrimState m ) )
newSolverAssignments = do
  assignments <- Growable.new 16
  varData     <- newVarData
  phase       <- Growable.new 16
  decidable   <- Growable.new 16
  trail       <- newAssignmentTrail
  pure $ Assignments { .. }

-- | Allocate an empty clause database.
newClauseDB :: PrimMonad m => m ( ClauseDB ( PrimState m ) )
newClauseDB = do
  -- TODO: expose the clause-store capacity via 'SolverOptions'.
  clauseStore <- newClauseStore defaultStoreCapacityLits
  learnts     <- Growable.new 16
  watches     <- Growable.new 32
  pure $ ClauseDB { .. }
  where
    defaultStoreCapacityLits :: Int
    defaultStoreCapacityLits = ( 1024 * 1024 * 1024 ) `div` 8

-- | Allocate empty per-variable reason/level tables.
newVarData :: PrimMonad m => m ( VarData ( PrimState m ) )
newVarData = do
  level  <- Growable.new 16
  reason <- Growable.new 16
  pure $ VarData { .. }

-- | Allocate zeroed statistics counters.
newStatistics :: PrimMonad m => m ( Statistics ( PrimState m ) )
newStatistics = do
  confCount <- newMutVar 0
  decCount  <- newMutVar 0
  pure $ Statistics { .. }

-- | Allocate empty conflict-analysis scratch state. The buffers are reset at
-- the start of each 'analyse' call and grown on demand.
newAnalysisState :: PrimMonad m => m ( AnalysisState ( PrimState m ) )
newAnalysisState = do
  analysePathC      <- newMutVar 0
  seen              <- Growable.new 16
  analyseTouched    <- Growable.new 32
  analyseOtherLits  <- Growable.new 16
  analyseOtherLevels<- Growable.new 16
  minFailed         <- Growable.new 16
  minFailedTouched  <- Growable.new 16
  pure $ AnalysisState { .. }

numVariables :: PrimMonad m => Assignments ( PrimState m ) -> m Int
numVariables assig = Growable.length ( assignments assig )

-- | Add the current bump increment to a variable's activity and re-percolate
-- it up the heap if it is currently a member.
bumpVarActivity :: PrimMonad m => SolverState ( PrimState m ) -> Var -> m ()
bumpVarActivity s = VarOrder.bumpActivity ( varOrder s )

-- | Allocate a fresh decision variable.
newVar :: PrimMonad m => SolverState ( PrimState m ) -> m Var
newVar s = newVarWith s True

-- | Allocate a fresh auxiliary (non-decision) variable.
newAuxVar :: PrimMonad m => SolverState ( PrimState m ) -> m Var
newAuxVar s = newVarWith s False

-- | Shared allocator for 'newVar'/'newAuxVar'.
newVarWith :: PrimMonad m => SolverState ( PrimState m ) -> Bool -> m Var
newVarWith
  ( SolverState
    { solverAssignments =
        Assignments
          { assignments
          , varData
          , phase
          , decidable
          }
    , seenLit
    , varOrder
    , clauseDB
    , analysisState
    } )
  isDecisionVar = do
  v <- ( if isDecisionVar then VarOrder.insertVar else VarOrder.insertAuxVar )
         varOrder
  Growable.push assignments                 ŁUndef
  Growable.push ( level  varData )          UnassignedLevel
  Growable.push ( reason varData )          Clause.RDecision
  Growable.push phase                       Positive
  Growable.push decidable                   ( Bit isDecisionVar )
  Growable.push ( seen analysisState )      ( Bit False )
  Growable.push ( minFailed analysisState ) ( Bit False )
  -- Two seenLit slots per variable (one per polarity).
  Growable.push seenLit                     ( Bit False )
  Growable.push seenLit                     ( Bit False )
  -- Two fresh empty watch lists per variable (one for each polarity).
  posWs <- Growable.new initialWatchListCapacity
  negWs <- Growable.new initialWatchListCapacity
  Growable.push ( watches clauseDB ) posWs
  Growable.push ( watches clauseDB ) negWs
  pure v
  where
    initialWatchListCapacity :: Int
    initialWatchListCapacity = 4

-------------------------------------------------------------------------------
-- Lookups.

-- | The value currently assigned to the given variable.
valueOf
  :: PrimMonad m
  => Assignments ( PrimState m ) -> Var -> m Ł3
valueOf assig v = Growable.read ( assignments assig ) ( varIndex v )

-- | The value currently assigned to the given literal.
litValue
  :: PrimMonad m
  => Assignments ( PrimState m ) -> Lit -> m Ł3
litValue s l = litValueFromVarValue l <$> valueOf s ( litVar l )

-- | The decision level we are currently exploring.
currentLevel :: PrimMonad m => Assignments ( PrimState m ) -> m DecisionLevel
currentLevel assigs =
  DecisionLevel <$> Growable.length ( levelStarts ( trail assigs ) )

-- | The decision level at which the given variable was assigned.
--
-- Precondition: the variable must currently be assigned.
levelOfAssignedVar
  :: PrimMonad m
  => Assignments ( PrimState m ) -> Var -> m DecisionLevel
levelOfAssignedVar assig v = do
  lvl <- Growable.read ( level $ varData assig ) ( varIndex v )
#ifdef DEBUG
  case lvl of
    UnassignedLevel -> do
      dump <- dumpAssignments assig
      error $ "SAT.Solver.levelOfAssignedVar: unassigned variable "
           ++ show v ++ "\n" ++ dump
    _ -> pure ()
#endif
  return lvl

-- | Render a snapshot of the trail (lits, levels, reasons) and the
-- current decision-level stack, for inclusion in panic messages.
dumpAssignments
  :: forall m
  .  PrimMonad m
  => Assignments ( PrimState m ) -> m String
dumpAssignments assigs@( Assignments { trail } ) = do
  TrailPos sz       <- trailSize assigs
  DecisionLevel cur <- currentLevel assigs
  nLim              <- Growable.length ( levelStarts trail )
  let
    readLim :: Int32 -> m Int32
    readLim k = do
      LevelStart { levelTrailPos = TrailPos p }
        <- Growable.read ( levelStarts trail ) ( fromIntegral k )
      pure p
    showLits :: Int32 -> m [ String ]
    showLits k
      | k >= sz   = pure []
      | otherwise = do
          l   <- Growable.read ( entries trail ) ( fromIntegral k )
          lvl <- Growable.read ( level  $ varData assigs ) ( varIndex ( litVar l ) )
          rsn <- Growable.read ( reason $ varData assigs ) ( varIndex ( litVar l ) )
          val <- Growable.read ( assignments assigs ) ( varIndex ( litVar l ) )
          rest <- showLits ( k + 1 )
          pure ( ( "  [" ++ show k ++ "] " ++ show l
                 ++ "  lvl=" ++ ( case lvl of UnassignedLevel -> "UNASSIGNED"; DecisionLevel d -> show d )
                 ++ "  assign=" ++ show val
                 ++ "  reason=" ++ showReason rsn ) : rest )
    limLine :: Int32 -> m [ String ]
    limLine k
      | fromIntegral k >= nLim = pure []
      | otherwise = do
          p <- readLim k
          rest <- limLine ( k + 1 )
          pure ( ( show ( k + 1 ) ++ "->" ++ show p ) : rest )
  trailLines <- showLits 0
  lims       <- limLine 0
  pure $ "  trailSize=" ++ show sz ++ " currentLevel=" ++ show cur
      ++ "  levelStarts=[" ++ intercalate "," lims ++ "]\n"
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
  => SolverState ( PrimState m ) -> Conflict -> m String
describeConflict s = \case
    ConflictClause cref -> do
      c <- clauseAt ( clauseDB s ) ( falsifiedClause cref )
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
      d1 <- describeLit ( underlyingLit l1 )
      d2 <- describeLit ( underlyingLit l2 )
      pure $ "ConflictBinary:\n" ++ unlines [ d1, d2 ]
  where
    describeLit :: Lit -> m String
    describeLit l = do
      let i = varIndex ( litVar l )
      val <- Growable.read ( assignments $ solverAssignments s ) i
      lvl <- Growable.read ( level  $ varData $ solverAssignments s ) i
      rsn <- Growable.read ( reason $ varData $ solverAssignments s ) i
      pure $ "    " ++ show l
          ++ "  assign=" ++ show val
          ++ "  lvl=" ++ ( case lvl of UnassignedLevel -> "UNASSIGNED"; DecisionLevel d -> show d )
          ++ "  reason=" ++ showReason rsn

trailSize :: PrimMonad m => Assignments ( PrimState m ) -> m TrailPos
trailSize assigs = TrailPos . fromIntegral
               <$> Growable.length ( entries $ trail assigs )

numConflicts, numDecisions :: PrimMonad m => SolverState ( PrimState m ) -> m Int
numConflicts = readMutVar . confCount . stats
numDecisions = readMutVar . decCount . stats

numLearnts :: PrimMonad m => SolverState ( PrimState m ) -> m Int
numLearnts = Growable.length . learnts . clauseDB

-- | Look up a clause by its reference. Precondition: the reference came
-- from a previous 'recordClause' on this database.
--
-- This is a thin wrapper around 'Clause.clauseAt' that drops the
-- 'clauseStore' indirection at call sites.
clauseAt
  :: PrimMonad m
  => ClauseDB ( PrimState m ) -> ClauseRef -> m ( Clause ( PrimState m ) )
clauseAt cdb = Clause.clauseAt ( clauseStore cdb )

-- | Build a fresh long clause in the store and return both its reference
-- and a view over it. Does not attach watches.
recordClause
  :: PrimMonad m
  => ClauseDB ( PrimState m ) -> Bool -> [ Lit ] -> m ( ClauseRef, Clause ( PrimState m ) )
recordClause cdb learnt ls = do
  ref <- ( if learnt then Clause.recordLearntClause else Clause.recordClause )
           ( clauseStore cdb ) ls
  c <- Clause.clauseAt ( clauseStore cdb ) ref
  pure ( ref, c )

-------------------------------------------------------------------------------
-- Assignment.

-- | Internal helper: write a variable's value, level, and reason, and
-- append the literal to the trail.
performAssignment
  :: PrimMonad m
  => Assignments ( PrimState m ) -> Lit -> Clause.Reason -> m ()
performAssignment assig l rsn = do
  let
    l_idx = varIndex ( litVar l )
    val  = polarityValue ( litPolarity l )
  lvl <- currentLevel assig
  Growable.write ( assignments assig ) l_idx val
  Growable.write ( level  $ varData assig ) l_idx lvl
  Growable.write ( reason $ varData assig ) l_idx rsn
  Growable.push  ( entries ( trail assig ) ) l

-- | Assign a literal at the current decision level.
--
-- Precondition: the literal's variable is currently unassigned.
enqueueUndef
  :: PrimMonad m
  => Assignments ( PrimState m ) -> Lit -> Clause.Reason -> m ()
enqueueUndef assig l rsn = do
  cur <- valueOf assig ( litVar l )
  case cur of
    ŁUndef -> performAssignment assig l rsn
    _      -> do
      lvl     <- currentLevel assig
      vlvl    <- levelOfAssignedVar assig ( litVar l )
      oldRsn  <- Growable.read ( reason $ varData assig ) ( varIndex ( litVar l ) )
      error $ unlines
        [ "SAT.Solver.enqueueUndef: variable already assigned"
        , "  literal:            " <> show l
        , "  variable:           " <> show ( litVar l )
        , "  current value:      " <> show cur
        , "  assigned at level:  " <> show vlvl <> " (existing reason: " <> describeReason oldRsn <> ")"
        , "  current level:      " <> show lvl
        , "  attempted reason:   " <> describeReason rsn
        ]
  where
    describeReason :: Clause.Reason -> String
    describeReason = \case
      Clause.RFact     -> "RFact"
      Clause.RDecision -> "RDecision"
      Clause.RBinary o -> "RBinary " <> show o
      Clause.RClause _ -> "RClause"
      Clause.RLazy r   -> "RLazy " <> show r

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
  => Assignments ( PrimState m ) -> Lit -> Clause.Reason -> m Bool
tryEnqueue assig l rsn = do
  let val = polarityValue ( litPolarity l )
  cur <- valueOf assig ( litVar l )
  case cur of
    ŁUndef -> performAssignment assig l rsn *> pure True
    _      -> pure ( cur == val )

-------------------------------------------------------------------------------
-- Clause attachment and input.

-- | Register @watcher@ on the /watched literal/ @watched@, so the watcher fires
-- when @watched@ is falsified.
pushWatcher
  :: PrimMonad m
  => ClauseDB ( PrimState m )
  -> Lit -- ^ literal to watch; watcher fires when this literal is falsified
  -> Watcher
  -> m ()
pushWatcher cdb watched w = do
  -- We want to watch the literal being falsified, so the trigger to wake-up
  -- is when the negated literal is assigned true.
  let trigger = negateLit watched
  inner <- Growable.read ( watches cdb ) ( fromIntegral $ litIndex trigger )
  Growable.push inner w

-- | Register a binary clause @[l, m]@ inline on both watch lists. No
-- 'Clause' is allocated; the pair of watcher entries IS the clause.
attachBinary
  :: PrimMonad m
  => ClauseDB ( PrimState m ) -> Lit -> Lit -> m ()
attachBinary cdb l m = do
  pushWatcher cdb l ( WBinary m )
  pushWatcher cdb m ( WBinary l )

-- | Register a long clause (size @>= 3@) on the watch lists of its first
-- two literals, using the other watched literal as the blocker hint.
attachLong
  :: PrimMonad m
  => ClauseDB ( PrimState m ) -> ClauseRef -> Clause ( PrimState m ) -> m ()
attachLong cdb cref c
  | clauseSize c < 3
  = error $ "attachLong: expected clause of size >= 3, got " ++ show ( clauseSize c )
  | otherwise = do
      l0 <- clauseLit c 0
      l1 <- clauseLit c 1
      pushWatcher cdb l0 ( WLong cref l1 )
      pushWatcher cdb l1 ( WLong cref l0 )

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

-- | Post an input clause to the solver, at the ground level.
--
-- Duplicate literals and clauses already satisfied by level-0 facts are
-- normalised away.
addClause
  :: PrimMonad m
  => SolverState ( PrimState m ) -> [ Lit ] -> m PostResult
addClause s@( SolverState { solverAssignments = assig }) ls0 = do
  ok <- readMutVar ( okFlag s )
  if not ok then pure InstantUnsat
  else do
    mb <- preprocessClause s ls0
    case mb of
      Nothing -> pure Tautology
      Just [] -> markFalse s >> pure InstantUnsat
      Just [ l ] -> do
        e <- tryEnqueue assig l Clause.RFact
        if e
        then do
          conf <- propagate s
          case conf of
            Just _  -> markFalse s >> pure InstantUnsat
            Nothing -> pure Posted
        else markFalse s >> pure InstantUnsat
      Just [ l, m ] -> do
        attachBinary ( clauseDB s ) l m
        pure Posted
      Just ls -> do
        ( cref, c ) <- recordClause ( clauseDB s ) False ls
        attachLong ( clauseDB s ) cref c
        pure Posted

-- | Attach a binary clause @[l, m]@ to the watch lists mid-search, /without/
-- the unit-collapse and level-0 normalisation of 'addClause'.
--
-- Precondition: the clause is not already /falsified/ (both literals false),
-- since such a clause would be attached without its conflict being detected.
addBinaryLemma
  :: PrimMonad m
  => SolverState ( PrimState m ) -> Lit -> Lit -> m ()
addBinaryLemma s@( SolverState { solverAssignments = assig }) l m = do
#ifdef DEBUG
  -- Check precondition: the clause is not already falsified.
  dbg_val_l <- litValue assig l
  dbg_val_m <- litValue assig m
  if
    | ŁFalse <- dbg_val_l
    , ŁFalse <- dbg_val_m
    ->
     error $ unlines
       [ "addBinaryLemma: clause already falsified"
       , show l ++ " = " ++ show dbg_val_l
       , show m ++ " = " ++ show dbg_val_m
       ]
    | otherwise
    -> return ()
#endif
  ok <- readMutVar ( okFlag s )
  when ok $ do
    -- Attach the clause.
    attachBinary ( clauseDB s ) l m

    -- If the clause is already unit, propagate immediately.
    val_l <- litValue assig l
    val_m <- litValue assig m
    case (val_l, val_m) of
      -- 'RBinary' carries the clause's /other/ literal (false here), as in
      -- 'installLearnt' and as consumed by 'walkUIP'.
      (ŁFalse, ŁUndef) -> enqueueUndef assig m $ Clause.RBinary ( FalsifiedLit l )
      (ŁUndef, ŁFalse) -> enqueueUndef assig l $ Clause.RBinary ( FalsifiedLit m )
      _                -> pure ()

markFalse :: PrimMonad m => SolverState ( PrimState m ) -> m ()
markFalse s = writeMutVar ( okFlag s ) False

-- | Normalise an input clause: drop duplicate literals, detect tautology,
-- drop literals already known false at level @0@, and report 'Nothing' if
-- any literal is already true at level @0@ (so the clause is trivially
-- satisfied).
preprocessClause
  :: forall m
  .  PrimMonad m
  => SolverState ( PrimState m )
  -> [ Lit ]
  -> m ( Maybe [ Lit ] )
preprocessClause s@( SolverState { solverAssignments = assig }) ls0 = do
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
          v <- valueOf assig ( litVar l )
          let keepIt = do
                Growable.write ( seenLit s ) li ( Bit True )
                go ( l : keep ) rest
          case litValueFromVarValue l v of
            ŁUndef -> keepIt
            here -> do
              atGround <- ( GroundLevel == ) <$> levelOfAssignedVar assig ( litVar l )
              case ( here, atGround ) of
                ( ŁTrue,  True ) -> pure Nothing
                ( ŁFalse, True ) -> go keep rest
                _                -> keepIt

-------------------------------------------------------------------------------
-- Boolean Constraint Propagation.

-- | Run BCP from the current trail tail until either no further propagation
-- is possible or a falsified clause is encountered.
propagate
  :: forall m
  .  PrimMonad m
  => SolverState ( PrimState m ) -> m ( Maybe Conflict )
propagate s@( SolverState { solverAssignments = assig@( Assignments { trail } ) } ) = loop
  where
    loop :: m ( Maybe Conflict )
    loop = do
      q  <- readMutVar ( trailHead trail )
      sz <- trailSize assig
      if q >= sz
      then pure Nothing
      else do
        p <- Growable.read ( entries trail ) ( fromIntegral $ unTrailPos q )
        writeMutVar ( trailHead trail ) ( q + 1 )
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
  => SolverState ( PrimState m )
  -> Lit -- ^ the literal we have just assigned to be true
  -> m ( Maybe Conflict )
propagateLit s@( SolverState { solverAssignments = assig }) p = do
  ws <- Growable.read ( watches ( clauseDB s ) ) ( litIndex p )
  total <- Growable.length ws
  loop ws total 0 0
  where
    falseLit :: FalsifiedLit
    falseLit = FalsifiedLit $ negateLit p

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
              v <- litValue assig other
              Growable.write ws wi w
              case v of
                ŁTrue  -> loop ws total ( ri + 1 ) ( wi + 1 )
                ŁUndef -> do
                  -- 'RBinary' carries the clause's other (false) literal, here
                  -- the just-falsified watched literal 'falseLit'.
                  enqueueUndef assig other ( Clause.RBinary falseLit )
                  loop ws total ( ri + 1 ) ( wi + 1 )
                ŁFalse -> do
                  -- Restore unprocessed remainder so the watch invariant
                  -- holds when the search later backjumps and re-runs BCP.
                  compactRest ws total ( ri + 1 ) ( wi + 1 )
                  pure $ Just $ ConflictBinary falseLit ( FalsifiedLit other )
            WLong cref blocker -> do
              -- Try the blocker shortcut before fetching the clause.
              bv <- litValue assig blocker
              if bv == ŁTrue
              then do
                Growable.write ws wi w
                loop ws total ( ri + 1 ) ( wi + 1 )
              else do
                c <- clauseAt ( clauseDB s ) cref
                r <- handleWatched s cref falseLit c
                case r of
                  WatchReplaced -> loop ws total ( ri + 1 ) wi
                  WatchKept newBlocker -> do
                    Growable.write ws wi ( WLong cref newBlocker )
                    loop ws total ( ri + 1 ) ( wi + 1 )
                  WatchConflict newBlocker -> do
                    Growable.write ws wi ( WLong cref newBlocker )
                    compactRest ws total ( ri + 1 ) ( wi + 1 )
                    pure $ Just $ ConflictClause ( FalsifiedClauseRef cref )

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
  => SolverState ( PrimState m )
  -> ClauseRef        -- ^ reference to the same clause; used for the new watch and the reason
  -> FalsifiedLit     -- ^ the watched literal that just became false
  -> Clause ( PrimState m )
  -> m WatchOutcome
handleWatched s@( SolverState { solverAssignments = assig })
  cref ( FalsifiedLit falseLit ) c = do
    -- Normalise so 'falseLit' sits at position 1 and the other watched
    -- literal at position 0.
    c0 <- clauseLit c 0
    when ( c0 == falseLit ) ( clauseSwap c 0 1 )
    other  <- clauseLit c 0
    otherV <- litValue assig other
    case otherV of
      ŁTrue -> pure ( WatchKept other )
      _ -> do
        mb <- findNonFalseFrom assig c 2
        case mb of
          Just ( i, newWatched ) -> do
            clauseSwap c 1 i
            -- The clause now watches 'other' at position 0 and 'newWatched'
            -- at position 1. Register it on the new watch list with 'other'
            -- as the blocker.
            pushWatcher ( clauseDB s ) newWatched ( WLong cref other )
            pure WatchReplaced
          Nothing ->
            case otherV of
              ŁFalse -> pure ( WatchConflict other )
              ŁUndef -> do
                enqueueUndef assig other ( Clause.RClause cref )
                pure ( WatchKept other )

-- | Scan a clause from position @start@ onwards for the first literal that
-- is not currently false, returning its position and value.
findNonFalseFrom
  :: forall m
  .  PrimMonad m
  => Assignments ( PrimState m )
  -> Clause ( PrimState m )
  -> Int
  -> m ( Maybe ( Int, Lit ) )
findNonFalseFrom assig c start = go start
  where
    n :: Int
    n = clauseSize c
    go :: Int -> m ( Maybe ( Int, Lit ) )
    go !j
      | j >= n = pure Nothing
      | otherwise = do
          l <- clauseLit c j
          v <- litValue assig l
          if v == ŁFalse
          then go ( j + 1 )
          else pure ( Just ( j, l ) )

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
  => SolverState ( PrimState m )
  -> Conflict
  -> m ( [ Lit ], DecisionLevel )
analyse s@( SolverState { solverAssignments = assig } ) conflict0 = do
  curLevel <- currentLevel assig
  let
    AnalysisState
      { analysePathC
      , seen
      , analyseTouched
      , analyseOtherLits
      , analyseOtherLevels
      } = analysisState s
  -- Reset the per-call scratch buffers. They are owned by the solver, so
  -- 'analyse' never needs to allocate fresh accumulators.
  writeMutVar analysePathC 0
  Growable.truncate analyseTouched     0
  Growable.truncate analyseOtherLits   0
  Growable.truncate analyseOtherLevels 0
  let
    -- Mark a variable as seen and remember it for batch-clearance.
    markSeen :: Int -> m ()
    markSeen i = do
      Growable.write seen i ( Bit True )
      Growable.push analyseTouched i

    -- Process a single literal during analysis, skipping the resolution
    -- variable @skipVi@ (@-1@ on the very first pass). Each
    -- previously-unseen literal at a non-zero level is either tallied on
    -- the path counter (if at the current level) or pushed onto the
    -- learnt-clause scratch buffers (if at a strictly lower level).
    visitLit :: Int -> FalsifiedLit -> m ()
    visitLit skip ( FalsifiedLit l ) = do
      let i = varIndex ( litVar l )
      Bit marker <- Growable.read seen i
      if marker || i == skip
      then pure ()
      else do
#ifdef DEBUG
        -- Check that 'l' is indeed false on the current trail.
        lv <- litValue assig l
        when ( lv /= ŁFalse ) $ do
          dump <- dumpAssignments assig
          error $ unlines
            [ "Non-false learnt clause literal " <> show lv
            , dump
            ]
#endif
        lvl <- levelOfAssignedVar assig ( litVar l )
        if lvl <= GroundLevel
        then pure ()
        else do
          VarOrder.bumpActivity ( varOrder s ) ( Var $ fromIntegral i )
          markSeen i
          if lvl >= curLevel
          then modifyMutVar' analysePathC ( + 1 )
          else do
            Growable.push analyseOtherLits   l
            Growable.push analyseOtherLevels lvl

    -- Walk a long-clause reason, deferring per-literal work to 'visitLit'.
    visit :: Int -> Clause ( PrimState m ) -> m ()
    visit skipVi c = do
      let n = clauseSize c
          loopK !k
            | k >= n = pure ()
            | otherwise = do
                l <- clauseLit c k
                visitLit skipVi ( FalsifiedLit l )
                loopK ( k + 1 )
      loopK 0

  -- Seed analysis from the conflict source.
  case conflict0 of
    ConflictClause cref -> do
      c <- clauseAt ( clauseDB s ) ( falsifiedClause cref )
      visit -1 c
    ConflictBinary l1 l2 -> do
      visitLit -1 l1
      visitLit -1 l2

#ifdef DEBUG
  -- BCP only fires this analysis when the conflict was produced at the
  -- current level, so the conflict source must mention at least one
  -- literal at 'curLevel'. Failing this points at a BCP / level-bookkeeping
  -- bug; panic loudly rather than walking the trail past its head.
  postVisitPC <- readMutVar analysePathC
  when ( postVisitPC == 0 ) $ do
    conflictDesc <- describeConflict s conflict0
    stateDump    <- dumpAssignments assig
    error $ unlines
      [ "SAT.Solver.analyse: conflict at level > 0 has no current-level literals."
      , "  currentLevel=" ++ show ( unDecisionLevel curLevel )
      , "  conflict source:"
      , conflictDesc
      , stateDump
      ]
#endif

  initTrail <- trailSize assig
  uipLit <- walkUIP s visit visitLit ( initTrail - 1 )

  -- Drop self-subsumed body literals while 'seen' still marks the body.
  minimiseLearnt
    ( solverAssignments s )
    ( clauseDB s )
    ( analysisState s )

  let asserting = negateLit uipLit

  -- Strengthen the body further by subsumption resolution against binary
  -- clauses (independent of 'seen', so order versus the clearance below is
  -- immaterial).
  binarySubsume s asserting

  -- Clear the 'seen' bits we set during this analysis (including variables
  -- 'minimiseLearnt' additionally marked while memoising proven-redundant ones).
  do
    touchedN <- Growable.length analyseTouched
    let clearLoop !i
          | i >= touchedN = pure ()
          | otherwise = do
              var_index <- Growable.read analyseTouched i
              Growable.write seen var_index ( Bit False )
              clearLoop ( i + 1 )
    clearLoop 0

  ( mbSecond, restLits, bjLevel ) <-
    pickSecondWatch analyseOtherLits analyseOtherLevels
  let learnt = case mbSecond of
        Nothing    -> [ asserting ]
        Just secnd -> asserting : secnd : restLits
  pure ( learnt, bjLevel )

-- | Recursive learnt-clause minimisation (Sörensson & Biere, 2009).
--
-- A body literal of a learnt clause is redundant when its negation is already
-- implied by the rest of the clause.
--
-- Precondition: 'seen' is set exactly for the body-literal variables (the state
-- 'walkUIP' leaves behind). A variable proven redundant is additionally marked
-- 'seen' (memoising success — harmlessly extending clause membership for the
-- recursive check) and appended to 'analyzeTouched' so the caller clears it; a
-- variable proven irredundant is marked 'minFailed', cleared before returning.
minimiseLearnt
  :: forall m
  .  PrimMonad m
  => Assignments ( PrimState m )
  -> ClauseDB ( PrimState m )
  -> AnalysisState ( PrimState m )
  -> m ()
minimiseLearnt assig clauseDB
  ( AnalysisState
      { analyseOtherLits
      , analyseOtherLevels
      , analyseTouched
      , seen
      , minFailed
      , minFailedTouched
      }
  ) = do
  Growable.truncate minFailedTouched  0
  n <- Growable.length analyseOtherLits
  -- The set of decision levels present in the body, hashed into a 64-bit mask
  -- ('hashDecisionLevel'). A literal can only be self-subsumed if every other
  -- literal of its reason resolves into a level already in the clause; a reason
  -- literal whose level is absent from this mask is therefore not coverable, and
  -- the redundancy check fails fast without forcing the (possibly large)
  -- reason. (MiniSat's abstraction-levels optimisation; conservative under hash
  -- collisions, never unsound.)
  abstraction <- collectAbstraction n
  let
    -- Walk the body buffer, dropping redundant literals and compacting both
    -- buffers in lockstep (read index @ri@, write index @wi@).
    compact :: Int -> Int -> m ()
    compact !ri !wi
      | ri >= n = do
          Growable.truncate analyseOtherLits   wi
          Growable.truncate analyseOtherLevels wi
      | otherwise = do
          l   <- Growable.read analyseOtherLits ri
          red <- reasonRedundant abstraction ( varIndex ( litVar l ) )
          if red
          then compact ( ri + 1 ) wi
          else do
            when ( wi /= ri ) do
              lvl <- Growable.read analyseOtherLevels  ri
              Growable.write analyseOtherLits   wi l
              Growable.write analyseOtherLevels wi lvl
            compact ( ri + 1 ) ( wi + 1 )
  compact 0 0
  clearFailed
  where
    -- OR together the abstraction bits of every body literal's level.
    collectAbstraction :: Int -> m Word64
    collectAbstraction n = go 0 0
      where
        go :: Int -> Word64 -> m Word64
        go !j !acc
          | j >= n    = pure acc
          | otherwise = do
              lvl <- Growable.read analyseOtherLevels j
              go ( j + 1 ) ( acc .|. hashDecisionLevel lvl )

    -- A variable's assignment is self-subsumed iff its reason exists and every
    -- /other/ literal of that reason is covered. A decision (no reason) is not.
    reasonRedundant :: Word64 -> Int -> m Bool
    reasonRedundant abstraction i = do
      rsn <- Growable.read ( reason $ varData assig ) i
      case rsn of
        Clause.RDecision     -> pure False
        Clause.RFact         -> pure True   -- a ground fact is unconditionally true
        Clause.RBinary other -> covered abstraction other
        Clause.RClause cref  -> clauseOthersCovered abstraction cref i
        Clause.RLazy lref    ->
          -- NB: we don't force lazy reasons just for the purpose of minimisation.
          do { lazyReason <- getLazyReason ( trail assig ) lref
             ; case lazyReason of
                Clause.LazyReason {} -> pure False
                Clause.AlreadyForcedReason others ->
                  othersCovered abstraction i $ map FalsifiedLit others
             }

    -- Whether reason-literal @q@ is covered: at the ground level, already a
    -- clause (or proven-redundant) variable, or recursively self-subsumed.
    -- Memoises both outcomes (success via 'seen', failure via 'minFailed'). A
    -- literal whose level is absent from the clause's @abstraction@ mask cannot
    -- be covered, so it fails fast without forcing its reason.
    covered :: Word64 -> FalsifiedLit -> m Bool
    covered abstraction ( FalsifiedLit q ) = do
      let vq = varIndex ( litVar q )
      lvl <- levelOfAssignedVar assig ( litVar q )
      if lvl <= GroundLevel
      then pure True
      else do
        Bit isSeen <- Growable.read seen vq
        if isSeen
        then pure True
        else do
          Bit isFailed <- Growable.read minFailed vq
          if isFailed
          then pure False
          else
            if hashDecisionLevel lvl .&. abstraction == 0
            then markFailed vq
            else do
              ok <- reasonRedundant abstraction vq
              if ok
              then do
                Growable.write seen vq ( Bit True )
                Growable.push  analyseTouched vq
                pure True
              else
                markFailed vq

    markFailed :: Int -> m Bool
    markFailed vq = do
      Growable.write minFailed vq ( Bit True )
      Growable.push  minFailedTouched vq
      pure False

    -- Every literal of the reason clause other than the resolved variable.
    clauseOthersCovered :: Word64 -> ClauseRef -> Int -> m Bool
    clauseOthersCovered abstraction cref resolved_var_idx = do
      c <- clauseAt clauseDB cref
      let
        sz = clauseSize c
        go :: Int -> m Bool
        go !k
          | k >= sz   = pure True
          | otherwise = do
              l <- clauseLit c k
              if varIndex ( litVar l ) == resolved_var_idx
              then go ( k + 1 )
              else do
                cov <- covered abstraction ( FalsifiedLit l )
                if cov then go ( k + 1 ) else pure False
      go 0

    othersCovered :: Word64 -> Int -> [ LitOfValue False ] -> m Bool
    othersCovered abstraction i = go
      where
        go :: [ LitOfValue False ] -> m Bool
        go [] = pure True
        go ( l : ls )
          | varIndex ( litVar $ underlyingLit l ) == i
          = go ls
          | otherwise
          = do
              cov <- covered abstraction l
              if cov
              then go ls
              else pure False

    clearFailed :: m ()
    clearFailed = do
      k <- Growable.length minFailedTouched
      let
        loop :: Int -> m ()
        loop !i
          | i >= k = pure ()
          | otherwise = do
              var_idx <- Growable.read minFailedTouched i
              Growable.write minFailed var_idx ( Bit False )
              loop ( i + 1 )
      loop 0

-- | Subsumption resolution against binary clauses (\"binary self-subsumption\").
--
-- A body literal @l@ of the learnt clause is dropped whenever the clause
-- database holds a binary clause @¬l ∨ q@ with @q@ also in the learnt clause:
-- resolving the two on @l@ yields the learnt clause minus @l@, which subsumes
-- the original.
--
-- Precondition: every learnt-clause literal is currently assigned false (the
-- post-analysis state), though only literal /identity/, not value, is used.
binarySubsume
  :: forall m
  .  PrimMonad m
  => SolverState ( PrimState m )
  -> Lit -- ^ asserting literal: kept, but eligible as a surviving witness
  -> m ()
binarySubsume s asserting = do
  let
    AnalysisState { analyseOtherLits, analyseOtherLevels } = analysisState s
    seenL = seenLit s
    ws    = watches ( clauseDB s )
  n <- Growable.length analyseOtherLits
  -- Mark every literal of the learnt clause (asserting literal + body).
  Growable.write seenL ( litIndex asserting ) ( Bit True )
  let
    markBody :: Int -> m ()
    markBody !i
      | i >= n    = pure ()
      | otherwise = do
          l <- Growable.read analyseOtherLits i
          Growable.write seenL ( litIndex l ) ( Bit True )
          markBody ( i + 1 )
  markBody 0

  let
    -- Whether some binary clause @¬l ∨ q@ has @q@ a current clause member
    -- (other than @l@ itself, which would be the tautology @¬l ∨ l@). The
    -- watch list @watches[litIndex l]@ holds a 'WBinary' @q@ for exactly the
    -- binary clauses @¬l ∨ q@ (see 'attachBinary' / 'pushWatcher').
    subsumed :: Lit -> m Bool
    subsumed l = do
      wl <- Growable.read ws ( litIndex l )
      m  <- Growable.length wl
      let
        scan :: Int -> m Bool
        scan !k
          | k >= m    = pure False
          | otherwise = do
              w <- Growable.read wl k
              case w of
                WLong {} -> scan ( k + 1 )
                WBinary q
                  | litIndex q == litIndex l -> scan ( k + 1 )
                  | otherwise -> do
                      Bit member <- Growable.read seenL ( litIndex q )
                      if member
                      then pure True
                      else scan ( k + 1 )
      scan 0

    -- Walk the body, dropping subsumed literals and compacting both buffers in
    -- lockstep (read index @ri@, write index @wi@), mirroring 'minimiseLearnt'.
    compact :: Int -> Int -> m ()
    compact !ri !wi
      | ri >= n = do
          Growable.truncate analyseOtherLits   wi
          Growable.truncate analyseOtherLevels wi
      | otherwise = do
          l       <- Growable.read analyseOtherLits ri
          dropLit <- subsumed l
          if dropLit
          then do
            -- Unmark @l@ so it cannot in turn justify dropping another literal:
            -- guards against an @l ≡ q@ pair (both @¬l ∨ q@ and @¬q ∨ l@ present)
            -- eliminating both literals, which would be unsound.
            Growable.write seenL ( litIndex l ) ( Bit False )
            compact ( ri + 1 ) wi
          else do
            when ( wi /= ri ) do
              lvl <- Growable.read analyseOtherLevels ri
              Growable.write analyseOtherLits   wi l
              Growable.write analyseOtherLevels wi lvl
            compact ( ri + 1 ) ( wi + 1 )
  compact 0 0

  -- Clear the membership marks: the asserting literal plus every surviving body
  -- literal (dropped ones were unmarked above), restoring 'seenLit' to all-False.
  Growable.write seenL ( litIndex asserting ) ( Bit False )
  finalN <- Growable.length analyseOtherLits
  let
    clearMarks :: Int -> m ()
    clearMarks !i
      | i >= finalN = pure ()
      | otherwise = do
          l <- Growable.read analyseOtherLits i
          Growable.write seenL ( litIndex l ) ( Bit False )
          clearMarks ( i + 1 )
  clearMarks 0

{- Note [Citability invariant]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
A lazy reason ('Clause.RLazy') is a deferred clause @propLit ∨ ¬a₁ ∨ … ∨ ¬aₙ@:
the propagated literal together with the negations of the /antecedents/ @aᵢ@
that forced it. Whoever produces the reason must maintain:

  /citability invariant/
    every antecedent is true on the trail at the moment the reason is forced

1-UIP relies on this invariant: when it resolves the conflict backwards through
a reason (see walkUIP), it reads the decision level each antecedent was assigned
at, until it reaches an antecedent assigned at an earlier decision level,
placing it into the learnt clause.
An antecedent not on the trail has no level ('levelOfAssignedVar' fails), so
the resolution is ill-defined and the learnt clause unsound.

A reason is forced only during conflict analysis, so the invariant need hold
only then, not when the reason is built.
-}

-- | Walk backwards along the trail at the current level, popping seen
-- variables and resolving against their reason clauses, until a single
-- current-level literal remains. That literal is the 1-UIP.
walkUIP
  :: forall m
  .  PrimMonad m
  => SolverState ( PrimState m )
  -> ( Int -> Clause ( PrimState m ) -> m () )
  -> ( Int -> FalsifiedLit -> m () )
  -> TrailPos
  -> m Lit
walkUIP
  ( SolverState
      { analysisState = AnalysisState { analysePathC, seen }
      , solverAssignments = Assignments { trail, varData }
      , clauseDB
      }
    )
  visit visitLit
  ( TrailPos start ) = go start
  where
    go :: Int32 -> m Lit
    go !idx
      | idx < 0 = error "SAT.Solver.analyse: trail underflow during UIP scan"
      | otherwise = do
          lit <- Growable.read ( entries trail ) ( fromIntegral idx )
          let lit_idx = varIndex ( litVar lit )
          Bit marker <- Growable.read seen lit_idx
          if not marker
          then go ( idx - 1 )
          else do
            modifyMutVar' analysePathC ( subtract 1 )
            Growable.write seen lit_idx ( Bit False )
            pc <- readMutVar analysePathC
            if pc == 0
            then pure lit
            else do
              rsn <- Growable.read ( reason varData ) lit_idx
              case rsn of
                Clause.RDecision ->
                  error "SAT.Solver.analyse: decision encountered before UIP"
                Clause.RFact ->
                  error "SAT.Solver.analyse: ground-level fact reached during UIP scan"
                Clause.RBinary other -> do
                  -- A binary reason is the clause [lit, other], resolved on
                  -- 'lit'; 'other' is its other (false) literal.
                  visitLit lit_idx other
                  go ( idx - 1 )
                Clause.RClause cref -> do
                  c' <- clauseAt clauseDB cref
                  visit lit_idx c'
                  go ( idx - 1 )
                Clause.RLazy lref -> do
                  -- Theory-propagated literal: force the deferred reason
                  -- closure to recover the supporting clause's literals.
                  ls <- forceLazyReason trail lref
                  -- Each forced literal must be currently assigned, so 'visitLit'
                  -- can read its decision level. See Note [Citability invariant].
                  visitLits lit_idx ls
                  go ( idx - 1 )

    visitLits :: Int -> [ Lit ] -> m ()
    visitLits skipVi = mapM_ ( visitLit skipVi . FalsifiedLit )

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
  => SolverState ( PrimState m ) -> DecisionLevel -> m ()
cancelUntil
  s@( SolverState { solverAssignments = assig })
  tgtLevel@( DecisionLevel tgt ) = do
  cur <- currentLevel assig
  when ( cur > tgtLevel ) do
    TrailPos sz <- trailSize assig
    start@( LevelStart { levelTrailPos = TrailPos limI } ) <-
      Growable.read ( levelStarts ( trail assig ) ) tgt
    let
      undo :: Int32 -> m ()
      undo !i
        | i < limI  = pure ()
        | otherwise = do
            lit <- Growable.read ( entries ( trail assig ) ) ( fromIntegral i )
            let v     = litVar lit
                v_idx = varIndex v
            -- The lit on the trail was the asserted-true literal, so its
            -- polarity is exactly the polarity we want to save for the
            -- next decision touching this variable.
            -- TODO: CaDiCaL vs MiniSat: do we want to save ALL phases or only
            -- decision phases?
            Growable.write ( phase       assig )      v_idx ( litPolarity lit )
            Growable.write ( assignments assig )      v_idx ŁUndef
            Growable.write ( level  $ varData assig ) v_idx UnassignedLevel
            Growable.write ( reason $ varData assig ) v_idx Clause.RDecision
            -- A decision variable is unassigned again, so it must be in the
            -- heap to be eligible for future decisions; 'reinsertVar' is a
            -- no-op if it was already there (i.e. it was propagated, not
            -- popped). Auxiliary (non-decision) variables are deliberately
            -- never returned to the heap.
            Bit dec <- Growable.read ( decidable assig ) v_idx
            when dec ( VarOrder.reinsertVar ( varOrder s ) v )
            undo ( i - 1 )
    undo ( sz - 1 )
    truncateToLevel ( trail assig ) tgtLevel start

-- | Snapshot the current lengths of every backjump-coupled array.
captureLevelStart :: PrimMonad m => AssignmentTrail ( PrimState m ) -> m LevelStart
captureLevelStart trl = do
  pos   <- TrailPos . fromIntegral <$> Growable.length ( entries trl )
  nLazy <- Growable.length ( lazyReasons trl )
  pure ( LevelStart { levelTrailPos = pos, levelLazyCount = fromIntegral nLazy } )

-- | Roll every backjump-coupled array back to the watermarks captured for the
-- target level, drop the cancelled levels from 'levelStarts', and resume BCP
-- at the level's trail position.
--
-- Precondition: the per-variable state of the dropped assignments has already
-- been undone.
truncateToLevel
  :: PrimMonad m
  => AssignmentTrail ( PrimState m ) -> DecisionLevel -> LevelStart -> m ()
truncateToLevel
  trl
  ( DecisionLevel tgt )
  LevelStart
    { levelTrailPos = pos@( TrailPos p )
    , levelLazyCount = nLazy
    } = do
  Growable.truncate ( entries trl )     ( fromIntegral p )
  Growable.truncate ( lazyReasons trl ) ( fromIntegral nLazy )
  Growable.truncate ( levelStarts trl ) tgt
  writeMutVar ( trailHead trl ) pos

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
  => SolverState ( PrimState m ) -> m ( Maybe Lit )
decide s@( SolverState { solverAssignments = assig } ) = do
  mbV <- VarOrder.extractMaxBy ( varOrder s ) isUnassigned
  case mbV of
    Nothing -> pure Nothing
    Just v  -> do
      modifyMutVar' ( decCount ( stats s ) ) ( + 1 )
      pol <- Growable.read ( phase assig ) ( varIndex v )
      pure ( Just ( mkLit v pol ) )
  where
    isUnassigned :: Var -> m Bool
    isUnassigned v = ( ŁUndef == ) <$> valueOf assig v

-- | Branch on a /specific/ variable, returning the literal with its saved phase
-- (defaulting to positive). 'Nothing' if the variable is already assigned.
--
-- Unlike 'decide', this neither consults the VSIDS heap nor counts the decision
-- (the caller is expected to count it via 'countDecision'), so a theory
-- heuristic can propose any variable while still honouring phase saving. The
-- variable need not be removed from the VSIDS heap: 'decide' filters out
-- already-assigned variables, and 'cancelUntil' reinserts it once it becomes
-- unassigned again.
decideVar
  :: forall m
  .  PrimMonad m
  => Assignments ( PrimState m ) -> Var -> m ( Maybe Lit )
decideVar assig v = do
  val <- valueOf assig v
  case val of
    ŁUndef -> do
      pol <- Growable.read ( phase assig ) ( varIndex v )
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
  => SolverState ( PrimState m ) -> m Verdict
solve = solveWith defaultSolverOptions

solveWith
  :: forall m
  .  PrimMonad m
  => SolverOptions -> SolverState ( PrimState m ) -> m Verdict
solveWith opts s@( SolverState { solverAssignments = assig } ) = do
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
              lvl <- currentLevel assig
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
                  enqueueUndef assig lit Clause.RDecision
                  step confs

        checkBudget :: m ( Maybe Verdict )
        checkBudget
          | optConflictBudget opts <= 0 = pure Nothing
          | otherwise = do
              n <- readMutVar ( confCount ( stats s ) )
              pure $ if n >= optConflictBudget opts then Just Unknown else Nothing

-------------------------------------------------------------------------------
-- Driver primitives.
--
-- The functions below carve up the inner step of 'solveWith' into discrete
-- pieces, exposed for DPLL(T) consumers that interleave theory work with
-- the SAT search.

-- | Open a fresh decision level by recording the current backjump watermarks
-- as its starting point (see 'captureLevelStart'). The next 'enqueueUndef'
-- call will be the head of the new level (typically a decision).
pushNewLevel
  :: PrimMonad m
  => SolverState ( PrimState m ) -> m ()
pushNewLevel ( SolverState { solverAssignments = Assignments { trail } } ) = do
  start <- captureLevelStart trail
  Growable.push ( levelStarts trail ) start

-- | Record a branching decision taken /outside/ 'decide' — e.g. a literal
-- proposed by a DPLL(T) theory's own decision heuristic — so that
-- 'numDecisions' counts the full search-tree size, not just VSIDS branches.
countDecision
  :: PrimMonad m
  => SolverState ( PrimState m ) -> m ()
countDecision s = modifyMutVar' ( decCount ( stats s ) ) ( + 1 )

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
  => SolverState ( PrimState m ) -> [ Lit ] -> m ()
installLearnt s@( SolverState { solverAssignments = assig } ) = \case
  [] -> markFalse s
  [ l ] -> enqueueUndef assig l Clause.RFact
  [ l, m ] -> do
    attachBinary ( clauseDB s ) l m
    enqueueUndef assig l ( Clause.RBinary $ FalsifiedLit m )
  ls@( l : _ ) -> do
    ( cref, c ) <- recordClause ( clauseDB s ) True ls
    Growable.push ( learnts ( clauseDB s ) ) cref
    attachLong ( clauseDB s ) cref c
    enqueueUndef assig l ( Clause.RClause cref )

-- | Resolve a non-ground conflict.
--
-- Precondition: the conflict is at a decision level strictly above
-- 'GroundLevel'; a ground-level conflict is terminal UNSAT and must be
-- handled by the caller via 'markFalse'.
--
-- Consequently, 'numConflicts' counts only resolved above-ground conflicts.
resolveConflict
  :: PrimMonad m
  => SolverState ( PrimState m )
  -> Conflict
  -> ( DecisionLevel -> m () )
       -- ^ post-backjump hook, run after 'cancelUntil' and before
       -- 'installLearnt'; given the backjump level
  -> m ()
resolveConflict s c onBackjump = do
  modifyMutVar' ( confCount ( stats s ) ) ( + 1 )
  ( learnt, bj ) <- analyse s c
  cancelUntil s bj
  onBackjump bj
  installLearnt s learnt
  VarOrder.decayActivities ( varOrder s )

-- | Whether the solver is still consistent (i.e. has not detected a
-- ground-level inconsistency).
isOk :: PrimMonad m => SolverState ( PrimState m ) -> m Bool
isOk = readMutVar . okFlag

-- | Read the literal at a trail position. Precondition: the position is
-- in @[0, trailSize)@.
trailAt
  :: PrimMonad m
  => SolverState ( PrimState m ) -> TrailPos -> m Lit
trailAt
  ( SolverState { solverAssignments = Assignments { trail } } )
  ( TrailPos i )
    = Growable.read ( entries trail ) ( fromIntegral i )

-- | Stash a lazy-reason closure in the solver and return its handle.
--
-- The closure can later be attached to a theory-propagated literal as a
-- 'Clause.RLazy' reason. It is forced only if 1-UIP analysis crosses the
-- literal, and must then satisfy Note [Citability invariant].
recordLazyReason
  :: PrimMonad m
  => SolverState ( PrimState m ) -> Clause.LazyReason ( PrimState m ) -> m Clause.LazyRef
recordLazyReason ( SolverState { solverAssignments = Assignments { trail } } ) lazy = do
  i <- Growable.length ( lazyReasons trail )
  Growable.push ( lazyReasons trail ) lazy
  pure ( Clause.LazyRef $ fromIntegral i )

-- | Retrieve a 'LazyReason' from its reference.
--
-- Does not force the 'LazyReason'.
getLazyReason
  :: PrimMonad m
  => AssignmentTrail ( PrimState m ) -> Clause.LazyRef -> m ( Clause.LazyReason ( PrimState m ) )
getLazyReason trail ( Clause.LazyRef i ) = do
#ifdef DEBUG
  n <- Growable.length ( lazyReasons trail )
  when ( i < 0 || i >= fromIntegral n ) $
    error $ "SAT.Solver.forceLazy: out-of-range LazyRef=" ++ show i
         ++ " lazyReasons.length=" ++ show n
#endif
  Growable.read ( lazyReasons trail ) ( fromIntegral i )

-- | Force a 'Clause.LazyReason' to obtain its supporting clause's literals.
forceLazyReason
  :: PrimMonad m
  => AssignmentTrail ( PrimState m ) -> Clause.LazyRef -> m [ Lit ]
forceLazyReason trail ref@( Clause.LazyRef i ) = do
  rea <- getLazyReason trail ref
  case rea of
    Clause.LazyReason forceIt ->
      do { lits <- forceIt
           -- Overwrite the thunk with what it evaluated to.
         ; Growable.write ( lazyReasons trail ) ( fromIntegral i ) $
             Clause.AlreadyForcedReason lits
         ; return lits
         }
    Clause.AlreadyForcedReason lits -> pure lits

-- | Record a long (size @≥ 3@) theory-supplied clause in the clause store
-- (without attaching watchers).
--
-- Intended for materialising a theory conflict so that 'analyse' can read
-- it via 'clauseAt'. Theory conflict clauses are consumed once by 1-UIP
-- and never need to participate in BCP, so they do not need to be in any
-- watch list. (The /learnt/ clause that 1-UIP produces from analysis is
-- attached normally via 'installLearnt'.)
recordTheoryClause
  :: PrimMonad m
  => SolverState ( PrimState m ) -> [ Lit ] -> m ClauseRef
recordTheoryClause s ls = fst <$> recordClause ( clauseDB s ) False ls
  -- TODO: these clauses are stored permanently, never reclaimed.

-- | Record a long (size @≥ 3@) conflicting clause from its falsified literals.
recordFalsifiedClause
  :: PrimMonad m
  => SolverState ( PrimState m ) -> [ FalsifiedLit ] -> m FalsifiedClauseRef
recordFalsifiedClause s ls =
  FalsifiedClauseRef <$> recordTheoryClause s ( map underlyingLit ls )

-------------------------------------------------------------------------------
-- Assignments.

-- | A snapshot of the solver's variable assignment.
--
-- Only variables with a definite value are present; unassigned variables
-- are absent and surface as 'ŁUndef' via 'assignmentValue'.
newtype Assignment = Assignment ( IntMap Bool )
  deriving stock Show

-- | The lifted-boolean value of a variable under the assignment.
assignmentValue :: Var -> Assignment -> Ł3
assignmentValue ( Var v ) ( Assignment m ) =
  case IntMap.lookup ( fromIntegral v ) m of
    Just True  -> ŁTrue
    Just False -> ŁFalse
    Nothing    -> ŁUndef

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
  => Assignments ( PrimState m ) -> m Assignment
getModel assig = do
  n <- numVariables assig
  let
    collect :: Int -> IntMap Bool -> m ( IntMap Bool )
    collect !i !acc
      | i < 0     = pure acc
      | otherwise = do
          val <- valueOf assig ( Var $ fromIntegral i )
          let !acc' = case val of
                ŁTrue  -> IntMap.insert i True  acc
                ŁFalse -> IntMap.insert i False acc
                ŁUndef -> acc
          collect ( i - 1 ) acc'
  Assignment <$> collect ( n - 1 ) IntMap.empty
