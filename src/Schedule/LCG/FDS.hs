{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Failure-directed search (Vilím, Laborie & Shaw, CPAIOR 2015).
module Schedule.LCG.FDS
  ( -- * Failure-directed decision strategy
    theoryDecide
    -- * Failure-directed rating updates
  , noteDecision
  , settlePending
  , settleConflict
  , measureSpace

    -- * Strong branching and shaving
  , strongBranch
  , StrongBranchResult(..)
  )
  where

-- base
import Control.Monad
  ( foldM )
import Control.Monad.ST
  ( ST )
import Data.Foldable
  ( for_, toList )
import Data.List
  ( sortOn )

-- acts
import Data.Act
  ( Torsor((-->)) )

-- containers
import qualified Data.IntMap.Strict as IntMap
  ( toList )

-- primitive
import Data.Primitive.MutVar
  ( readMutVar, writeMutVar )

-- memory-arena
import qualified Memory.Growable as Growable

-- unary-scheduling
import SAT.Base
  ( Ł3(..), Lit, litIndex, negateLit )
import SAT.Clause
  ( Reason(..) )
import qualified SAT.Solver as SAT
import Schedule.Interval
  ( Endpoint(endpoint), Intervals(..), Measurable(..)
  )
import Schedule.LCG.Atoms
  ( precLit, precedenceAtomsNumTasks )
import Schedule.LCG.Theory
import Schedule.Monitor
  ( MonitorMode(..) )
import Schedule.Ordering
  ( Order(..), readOrdering
  )

import Schedule.Task
  ( TaskInfos(..), Task(..)
  , ect, lst
  )
import Schedule.Time
  ( Delta(getDelta), HandedTime(handedTime)
  )

-------------------------------------------------------------------------------
-- Failure-directed decision heuristic.
--
-- Failure-Directed Search (Vilím, Laborie & Shaw, CPAIOR 2015) rates each
-- /branch/ (a variable+polarity) by how close it tends to come to a wipeout, and
-- dives the branch most likely to fail first — provably shrinking the space
-- fastest, which is what closes a search on feasible and infeasible alike.
--
-- The pieces, each documented at its own definition:
--
--   * a branch's rating ('branchRating') matures via an EMA of its per-decision
--     local ratings ('settlePending' \/ 'settleConflict' \/ 'settleBranch');
--   * 'theoryDecide' consults those ratings to choose the next branch;
--   * 'strongBranch' warm-starts the ratings (and shaves) at each restart root.

-- | The neutral starting value for every branch rating and depth average.
initialRating :: Double
initialRating = 1

-- | EMA retention weight @α@ in the rating update.
--
-- The paper uses a slow decay @α ∈ [0.9, 0.99]@: a single observation nudges a
-- rating, and it takes a run of failures to drive a branch toward @0@.
fdsAlpha :: Double
fdsAlpha = 0.95

-- | Floor on a depth's average rating, guarding the per-depth normalisation
-- against a depth whose observations have driven the average toward @0@.
avgRatingFloor :: Double
avgRatingFloor = 1e-3

-- | Grow 'branchRating' to cover the given literal, filling fresh cells with the
-- neutral 'initialRating'.
ensureRating :: TheoryState mode s task t -> Lit -> ST s ()
ensureRating t lit =
  Growable.ensureSize ( branchRating t ) ( litIndex lit + 1 ) initialRating

-- | The current rating of a branch ('initialRating' if never rated), growing the
-- store as needed.
readRating :: TheoryState mode s task t -> Lit -> ST s Double
readRating t lit = do
  ensureRating t lit
  Growable.read ( branchRating t ) ( litIndex lit )

writeRating :: TheoryState mode s task t -> Lit -> Double -> ST s ()
writeRating t lit r = do
  ensureRating t lit
  Growable.write ( branchRating t ) ( litIndex lit ) r

-- | The running average rating at a search depth (the paper's @avgRating[d]@),
-- 'initialRating' until any branch at that depth is rated.
readAvgRating :: TheoryState mode s task t -> Int -> ST s Double
readAvgRating t d = do
  Growable.ensureSize ( avgRating t ) ( d + 1 ) initialRating
  Growable.read ( avgRating t ) d

writeAvgRating :: TheoryState mode s task t -> Int -> Double -> ST s ()
writeAvgRating t d r = do
  Growable.ensureSize ( avgRating t ) ( d + 1 ) initialRating
  Growable.write ( avgRating t ) d r

-- | The current SAT decision level as a plain depth.
currentDepth :: TheoryState mode s task t -> ST s Int
currentDepth t = do
  SAT.DecisionLevel d <- SAT.currentLevel ( theoryAssignments t )
  pure d

-- | The log of the remaining search-space size: @Σ_tasks log |domain|@, the
-- domain of a task being the measure of its current availability (its feasible
-- start positions). The paper's reduction @R@ is the /product/ of per-variable
-- domain ratios before and after a decision, so working in this log-sum lets
-- 'settlePending' recover @R = exp(after − before)@ in one subtraction.
--
-- A fixed task contributes a unit (log @0@) domain; an /emptied/ domain is a
-- failure, surfaced as a conflict and rated by 'settleConflict', so it is never
-- measured here (the @max 1@ only guards against @log 0@ on a degenerate slot).
measureSpace
  :: forall mode s task t
  .  ( Real t, Measurable t )
  => TheoryState mode s task t -> ST s Double
measureSpace t = go 0 0
  where
    n = precedenceAtomsNumTasks ( atoms t )
    go :: Int -> Double -> ST s Double
    go !i !acc
      | i >= n    = pure acc
      | otherwise = do
          task <- readTask t i
          let vol = sum [ getDelta ( measure iv )
                        | iv <- toList ( intervals ( taskAvailability task ) ) ]
          go ( i + 1 ) ( acc + log ( max 1 ( realToFrac vol ) ) )


-------------------------------------------------------------------------------
-- Failure-directed rating updates.
--
-- A one-slot pending observation links the two hook points: 'noteDecision'
-- records the branch just taken with the (log) search-space measure then in
-- effect; 'settlePending' \/ 'settleConflict' fold its measured failure-directed
-- local rating into the branch's EMA when the next decision is taken or a
-- conflict fires. Because nothing happens between a decision and its settlement
-- but that branch's own propagation, the settlement sees exactly the branch's
-- effect (the paper's "update rating of branch right after it propagates").

-- | Record the branch just taken, with the (log) search-space measure
-- ('measureSpace') in effect when it was chosen, as the one-slot pending
-- observation to be settled later.
noteDecision :: TheoryState mode s task t -> Lit -> Double -> ST s ()
noteDecision t lit spaceBefore =
  writeMutVar ( pendingDecision t ) ( Just ( lit, spaceBefore ) )

-- | Settle the pending decision against the (log) search-space measure now in
-- effect (after it propagated to a fixpoint). Its local rating is the paper's
-- @1 + R@, where @R = exp(after − before) ∈ (0, 1]@ is the product of per-task
-- domain ratios — so a non-failing branch rates in @(1, 2]@, sharply above the
-- @0@ a wipeout earns ('settleConflict'). A no-op when no decision is pending.
settlePending :: TheoryState mode s task t -> Double -> ST s ()
settlePending t spaceAfter = do
  mb <- readMutVar ( pendingDecision t )
  case mb of
    Nothing -> pure ()
    Just ( lit, spaceBefore ) -> do
      let r = min 1 ( exp ( spaceAfter - spaceBefore ) )
      settleBranch t lit ( 1 + r )
      writeMutVar ( pendingDecision t ) Nothing

-- | Settle the pending decision as a wipeout (local rating @0@): the branch led
-- straight to a conflict, the maximally failure-directed outcome. A no-op when
-- no decision is pending.
settleConflict :: TheoryState mode s task t -> ST s ()
settleConflict t = do
  mb <- readMutVar ( pendingDecision t )
  case mb of
    Nothing -> pure ()
    Just ( lit, _ ) -> do
      settleBranch t lit 0
      writeMutVar ( pendingDecision t ) Nothing

-- | Fold a branch's fresh local rating into its EMA, normalised by the running
-- average rating at the current depth (so a branch is judged against its peers
-- at the same depth, where local ratings are systematically higher near the
-- root): @rating ← α·rating + (1−α)·localRating \/ avgRating[d]@. The depth's
-- average absorbs the same observation.
settleBranch :: TheoryState mode s task t -> Lit -> Double -> ST s ()
settleBranch t lit localRating = do
  d   <- currentDepth t
  avg <- readAvgRating t d
  r0  <- readRating t lit
  let avg' = max avgRatingFloor avg
      r'   = fdsAlpha * r0  + ( 1 - fdsAlpha ) * ( localRating / avg' )
      avgN = fdsAlpha * avg + ( 1 - fdsAlpha ) * localRating
  writeRating t lit r'
  writeAvgRating t d avgN

-------------------------------------------------------------------------------
-- Strong branching and shaving (FDS §6.3).
--
-- At the root of each restart the EMA ratings are at their most imprecise, yet
-- the choices there matter most. So FDS pre-evaluates a limited number of the
-- best-rated choices by probing both branches: apply each decision,
-- propagating to a fixpoint, measuring the actual space reduction, then undoing.
-- This matures the ratings. Two extra payoffs fall out:
--
--   * /Shaving/: if a probed branch fails, its opposite is entailed.
--
--   * /Best local rating pick/: after probing, the open branch with the smallest
--     fresh @localRating@ is pre-selected as the next decision (via 'forcedDecision').
--
-- The paper's §6.3 also describes a third inference: when both probed branches
-- tighten the same variable's bound, the weaker common bound is entailed (by the
-- branch being a valid disjunction) and can be applied at the root.
-- We don't currently implement this, as the LCG machinery requires a clausal
-- reason to justify this inference, which is a bit tricky to conjure up.

-- | The outcome of strong branching at a restart root.
data StrongBranchResult
  = -- | A shave (or a choice with both branches failing) made the root
    -- inconsistent: the instance is infeasible.
    StrongBranchUnsat
  | -- | Probing completed: ratings matured, infeasible branches shaved, and
    -- 'forcedDecision' set to the best-localRating open branch (if any).
    StrongBranchOk

-- | Run the SAT\/theory propagation to a fixpoint, returning the first conflict
-- found (or 'Nothing' at a clean fixpoint). Mirrors the BCP\/theory interleaving
-- of the main search loop ('Schedule.LCG.Search.searchWindow'), without deciding.
propagateFixpoint
  :: forall mode s task t
  .  ( Real t, Num t, Measurable t, Bounded t, Show t, Show task, MonitorMode mode )
  => TheoryState mode s task t -> ST s ( Maybe SAT.Conflict )
propagateFixpoint t = loop
  where
    ss = theorySolverState t
    loop = do
      mbC <- SAT.propagate ss
      case mbC of
        Just c  -> pure ( Just c )
        Nothing -> do
          before <- SAT.trailSize ( SAT.solverAssignments ss )
          mbTC   <- theoryPropagate t
          case mbTC of
            Just c  -> pure ( Just c )
            Nothing -> do
              after <- SAT.trailSize ( SAT.solverAssignments ss )
              if after > before then loop else pure Nothing

-- | Strong branching with shaving at a restart root.
--
-- Must be called at 'SAT.GroundLevel', with the root not yet necessarily
-- propagated.
strongBranch
  :: forall mode s task t
  .  ( Real t, Num t, Measurable t, Bounded t, Show t, Show task, MonitorMode mode )
  => TheoryState mode s task t
  -> Int   -- ^ width: how many best-rated choices to pre-evaluate
  -> ST s StrongBranchResult
strongBranch t width
  | width <= 0 = pure StrongBranchOk
  | otherwise = do
      writeMutVar ( pendingDecision t ) Nothing
      writeMutVar ( forcedDecision t )  Nothing
      -- The root must be at a fixpoint before measuring or probing.
      mbConf <- propagateFixpoint t
      ok     <- SAT.isOk ss
      case mbConf of
        Just _              -> pure StrongBranchUnsat
        Nothing | not ok    -> pure StrongBranchUnsat
                | otherwise -> do
                    cands <- bestCandidates t width
                    go cands Nothing
  where
    ss = theorySolverState t

    -- Probe each candidate in turn, threading the best (lowest local rating)
    -- open branch seen so far for the final 'forcedDecision'.
    go :: [ ( Lit, Lit ) ] -> Maybe ( Lit, Double ) -> ST s StrongBranchResult
    go [] best = do
      for_ best \ ( lit, _ ) -> writeMutVar ( forcedDecision t ) ( Just lit )
      pure StrongBranchOk
    go ( ( posLit, negLit ) : rest ) best = do
      -- A prior shave may already have decided this choice.
      open <- isUndecided t posLit
      if not open then go rest best else do
        outcome <- probeChoice t posLit negLit
        case outcome of
          ChoiceShaved -> do
            -- A ground fact was committed; propagate it and re-check consistency
            -- before the next probe measures a tightened root.
            mbC <- propagateFixpoint t
            okS <- SAT.isOk ss
            case mbC of
              Just _              -> pure StrongBranchUnsat
              Nothing | not okS   -> pure StrongBranchUnsat
                      | otherwise -> go rest best
          ChoiceOpen branches ->
            go rest ( foldl' keepLower best branches )

    keepLower :: Maybe ( Lit, Double ) -> ( Lit, Double ) -> Maybe ( Lit, Double )
    keepLower Nothing             cand = Just cand
    keepLower acc@( Just ( _, r0 ) ) cand@( _, r )
      | r < r0    = Just cand
      | otherwise = acc

-- | The result of probing both branches of one choice.
data ChoiceOutcome
  = -- | One branch failed; its negation was committed at the root (the choice is
    -- decided).
    ChoiceShaved
  | -- | Both branches feasible: the choice stays open, with each branch's
    -- @(literal, localRating)@ for the best local rating pick.
    ChoiceOpen ![ ( Lit, Double ) ]

-- | Probe both branches of a choice from the current root.
probeChoice
  :: forall mode s task t
  .  ( Real t, Num t, Measurable t, Bounded t, Show t, Show task, MonitorMode mode )
  => TheoryState mode s task t -> Lit -> Lit -> ST s ChoiceOutcome
probeChoice t posLit negLit = do
  before <- measureSpace t
  rp <- probeBranch t posLit before
  case rp of
    ProbeConflict  -> pure ChoiceShaved      -- ¬pos committed at root
    ProbeOk ratPos -> do
      -- The pos probe was undone, so the root (and 'before') is unchanged.
      rn <- probeBranch t negLit before
      case rn of
        ProbeConflict  -> pure ChoiceShaved   -- ¬neg committed at root
        ProbeOk ratNeg ->
          pure ( ChoiceOpen [ ( posLit, ratPos ), ( negLit, ratNeg ) ] )

-- | The result of probing a single branch literal.
data ProbeResult
  = -- | The branch is infeasible: its conflict was resolved by 1-UIP, which
    -- backjumped to the root and committed the branch's negation (a shave).
    ProbeConflict
  | -- | The branch is feasible; its local rating @1 + R@ was folded into the EMA
    -- and the probe undone. Carries that local rating for the best-pick.
    ProbeOk !Double

-- | Probe one branch literal from the current (root) level: push it as a
-- decision, propagate to a fixpoint, and either resolve the resulting conflict
-- (committing the negation at the root — shaving) or measure the space reduction,
-- mature the branch rating, and undo the probe.
probeBranch
  :: forall mode s task t
  .  ( Real t, Num t, Measurable t, Bounded t, Show t, Show task, MonitorMode mode )
  => TheoryState mode s task t -> Lit -> Double -> ST s ProbeResult
probeBranch t l before = do
  let assigs = theoryAssignments t
  rootLvl <- SAT.currentLevel assigs
  SAT.pushNewLevel ss
  pushLevel t
  SAT.enqueueUndef assigs l RDecision
  mbConf <- propagateFixpoint t
  case mbConf of
    Just c  -> do
      -- localRating 0 (immediate failure), rated at the probe depth before the
      -- conflict backjumps it away.
      settleBranch t l 0
      SAT.resolveConflict ss c ( popToLevel t )
      pure ProbeConflict
    Nothing -> do
      after <- measureSpace t
      let r = 1 + min 1 ( exp ( after - before ) )
      settleBranch t l r
      SAT.cancelUntil ss rootLvl
      popToLevel t rootLvl
      pure ( ProbeOk r )
  where
    ss = theorySolverState t

-- | Whether a precedence branch literal is still unassigned (its choice undecided).
isUndecided :: TheoryState mode s task t -> Lit -> ST s Bool
isUndecided t lit = do
  v <- SAT.litValue ( theoryAssignments t ) lit
  pure $ case v of { ŁUndef -> True; _ -> False }

-- | The @width@ best-rated undecided precedence choices, lowest @rating[c]@
-- first, ties broken by criticality (so an all-neutral root probes the most
-- contended pairs). Each is returned as its @(positive, negative)@ branch pair.
bestCandidates
  :: forall mode s task t
  .  ( Real t, Num t, Measurable t, Bounded t )
  => TheoryState mode s task t -> Int -> ST s [ ( Lit, Lit ) ]
bestCandidates t width = do
  scored <- collect 0 1 []
  pure [ ( p, n ) | ( _, _, p, n ) <- take width ( sortOn ( \ ( s, tie, _, _ ) -> ( s, tie ) ) scored ) ]
  where
    ps  = atoms t
    nT  = precedenceAtomsNumTasks ps
    mat = orderings ( tasks t )
    collect :: Int -> Int -> [ ( Double, Double, Lit, Lit ) ]
            -> ST s [ ( Double, Double, Lit, Lit ) ]
    collect i j acc
      | i >= nT - 1 = pure acc
      | j >= nT     = collect ( i + 1 ) ( i + 2 ) acc
      | otherwise   = do
          o <- readOrdering mat i j
          case o of
            Unknown -> do
              v <- SAT.litValue ( theoryAssignments t ) ( precLit ps i j )
              case v of
                ŁUndef -> do
                  let posLit = precLit ps i j
                      negLit = precLit ps j i
                  rPos <- readRating t posLit
                  rNeg <- readRating t negLit
                  ( crit, _ ) <- evalPair t i j
                  collect i ( j + 1 )
                    ( ( rPos + rNeg, realToFrac ( getDelta crit ), posLit, negLit ) : acc )
                _ -> collect i ( j + 1 ) acc
            _ -> collect i ( j + 1 ) acc

-- | The criticality of an unordered task pair (the larger of the two ordering
-- slacks; smaller = more contended) together with the larger-slack directed
-- precedence literal — the textbook direction to branch first.
--
-- (Clusivity is ignored in the slack — it shifts a bound by at most one unit,
-- immaterial to a branching /heuristic/.)
evalPair
  :: ( Num t, Measurable t, Bounded t )
  => TheoryState mode s task t -> Int -> Int -> ST s ( Delta t, Lit )
evalPair t i j = do
  ti <- readTask t i
  tj <- readTask t j
  let ps   = atoms t
      ectI = handedTime ( endpoint ( ect ti ) )
      lstI = handedTime ( endpoint ( lst ti ) )
      ectJ = handedTime ( endpoint ( ect tj ) )
      lstJ = handedTime ( endpoint ( lst tj ) )
      slackIJ = ectI --> lstJ   -- room if i precedes j
      slackJI = ectJ --> lstI   -- room if j precedes i
      crit    = max slackIJ slackJI
      lit | slackIJ >= slackJI = precLit ps i j   -- larger-slack direction first
          | otherwise          = precLit ps j i
  pure ( crit, lit )

-- | Propose the next branching literal by failure-directed selection, or
-- 'Nothing' to defer to VSIDS.
--
-- The precedence tournament is the /primary/ choice set: a complete acyclic
-- ordering plus propagation determines a schedule, so precedences alone are a
-- sound and complete branching. Each undecided pair's variable @v@ is scored by
-- the combined rating of its two branches,
--
-- > score v = rating[pos v] + rating[neg v]
--
-- (both branches failure-prone ⇒ a /closing choice/, the best). The
-- minimum-score candidate is branched on its lower-rated — more failure-prone —
-- side first (fail-first); score ties are broken by criticality (see 'evalPair').
-- An unrated branch keeps the neutral 'initialRating', so on a conflict-free dive
-- every candidate ties and the criticality tie-break reproduces the structural
-- critical-pair dive exactly. Once branches are rated (post-conflict, or
-- warm-started at a restart root by 'strongBranch') their ratings govern and
-- pure FDS takes over. A branch pre-selected by 'strongBranch' (in 'forcedDecision')
-- pre-empts the scan entirely.
--
-- Interval-commit atoms are /completion/ choices: redundant given the
-- precedences, they are considered only once every precedence is decided but the
-- formula is not yet fully assigned (cf. the paper completing a fully-decided
-- choice set). Mixing them into the primary pool lets shallow interval-commit
-- failures crowd out the precedence proof, which the per-instance sweep confirms
-- hurts the infeasible families without helping the feasible ones.
--
-- 'Nothing' once every structural atom is decided (or when 'useTheoryDecide' is
-- off): any remaining decision variables fall through to VSIDS, so search
-- stays complete.
theoryDecide
  :: forall mode s task t
  .  ( Real t, Measurable t, Bounded t )
  => TheoryState mode s task t
  -> ST s ( Maybe Lit )
theoryDecide t
  | not ( useTheoryDecide $ theoryOptions t ) = pure Nothing
  | otherwise = do
      -- A branch pre-selected by strong branching at the restart root takes
      -- precedence (the paper's best-localRating pick), provided propagation
      -- since has not already decided it.
      mbForced <- readMutVar ( forcedDecision t )
      case mbForced of
        Just lit -> do
          writeMutVar ( forcedDecision t ) Nothing
          v <- SAT.litValue ( theoryAssignments t ) lit
          case v of
            ŁUndef -> pure ( Just lit )
            _      -> ratingScan
        Nothing -> ratingScan
  where
    ratingScan = do
      mbPrec <- scanPrecedences t Nothing
      case mbPrec of
        Just cand -> pure ( Just ( candidateLit cand ) )
        Nothing   -> fmap candidateLit <$> scanBoundDecisions t Nothing

-- | A scored failure-directed candidate: its combined @score@ (lower =
-- preferred), a @tieKey@ breaking equal scores (lower = preferred), and the
-- branch literal to assert first (its lower-rated, more failure-prone side).
type Candidate = ( Double, Double, Lit )

candidateLit :: Candidate -> Lit
candidateLit ( _, _, lit ) = lit

-- | Keep the better of an incumbent candidate and a new one, comparing by
-- @(score, tieKey)@ lexicographically.
keepBest :: Maybe Candidate -> Candidate -> Maybe Candidate
keepBest Nothing cand = Just cand
keepBest acc@( Just ( bScore, bTie, _ ) ) cand@( cScore, cTie, _ )
  | ( cScore, cTie ) < ( bScore, bTie ) = Just cand
  | otherwise                            = acc

-- | Assemble a candidate from a variable's two branch ratings, a score-tie key,
-- and the side to branch first when the two ratings are equal.
mkCandidate :: Lit -> Lit -> Double -> Double -> Double -> Lit -> Candidate
mkCandidate posLit negLit ratPos ratNeg tieKey tieSide =
  ( ratPos + ratNeg
  , tieKey
  , case compare ratPos ratNeg of
      LT -> posLit
      GT -> negLit
      EQ -> tieSide
  )

-- | Scan the undecided precedence pairs (the upper-triangular ordering matrix),
-- scoring each and keeping the best-scoring candidate.
scanPrecedences
  :: forall mode s task t
  .  ( Real t, Measurable t, Bounded t )
  => TheoryState mode s task t -> Maybe Candidate -> ST s ( Maybe Candidate )
scanPrecedences t = go 0 1
  where
    ps  = atoms t
    n   = precedenceAtomsNumTasks ps
    mat = orderings ( tasks t )
    go :: Int -> Int -> Maybe Candidate -> ST s ( Maybe Candidate )
    go i j best
      | i >= n - 1 = pure best
      | j >= n     = go ( i + 1 ) ( i + 2 ) best
      | otherwise  = do
          o <- readOrdering mat i j
          case o of
            Unknown -> do
              v <- SAT.litValue ( theoryAssignments t ) ( precLit ps i j )
              case v of
                -- 'Unknown' in the matrix should mean the precedence atom is
                -- unassigned; the check guards against branching an assigned one.
                ŁUndef -> do
                  cand <- precCandidate t i j
                  go i ( j + 1 ) ( keepBest best cand )
                _ -> go i ( j + 1 ) best
            _ -> go i ( j + 1 ) best

-- | Score one undecided precedence pair: combined branch rating, with the pair's
-- criticality ('evalPair') as the score-tie key and its larger-slack direction
-- as the within-pair tie side. On an untrained dive every rating is neutral, so
-- the criticality tie-break drives selection — the structural critical-pair dive.
precCandidate
  :: ( Real t, Measurable t, Bounded t )
  => TheoryState mode s task t -> Int -> Int -> ST s Candidate
precCandidate t i j = do
  let ps     = atoms t
      posLit = precLit ps i j   -- i ≺ j
      negLit = precLit ps j i   -- j ≺ i
  ( crit, dirLit ) <- evalPair t i j
  rPos <- readRating t posLit
  rNeg <- readRating t negLit
  pure ( mkCandidate posLit negLit rPos rNeg ( realToFrac ( getDelta crit ) ) dirLit )

-- | Scan each gappy task's lowest undecided interval-commit atom (a completion
-- choice; see 'theoryDecide') and keep the best-scoring candidate. With no
-- precedence left to compete with, score alone decides; equal scores fall to the
-- first (lowest-threshold) atom.
scanBoundDecisions
  :: forall mode s task t
  .  TheoryState mode s task t -> Maybe Candidate -> ST s ( Maybe Candidate )
scanBoundDecisions t acc0 = do
  dbs <- readMutVar ( decisionBounds t )
  foldM step acc0 ( IntMap.toList dbs )
  where
    step :: Maybe Candidate -> ( Int, [ Lit ] ) -> ST s ( Maybe Candidate )
    step acc ( i, lits ) = do
      task <- readTask t i
      let nIvals = length ( intervals ( taskAvailability task ) )
      if nIvals <= 1
      then pure acc   -- already committed to a single interval
      else do
        mbLit <- firstUndecided t lits
        case mbLit of
          Nothing     -> pure acc   -- all decided already
          Just posLit -> do
            let negLit = negateLit posLit
            rPos <- readRating t posLit
            rNeg <- readRating t negLit
            pure ( keepBest acc ( mkCandidate posLit negLit rPos rNeg 0 posLit ) )

-- | The lowest-threshold interval-commit atom of the list not yet assigned.
firstUndecided :: TheoryState mode s task t -> [ Lit ] -> ST s ( Maybe Lit )
firstUndecided _ [] = pure Nothing
firstUndecided t ( l : ls ) = do
  v <- SAT.litValue ( theoryAssignments t ) l
  case v of
    ŁUndef -> pure ( Just l )
    _      -> firstUndecided t ls
