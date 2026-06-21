{-# LANGUAGE ScopedTypeVariables #-}

-- | Atom registry for the LCG encoding.
--
-- Two families of SAT atoms share one variable space:
--
--   * /precedence atoms/ ('PrecedenceAtoms'): one per unordered task pair,
--     asserting an ordering @T_i ≺ T_j@.
--
--   * /bound atoms/ ('BoundAtoms'): a task's start-time bounds, reified on a
--     single latest-start axis. Created /lazily/, as the search needs them, so
--     the time horizon is never enumerated.
--
-- 'litMeaning' decodes the atom a literal denotes.
module Schedule.LCG.Atoms
  ( -- * Precedence atoms
    PrecedenceAtoms
  , mkPrecedenceAtoms
  , numTasks
  , numAtoms
  , precLit
  , litPrecedence
  , isPrecedenceVar
    -- * Bound atoms (lazy)
  , BoundAtoms
  , newBoundAtoms
  , internStartUpper
  , boundNeighbours
  , isBoundVar
    -- * Decoding a trail literal
  , AtomMeaning(..)
  , litMeaning
  )
  where

-- base
import Control.Monad.ST
  ( ST )
import Data.Bits
  ( shiftR )

-- containers
import Data.IntMap.Strict
  ( IntMap )
import qualified Data.IntMap.Strict as IntMap
  ( empty, insert, lookup, findWithDefault )
import Data.Map.Strict
  ( Map )
import qualified Data.Map.Strict as Map
  ( empty, insert, lookup, lookupLT, lookupGT )

-- primitive
import Data.Primitive.MutVar
  ( MutVar, newMutVar, readMutVar, writeMutVar, modifyMutVar' )

-- vector
import qualified Data.Vector.Unboxed as Unboxed
  ( Vector, fromListN, length, (!) )

-- unary-scheduling
import SAT.Base
  ( Var(..), varIndex
  , Lit, litVar, litPolarity
  , mkLit, Polarity(..)
  )
import Schedule.Interval
  ( Endpoint, Measurable(canonicalStartUpper) )
import Schedule.Ordering
  ( upperTriangular )
import Schedule.Time
  ( LatestTime )

-------------------------------------------------------------------------------

-- | Bijection between the unordered task pairs @{(i, j) | 0 ≤ i < j < dim}@
-- of a fixed task set and a contiguous block of SAT variables.
--
-- Carries the precomputed inverse table so decoding a precedence variable
-- back to its task pair is O(1).
data PrecedenceAtoms = PrecedenceAtoms
  { -- | Number of tasks the registry covers.
    dim         :: !Int
  , -- | 'Var' index of the first atom in the block. The atom for the
    -- canonical pair @(i, j)@ with @i < j@ has variable index
    -- @firstVarIx + upperTriangular dim i j@.
    firstVarIx  :: !Int
  , -- | Reverse lookup: indexed by @varIndex - firstVarIx@, holds the
    -- canonical pair @(i, j)@ with @i < j@ for that atom.
    atomPairTbl :: !( Unboxed.Vector ( Int, Int ) )
  }

-- | Number of tasks the registry covers.
numTasks :: PrecedenceAtoms -> Int
numTasks = dim

-- | Number of precedence atoms (one per unordered task pair).
numAtoms :: PrecedenceAtoms -> Int
numAtoms ps = Unboxed.length ( atomPairTbl ps )

-- | Build a registry that maps the unordered task pairs of a @dim@-task
-- problem onto the @dim * (dim - 1) / 2@ SAT variables starting at the
-- given 'firstVarIx'.
--
-- The caller is responsible for ensuring those variables are actually
-- allocated in the solver. Allocation is decoupled from registry
-- construction so the SAT-side handle stays out of this module.
mkPrecedenceAtoms
  :: Int          -- ^ number of tasks
  -> Int          -- ^ variable index of the first atom
  -> PrecedenceAtoms
mkPrecedenceAtoms d firstIx =
  PrecedenceAtoms
    { dim         = d
    , firstVarIx  = firstIx
    , atomPairTbl = Unboxed.fromListN n
                      [ ( i, j ) | i <- [ 0 .. d - 1 ], j <- [ i + 1 .. d - 1 ] ]
    }
  where
    !n = ( d * ( d - 1 ) ) `shiftR` 1

-- | The literal asserting that @T_pred@ precedes @T_succ@.
--
-- Pre-condition: @pred /= succ@.
precLit :: PrecedenceAtoms -> Int -> Int -> Lit
precLit ps predTask succTask = case compare predTask succTask of
  EQ -> error "Schedule.LCG.Atoms.precLit: predecessor equals successor"
  LT -> mkLit
          ( Var ( firstVarIx ps + upperTriangular ( dim ps ) predTask succTask ) )
          Positive
  GT -> mkLit
          ( Var ( firstVarIx ps + upperTriangular ( dim ps ) succTask predTask ) )
          Negative

-- | Decode a literal into its directed precedence @(predecessor, successor)@
-- pair: @Just (p, s)@ when the literal asserts @T_p ≺ T_s@, 'Nothing' if
-- the literal's variable is not a precedence atom.
litPrecedence :: PrecedenceAtoms -> Lit -> Maybe ( Int, Int )
litPrecedence ps lit
  | offset < 0 || offset >= numAtoms ps = Nothing
  | otherwise = Just $ case litPolarity lit of
      Positive -> ( i, j )
      Negative -> ( j, i )
  where
    !offset    = varIndex ( litVar lit ) - firstVarIx ps
    ( !i, !j ) = atomPairTbl ps Unboxed.! offset

-- | Whether a variable belongs to the precedence-atom block.
isPrecedenceVar :: PrecedenceAtoms -> Var -> Bool
isPrecedenceVar ps v =
  let !offset = varIndex v - firstVarIx ps
  in  offset >= 0 && offset < numAtoms ps

-------------------------------------------------------------------------------
-- Bound atoms.

-- | Lazily-grown registry of start-time bound atoms.
--
-- A single family on the latest-start axis: the atom @(task, l)@ has positive
-- literal @start_task ≤ l@ (@l@ a 'LatestTime' endpoint). Variables are
-- allocated /after/ the fixed precedence block (variable index
-- @≥ firstBoundVar@), so 'isBoundVar' and 'isPrecedenceVar' classify any
-- variable in O(1).
data BoundAtoms s t = BoundAtoms
  { -- | First variable index reserved for bound atoms (one past the last
    -- precedence atom). Bound variables have index @≥ firstBoundVar@.
    firstBoundVar :: !Int
  , -- | Per task, the created latest-start thresholds and their variables
    -- (positive literal: @start ≤ l@).
    boundFwd      :: !( MutVar s ( IntMap ( Map ( Endpoint ( LatestTime t ) ) Var ) ) )
  , -- | Reverse map: variable index → @(task, threshold)@, for decoding a
    -- drained trail literal.
    boundRev      :: !( MutVar s ( IntMap ( Int, Endpoint ( LatestTime t ) ) ) )
  }

-- | Allocate an empty bound-atom registry. @firstBoundVar@ is the variable
-- index one past the last precedence atom (i.e. 'numAtoms' of the precedence
-- block).
newBoundAtoms :: Int -> ST s ( BoundAtoms s t )
newBoundAtoms firstIx = do
  fwd <- newMutVar IntMap.empty
  rev <- newMutVar IntMap.empty
  pure BoundAtoms
    { firstBoundVar = firstIx
    , boundFwd      = fwd
    , boundRev      = rev
    }

-- | Get-or-create the latest-start atom @start ≤ l@ for a task, returning its
-- positive literal and whether the atom was freshly created.
--
-- A task's /upper/ bound @start ≤ lst@ is this positive literal; its /lower/
-- bound @start ≥ e@ is the /negative/ literal of the atom at threshold
-- @'estLowerToStartUpper' e@.
internStartUpper
  :: Measurable t
  => BoundAtoms s t
  -> ST s Var                    -- ^ fresh-variable allocator (the caller chooses the atom's role)
  -> Int                         -- ^ task index
  -> Endpoint ( LatestTime t )   -- ^ latest-start threshold @l@
  -> ST s ( Lit, Bool )
internStartUpper ba allocVar task thr0 = do
  -- Canonicalise the threshold's clusivity so endpoints denoting the same cut
  -- map to a single atom (see 'canonicalStartUpper').
  let thr = canonicalStartUpper thr0
  fwd <- readMutVar ( boundFwd ba )
  let perTask = IntMap.findWithDefault Map.empty task fwd
  case Map.lookup thr perTask of
    Just v  -> pure ( mkLit v Positive, False )
    Nothing -> do
      v <- allocVar
      writeMutVar   ( boundFwd ba ) ( IntMap.insert task ( Map.insert thr v perTask ) fwd )
      modifyMutVar' ( boundRev ba ) ( IntMap.insert ( varIndex v ) ( task, thr ) )
      pure ( mkLit v Positive, True )

-- | The positive literals of a task's nearest /below/ and /above/ interned
-- thresholds (strictly), for wiring monotonicity links @A_below ⟹ A_thr@ and
-- @A_thr ⟹ A_above@. Query /after/ interning @thr@ (its own entry is excluded
-- by the strict lookups).
boundNeighbours
  :: forall t s
  .  Measurable t
  => BoundAtoms s t -> Int -> Endpoint ( LatestTime t ) -> ST s ( Maybe Lit, Maybe Lit )
boundNeighbours ba task thr0 = do
  -- Always canonicalise: avoids having two different atoms for the same bound.
  let thr = canonicalStartUpper thr0
  fwd <- readMutVar ( boundFwd ba )
  let
    perTask :: Map ( Endpoint ( LatestTime t ) ) Var
    perTask  = IntMap.findWithDefault Map.empty task fwd
    toLit :: ( x, Var ) -> Lit
    toLit ( _, v ) = mkLit v Positive
  pure ( toLit <$> Map.lookupLT thr perTask
       , toLit <$> Map.lookupGT thr perTask )

-- | Whether a variable is a bound atom (i.e. lies above the fixed precedence
-- block).
isBoundVar :: BoundAtoms s t -> Var -> Bool
isBoundVar ba v = varIndex v >= firstBoundVar ba

-------------------------------------------------------------------------------
-- Decoding a trail literal.

-- | The scheduling meaning of a SAT literal drained from the trail.
data AtomMeaning t
  = -- | A precedence literal asserting @T_predecessor ≺ T_successor@.
    MeansPrecedence !Int !Int
  | -- | A latest-start bound literal on @task@ at threshold @l@, with the
    -- literal's 'Polarity': 'Positive' is @start ≤ l@, 'Negative' is
    -- @start > l@.
    MeansBound !Int !( Endpoint ( LatestTime t ) ) !Polarity

-- | Decode a trail literal into its scheduling meaning. 'Nothing' only for a
-- variable belonging to neither registry (which should not occur).
litMeaning
  :: PrecedenceAtoms
  -> BoundAtoms s t
  -> Lit
  -> ST s ( Maybe ( AtomMeaning t ) )
litMeaning ps ba lit =
  case litPrecedence ps lit of
    Just ( p, s ) -> pure ( Just ( MeansPrecedence p s ) )
    Nothing       -> do
      rev <- readMutVar ( boundRev ba )
      pure $ case IntMap.lookup ( varIndex ( litVar lit ) ) rev of
        Just ( task, thr ) -> Just ( MeansBound task thr ( litPolarity lit ) )
        Nothing            -> Nothing
