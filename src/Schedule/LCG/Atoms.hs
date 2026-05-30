{-# LANGUAGE ScopedTypeVariables #-}

-- | Atom registry for the LCG encoding.
--
-- Two families of SAT atoms share one variable space:
--
--   * /precedence atoms/ ('PrecedenceAtoms'): a fixed, contiguous block, one
--     variable per unordered task pair @{i, j}@ (the literal asserts
--     @T_i ≺ T_j@). These are the only /decision/ variables.
--
--   * /bound atoms/ ('BoundAtoms'): lazily-created auxiliary variables
--     reifying each task's start-time bounds. Two separate families avoid any
--     clusivity clash between the earliest- and latest-time conventions:
--
--       - a /lower-bound/ atom @(task, e)@ whose positive literal means
--         @start_task ≥ e@ (@e@ an 'EarliestTime' endpoint);
--       - an /upper-bound/ atom @(task, l)@ whose positive literal means
--         @start_task ≤ l@ (@l@ a 'LatestTime' endpoint, i.e. a latest start).
--
--     Atoms are allocated on demand (we never enumerate the time horizon) and
--     laid out /after/ the fixed precedence block, so a variable index alone
--     classifies the atom family.
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
  , internLowerBound, internUpperBound
  , isBoundVar
    -- * Decoding a trail literal
  , BoundThreshold(..)
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
  ( empty, insert, lookup )

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
  ( Endpoint )
import Schedule.Ordering
  ( upperTriangular )
import Schedule.Time
  ( EarliestTime, LatestTime )

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

-- | A start-time bound reified as a bound atom: the positive literal of the
-- atom asserts this bound.
data BoundThreshold t
  = -- | Lower bound: @start ≥ e@.
    LowerThreshold !( Endpoint ( EarliestTime t ) )
  | -- | Upper bound: @start ≤ l@ (a latest start).
    UpperThreshold !( Endpoint ( LatestTime t ) )

-- | Lazily-grown registry of start-time bound atoms.
--
-- Lower- and upper-bound atoms are kept in separate forward maps so that the
-- earliest- and latest-time clusivity conventions never clash (in particular,
-- a zero-slack task's coincident lower and upper bounds get distinct atoms).
-- Variables are allocated /after/ the fixed precedence block (variable index
-- @≥ firstBoundVar@), so 'isBoundVar' and 'isPrecedenceVar' classify any
-- variable in O(1).
data BoundAtoms s t = BoundAtoms
  { -- | First variable index reserved for bound atoms (one past the last
    -- precedence atom). Bound variables have index @≥ firstBoundVar@.
    firstBoundVar :: !Int
  , -- | Lower-bound atoms: per task, the created earliest-start thresholds and
    -- their variables (positive literal: @start ≥ e@).
    boundLowerFwd :: !( MutVar s ( IntMap ( Map ( Endpoint ( EarliestTime t ) ) Var ) ) )
  , -- | Upper-bound atoms: per task, the created latest-start thresholds and
    -- their variables (positive literal: @start ≤ l@).
    boundUpperFwd :: !( MutVar s ( IntMap ( Map ( Endpoint ( LatestTime t ) ) Var ) ) )
  , -- | Reverse map: variable index → @(task, threshold)@, for decoding a
    -- drained trail literal.
    boundRev      :: !( MutVar s ( IntMap ( Int, BoundThreshold t ) ) )
  }

-- | Allocate an empty bound-atom registry. @firstBoundVar@ is the variable
-- index one past the last precedence atom (i.e. 'numAtoms' of the precedence
-- block).
newBoundAtoms :: Int -> ST s ( BoundAtoms s t )
newBoundAtoms firstIx = do
  lo  <- newMutVar IntMap.empty
  hi  <- newMutVar IntMap.empty
  rev <- newMutVar IntMap.empty
  pure BoundAtoms
    { firstBoundVar = firstIx
    , boundLowerFwd = lo
    , boundUpperFwd = hi
    , boundRev      = rev
    }

-- | Get-or-create the lower-bound atom @start ≥ e@ for a task, returning its
-- positive literal and whether the atom was freshly created.
internLowerBound
  :: Ord t
  => BoundAtoms s t
  -> ST s Var                    -- ^ fresh auxiliary (non-decision) variable allocator
  -> Int                         -- ^ task index
  -> Endpoint ( EarliestTime t ) -- ^ earliest-start threshold @e@
  -> ST s ( Lit, Bool )
internLowerBound ba =
  internWith ( boundLowerFwd ba ) ( boundRev ba ) LowerThreshold

-- | Get-or-create the upper-bound atom @start ≤ l@ for a task, returning its
-- positive literal and whether the atom was freshly created.
internUpperBound
  :: Ord t
  => BoundAtoms s t
  -> ST s Var                    -- ^ fresh auxiliary (non-decision) variable allocator
  -> Int                         -- ^ task index
  -> Endpoint ( LatestTime t )   -- ^ latest-start threshold @l@
  -> ST s ( Lit, Bool )
internUpperBound ba =
  internWith ( boundUpperFwd ba ) ( boundRev ba ) UpperThreshold

-- | Shared get-or-create over one bound-atom family.
internWith
  :: Ord k
  => MutVar s ( IntMap ( Map k Var ) )
  -> MutVar s ( IntMap ( Int, BoundThreshold t ) )
  -> ( k -> BoundThreshold t )   -- ^ how to record this threshold in the reverse map
  -> ST s Var
  -> Int
  -> k
  -> ST s ( Lit, Bool )
internWith fwdRef revRef mkThreshold allocVar task thr = do
  fwd <- readMutVar fwdRef
  let perTask = IntMap.findWithDefault Map.empty task fwd
  case Map.lookup thr perTask of
    Just v  -> pure ( mkLit v Positive, False )
    Nothing -> do
      v <- allocVar
      writeMutVar   fwdRef ( IntMap.insert task ( Map.insert thr v perTask ) fwd )
      modifyMutVar' revRef ( IntMap.insert ( varIndex v ) ( task, mkThreshold thr ) )
      pure ( mkLit v Positive, True )

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
  | -- | A bound literal on @task@ at the given threshold, with the literal's
    -- 'Polarity'. With a 'LowerThreshold' @e@: 'Positive' is @start ≥ e@,
    -- 'Negative' is @start < e@. With an 'UpperThreshold' @l@: 'Positive' is
    -- @start ≤ l@, 'Negative' is @start > l@.
    MeansBound !Int !( BoundThreshold t ) !Polarity

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
