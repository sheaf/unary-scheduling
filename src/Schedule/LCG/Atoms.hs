{-# LANGUAGE ScopedTypeVariables #-}

-- | Precedence-atom registry: a bijection between the unordered task pairs
-- @{i, j}@ of a fixed task set and a contiguous block of SAT variables.
module Schedule.LCG.Atoms
  ( -- * Registry
    PrecedenceAtoms
  , mkPrecedenceAtoms
  , numTasks
  , numAtoms
    -- * Encoding: directed pair → literal
  , precLit
    -- * Decoding: literal → directed pair
  , litPrecedence
    -- * Membership
  , isPrecedenceVar
  )
  where

-- base
import Data.Bits
  ( shiftR )

-- vector
import qualified Data.Vector.Unboxed as Unboxed
  ( Vector, fromListN, length, (!) )

-- unary-scheduling
import SAT.Base
  ( Var(..), varIndex
  , Lit, litVar, litPolarity
  , mkLit, Polarity(..)
  )
import Schedule.Ordering
  ( upperTriangular )

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
