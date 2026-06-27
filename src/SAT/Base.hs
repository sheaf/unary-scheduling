{-# LANGUAGE PatternSynonyms      #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Propositional variables, literals, and three-valued booleans.
module SAT.Base
  ( -- * Variables
    Var(..), varIndex
    -- * Polarity
  , Polarity( Positive, Negative )
  , negatePolarity
  , polarityValue
    -- * Literals
  , Lit(..), litIndex
  , mkLit
  , litVar
  , litPolarity
  , negateLit
  , LitOfValue(SatisfiedLit, FalsifiedLit, ..)
  , SatisfiedLit, FalsifiedLit
  , negateLitOfValue
    -- * Three-valued booleans
  , LBool(LUndef, LTrue, LFalse)
  , liftBool
  , lnot
  , litValueFromVar
  )
  where

-- base
import Data.Bits
  ( shiftL, shiftR, xor, (.|.), (.&.) )
import Data.Int
  ( Int32 )
import Data.Kind
  ( Type )
import Data.Type.Bool
  ( Not )
import Data.Word
  ( Word8 )
import GHC.Generics
  ( Generic )

-- bitvec
import Data.Bit
  ( Bit(..) )

-- deepseq
import Control.DeepSeq
  ( NFData )

-- primitive
import Data.Primitive
  ( Prim )

-- vector
import qualified Data.Vector.Generic as Generic
  ( Vector )
import qualified Data.Vector.Generic.Mutable as Generic
  ( MVector )
import qualified Data.Vector.Unboxed as Vector
  ( Unbox )
import qualified Data.Vector.Unboxed as Unboxed
  ( Vector )
import qualified Data.Vector.Unboxed.Mutable as Unboxed
  ( MVector )

-------------------------------------------------------------------------------
-- Variables.

-- | A propositional variable, identified by its 0-based index.
newtype Var = Var Int32
  deriving stock   ( Eq, Ord, Show, Generic )
  deriving newtype ( NFData, Prim )

varIndex :: Var -> Int
varIndex ( Var v ) = fromIntegral v
{-# INLINE varIndex #-}

-------------------------------------------------------------------------------
-- Polarity.

-- | The sign of a literal: whether the variable appears as-is ('Positive')
-- or negated ('Negative').
newtype Polarity = Polarity Bit
  deriving stock   Generic
  deriving newtype ( Eq, Ord, NFData )

newtype instance Unboxed.MVector s Polarity = MVPolarity ( Unboxed.MVector s Bit )
newtype instance Unboxed.Vector    Polarity = VPolarity  ( Unboxed.Vector    Bit )
deriving newtype instance Generic.MVector Unboxed.MVector Polarity
deriving newtype instance Generic.Vector  Unboxed.Vector  Polarity
deriving newtype instance Vector.Unbox Polarity

pattern Positive, Negative :: Polarity
pattern Positive = Polarity ( Bit True )
pattern Negative = Polarity ( Bit False )
{-# COMPLETE Positive, Negative #-}

instance Show Polarity where
  show Positive = "Positive"
  show Negative = "Negative"

negatePolarity :: Polarity -> Polarity
negatePolarity Positive = Negative
negatePolarity Negative = Positive

-- | The lifted-boolean value a variable takes when a literal of this
-- polarity is enqueued true.
polarityValue :: Polarity -> LBool
polarityValue Positive = LTrue
polarityValue Negative = LFalse

-------------------------------------------------------------------------------
-- Literals.

-- | A signed propositional variable. Build with 'mkLit'.
newtype Lit = Lit Int32
  deriving stock   ( Eq, Ord, Show, Generic )
  deriving newtype ( NFData, Prim )

-- | The literal's nonnegative integer key, in the range  @[0, 2 * numVars)@.
litIndex :: Lit -> Int
litIndex ( Lit i ) = fromIntegral i

newtype instance Unboxed.MVector s Lit = MVLit ( Unboxed.MVector s Int32 )
newtype instance Unboxed.Vector    Lit = VLit  ( Unboxed.Vector    Int32 )
deriving newtype instance Generic.MVector Unboxed.MVector Lit
deriving newtype instance Generic.Vector  Unboxed.Vector  Lit
deriving newtype instance Vector.Unbox Lit

mkLit :: Var -> Polarity -> Lit
mkLit ( Var v ) Positive = Lit ( v `shiftL` 1 )
mkLit ( Var v ) Negative = Lit ( ( v `shiftL` 1 ) .|. 1 )

litVar :: Lit -> Var
litVar ( Lit l ) = Var ( l `shiftR` 1 )

litPolarity :: Lit -> Polarity
litPolarity ( Lit l )
  | ( l .&. 1 ) == 0 = Positive
  | otherwise        = Negative

negateLit :: Lit -> Lit
negateLit ( Lit l ) = Lit ( l `xor` 1 )

-- | A literal of the given value under the current assignment.
type LitOfValue :: Bool -> Type
newtype LitOfValue v =
  LitOfValue { underlyingLit :: Lit }
    deriving newtype ( Eq, Ord, Show )

-- | A satisfied literal, e.g. the antecedent of an inference.
type SatisfiedLit = LitOfValue True

-- | A falsified literal, e.g. a member of a conflicting or reason clause.
type FalsifiedLit = LitOfValue False

pattern SatisfiedLit :: Lit -> SatisfiedLit
pattern SatisfiedLit a = LitOfValue a
{-# COMPLETE SatisfiedLit #-}

pattern FalsifiedLit :: Lit -> FalsifiedLit
pattern FalsifiedLit a = LitOfValue a
{-# COMPLETE FalsifiedLit #-}

negateLitOfValue :: LitOfValue v -> LitOfValue ( Not v )
negateLitOfValue ( LitOfValue l ) = LitOfValue $ negateLit l

-------------------------------------------------------------------------------
-- Three-valued booleans.

-- | The lifted boolean domain @ { undef, true, false } @.
newtype LBool = LBool Word8
  deriving stock   ( Eq, Generic )
  deriving newtype NFData

pattern LUndef, LTrue, LFalse :: LBool
pattern LUndef = LBool 0
pattern LTrue  = LBool 1
pattern LFalse = LBool 2
{-# COMPLETE LUndef, LTrue, LFalse #-}

newtype instance Unboxed.MVector s LBool = MVLBool ( Unboxed.MVector s Word8 )
newtype instance Unboxed.Vector    LBool = VLBool  ( Unboxed.Vector    Word8 )
deriving newtype instance Generic.MVector Unboxed.MVector LBool
deriving newtype instance Generic.Vector  Unboxed.Vector  LBool
deriving newtype instance Vector.Unbox LBool

instance Show LBool where
  show LUndef = "undef"
  show LTrue  = "true"
  show LFalse = "false"

liftBool :: Bool -> LBool
liftBool True  = LTrue
liftBool False = LFalse

lnot :: LBool -> LBool
lnot LUndef = LUndef
lnot LTrue  = LFalse
lnot LFalse = LTrue

-- | The value of a literal given the lifted value of its variable.
litValueFromVar :: Lit -> LBool -> LBool
litValueFromVar l vb =
  case litPolarity l of
    Positive -> vb
    Negative -> lnot vb
