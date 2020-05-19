{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE UndecidableInstances       #-}

module Schedule.Interval
  ( Clusivity(..), Endpoint(..)
  , Interval(.., (:<..<), (:<..<=), (:<=..<), (:<=..<=))
  , validInterval
  , startTime, endTime, duration
  , intersection
  , inside, insideLax
  , Intervals(..)
  , cutBefore, cutAfter, remove, pruneShorterThan
  ) where

-- base
import Control.Arrow
  ( first )
import Control.Category
  ( (>>>) )
import Control.Monad
  ( guard )
import Data.Coerce
  ( coerce )
import Data.Semigroup
  ( Arg(..) )
import GHC.Generics
  ( Generic )

-- acts
import Data.Act
  ( Act((•)), Torsor((-->)) )

-- containers
import Data.Sequence
  ( Seq
    ( Empty, (:<|), (:|>) )
  )
import qualified Data.Sequence as Seq
  ( singleton, sortOn )

-- deepseq
import Control.DeepSeq
  ( NFData )

-- unary-scheduling
import Data.Lattice
  ( Lattice(..), BoundedLattice(..), Heyting(..), TotallyOrderedLattice(..) )
import Schedule.Time
  ( Time, Delta
  , HandedTime(..), EarliestTime, LatestTime
  )

-------------------------------------------------------------------------------
-- Endpoints.

data Clusivity
  = Exclusive
  | Inclusive
  deriving stock    ( Show, Eq, Ord, Generic )
  deriving anyclass NFData

instance Lattice Clusivity where
  Exclusive /\ _   = Exclusive
  _         /\ clu = clu
  Inclusive \/ _   = Inclusive
  _         \/ clu = clu
instance BoundedLattice Clusivity where
  bottom = Exclusive
  top    = Inclusive
instance Heyting Clusivity where
  Exclusive ==> _   = Inclusive
  _         ==> clu = clu
  negation Exclusive = Inclusive
  negation Inclusive = Exclusive

data Endpoint t
  = Endpoint
    { endpoint  :: !t
    , clusivity :: !Clusivity
    }
  deriving stock    ( Show, Eq, Generic )
  deriving anyclass NFData

instance Ord t => Ord ( Endpoint ( EarliestTime t ) ) where
  compare ( Endpoint t1 clu1 ) ( Endpoint t2 clu2 ) =
    case compare t1 t2 of
      EQ -> compare clu2 clu1 -- flipped
      un -> un

instance Ord t => Ord ( Endpoint ( LatestTime t ) ) where
  compare ( Endpoint t1 clu1 ) ( Endpoint t2 clu2 ) =
    case compare t1 t2 of
      EQ -> compare clu1 clu2 -- not flipped
      un -> un

instance Act s t => Act s ( Endpoint t ) where
  s • Endpoint t clu = Endpoint ( s • t ) clu

instance Ord t => Lattice ( Endpoint ( EarliestTime t ) ) where
  -- Minimum.
  Endpoint t1 clu1 \/ Endpoint t2 clu2 = case compare t1 t2 of
    EQ -> Endpoint t1 ( clu1 \/ clu2 )
    LT -> Endpoint t1 clu1
    GT -> Endpoint t2 clu2
  -- Maximum.
  Endpoint t1 clu1 /\ Endpoint t2 clu2 = case compare t1 t2 of
    EQ -> Endpoint t1 ( clu1 /\ clu2 )
    LT -> Endpoint t2 clu2
    GT -> Endpoint t1 clu1

instance Ord t => Lattice ( Endpoint ( LatestTime t ) ) where
  -- Maximum.
  Endpoint t1 clu1 \/ Endpoint t2 clu2 = case compare t1 t2 of
    EQ -> Endpoint t1 ( clu1 \/ clu2 )
    LT -> Endpoint t2 clu2
    GT -> Endpoint t1 clu1
  -- Minimum.
  Endpoint t1 clu1 /\ Endpoint t2 clu2 = case compare t1 t2 of
    EQ -> Endpoint t1 ( clu1 /\ clu2 )
    LT -> Endpoint t1 clu1
    GT -> Endpoint t2 clu2

instance ( Ord t, Bounded t ) => BoundedLattice ( Endpoint ( EarliestTime t ) ) where
  bottom = Endpoint maxBound Exclusive
  top    = Endpoint minBound Inclusive
instance ( Ord t, Bounded t ) => BoundedLattice ( Endpoint ( LatestTime t ) ) where
  bottom = Endpoint minBound Exclusive
  top    = Endpoint maxBound Inclusive

instance Ord t => TotallyOrderedLattice ( Endpoint ( EarliestTime t ) ) where
  -- Minimum.
  e1@(Arg ( Endpoint t1 clu1 ) _) \./ e2@(Arg ( Endpoint t2 clu2 ) _) = case compare t1 t2 of
    GT -> e2
    EQ
      | Exclusive <- clu1
      , Inclusive <- clu2
      -> e2
    _ -> e1
  -- Maximum.
  e1@(Arg ( Endpoint t1 clu1 ) _) /.\ e2@(Arg ( Endpoint t2 clu2 ) _) = case compare t1 t2 of
    GT -> e1
    EQ
      | Exclusive <- clu1
      , Inclusive <- clu2
      -> e1
    _ -> e2

instance Ord t => TotallyOrderedLattice ( Endpoint ( LatestTime t ) ) where
  -- Maximum.
  e1@(Arg ( Endpoint t1 clu1 ) _) \./ e2@(Arg ( Endpoint t2 clu2 ) _) = case compare t1 t2 of
    LT -> e2
    EQ
      | Exclusive <- clu1
      , Inclusive <- clu2
      -> e2
    _ -> e1
  -- Minimum.
  e1@(Arg ( Endpoint t1 clu1 ) _) /.\ e2@(Arg ( Endpoint t2 clu2 ) _) = case compare t1 t2 of
    LT -> e1
    EQ
      | Exclusive <- clu1
      , Inclusive <- clu2
      -> e1
    _ -> e2

-------------------------------------------------------------------------------
-- Intervals.

-- | Non-empty interval.
data Interval t
  = Interval
  { start :: !(Endpoint (EarliestTime t))
  , end   :: !(Endpoint (  LatestTime t))
  }
  deriving stock    ( Show, Eq, Generic )
  deriving anyclass NFData

{-# COMPLETE (:<..<), (:<=..<), (:<..<=), (:<=..<=) #-}
pattern (:<..<), (:<=..<), (:<..<=), (:<=..<=) :: Time t -> Time t -> Interval t
pattern (:<..<)   s e = Interval ( Endpoint ( EarliestTime s ) Exclusive ) ( Endpoint ( LatestTime e ) Exclusive )
pattern (:<=..<)  s e = Interval ( Endpoint ( EarliestTime s ) Inclusive ) ( Endpoint ( LatestTime e ) Exclusive )
pattern (:<..<=)  s e = Interval ( Endpoint ( EarliestTime s ) Exclusive ) ( Endpoint ( LatestTime e ) Inclusive )
pattern (:<=..<=) s e = Interval ( Endpoint ( EarliestTime s ) Inclusive ) ( Endpoint ( LatestTime e ) Inclusive )

startTime :: Interval t -> EarliestTime t
startTime = start >>> endpoint

endTime :: Interval t -> LatestTime t
endTime = end >>> endpoint

duration :: Num t => Interval t -> Delta t
duration ( Interval ( Endpoint ( EarliestTime s ) _ ) ( Endpoint ( LatestTime e ) _ ) ) = s --> e

validInterval :: Ord t => Interval t -> Bool
validInterval ( Interval ( Endpoint ( EarliestTime s ) s_clu ) ( Endpoint ( LatestTime e ) e_clu ) ) =
  case compare s e of
    LT -> True
    EQ 
      | Inclusive <- s_clu
      , Inclusive <- e_clu
      -> True
    _ -> False

intersection :: Ord t => Interval t -> Interval t -> Maybe ( Interval t )
intersection ( Interval s1 e1 ) ( Interval s2 e2 ) = do
  let
    ival = Interval ( s1 /\ s2 ) ( e1 /\ e2 )
  guard ( validInterval ival )
  pure ival

inside :: forall t. Ord t => Time t -> Intervals t -> Bool
inside = coerce inside'
  where
    inside' :: Time t -> Seq ( Interval t ) -> Bool
    inside' _ Empty = False
    inside' t ( Interval ( Endpoint ( EarliestTime s ) s_clu ) ( Endpoint ( LatestTime e ) e_clu ) :<| ivals )
      = case compare t s of
          LT -> False
          EQ -> s_clu == Inclusive
          GT -> case compare t e of
            LT -> True
            EQ -> e_clu == Inclusive
            GT -> t `inside'` ivals

-- | Like 'inside', but assumes endpoints are always included.
insideLax :: forall t. Ord t => Time t -> Intervals t -> Bool
insideLax = coerce insideLax'
  where
    insideLax' :: Time t -> Seq ( Interval t ) -> Bool
    insideLax' _ Empty = False
    insideLax' t ( Interval ( Endpoint ( EarliestTime s ) _ ) ( Endpoint ( LatestTime e ) _ ) :<| ivals )
      = case compare t s of
          LT -> False
          EQ -> True
          GT -> case compare t e of
            GT -> t `insideLax'` ivals
            _ -> True

-------------------------------------------------------------------------------
-- Intervals.

-- | Ordered collection of non-overlapping intervals.
newtype Intervals t = Intervals { intervals :: Seq (Interval t) }
  deriving stock   Show
  deriving newtype ( Eq, NFData )

instance Ord t => Lattice ( Intervals t ) where
  Intervals ivals1 \/ Intervals ivals2 = Intervals ( merge ( Seq.sortOn start ( ivals1 <> ivals2 ) ) )
    where
      merge :: Seq (Interval t) -> Seq (Interval t)
      merge ( Interval s1 e1 :<| Interval s2 e2 :<| ivals )
        | validInterval ( Interval s2 e1 )
        = merge ( Interval s1 e2 :<| ivals )
        | otherwise
        = Interval s1 e1 :<| merge ( Interval s2 e2 :<| ivals )
      merge ivals = ivals
  Intervals ivals1 /\ Intervals ivals2 = Intervals ( go ivals1 ivals2 )
    where
      go :: Seq (Interval t) -> Seq (Interval t) -> Seq (Interval t)
      go Empty _ = Empty
      go ( ival :<| ivals ) others = go' ival others <> go ivals others
      go' :: Interval t -> Seq (Interval t) -> Seq (Interval t)
      go' _ Empty = Empty
      go' ival ( other :<| others )
        | handedTime ( endTime ival ) < handedTime ( startTime other )
        = Empty
        | Just inter <- ival `intersection` other
        = inter :<| go' ival others
        | otherwise
        = go' ival others

instance ( Ord t, Bounded t ) => BoundedLattice ( Intervals t ) where
  bottom = Intervals Empty
  top    = Intervals ( Seq.singleton $ Interval top top )

cutBefore :: forall t. Ord t => Endpoint (EarliestTime t) -> Intervals t -> Intervals t
cutBefore = coerce cutBefore'
  where
    cutBefore' :: Endpoint (Time t) -> Seq (Interval t) -> Seq (Interval t)
    cutBefore' _ Empty = Empty
    cutBefore' cut@( Endpoint t clu ) full@( Interval ( Endpoint ( EarliestTime s ) s_clu ) ( Endpoint ( LatestTime e ) e_clu ) :<| ivals )
      | t < s || ( t == s && ( clu == Exclusive || s_clu == Exclusive ) )
      = full
      | t < e
      = Interval ( Endpoint ( EarliestTime t ) ( negation clu ) ) ( Endpoint ( LatestTime e ) e_clu ) :<| ivals
      | t == e && clu == Exclusive && e_clu == Inclusive
      = Interval ( Endpoint ( EarliestTime e ) Inclusive ) ( Endpoint ( LatestTime e ) Inclusive ) :<| ivals
      | otherwise
      = cutBefore' cut ivals

cutAfter :: forall t. Ord t => Endpoint (LatestTime t) -> Intervals t -> Intervals t
cutAfter = coerce cutAfter'
  where 
    cutAfter' :: Endpoint (Time t) -> Seq (Interval t) -> Seq (Interval t)
    cutAfter' _ Empty = Empty
    cutAfter' cut@( Endpoint t clu ) full@( ivals :|> Interval ( Endpoint ( EarliestTime s ) s_clu ) ( Endpoint ( LatestTime e ) e_clu ) )
      | e < t || ( e == t && ( clu == Exclusive || e_clu == Exclusive ) )
      = full
      | s < t
      = ivals :|> Interval ( Endpoint ( EarliestTime s ) s_clu ) ( Endpoint ( LatestTime t ) ( negation clu ) )
      | s == e && clu == Exclusive && s_clu == Inclusive
      = ivals :|> Interval ( Endpoint ( EarliestTime s ) Inclusive ) ( Endpoint ( LatestTime s ) Inclusive )
      | otherwise
      = cutAfter' cut ivals

remove :: forall t. Ord t => Intervals t -> Interval t -> Intervals t
remove = coerce remove'
  where
    remove' :: Seq (Interval t) -> Interval t -> Seq (Interval t)
    remove' Empty _ = Empty
    remove'
      full@( ival@( Interval ( Endpoint ( EarliestTime s ) s_clu ) ( Endpoint ( LatestTime e ) e_clu ) ) :<| ivals )
      cut@( Interval ( Endpoint ( EarliestTime cut_s ) cut_s_clu ) ( Endpoint ( LatestTime cut_e ) cut_e_clu ) )
        -- Cut ends before start of given intervals: nothing to remove.
        | cut_e < s || ( cut_e == s && ( s_clu == Exclusive || cut_e_clu == Exclusive ) )
        = full
        -- Cut starts after end of current interval: leave current interval alone, recurse onto next intervals.
        | cut_s > e || ( cut_s == e && ( e_clu == Exclusive || cut_s_clu == Exclusive ) )
        = ival :<| ivals `remove'` cut
        -- Cut ends before end of current interval: cut current interval, leave the rest alone.
        | cut_e < e || ( cut_e == e && ( e_clu == Inclusive && cut_e_clu == Exclusive ) )
        = if cut_s < s || ( cut_s == s && ( s_clu == Exclusive || cut_s_clu == Inclusive ) )
          -- Cut starts before start of current interval: only keep the end part of the current interval.
          then Interval ( Endpoint ( EarliestTime cut_e ) ( negation cut_e_clu ) ) ( Endpoint ( LatestTime e ) e_clu )
           :<| ivals
          -- Cut starts after start of current interval: remove middle part of interval.
          else Interval ( Endpoint ( EarliestTime s ) s_clu ) ( Endpoint ( LatestTime cut_s ) ( negation cut_s_clu ) )
           :<| Interval ( Endpoint ( EarliestTime cut_e ) ( negation cut_e_clu ) ) ( Endpoint ( LatestTime e ) e_clu )
           :<| ivals
        -- Cut ends after end of current interval: cut current interval, recurse onto next intervals.
        | otherwise
        = if cut_s < s || ( cut_s == s && ( s_clu == Exclusive || cut_s_clu == Inclusive ) )
          -- Cut starts before start of current interval: current interval entirely removed.
          then ivals `remove'` cut
          -- Cut starts after start of current interval: only keep the beginning part of the current interval.
          else Interval ( Endpoint ( EarliestTime s ) s_clu ) ( Endpoint ( LatestTime cut_s ) ( negation cut_s_clu ) )
           :<| ivals `remove'` cut

-- | Prunes away intervals shorter than specified amount.
--
--   - Returns `Nothing` when no pruning was necessary.
--   - When pruning was necessary, returns ( kept, removed ),
--     where `kept` are the kept intervals (longer than the given amount),
--     and `removed` are the intervals that were pruned away.
pruneShorterThan :: forall t. ( Num t, Ord t ) => Delta t -> Intervals t -> Maybe ( Intervals t, Intervals t )
pruneShorterThan = coerce pruneShorterThan'
  where
    pruneShorterThan' :: Delta t -> Seq (Interval t) -> Maybe ( Seq (Interval t), Seq (Interval t) )
    pruneShorterThan' _ Empty = Nothing
    pruneShorterThan' delta ( ival@( Interval ( Endpoint ( EarliestTime s ) _ ) ( Endpoint ( LatestTime e ) _ ) ) :<| ivals )
      | ( s --> e ) < delta
      = Just ( mempty, Seq.singleton ival )  <> pruneShorterThan' delta ivals
      | otherwise
      = ( first ( Seq.singleton ival <> ) ) <$> pruneShorterThan' delta ivals
