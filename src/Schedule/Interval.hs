{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE UndecidableInstances #-}

module Schedule.Interval
  ( Clusivity(..), Endpoint(..)
  , Interval(.., (:<..<), (:<..<=), (:<=..<), (:<=..<=))
  , startTime, endTime
  , intersection
  , inside, insideLax
  , Measurable(..)
  , Intervals(..)
  , mkIntervals
  , cutBefore, cutAfter, remove, pruneShorterThan
  , intersectIntervalsWith
  ) where

-- base
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
  ( singleton, sortOn, partition, filter )

-- deepseq
import Control.DeepSeq
  ( NFData )

-- unary-scheduling
import Data.Lattice
  ( Lattice(..), BoundedLattice(..), Heyting(..), TotallyOrderedLattice(..) )
import Schedule.Time
  ( Time (..), Delta (..)
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


intersection :: Measurable t => Interval t -> Interval t -> Maybe ( Interval t )
intersection ( Interval s1 e1 ) ( Interval s2 e2 ) = do
  let
    ival = Interval ( s1 /\ s2 ) ( e1 /\ e2 )
  guard ( not $ isEmpty ival )
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
-- Measures.

class Ord t => Measurable t where
  -- | The measure of an interval.
  measure :: Interval t -> Delta t
  -- | Is an interval empty?
  isEmpty :: Interval t -> Bool


instance Measurable Double where
  measure ival = max ( Delta 0 ) $ handedTime ( startTime ival ) --> handedTime ( endTime ival )
  isEmpty ( Interval (Endpoint (EarliestTime s) s_clu) (Endpoint (LatestTime e) e_clu) )
    =  s > e
    || ( s == e && ( s_clu == Exclusive || e_clu == Exclusive ) )

instance Measurable Int where
  measure ( Interval (Endpoint (EarliestTime (Time s)) s_clu) (Endpoint (LatestTime (Time e)) e_clu) ) =
    let s' = if s_clu == Inclusive then s else s + 1
        e' = if e_clu == Inclusive then e else e - 1
    in Delta $ max 0 (e' - s' + 1)

  isEmpty ( Interval (Endpoint (EarliestTime (Time s)) s_clu) (Endpoint (LatestTime (Time e)) e_clu) ) =
    let s' = if s_clu == Inclusive then s else s + 1
        e' = if e_clu == Inclusive then e else e - 1
    in s' > e'

-------------------------------------------------------------------------------
-- Intervals.

-- | Ordered collection of non-overlapping intervals.
newtype Intervals t = Intervals { intervals :: Seq ( Interval t ) }
  deriving stock   Show
  deriving newtype ( Eq, NFData )

-- | Smart constructor for 'Intervals'.
mkIntervals :: forall t. Measurable t => Seq ( Interval t ) -> Intervals t
mkIntervals = Intervals . mergeSorted . Seq.sortOn start . Seq.filter ( not . isEmpty )
  where
    mergeSorted :: Ord t => Seq (Interval t) -> Seq (Interval t)
    mergeSorted ( Interval s1 e1 :<| Interval s2 e2 :<| ivals )
      | touchesOrOverlaps e1 s2
      = mergeSorted ( Interval s1 ( e1 \/ e2 ) :<| ivals )
      | otherwise
      = Interval s1 e1 :<| mergeSorted ( Interval s2 e2 :<| ivals )
      where
        touchesOrOverlaps :: Endpoint (LatestTime t) -> Endpoint (EarliestTime t) -> Bool
        touchesOrOverlaps
          ( Endpoint ( LatestTime   e1_t ) e1_clu )
          ( Endpoint ( EarliestTime s2_t ) s2_clu )
            = not $ isEmpty $
               Interval
                 ( Endpoint ( EarliestTime e1_t ) ( negation e1_clu ) )
                 ( Endpoint ( LatestTime   s2_t ) ( negation s2_clu ) )
    mergeSorted ivals = ivals

instance Measurable t => Lattice ( Intervals t ) where
  -- Union: concatenate, then re-sort and merge into canonical form.
  Intervals ivals1 \/ Intervals ivals2 = mkIntervals ( ivals1 <> ivals2 )
  Intervals ivals1 /\ Intervals ivals2 = Intervals ( go ivals1 ivals2 )
    where
      go :: Seq ( Interval t  ) -> Seq ( Interval t  ) -> Seq ( Interval t )
      go Empty _ = Empty
      go _ Empty = Empty
      go as@( ivalA :<| as' ) bs@( ivalB :<| bs' ) =
        let
          rest =
            case compare ( handedTime ( endTime ivalA ) ) ( handedTime ( endTime ivalB ) ) of
              LT -> go as' bs
              GT -> go as  bs'
              EQ -> go as' bs'
        in case ivalA `intersection` ivalB of
             Just ival -> ival :<| rest
             Nothing   -> rest

-- | Compute the intersection of two collections of intervals,
-- combining the values associated to the intervals using the provided combining function.
intersectIntervalsWith
  :: forall t a b c
  .  Measurable t
  => ( a -> b -> c )
  -> Seq ( Interval t, a ) -> Seq ( Interval t, b ) -> Seq ( Interval t, c )
intersectIntervalsWith f = go
  where
    go :: Seq ( Interval t, a ) -> Seq ( Interval t, b ) -> Seq ( Interval t, c )
    go Empty _ = Empty
    go _ Empty = Empty
    go as@( ( ivalA, a ) :<| as' ) bs@( ( ivalB, b ) :<| bs' ) =
      let
        rest =
          case compare ( handedTime ( endTime ivalA ) ) ( handedTime ( endTime ivalB ) ) of
            LT -> go as' bs
            GT -> go as  bs'
            EQ -> go as' bs'
      in
        case ivalA `intersection` ivalB of
          Just ival -> ( ival, f a b ) :<| rest
          Nothing   -> rest

instance ( Measurable t, Bounded t ) => BoundedLattice ( Intervals t ) where
  bottom = Intervals Empty
  top    = Intervals ( Seq.singleton $ Interval top top )

-- | Restrict availability to time not earlier than the given bound.
cutBefore :: forall t. Ord t => Endpoint ( EarliestTime t ) -> Intervals t -> Intervals t
cutBefore = coerce cutBefore'
  where
    cutBefore' :: Endpoint (Time t) -> Seq ( Interval t ) -> Seq ( Interval t )
    cutBefore' _ Empty = Empty
    cutBefore' cut@( Endpoint t clu ) full@( Interval ( Endpoint ( EarliestTime s ) s_clu ) ( Endpoint ( LatestTime e ) e_clu ) :<| ivals )
      -- Bound at or before the interval start: nothing to cut, keep it whole.
      | t < s || ( t == s && ( clu == Inclusive || s_clu == Exclusive ) )
      = full
      -- Bound strictly inside the interval: move the start up to the bound.
      | t < e
      = Interval ( Endpoint ( EarliestTime t ) clu ) ( Endpoint ( LatestTime e ) e_clu ) :<| ivals
      -- Bound on the interval end, kept on both sides: only the point @[e,e]@ survives.
      | t == e && clu == Inclusive && e_clu == Inclusive
      = Interval ( Endpoint ( EarliestTime e ) Inclusive ) ( Endpoint ( LatestTime e ) Inclusive ) :<| ivals
      -- Bound past the interval: drop it and recurse.
      | otherwise
      = cutBefore' cut ivals

-- | Restrict availability to time not later than the given bound.
cutAfter :: forall t. Ord t => Endpoint ( LatestTime t ) -> Intervals t -> Intervals t
cutAfter = coerce cutAfter'
  where
    cutAfter' :: Endpoint ( Time t ) -> Seq ( Interval t ) -> Seq ( Interval t )
    cutAfter' _ Empty = Empty
    cutAfter' cut@( Endpoint t clu ) full@( ivals :|> Interval ( Endpoint ( EarliestTime s ) s_clu ) ( Endpoint ( LatestTime e ) e_clu ) )
      -- Bound at or after the interval end: nothing to cut, keep it whole.
      | e < t || ( e == t && ( clu == Inclusive || e_clu == Exclusive ) )
      = full
      -- Bound strictly inside the interval: move the end down to the bound.
      | s < t
      = ivals :|> Interval ( Endpoint ( EarliestTime s ) s_clu ) ( Endpoint ( LatestTime t ) clu )
      -- Bound on the interval start, kept on both sides: only the point @[s,s]@ survives.
      | t == s && clu == Inclusive && s_clu == Inclusive
      = ivals :|> Interval ( Endpoint ( EarliestTime s ) Inclusive ) ( Endpoint ( LatestTime s ) Inclusive )
      -- Bound before the interval: drop it and recurse.
      | otherwise
      = cutAfter' cut ivals

remove :: forall t. Ord t => Intervals t -> Interval t -> Intervals t
remove = coerce remove'
  where
    remove' :: Seq ( Interval t ) -> Interval t -> Seq ( Interval t )
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
pruneShorterThan :: forall t. ( Num t, Measurable t ) => Delta t -> Intervals t -> Maybe ( Intervals t, Intervals t )
pruneShorterThan = coerce pruneShorterThan'
  where
    pruneShorterThan' :: Delta t -> Seq ( Interval t ) -> Maybe ( Seq ( Interval t ), Seq ( Interval t ) )
    pruneShorterThan' delta ivals
      | null removed = Nothing
      | otherwise    = Just ( kept, removed )
      where
        ( kept, removed ) = Seq.partition longEnough ivals
        longEnough :: Interval t -> Bool
        longEnough ival = measure ival >= delta
