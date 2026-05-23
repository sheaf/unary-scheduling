{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingVia                #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE NamedFieldPuns             #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE ViewPatterns               #-}

module Schedule.Contention where

-- base
import Data.Coerce
  ( coerce )
import Data.Foldable
  ( fold, foldl' )
import Data.Monoid
  ( Sum(..) )
import Data.Semigroup
  ( Arg(..), Max(..), ArgMax )
import GHC.Generics
  ( Generic )

-- acts
import Data.Act
  ( Act((•)), Torsor((-->)) )

-- containers
import Data.Map.Strict
  ( Map )
import qualified Data.Map.Strict as Map
  ( singleton, fromAscList
  , insert, unionWith
  , foldMapWithKey
  )
import Data.Sequence
  ( Seq )
import qualified Data.Sequence as Seq
  ( fromList )

-- deepseq
import Control.DeepSeq
  ( NFData )

-- fingertree
import Data.FingerTree
  ( FingerTree, Measured(..)
  , ViewL(..), ViewR(..)
  , viewl, viewr, (<|), (|>)
  )
import qualified Data.FingerTree as FingerTree
  ( split, fmap', null, empty )

-- generic-data
import Generic.Data
  ( GenericProduct(..) )

-- generic-lens
import Data.GenericLens.Internal
  ( over )
import Data.Generics.Product.Fields
  ( field, field' )

-- groups
import Data.Group
  ( Group(invert) )

-- unary-scheduling
import Data.Lattice
  ( Lattice((\/)) )
import Schedule.Interval
  ( Clusivity(..), Endpoint(..)
  , Interval(..), startTime, endTime
  , Intervals(..)
  , intersection, intersectIntervalsWith
  )
import Schedule.Task
  ( Task(..) )
import Schedule.Time
  ( Time, EarliestTime, LatestTime
  , Delta(..), HandedTime(..)
  )

-------------------------------------------------------------------------------

pattern Empty :: Measured v a => FingerTree v a
pattern Empty <- ( FingerTree.null -> True )
  where Empty = FingerTree.empty

infixr 5 :<|
pattern (:<|) :: Measured v a => a -> FingerTree v a -> FingerTree v a
pattern x :<| xs <- ( viewl -> x :< xs )
  where x :<| xs = x <| xs
{-# COMPLETE Empty, (:<|) #-}

infixl 5 :|>
pattern (:|>) :: Measured v a => FingerTree v a -> a -> FingerTree v a
pattern xs :|> x <- ( viewr -> xs :> x )
  where xs :|> x = xs |> x
{-# COMPLETE Empty, (:|>) #-}

-------------------------------------------------------------------------------

-- | Joint contention criticality estimate,
-- under the assumption that no precedence information
-- between the two tasks is known.
--
-- This is a piecewise-quadratic function, the product
-- of the tasks' individual piecewise-linear contention functions.
jointContention :: ( Num t, Real t , Ord t ) => Task task t -> Task task t -> Seq ( Interval t, Quadratic t )
jointContention tk1 tk2
  = intersectIntervalsWith multiplyLinear ( taskContention tk1 ) ( taskContention tk2 )

-- | Computes the piecewise linear contention function for a single task.
taskContention
  :: forall task t
  .  ( Num t, Real t, Ord t )
  => Task task t -> Seq ( Interval t, Linear t )
taskContention ( Task { taskAvailability = Intervals ivals, taskDuration = dur } ) = undefined {-
  fmap ( \ ( Delta t ) -> realToFrac t / realToFrac totalArea ) controlPoints
  where
    totalArea     :: t
    controlPoints :: Map ( Time t ) ( Delta t )
    ( Delta totalArea, controlPoints ) =
      foldl'
        ( \ ( totArea, totPoints ) ival ->
          let
            ( area, points ) = intervalContention dur ival
          in
          ( totArea <> area, Map.unionWith (<>) totPoints points )
        )
        mempty ivals
-}


data LinearPiece
  = Down
  | Flat
  | Up
  deriving stock Show

-- | Compute a single task's contribution to contention on a unary resource,
-- assuming start times are uniformly distributed within the provided interval.
--
-- This is a piecewise function in the shape of a tent.
intervalContention
  :: forall t
  .  ( Num t, Ord t )
  => Delta t
  -> Interval t
  -> ( Delta t, Seq ( Interval t, LinearPiece ) )
intervalContention dur ( Interval sp ep ) = case compare dur lg of
  LT -> ( invert dur <> lg
        , Seq.fromList
          [ ( Interval              sp              ( coerce $ dur • sp ), Up   )
          , ( Interval         ( dur • sp )          ( invert dur • ep ) , Flat )
          , ( Interval ( coerce $ invert dur • ep )          ep          , Down )
          ]
        )
  EQ
    | Inclusive <- clusivity sp \/ clusivity ep
    ->  ( mempty
        , Seq.fromList
          [ ( Interval              sp              ( coerce $ dur • sp ), Up   )
          , ( Interval ( coerce $ invert dur • ep )          ep          , Down )
          ]
        )
  _ -> mempty
  where
    lg :: Delta t
    lg = handedTime ( endpoint sp ) --> handedTime ( endpoint ep )

data Piece t f =
  Piece
    { pieceStart    :: !t
    , pieceEnd      :: !t
    , pieceFunction :: !f
    }
  deriving stock    ( Show, Generic )
  deriving anyclass NFData
  deriving ( Semigroup, Monoid )
    via GenericProduct ( Piece t f )

-- | Pieces in a piecewise representation.
--
-- Leaves hold individual summands @ Piece t ( Map i f ) @
--   - @t@ is the time domain,
--   - @f@ is the function domain (e.g. linear piece, quadratic piece, etc),
--   - @Map i f@ represents the summands giving rise to the function on this piece.
--
-- Nodes hold:
--   - the maximum start and end points over all their descendants,
--     useful in the finger tree structure to quickly zoom into given time domains,
--   - the maximum value of all the pieces below, together with their origin
--     @ ArgMax d ( t, i ) @
--     Here:
--       - @d@ represents the value domain (the value being maximised),
--       - @t@ represents the time domain (the time at which the maximum is achieved),
--       - @i@ records the index of the summand contributing the most to contention
--         at the maximum point.
type Pieces i t d f
  = FingerTree
      ( Piece ( Max t ) ( ArgMax d ( t, i ) ) )
      ( Piece       t   ( Map i f )           )

-- | Resource contention function with piecewise representation.
--
-- Invariants of the piecewise representation:
--  - the pieces have disjoint interiors,
--  - the pieces are sorted in increasing order.
newtype Contention i t f d = Contention { contentionPieces :: Pieces i t d f }
  deriving stock Show

-- | Coefficients for a linear function @ f(x) = a x + b @.
data Linear t
  = Linear
  { a :: !t
  , b :: !t
  }
  deriving stock    ( Show, Eq, Ord, Generic )
  deriving anyclass NFData
  deriving ( Semigroup, Monoid )
    via GenericProduct ( Linear ( Sum t ) )

-- | Coefficients for a quadratic function @ f(x) = a₂x² + a₁x + a₀ @.
data Quadratic t
  = Quadratic
  { a2 :: !t
  , a1 :: !t
  , a0 :: !t
  }
  deriving stock    ( Show, Eq, Ord, Generic )
  deriving anyclass NFData
  deriving ( Semigroup, Monoid )
    via GenericProduct ( Quadratic ( Sum t ) )

multiplyLinear :: Num t => Linear t -> Linear t -> Quadratic t
multiplyLinear ( Linear { a, b } ) ( Linear { a = a', b = b' } )
  = Quadratic
  { a0 = b * b'
  , a1 = a * b' + a' * b
  , a2 = a * a'
  }

evalQuadratic :: Num t => Quadratic t -> t -> t
evalQuadratic ( Quadratic { a2, a1, a0 } ) t = a0 + t * ( a1 + t * a2 )

class Maximisable t f d | t f -> d where
  maximise :: Bounded ( Arg t i ) => Piece t ( Map i f ) -> ArgMax d ( t, i )

instance ( Ord t, Fractional t ) => Maximisable t ( Quadratic t ) t where
  maximise :: forall i. Bounded ( Arg t i ) => Piece t ( Map i ( Quadratic t ) ) -> ArgMax t ( t, i )
  maximise ( Piece { pieceFunction = summands, pieceStart = t0, pieceEnd = t1 } )
    | a2 == 0
    = if a1 >= 0
      then maximumAt ( Arg ( a0 + a1 * t1 ) t1 )
      else maximumAt ( Arg ( a0 + a1 * t0 ) t0 )
    | otherwise
    = maximumAt
      $ maximum
        [ Arg    ( evalQuadratic p t0 )            t0
        , Arg    ( evalQuadratic p t1 )            t1
        , Arg ( a0 - 0.25 * a1 * a1 / a2 ) ( - 0.5 * a1 / a2 )
        ]
    where
      a0, a1, a2 :: t
      p@( Quadratic { a2, a1, a0 } ) = fold summands
      maximumAt :: Arg t t -> ArgMax t ( t, i )
      maximumAt ( Arg m x ) = Max ( Arg m ( x, i ) )
        where
          i :: i
          Max ( Arg _ i ) =
            Map.foldMapWithKey ( \ k q -> Max ( Arg ( evalQuadratic q x ) k ) ) summands

instance
     ( Ord t, Ord d, Ord i
     , Bounded t, Bounded ( Arg t i ), Bounded ( Arg d ( t, i ) )
     , Maximisable t f d
     )
  => Measured ( Piece ( Max t ) ( ArgMax d ( t, i ) ) ) ( Piece t ( Map i f ) ) where
  measure pc@( Piece { pieceStart = s, pieceEnd = e } )
    = Piece { pieceStart = Max s, pieceEnd = Max e, pieceFunction = maximise pc }

fmapPieces :: Measured v ( Piece t f ) => ( f -> f ) -> FingerTree v ( Piece t f ) -> FingerTree v ( Piece t f )
fmapPieces upd = FingerTree.fmap' ( over ( field' @"pieceFunction" ) upd )

addContentionPiece
  :: forall i t f d
  .  ( Ord t, Ord d, Ord i
     , Bounded t, Bounded d
     , Bounded ( Arg t i ), Bounded ( Arg d ( t, i ) )
     , Maximisable t f d
     , Monoid f
     )
  => i -> Piece t f -> Contention i t f d -> Contention i t f d
addContentionPiece
  pieceNumber
  piece@( Piece { pieceStart = start, pieceEnd = end, pieceFunction = f } )
  ( Contention { contentionPieces = ps } )
  = Contention { contentionPieces = qs }
  where
    addedPiece :: Piece t ( Map i f )
    addedPiece = over ( field @"pieceFunction" ) ( Map.singleton pieceNumber ) piece
    qs :: Pieces i t d f
    -- Start by sorting the pre-existing pieces into two, based on whether they end before or after the start of the piece we are adding.
    qs = case FingerTree.split ( \ ( Piece { pieceEnd = Max otherEnd } ) -> otherEnd >= start ) ps of
      ( endBefore, endAfter ) -> case endAfter of
        Empty
        -- The start of the piece we are adding occurs after all other pieces: add it at the end.
          -> ps :|> addedPiece
        ( pc@( Piece { pieceStart = nextStart } ) :<| nextEndAfters )
        -- The start of the piece we are adding occurs outside of all pre-existing piece:
        --  - add a new interval starting from the new start point,
        --  - update other intervals that occur within the updated piece.
          | nextStart > start
          ->
            if nextStart >= end
            -- None of the pieces overlap with the piece we are adding: simply add the piece.
            then ( endBefore :|>   addedPiece                            ) <>             endAfter
            -- Some pieces overlap with the piece we are adding: add the non-overlapping part, and then update the overlapping pieces.
            else ( endBefore :|> ( addedPiece { pieceEnd = nextStart } ) ) <> addUntilEnd endAfter
        -- The piece we are adding starts inside an existing piece:
        --  - split up this interval,
        --  - update other intervals that occur within the updated piece.
          | otherwise
          -> ( endBefore :|> pc { pieceEnd = start } ) <> addUntilEnd ( pc { pieceStart = start } :<| nextEndAfters )
    -- Update all the intervals in the fingertree to add a piece, up until the end of the piece being added.
    addUntilEnd :: Pieces i t d f -> Pieces i t d f
    addUntilEnd os = case FingerTree.split ( \ ( Piece { pieceStart = Max otherStart } ) -> otherStart >= end ) os of
      ( startBefore, startAfter ) -> case startBefore of
        -- None of the remaining pieces start before the end of the piece we are updating: nothing left to do.
        Empty
          -> os
        ( previousStartBefores :|> pc@( Piece { pieceEnd = previousEnd } ) )
        -- The end of the piece we are adding occurs outside existing pieces:
        --   - update the previous intervals,
        --   - add a new interval ending at the new endpoint.
          | previousEnd < end
          ->
            (   fmapPieces ( Map.insert pieceNumber f ) previousStartBefores
            :|> addedPiece { pieceStart = previousEnd }
            )
            <> startAfter
          | otherwise
        -- The piece we are adding ends inside an existing piece:
        --  - update the intervals up until the end,
        --  - split up the interval at the end.
          ->
            (   fmapPieces ( Map.insert pieceNumber f ) ( previousStartBefores :|> pc { pieceEnd = end } )
            :|> pc { pieceStart = end }
            )
            <> startAfter
