{-# LANGUAGE PatternSynonyms #-}

{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE NamedWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Data.Sequence.Insert
  ( insertIntoSorted )
  where

-- containers
import Data.Sequence
  ( Seq(..) )
import qualified Data.Sequence as Seq
  ( singleton, length, splitAt )

{-
-- fingertree
import Data.FingerTree
  ( FingerTree, split )
-}

-------------------------------------------------------------------------------

-- | Insert an element into a sorted (non-decreasing) sequence.
insertIntoSorted :: Ord a => a -> Seq a -> Seq a
insertIntoSorted a Empty = Seq.singleton a
insertIntoSorted a ( b :<| Empty )
  | a > b
  = b :<| a :<| Empty
  | otherwise
  = a :<| b :<| Empty
insertIntoSorted a as = case Seq.splitAt ( 1 + Seq.length as `div` 2 ) as of
  ( xs :|> pivot, ys ) -> case compare a pivot of
    EQ -> ( xs :|> a :|> pivot ) <> ys
    LT -> ( insertIntoSorted a xs :|> pivot ) <> ys
    GT -> ( xs :|> pivot ) <> insertIntoSorted a ys
  ( Empty, ys ) -> insertIntoSorted a ys