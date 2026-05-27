-- | Luby restart schedule.
--
-- Reference: Luby, Sinclair, Zuckerman (1993),
-- /Optimal Speedup of Las Vegas Algorithms/.
module SAT.Restart
  ( luby )
  where

-- base
import Data.Bits
  ( shiftL )

-------------------------------------------------------------------------------

-- | The @n@-th term (one-based) of the Luby sequence:
-- @1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, ...@.
luby :: Int -> Int
luby = go 1
  where
    go :: Int -> Int -> Int
    go !k !i
      | i == p2k - 1 = p2k1
      | i <  p2k - 1 = go 1 ( i - p2k1 + 1 )
      | otherwise    = go ( k + 1 ) i
      where
        p2k, p2k1 :: Int
        p2k  = 1 `shiftL` k
        p2k1 = 1 `shiftL` ( k - 1 )
