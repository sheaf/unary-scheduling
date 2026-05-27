module Main ( main ) where

-- tasty-bench
import Test.Tasty.Bench
  ( defaultMain )

-- unary-scheduling bench suite
import qualified SAT.Bench as SAT
  ( benchmarks )

main :: IO ()
main = defaultMain SAT.benchmarks
