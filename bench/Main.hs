module Main ( main ) where

-- tasty
import Test.Tasty
  ( testGroup )

-- tasty-bench
import Test.Tasty.Bench
  ( defaultMain )

-- unary-scheduling bench suite
import qualified SAT.Bench      as SAT
  ( benchmarks )
import qualified Schedule.Bench as Sched
  ( benchmarks )

main :: IO ()
main = defaultMain
  [ testGroup "SAT"        SAT.benchmarks
  , testGroup "Scheduling" Sched.benchmarks
  ]
