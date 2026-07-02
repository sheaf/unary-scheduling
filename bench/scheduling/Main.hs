module Main ( main ) where

-- code-page
import System.IO.CodePage
  ( withCP65001 )

-- tasty
import Test.Tasty
  ( testGroup )

-- tasty-bench
import Test.Tasty.Bench
  ( defaultMain )

-- unary-scheduling bench suite
import qualified Schedule.Bench as Sched
  ( benchmarks )

--------------------------------------------------------------------------------

main :: IO ()
main = withCP65001 $
  defaultMain [ testGroup "Scheduling" Sched.benchmarks ]
