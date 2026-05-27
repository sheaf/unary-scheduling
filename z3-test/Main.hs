module Main ( main ) where

-- tasty
import Test.Tasty
  ( defaultMain, testGroup )

-- unary-scheduling z3 test-suite
import qualified SAT.Test as SAT
  ( tests )
import qualified Schedule.Z3.Test as Z3
  ( tests )

main :: IO ()
main = defaultMain $ testGroup "z3-differential"
  [ SAT.tests
  , Z3.tests
  ]
