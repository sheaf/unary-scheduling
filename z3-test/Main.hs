module Main ( main ) where

-- tasty
import Test.Tasty
  ( defaultMain )

-- unary-scheduling z3 test-suite
import qualified Schedule.Z3.Test as Z3
  ( tests )

main :: IO ()
main = defaultMain Z3.tests
