module Main ( main ) where

-- tasty
import Test.Tasty
  ( defaultMain )

-- unary-scheduling test-suite
import qualified Schedule.Test as Schedule
  ( tests )

main :: IO ()
main = defaultMain Schedule.tests
