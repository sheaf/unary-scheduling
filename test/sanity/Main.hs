module Main ( main ) where

-- code-page
import System.IO.CodePage
  ( withCP65001 )

-- tasty
import Test.Tasty
  ( defaultMain )

-- unary-scheduling
import qualified Schedule.Test as Schedule
  ( tests )

--------------------------------------------------------------------------------

main :: IO ()
main = withCP65001 $ defaultMain Schedule.tests
