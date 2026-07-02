module Main ( main ) where

-- code-page
import System.IO.CodePage
  ( withCP65001 )

-- tasty
import Test.Tasty
  ( defaultMain )

-- unary-scheduling
import qualified Schedule.Z3.Test as Z3
  ( tests )

--------------------------------------------------------------------------------

main :: IO ()
main = withCP65001 $ defaultMain Z3.tests
