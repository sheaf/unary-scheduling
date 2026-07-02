module Main ( main ) where

-- code-page
import System.IO.CodePage
  ( withCP65001 )

-- tasty
import Test.Tasty
  ( defaultMain )

-- unary-scheduling
import qualified SAT.Test as SAT
  ( tests )

--------------------------------------------------------------------------------

main :: IO ()
main = withCP65001 $ defaultMain SAT.tests
