module Main ( main ) where

-- code-page
import System.IO.CodePage
  ( withCP65001 )

-- tasty
import Test.Tasty
  ( defaultMain, testGroup )

-- unary-scheduling
import qualified SAT.Test as SAT
  ( tests )
import qualified Schedule.Z3.Test as Z3
  ( tests )

--------------------------------------------------------------------------------

main :: IO ()
main = withCP65001 $ defaultMain $ testGroup "z3-differential"
  [ SAT.tests
  , Z3.tests
  ]
