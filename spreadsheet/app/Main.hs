module Main where

-- code-page
import System.IO.CodePage
  ( withCP65001 )

-- transformers
import Control.Monad.Trans.Except
  ( runExceptT )

-- unary-scheduling
import Schedule.Spreadsheet
  ( scheduleSpreadsheet, handleError )

-------------------------------------------------------------------------------

main :: IO ()
main = withCP65001 $ do
  res <- runExceptT scheduleSpreadsheet
  case res of
    Left err -> handleError err
    _        -> pure ()
