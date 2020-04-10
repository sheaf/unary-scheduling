module Main where

-- transformers
import Control.Monad.Trans.Except
  ( runExceptT )

-- unary-scheduling
import Schedule.Spreadsheet
  ( scheduleSpreadsheet )

main :: IO ()
main = do
  res <- runExceptT scheduleSpreadsheet
  case res of
    Left err -> error ( show err )
    _        -> pure ()
