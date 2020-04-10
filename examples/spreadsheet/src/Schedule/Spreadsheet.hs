{-# LANGUAGE BlockArguments             #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns             #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE TypeApplications           #-}

module Schedule.Spreadsheet
  ( scheduleSpreadsheet, handleError )
  where

-- base
import Control.Applicative
  ( liftA2 )
import Control.Monad
  ( when, unless )
import qualified Data.Char as Char
  ( chr, ord
  , toUpper
  , isLetter, isDigit, isAscii, isAlphaNum
  )
import Data.Coerce
  ( coerce )
import Data.Either
  ( rights )
import Data.Foldable
  ( for_ )
import Data.Functor
  ( (<&>) )
import Data.Traversable
  ( for )
import qualified Numeric
  ( readInt )
import System.Environment
  ( getArgs, getProgName )
import System.Exit
  ( ExitCode(..), exitWith, exitSuccess )
import System.IO
  ( hPutStrLn, stderr )

-- ansi-wl-pprint
import qualified Text.PrettyPrint.ANSI.Leijen as Pretty
  ( Doc
  , linebreak, hardline, indent, hang
  )

-- bytestring
import qualified Data.ByteString.Lazy as LazyByteString
  ( readFile, writeFile )

-- containers
import Data.Map.Strict
  ( Map )
import qualified Data.Map.Strict as Map
  ( lookup, mapWithKey )
import Data.Set
  ( Set )
import qualified Data.Set as Set
  ( fromList )
import Data.Sequence
  ( Seq(..) )

-- directory
import qualified System.Directory as Directory
  ( doesFileExist )

-- filepath
import System.FilePath
  ( (-<.>) )

-- generic-lens
import Data.Generics.Product.Fields
  ( field' )
import Data.Generics.Product.Typed
  ( typed )

-- lens
import Control.Lens
  ( Traversal'
  , view, over
  )
import Control.Lens.At
  ( ix )

-- mtl
import Control.Monad.Except
  ( liftEither )

-- optparse-applicative
import qualified Options.Applicative as OptParse
  ( execParserPure, execCompletion, renderFailure
  , ParserResult(..), CompletionResult(..)
  , Parser, ParserInfo(..), ParserPrefs(..)
  , strOption, switch, helper
  , long, short, metavar, value, help
  )
import qualified Options.Applicative.Help.Chunk as OptParse
  ( Chunk(Chunk) )
import qualified Options.Applicative.Types as OptParse
  ( Backtracking(Backtrack), ArgPolicy(Intersperse) )

-- text
import Data.Text
  ( Text )
import qualified Data.Text as Text
  ( pack, unpack
  , replicate
  , span, all, null
  , dropWhile, dropWhileEnd
  , strip, split
  )
import qualified Data.Text.IO as Text
  ( appendFile, hPutStrLn )

-- time
import qualified Data.Time.Clock.POSIX as Time
  ( getPOSIXTime, posixSecondsToUTCTime )
import qualified Data.Time.Format as Time
  ( formatTime, defaultTimeLocale)

-- transformers
import Control.Monad.Trans.Class
  ( lift )
import Control.Monad.Trans.Except
  ( ExceptT(..), Except
  , runExcept, withExceptT, throwE
  )

-- vector
import qualified Data.Vector as Boxed
  ( Vector )
import qualified Data.Vector as Boxed.Vector
  ( fromList, (!) )

-- xlsx
import qualified Codec.Xlsx as Xlsx
  ( Xlsx(..), Worksheet(..)
  , Cell(..), CellValue(..)
  , CellFormula(..), FormulaExpression(..), Formula(..)
  , ParseError(..)
  , toXlsxEither, fromXlsx
  )

-- unary-scheduling
import Data.Lattice
  ( Meet(..) )
import Schedule
  ( propagateConstraints, allPropagators )
import Schedule.Interval
  ( Interval((:<=..<=)), Intervals(..)
  , inside
  )
import Schedule.Task
  ( Task(..), Tasks(taskInfos), TaskInfos(tasks) )
import Schedule.Time
  ( Delta(..), Time(..) )

-------------------------------------------------------------------------------

-- | Read scheduling data from a spreadsheet file,
-- compute updated availabilities, and write them to an output spreadsheet file.
--
-- See the documentation for 'parseSpreadSheet' for details on
-- the expected format of the input spreadsheet.
scheduleSpreadsheet :: ExceptT Error IO ()
scheduleSpreadsheet = do

  -- Get command line arguments: input/output spreadsheet file paths,
  -- and whether to perform constraint propoagation (if so, include filepath for logging).
  Args { inputSpreadsheetPath, outputSpreadsheetPath, constraintLoggingPath } <- parseArgs
  currentPosixTime <- lift Time.getPOSIXTime
  let
    formattedTime :: String
    formattedTime = Time.formatTime Time.defaultTimeLocale "%0Y-%m-%d-%H-%M-%S" ( Time.posixSecondsToUTCTime currentPosixTime )

  -- Read input spreadsheet.
  let
    inputPath, outputPath :: FilePath
    inputPath  =  inputSpreadsheetPath -<.> "xlsx"
    outputPath = outputSpreadsheetPath -<.> "xlsx"
  inputExists <- lift $ Directory.doesFileExist inputPath
  unless inputExists do
    throwE ( MissingFile inputPath )
  spreadsheet <- withExceptT XlsxParseError . ExceptT
               $ Xlsx.toXlsxEither <$> LazyByteString.readFile inputPath

  -- Parse spreadsheet data.
  SchedulingData { schedulingTasks, schedulingRanges } <- liftEither $ parseSpreadsheet spreadsheet

  -- Perform constraint propagation (if enabled).
  newTaskData <- case constraintLoggingPath of
    Nothing ->
      pure ( Boxed.Vector.fromList $ map fst schedulingTasks )
    Just justificationsPath -> do
      -- Propagate constraints using unary scheduling algorithms.
      let
        ( newTasks, justifications, mbError ) = propagateConstraints ( Left schedulingTasks ) 100 allPropagators
      -- Log constraint propagation information.
      lift $ Text.appendFile justificationsPath
        ( "\n" <> Text.replicate 25 "-" <> "\n" <>
        "-- " <> Text.pack formattedTime <> " --\n" <>
        Text.replicate 25 "-" <> "\n\n-------\n" <>
        "Input:  " <> Text.pack inputPath <> "\n" <>
        "Output: " <> Text.pack outputPath <> "\n-------\n\n" <>
        justifications
        )
      -- Throw an error if scheduling has been found to be impossible.
      for_ mbError \ err -> throwE ( NoSchedulingPossible err )
      pure ( tasks $ taskInfos newTasks )

  -- Write output spreadsheet with updated availability information.
  let
    outputData = Xlsx.fromXlsx currentPosixTime ( updateSpreadsheet schedulingRanges newTaskData spreadsheet )
  lift $ LazyByteString.writeFile outputPath outputData

-------------------------------------------------------------------------------

-- | Combined monolithic error type for the application.
data Error
  = NoSchedulingPossible Text            -- ^ Constraint solving has established that no solution exists.
  | XlsxParseError  Xlsx.ParseError      -- ^ Could not read spreadsheet (parsing error thrown by the @xlsx@ library).
  | SheetParseError Text                 -- ^ Could not parse the necessary scheduling information from the spreadsheet.
  | MissingFile FilePath                 -- ^ Missing input spreadsheet file.
  | ArgsError String                     -- ^ Error parsing command line arguments.
  | Completion OptParse.CompletionResult -- ^ Command line completion.
  deriving stock Show

handleError :: Error -> IO ()
handleError ( NoSchedulingPossible reason ) = do
  Text.hPutStrLn stderr ( "No scheduling possible:\n" <> reason )
  exitSuccess
handleError ( XlsxParseError err ) = do
  hPutStrLn stderr ( "Could not parse spreadsheet :\n" <> show err )
  exitWith ( ExitFailure 2 )
handleError ( SheetParseError err ) = do
  hPutStrLn stderr ( "Could not parse scheduling data from spreadsheet." )
  Text.hPutStrLn stderr err
  exitWith ( ExitFailure 3 )
handleError ( MissingFile filePath ) = do
  hPutStrLn stderr ( "Missing file: " <> filePath )
  exitWith ( ExitFailure 4 )
handleError ( ArgsError msg ) = do
  hPutStrLn stderr msg
  exitWith ( ExitFailure 5 )
handleError ( Completion compl ) = do
  progName <- getProgName
  msg <- OptParse.execCompletion compl progName
  putStr msg
  exitSuccess

-- | Record of expected command line arguments.
data Args
  = Args
  { inputSpreadsheetPath  :: !FilePath
  , outputSpreadsheetPath :: !FilePath
  , constraintLoggingPath :: !(Maybe FilePath)
  }
  deriving stock Show

-- | Spreadsheet row/column ranges in which to find staff/task/availabilities.
--
-- Expects all ranges to be contiguous.
data SchedulingRanges
  = SchedulingRanges
  { firstStaffRow       :: !Int
  , lastStaffRow        :: !Int
  , firstTaskRow        :: !Int
  , lastTaskRow         :: !Int
  , firstScheduleColumn :: !Int
  , lastScheduleColumn  :: !Int
  }
  deriving stock Show

-- | All the information needed to run the scheduling algorithms:
--
-- - staff availabilities,
-- - availabilities of each task, and staff assigned to that task
-- - spreadsheet ranges, giving us the info of where to write the result to the spreadsheet.
data SchedulingData
  = SchedulingData
  { schedulingStaff  :: !(Boxed.Vector ( Intervals Column ))
  , schedulingTasks  :: ![ ( Task (Set Staff) Column, Text ) ]
  , schedulingRanges :: !SchedulingRanges
  }
  deriving stock Show

newtype Staff = Staff { staffID :: Int }
  deriving stock   Show
  deriving newtype ( Eq, Ord )

newtype Column = Column { getColumn :: Int }
  deriving newtype ( Eq, Ord, Enum, Bounded, Num )
-- Bijective base 26 system.
instance Show Column where
  show ( Column { getColumn = c } )
    | c <= 0          = "-oo"
    | c >  1000000000 = "+oo"
    | otherwise
    = reverse $ go ( ( c - 1 ) `divMod` 26 )
    where
      go :: ( Int, Int ) -> String
      go ( tens, ones )
        | tens < 1  = [ units ]
        | otherwise = units : go ( ( tens - 1 ) `divMod` 26 )
        where
          units :: Char
          units = Char.chr ( ones + Char.ord 'A' )

-------------------------------------------------------------------------------

note :: Monad m => e -> Maybe a -> ExceptT e m a
note _ ( Just a ) = pure a
note e _          = throwE e

-- | Parse command line arguments: filename of input and output spreadsheets,
-- and whether to perform constraint propagation (if so, provide a filename for logging output).
parseArgs :: ExceptT Error IO Args
parseArgs = do
  args <- lift getArgs
  case OptParse.execParserPure parserPrefs parserInfo args of
    OptParse.Success res -> pure res
    OptParse.CompletionInvoked compl -> throwE ( Completion compl )
    OptParse.Failure err -> do
      progName <- lift getProgName
      let
        ( msg, _ ) = OptParse.renderFailure err progName
      throwE ( ArgsError msg )

  where
    header, desc, usageInfo :: Pretty.Doc
    header = "schedule-spreadsheet - propagate unary scheduling constraints read from a spreadsheet"
    desc = "Computes up to date scheduling constraints read from a spreadsheet"
    usageInfo =
      "The scheduling information is expected to be provided within the spreadsheet in the following manner:"
      <> Pretty.linebreak
      <> Pretty.linebreak <>
        ( Pretty.indent 2
          ( "Range information, in the form of a formula pointing to another cell:"
          <> Pretty.linebreak <>
            ( Pretty.indent 2
              (  Pretty.hang 2 "- in cells B1 & C1: point to first and last cells of tasks to be scheduled (range of rows),"
              <> Pretty.linebreak
              <> Pretty.hang 2 "- in cells B2 & C2: point to first and last cells of staff to be assigned to the tasks (range of rows),"
              <> Pretty.linebreak
              <> Pretty.hang 2 "- in cells B3 & C3: point to first and last cells of available time slots (range of columns)."
              <> Pretty.linebreak
              )
            ) <> Pretty.hardline <>
            "Information for each task, in the same row as the task:"
            <> Pretty.linebreak <>
            ( Pretty.indent 2
              (  Pretty.hang 2
                  ( "- column A: staff assigned to the task in the row, in the form of a formula " <> Pretty.linebreak
                  <> Pretty.indent 4 "TEXTJOIN( delimiter, ignore_empty, staff_cell_1, staff_cell_2, ..., staff_cell_n )"
                  )
              <> Pretty.linebreak
              <> Pretty.hang 2 "- column B: duration of the task, in number of columns,"
              <> Pretty.linebreak
              <> Pretty.hang 2 "- for each scheduling column: availability value."
              <> Pretty.linebreak
              )
            ) <> Pretty.hardline <>
            "Availability values for staff, for the available time columns, in each of the staff member rows."
            <> Pretty.hardline
            <> Pretty.hardline <>
            "Availability for staff and tasks is specified as follows:" <> Pretty.hardline <>
              ( Pretty.indent 2
                (  Pretty.hang 2 "- an unavailable time slot corresponds to a cell value of 0,"
                <> Pretty.linebreak
                <> Pretty.hang 2 "- an available time slot is a cell with any other value."
                )
              )
           )
         )

    parserPrefs :: OptParse.ParserPrefs
    parserPrefs = OptParse.ParserPrefs
      { OptParse.prefMultiSuffix     = ""
      , OptParse.prefDisambiguate    = True
      , OptParse.prefShowHelpOnError = True
      , OptParse.prefShowHelpOnEmpty = False
      , OptParse.prefBacktrack       = OptParse.Backtrack
      , OptParse.prefColumns         = 80
      , OptParse.prefHelpLongEquals  = False
      }

    parserInfo :: OptParse.ParserInfo Args
    parserInfo = OptParse.ParserInfo
      { OptParse.infoParser      = OptParse.helper <*> ( Args <$> inputArg <*> outputArg <*> logArg )
      , OptParse.infoFullDesc    = True
      , OptParse.infoProgDesc    = OptParse.Chunk ( Just desc )
      , OptParse.infoHeader      = OptParse.Chunk ( Just header )
      , OptParse.infoFooter      = OptParse.Chunk ( Just usageInfo )
      , OptParse.infoFailureCode = 255
      , OptParse.infoPolicy      = OptParse.Intersperse
      }

    inputArg :: OptParse.Parser FilePath
    inputArg =
      OptParse.strOption
        (  OptParse.long "input"
        <> OptParse.short 'i'
        <> OptParse.metavar "INPUTFILE"
        <> OptParse.value "input.xlsx"
        <> OptParse.help "Read scheduling data from XLSX spreadsheet INPUTFILE"
        )

    outputArg :: OptParse.Parser FilePath
    outputArg =
      OptParse.strOption
        (  OptParse.long "output"
        <> OptParse.short 'o'
        <> OptParse.metavar "OUTPUTFILE"
        <> OptParse.value "output.xlsx"
        <> OptParse.help "Write scheduling data to XLSX spreadsheet OUTPUTFILE"
        )

    logArg :: OptParse.Parser ( Maybe FilePath )
    logArg =  ( \ b fp -> if b then Nothing else Just fp )
          <$> OptParse.switch
                (  OptParse.long "noprop"
                <> OptParse.help "Disable constraint propagation"
                )
          <*> OptParse.strOption
                (  OptParse.long "log"
                <> OptParse.short 'l'
                <> OptParse.metavar "LOGFILE"
                <> OptParse.value "log.txt"
                <> OptParse.help "Log constraint solving information to LOGFILE"
                )

-- | Parse a spreadsheet into scheduling information.
--
-- The following metadata is expected to be found in the spreadsheet:
--
--  - cells B1 & C1: first and last cells of tasks to be scheduled (range of rows),
--  - cells B2 & C2: first and last cells of staff to be assigned to the tasks (range of rows),
--  - cells B3 & C3: first and last cells of available time slots (range of columns).
--
-- For the range of rows containing tasks, the following task information must appear in columns A and B:
--
--  - column A: staff assigned to the task in the row, in the form of a formula
--    @TEXTJOIN( delimiter, ignore_empty, cell_1, cell_2, ..., cell_n )@,
--    where @cell_1@, ..., @cell_n@ refer to cells corresponding to the staff needed for the task,
--  - column B: duration of the task, in number of columns.
--
-- The availability information in the spreadsheet is specified as follows:
--
--  - unavailable time slots (either for tasks or for staff) should be indicated
--    by the corresponding cell containing the value @0@,
--  - available time slots can be left blank.
parseSpreadsheet :: Xlsx.Xlsx -> Either Error SchedulingData
parseSpreadsheet spreadsheet = runExcept do
  let
    cells :: Map ( Int, Int ) Xlsx.Cell
    cells = view _cells spreadsheet
  when ( null cells ) do
    throwE ( SheetParseError "No cell data found in spreadsheet" )

  -- Parse the ranges telling us:
  --   - the rows containing tasks,
  --   - the rows containing staff,
  --   - the columns containing available scheduling slots.
  schedulingRanges@( SchedulingRanges{ .. } ) <- parseRanges cells

  -- Parse the staff availabilities.
  let
    schedulingStaff :: Boxed.Vector ( Intervals Column )
    schedulingStaff
      =   Boxed.Vector.fromList
      $ [ firstStaffRow .. lastStaffRow ] <&> \ staffRow ->
        parseAvailability firstScheduleColumn lastScheduleColumn staffRow cells

  -- Parse the task availabilities, combining task availability info with availability of the staff affected to each task.
  schedulingTasks <- for [ firstTaskRow .. lastTaskRow ] \ taskRow -> do
    let
      givenAvailability :: Intervals Column
      givenAvailability = parseAvailability firstScheduleColumn lastScheduleColumn taskRow cells
      taskCellLocation :: ( Int, Int )
      taskCellLocation = ( taskRow, 1 )
    taskStaffCell
      <- note ( SheetParseError $ "Missing cell data at " <> location taskCellLocation <> ": expected to find staff allocated to the task in that row." )
       $ Map.lookup ( taskRow, 1 ) cells
    taskStaffIDs <- parseTaskStaffIDs taskRow firstStaffRow lastStaffRow taskStaffCell
    let
      taskAvailability :: Intervals Column
      taskAvailability
        = getMeet
        $ Meet givenAvailability
        <> ( foldMap ( \ ( Staff { staffID } ) -> Meet $ schedulingStaff Boxed.Vector.! staffID ) taskStaffIDs )
      taskNameLocation :: ( Int, Int )
      taskNameLocation = ( taskRow, 3 )
      taskDurationLocation :: ( Int, Int )
      taskDurationLocation = ( taskRow, 2 )
    taskName     <- parseTaskName     taskNameLocation     cells
    taskDuration <- parseTaskDuration taskDurationLocation cells
    pure ( Task { taskAvailability, taskDuration, taskInfo = taskStaffIDs }, taskName )

  -- Return the above info.
  pure ( SchedulingData { schedulingStaff, schedulingTasks, schedulingRanges } )


-- | Parse ranges for scheduling:
--
--  - cells B1 & C1: first and last cells of tasks to be scheduled (range of rows),
--  - cells B2 & C2: first and last cells of staff to be assigned to the tasks (range of rows),
--  - cells B3 & C3: first and last cells of available time slots (range of columns).
parseRanges :: Map ( Int, Int ) Xlsx.Cell -> Except Error SchedulingRanges
parseRanges cells = do
  firstStaffRow       <- fst <$> parseLocationFromCellFormulaAt "first staff row"           (2,2) cells
  lastStaffRow        <- fst <$> parseLocationFromCellFormulaAt "last staff row"            (2,3) cells
  firstTaskRow        <- fst <$> parseLocationFromCellFormulaAt "first task row"            (1,2) cells
  lastTaskRow         <- fst <$> parseLocationFromCellFormulaAt "last task row"             (1,3) cells
  firstScheduleColumn <- snd <$> parseLocationFromCellFormulaAt "first availability column" (3,2) cells
  lastScheduleColumn  <- snd <$> parseLocationFromCellFormulaAt "last availability column"  (3,3) cells
  pure ( SchedulingRanges { .. } )

-- | Pattern synonym for a cell containing a simple textual formula.
pattern SimpleFormulaCell :: Text -> Xlsx.Cell
pattern SimpleFormulaCell formula <-
  ( Xlsx.Cell
    { Xlsx._cellFormula =
      Just ( Xlsx.CellFormula { Xlsx._cellfExpression = Xlsx.NormalFormula ( Xlsx.Formula formula ) } )
    }
  )

-- | Obtains the location a cell is pointing at, in the case that the cell is pointing at a single other cell.
--
-- This corresponds to a spreadsheet formula of the form @=AB7@ (for instance).
parseLocationFromCellFormulaAt :: Text -> ( Int, Int ) -> Map (Int, Int) Xlsx.Cell -> Except Error ( Int, Int )
parseLocationFromCellFormulaAt desc loc cells = do
  cell <- note ( SheetParseError $ "Could not parse " <> desc <> " from cell formula: no cell at " <> location loc )
        $ Map.lookup loc cells
  case cell of
    SimpleFormulaCell formula
      -> parseLocation formula
    _ -> throwE ( SheetParseError $ "Could not parse " <> desc <> " from cell " <> location loc <> ":\n\
                                    \cell does not appear to contain a simple formula referring to a single other cell."
                )

-- | Parse an alphanumeric cell reference into a numeric @(row, column)@ pair.
--
-- > parseLocation "C1" = pure ( 1, 3 )
parseLocation :: Text -> Except Error ( Int, Int )
parseLocation loc = do
  let
    ( letters, rest ) = Text.span ( liftA2 (&&) Char.isLetter Char.isAscii ) ( Text.strip loc )
  unless ( Text.all Char.isDigit rest && not ( Text.null rest ) ) do
    throwE ( SheetParseError $ "Could not parse row number from '" <> loc <> "'." )
  let
    letterValue :: Char -> Int
    letterValue c = 1 + Char.ord ( Char.toUpper c ) - Char.ord 'A'
    row = read $ Text.unpack rest
  col <- case Numeric.readInt 26 ( const True ) letterValue $ Text.unpack letters of
    [ ( col', _ ) ] -> pure col'
    _ -> throwE ( SheetParseError $ "Could not parse column number from '" <> loc <> "'." )
  pure ( row, col )

-- | Display a numeric cell location pair @(row, column)@ as an alphanumeric reference.
--
-- > location ( 1, 3 ) = "C1"
location :: ( Int, Int ) -> Text
location ( r, c ) = Text.pack ( show $ Column c ) <> Text.pack ( show r )

-- | Parse the availability in a given row, as read off from the spreadsheet cells.
parseAvailability :: Int -> Int -> Int -> Map ( Int, Int ) Xlsx.Cell -> Intervals Column
parseAvailability firstCol lastCol row cells = Intervals $ go Empty firstCol
  where
    go :: Seq ( Interval Column ) -> Int -> Seq ( Interval Column )
    go ivals col
      | Just i <- nextAvailableColumn row lastCol cells col
      , let j = lastAvailableColumnAfter row lastCol cells i
      = go ( ivals :|> ( coerce i :<=..<= coerce j ) ) ( j + 1 )
      | otherwise
      = ivals

-- | Returns the next available column in the given row, starting from the given column (inclusive).
nextAvailableColumn :: Int -> Int -> Map ( Int, Int ) Xlsx.Cell -> Int -> Maybe Int
nextAvailableColumn _   lastCol _ col 
  | col > lastCol
  = Nothing
nextAvailableColumn row lastCol cells col = case Map.lookup ( row, col ) cells of
  Just cell -> case Xlsx._cellValue cell of
    Just ( Xlsx.CellDouble 0 ) -> nextAvailableColumn row lastCol cells ( col + 1 )
    _                          -> Just col
  _ -> nextAvailableColumn row lastCol cells ( col + 1 )

-- | Returns the last available column in the given row, starting from the given column.
lastAvailableColumnAfter :: Int -> Int -> Map ( Int, Int ) Xlsx.Cell -> Int -> Int
lastAvailableColumnAfter _   lastCol _ prevAvailCol
  | prevAvailCol >= lastCol
  = prevAvailCol
lastAvailableColumnAfter row lastCol cells prevAvailCol = case Map.lookup ( row, prevAvailCol + 1 ) cells of
  Just cell 
    | Just ( Xlsx.CellDouble 0 ) <- Xlsx._cellValue cell
    -> prevAvailCol
  _ -> lastAvailableColumnAfter row lastCol cells ( prevAvailCol + 1 )

-- | Obtain the staff IDs of the staff allocated to a given task.
--
-- These are numbered from @0@ (can be used as indices into the staff vector).
parseTaskStaffIDs :: Int -> Int -> Int -> Xlsx.Cell -> Except Error ( Set Staff )
parseTaskStaffIDs taskRow firstRow lastRow ( SimpleFormulaCell formula ) = do
  let 
    staffRows :: [Int]
    staffRows = parseStaffRows formula
  when ( null staffRows ) do
    throwE
      ( SheetParseError $ "No staff seems to be assigned to task in row " <> Text.pack ( show taskRow ) <> "\n\
                          \Perhaps the staff is not written in the expected format:\
                          \  =TEXTJOIN( \" | \"; False; C5; D5; G5; AC5 )"
      )
  Set.fromList <$> for staffRows \ staffRow -> do
    when ( staffRow < firstRow || staffRow > lastRow ) do
      throwE
        ( SheetParseError $ "Task in row " <> Text.pack ( show taskRow ) <> " refers to staff in row " <> Text.pack ( show staffRow ) <> ",\n\
                            \but this is outside of the specified range of staff: " <> Text.pack ( show firstRow ) <> " -- " <> Text.pack ( show lastRow )
        )
    pure ( Staff ( staffRow - firstRow ) )
parseTaskStaffIDs taskRow _ _ _ =
  throwE ( SheetParseError $ "Unable to parse staff assigned to task in row " <> Text.pack ( show taskRow ) )

-- | Parse staff referred to by a formula of the form
--
-- @TEXTJOIN( sep ; ignore_empty; B5 ; B7 ; ... ; AA11 )@
--
-- Lazy approach without parser combinators (sorry).
parseStaffRows :: Text -> [Int]
parseStaffRows
  = rights
  . map 
    ( fmap fst
    . runExcept
    . parseLocation
    . Text.dropWhileEnd ignored
    . Text.dropWhile    ignored
    )
  . Text.split ( \ sep -> sep == ',' || sep == ';' )
  where
    ignored :: Char -> Bool
    ignored c = not ( Char.isAscii c ) || not ( Char.isAlphaNum c )

-- | Obtain the task name from a cell.
--
-- Expects the cell to contain a constant plain text value, not rich text nor a formula.
parseTaskName :: ( Int, Int ) -> Map ( Int, Int ) Xlsx.Cell -> Except Error Text
parseTaskName loc cells
  | Just ( Xlsx.Cell { Xlsx._cellValue = Just ( Xlsx.CellText text ) } ) <- Map.lookup loc cells
  = pure text
  | otherwise
  = throwE ( SheetParseError $ "Could not parse task name expected in cell " <> location loc <> "." )

-- | Obtain the task duration from a cell, in number of columns.
--
-- Expects the cell to contain a constant numeric value, not a formula.
parseTaskDuration :: ( Int, Int ) -> Map ( Int, Int ) Xlsx.Cell -> Except Error ( Delta Column )
parseTaskDuration loc cells
  | Just ( Xlsx.Cell { Xlsx._cellValue = Just ( Xlsx.CellDouble d ) } ) <- Map.lookup loc cells
  = pure $ Delta ( Column ( round d ) )
  | otherwise
  = throwE ( SheetParseError $ "Could not parse task duration expceted in cell " <> location loc <> "." ) 

-- | Traversal for obtaining the cells in the first worksheet of the spreadsheet.
_cells :: Traversal' Xlsx.Xlsx ( Map ( Int,Int ) Xlsx.Cell )
_cells = field' @"_xlSheets" . ix 0 . typed @Xlsx.Worksheet . field' @"_wsCells"

-- | Update the spreadsheet availability information by filling in
-- unavailable task time slots with the value @0@.
updateSpreadsheet :: SchedulingRanges -> Boxed.Vector ( Task taskData Column ) -> Xlsx.Xlsx -> Xlsx.Xlsx
updateSpreadsheet ( SchedulingRanges { firstTaskRow, lastTaskRow, firstScheduleColumn, lastScheduleColumn } ) avails =
  over _cells ( Map.mapWithKey makeCellUnavailable )
  where
    makeCellUnavailable :: ( Int,Int ) -> Xlsx.Cell -> Xlsx.Cell
    makeCellUnavailable ( r, c ) cell
      |  r < firstTaskRow
      || r > lastTaskRow
      || c < firstScheduleColumn
      || c > lastScheduleColumn
      = cell
      | let 
          avail :: Intervals Column
          avail = taskAvailability $ avails Boxed.Vector.! ( r - firstTaskRow )
      , coerce c `inside` avail
      = cell
      | otherwise
      = cell { Xlsx._cellValue = Just ( Xlsx.CellDouble 0 ) }
