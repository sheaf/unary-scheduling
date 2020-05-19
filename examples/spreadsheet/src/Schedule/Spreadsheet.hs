{-# LANGUAGE AllowAmbiguousTypes        #-}
{-# LANGUAGE BlockArguments             #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MagicHash                  #-}
{-# LANGUAGE NamedFieldPuns             #-}
{-# LANGUAGE NamedWildCards             #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE PartialTypeSignatures      #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeApplications           #-}

module Schedule.Spreadsheet
  ( scheduleSpreadsheet, handleError )
  where

-- base
import Control.Applicative
  ( Alternative((<|>)) )
import Control.Monad
  ( when, unless )
import Control.Monad.ST
  ( runST )
import qualified Data.Char as Char
  ( chr, ord, toUpper )
import Data.Coerce
  ( coerce )
import Data.Foldable
  ( for_, toList )
import Data.Functor
  ( ($>) )
import Data.Semigroup
  ( Arg(..) )
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

-- attoparsec
import qualified Data.Attoparsec.Text as Atto
  ( Parser, parseOnly, endOfInput
  , asciiCI, char, anyChar, letter, decimal
  , many1', takeTill, skipMany, skipSpace
  )
import Data.Attoparsec.Text
  ( (<?>) )

-- bytestring
import qualified Data.ByteString.Lazy as LazyByteString
  ( readFile, writeFile )

-- containers
import Data.Map.Strict
  ( Map )
import qualified Data.Map.Strict as Map
  ( lookup, mapWithKey, fromList, unionWith )
import Data.Set
  ( Set )
import qualified Data.Set as Set
  ( fromList, insert, empty )
import Data.Sequence
  ( Seq(..) )

-- deepseq
import Control.DeepSeq
  ( NFData )

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
  ( MonadError(throwError), liftEither )

-- optparse-applicative
import qualified Options.Applicative as OptParse
  ( execParserPure, execCompletion, renderFailure
  , ParserResult(..), CompletionResult(..)
  , Parser, ParserInfo(..), ParserPrefs(..)
  , strOption, strArgument, switch, flag, helper
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
  ( pack, replicate, intercalate )
import qualified Data.Text.IO as Text
  ( appendFile, writeFile, hPutStrLn )

-- time
import qualified Data.Time.Clock.POSIX as Time
  ( getPOSIXTime, posixSecondsToUTCTime )
import qualified Data.Time.Format as Time
  ( formatTime, defaultTimeLocale)
import qualified Data.Time.LocalTime as Time
  ( getCurrentTimeZone, utcToLocalTime )

-- transformers
import Control.Monad.Trans.Class
  ( lift )
import Control.Monad.Trans.Except
  ( ExceptT(..)
  , runExceptT, withExceptT
  )
import Control.Monad.IO.Class
  ( liftIO )

-- vector
import qualified Data.Vector as Boxed
  ( Vector )
import qualified Data.Vector as Boxed.Vector
  ( length, fromList, (!), zipWith, unsafeFreeze )
import qualified Data.Vector.Mutable as Boxed.MVector
  ( replicate, modify )

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
import Schedule.Propagators
  ( propagateConstraints, Propagator(..), basicPropagators
  , makespan
  )
import Schedule.Interval
  ( Interval((:<=..<=)), Intervals(..)
  , insideLax
  )
import Schedule.Monad
  ( BroadcastTarget(..) )
import Schedule.Ordering
  ( visualiseEdges )
import Schedule.Search
  ( SearchState(..), search )
import Schedule.Task
  ( Task(..), TaskInfos(..)
  , ImmutableTaskInfos
  )
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
  -- whether to perform constraint propagation (if so, include filepath for logging) and search.
  Args { .. } <- parseArgs
  currentPosixTime <- lift Time.getPOSIXTime
  currentTimeZone  <- lift Time.getCurrentTimeZone
  let
    formattedTime :: String
    formattedTime = Time.formatTime Time.defaultTimeLocale "%0Y-%m-%d %H:%M:%S"
                  . Time.utcToLocalTime currentTimeZone
                  . Time.posixSecondsToUTCTime
                  $ currentPosixTime

  -- Read input spreadsheet.
  let
    inputPath, outputPath :: FilePath
    inputPath  =  inputSpreadsheetPath -<.> "xlsx"
    outputPath = outputSpreadsheetPath -<.> "xlsx"
  inputExists <- lift $ Directory.doesFileExist inputPath
  unless inputExists do
    throwError ( MissingFile inputPath )
  spreadsheet <- withExceptT XlsxParseError . ExceptT
               $ Xlsx.toXlsxEither <$> LazyByteString.readFile inputPath

  -- Parse spreadsheet data.
  {-allSpreadsheetData@-}
  SchedulingData { schedulingTasks, schedulingStaff, schedulingRanges, totalSchedulingCost }
    <- liftEither $ parseSpreadsheet useMakespanConstraints spreadsheet

  {-
  -- Log parsed data for debugging.
  lift $ writeFile "data.txt" ( show allSpreadsheetData )
  -}

  -- Perform constraint propagation (if enabled).
  let
    propagators :: [ Propagator ( Set Staff ) Column ]
    propagators
      | Nothing <- constraintLoggingPath
      = [ ]
      | useMakespanConstraints
      , let
          makespanPropagators :: [ Propagator ( Set Staff ) Column ]
          makespanPropagators
            = toList
            $ fmap
                ( \ StaffMemberData { memberName, memberMakespanRanges, memberAssignedTasks } ->
                  Propagator
                    { mbNotifiee     = Nothing
                    , notifyTarget   = TellEveryone
                    , runPropagator  = makespan memberName memberAssignedTasks memberMakespanRanges
                    }
                )
                schedulingStaff
      = basicPropagators ++ makespanPropagators
      | otherwise
      = basicPropagators

    -- Propagate constraints using unary scheduling algorithms.
    ( afterPropTasks, justifications, mbError ) =
      propagateConstraints schedulingTasks 100 propagators

  for_ constraintLoggingPath \ justificationsPath -> do
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
  for_ mbError \ err -> throwError ( NoSchedulingPossible err )

  -- Search the remaining possibilities (if search is enabled).
  finalTasks <-
    if useSearch
    then do
      let
        searchRes :: SearchState (Set Staff) Column
        searchRes = search totalSchedulingCost 10 propagators afterPropTasks
      liftIO $ Text.appendFile "search_statistics.txt"
        ( "Found " <> Text.pack ( show ( totalSolutionsFound searchRes ) ) <> " solutions after "
        <> Text.pack ( show ( totalDecisionsTaken searchRes ) ) <> " decisions\n\n"
        )
      case solutions searchRes of
        ( Arg cost bestSol : _ ) -> do
          liftIO $ Text.writeFile "dotfile.txt" ( visualiseEdges . orderings $ bestSol )
          liftIO $ Text.writeFile "cost.txt" ( Text.pack ( show cost ) )
          pure bestSol
        _ -> throwError ( NoSchedulingPossible "Search has found no results" )
    else pure afterPropTasks

  -- Write output spreadsheet with updated availability information.
  let
    outputData =
      Xlsx.fromXlsx currentPosixTime
        ( updateSpreadsheet schedulingRanges finalTasks schedulingStaff spreadsheet )
  lift $ LazyByteString.writeFile outputPath outputData

-------------------------------------------------------------------------------
-- Spreadsheet parsing.

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

data StaffMemberData
  = StaffMemberData
  { memberAvailability   :: !(Intervals Column)
  , memberName           :: !Text
  , memberMakespanRanges :: ![ ( Interval Column, Delta Column ) ]
  , memberSchedulingCost :: ( ImmutableTaskInfos ( Set Staff ) Column -> Double )
  , memberAssignedTasks  :: !(Set Int)
  }

-- | All the information needed to run the scheduling algorithms:
--
-- - staff availabilities, names, makespan constraints and assigned tasks,
-- - staff assigned to each task, and the corresponding task name,
-- - spreadsheet ranges, giving us the info of where to write results to.
data SchedulingData
  = SchedulingData
  { schedulingStaff     :: !( Boxed.Vector StaffMemberData )
  , schedulingTasks     :: ![ ( Task ( Set Staff ) Column, Text ) ]
  , schedulingRanges    :: !SchedulingRanges
  , totalSchedulingCost :: ( ImmutableTaskInfos ( Set Staff ) Column -> Double )
  }

newtype Staff = Staff { staffID :: Int }
  deriving stock   Show
  deriving newtype ( Eq, Ord, NFData )

newtype Column = Column { getColumn :: Int }
  deriving newtype ( Eq, Ord, Enum, Bounded, Num, NFData )
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

-- | Traversal for obtaining the cells in the first worksheet of the spreadsheet.
_cells :: Traversal' Xlsx.Xlsx ( Map ( Int,Int ) Xlsx.Cell )
_cells = field' @"_xlSheets" . ix 0 . typed @Xlsx.Worksheet . field' @"_wsCells"

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
parseSpreadsheet :: Bool -> Xlsx.Xlsx -> Either Error SchedulingData
parseSpreadsheet enableMakespanConstraints spreadsheet = runST $ runExceptT do
  let
    cells :: Map ( Int, Int ) Xlsx.Cell
    cells = view _cells spreadsheet
  when ( null cells ) do
    throwError ( SheetParseError "No cell data found in spreadsheet" )

  -- Parse the ranges telling us:
  --   - the rows containing tasks,
  --   - the rows containing staff,
  --   - the columns containing available scheduling slots.
  schedulingRanges@( SchedulingRanges{ .. } ) <- parseRanges cells

  -- Parse the staff names, availabilities, makespan constraints and cost parameters.
  schedulingStaffInfo <- Boxed.Vector.fromList <$>
    for [ firstStaffRow .. lastStaffRow ] \ staffRow -> do
      let
        staffNameLocation, makespanConstraintLocation :: ( Int, Int )
        staffNameLocation = ( staffRow, 3 )
        makespanConstraintLocation = ( staffRow, 2 )
        avail :: Intervals Column
        avail = parseAvailability firstScheduleColumn lastScheduleColumn staffRow cells
      name  <- parseText staffNameLocation cells
      makespanCt <-
        if enableMakespanConstraints
        then case Map.lookup makespanConstraintLocation cells of
          Nothing   -> pure []
          Just cell -> parseMakespanConstraints makespanConstraintLocation cell
        else pure []
      -- Parsing individual staff member scheduling cost function (TODO)
      let
        schedulingCost :: ImmutableTaskInfos ( Set Staff ) Column -> Double
        schedulingCost = const 0
      pure ( avail, name, makespanCt, schedulingCost )

  let
    nbStaff :: Int
    nbStaff = Boxed.Vector.length schedulingStaffInfo

  -- Initialise vector keeping track of tasks assigned to each staff member.
  staffTaskNbs <- Boxed.MVector.replicate nbStaff Set.empty

  -- Parse the task availabilities, combining task availability info with availability of the staff affected to each task.
  schedulingTasks <- for [ firstTaskRow .. lastTaskRow ] \ taskRow -> do
    let
      givenAvailability :: Intervals Column
      givenAvailability = parseAvailability firstScheduleColumn lastScheduleColumn taskRow cells
      taskCellLocation :: ( Int, Int )
      taskCellLocation = ( taskRow, 1 )
    taskStaffCell
      <- note ( SheetParseError $ "Missing cell data at " <> located taskCellLocation <> ": expected to find staff allocated to the task in that row." )
       $ Map.lookup ( taskRow, 1 ) cells
    taskStaffIDs <- parseTaskStaffIDs taskRow firstStaffRow lastStaffRow taskStaffCell
    let
      taskAvailability :: Intervals Column
      taskAvailability
        = getMeet
        $ Meet givenAvailability
        <> foldMap
            ( \ ( Staff { staffID } ) ->
              let
                ( avail, _, _, _ ) = schedulingStaffInfo Boxed.Vector.! staffID
              in Meet avail
            )
            taskStaffIDs
      taskNameLocation :: ( Int, Int )
      taskNameLocation = ( taskRow, 3 )
      taskDurationLocation :: ( Int, Int )
      taskDurationLocation = ( taskRow, 2 )
    taskName     <- parseText         taskNameLocation     cells
    taskDuration <- parseTaskDuration taskDurationLocation cells
    -- Add this task to the staff members assigned to it.
    let
      taskNb :: Int
      taskNb = taskRow - firstTaskRow
    for_ taskStaffIDs \ ( Staff { staffID } ) -> do
      Boxed.MVector.modify staffTaskNbs ( Set.insert taskNb ) staffID
    pure ( Task { taskAvailability, taskDuration, taskInfo = taskStaffIDs }, taskName )

  -- Return the complete staff information:
  --  - names,
  --  - availabilities,
  --  - tasks they are assigned to,
  --  - cost parameters,
  --  - makespan constraints.
  staffTasks <- Boxed.Vector.unsafeFreeze staffTaskNbs
  let
    schedulingStaff :: Boxed.Vector StaffMemberData
    schedulingStaff =
      Boxed.Vector.zipWith
        ( \ ( memberAvailability, memberName, memberMakespanRanges, memberSchedulingCost )
            memberAssignedTasks
         -> StaffMemberData { .. }
        )
        schedulingStaffInfo staffTasks
    -- Total scheduling cost function (TODO).
    totalSchedulingCost :: ImmutableTaskInfos ( Set Staff ) Column -> Double
    totalSchedulingCost = const 0

  -- Return the above info.
  pure ( SchedulingData { schedulingStaff, schedulingTasks, schedulingRanges, totalSchedulingCost } )

-- | Parse ranges for scheduling:
--
--  - cells B1 & C1: first and last cells of tasks to be scheduled (range of rows),
--  - cells B2 & C2: first and last cells of staff to be assigned to the tasks (range of rows),
--  - cells B3 & C3: first and last cells of available time slots (range of columns).
parseRanges :: Monad m => Map ( Int, Int ) Xlsx.Cell -> ExceptT Error m SchedulingRanges
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

-- | Pattern synonym for a cell containing a simple textual value.
pattern TextCell :: Text -> Xlsx.Cell
pattern TextCell text <- Xlsx.Cell { Xlsx._cellValue = Just ( Xlsx.CellText text ) }

-- | Obtains the location a cell is pointing at, in the case that the cell is pointing at a single other cell.
--
-- This corresponds to a spreadsheet formula of the form @=AB7@ (for instance).
parseLocationFromCellFormulaAt :: MonadError Error m => Text -> ( Int, Int ) -> Map (Int, Int) Xlsx.Cell -> m ( Int, Int )
parseLocationFromCellFormulaAt desc loc cells = do
  cell <- note ( SheetParseError $ "Could not parse " <> desc <> " from cell formula: no cell at " <> located loc )
        $ Map.lookup loc cells
  case cell of
    SimpleFormulaCell formula
      -> case Atto.parseOnly ( location <* Atto.endOfInput ) formula of
            Right res -> pure res
            Left  err -> throwError
              ( SheetParseError $ "Could not parse " <> desc <> " from cell " <> located loc <> ":\n" <>
                                  Text.pack err
              )
    _ -> throwError
      ( SheetParseError $ "Could not parse " <> desc <> " from cell " <> located loc <> ":\n\
                          \ - cell does not appear to contain a simple formula referring to a single other cell."
      )

-- | Parse an alphanumeric cell reference into a numeric @(row, column)@ pair.
location :: Atto.Parser ( Int, Int )
location = do
  Atto.skipSpace
  letters <- Atto.many1' Atto.letter
  row     <- Atto.decimal
  Atto.skipSpace
  let
    letterValue :: Char -> Int
    letterValue c = 1 + Char.ord ( Char.toUpper c ) - Char.ord 'A'
    col :: Int
    col = case Numeric.readInt 26 ( const True ) letterValue $ letters of
      [ ( col', _ ) ] -> col'
      _               -> error ( "internal error: could not parse column number from '" <> letters <> "'." )
  pure ( row, col )

-- | Display a numeric cell location pair @(row, column)@ as an alphanumeric reference.
--
-- > located ( 1, 3 ) = "C1"
located :: ( Int, Int ) -> Text
located ( r, c ) = Text.pack ( show $ Column c ) <> Text.pack ( show r )

-- | Parse the availability in a given row, as read off from the spreadsheet cells.
parseAvailability :: Int -> Int -> Int -> Map ( Int, Int ) Xlsx.Cell -> Intervals Column
parseAvailability firstCol lastCol row cells = Intervals $ go Empty firstCol
  where
    go :: Seq ( Interval Column ) -> Int -> Seq ( Interval Column )
    go ivals col
      | Just i <- nextAvailableColumn row lastCol cells col
      , let j = lastAvailableColumnAfter row lastCol cells i + 1
      -- +1 so that the difference between endpoints is the number of available columns
      = go ( ivals :|> ( coerce i :<=..<= coerce j ) ) j
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
parseTaskStaffIDs :: MonadError Error m => Int -> Int -> Int -> Xlsx.Cell -> m ( Set Staff )
parseTaskStaffIDs taskRow firstRow lastRow ( SimpleFormulaCell formula ) = do
  staffRows <- parseStaffRows taskRow formula
  when ( null staffRows ) do
    throwError
      ( SheetParseError $ "No staff seems to be assigned to task in row " <> Text.pack ( show taskRow ) <> "\n\
                          \Perhaps the staff is not written in the expected format:\
                          \  =TEXTJOIN( \" | \"; False; C5; D5; G5; AC5 )"
      )
  Set.fromList <$> for staffRows \ staffRow -> do
    when ( staffRow < firstRow || staffRow > lastRow ) do
      throwError
        ( SheetParseError $ "Task in row " <> Text.pack ( show taskRow ) <> " refers to staff in row " <> Text.pack ( show staffRow ) <> ",\n\
                            \but this is outside of the specified range of staff: " <> Text.pack ( show firstRow ) <> " -- " <> Text.pack ( show lastRow )
        )
    pure ( Staff ( staffRow - firstRow ) )
parseTaskStaffIDs taskRow _ _ _ =
  throwError ( SheetParseError $ "Unable to parse staff assigned to task in row " <> Text.pack ( show taskRow ) )

-- | Parse staff referred to by a formula of the form
--
-- @TEXTJOIN( sep ; ignore_empty; B5 ; B7 ; ... ; AA11 )@.
parseStaffRows :: MonadError Error m => Int -> Text -> m [Int]
parseStaffRows taskRow formula = case Atto.parseOnly ( textjoinParser <* Atto.endOfInput <?> ( "task staff formula" ) ) formula of
  Left err -> throwError $
    SheetParseError
      ( "Unable to parse staff assigned to task in row " <> Text.pack ( show taskRow ) <> ":\n\
        \  - " <> Text.pack err
      )
  Right r -> pure r
  where
    textjoinParser :: Atto.Parser [Int]
    textjoinParser = textjoinFormula ( repeat ( ( fst <$> location ) <|> Atto.decimal @Int ) )

-- | Parse a formula of the form
--
-- @TEXTJOIN( textSep ; bool; val_0 ; val_1 ; ... )@
--
-- where @textSep@ is a literal string (e.g. @" | "@),
-- bool is either @True@ or @False@,
-- and the values are parsed by the provided parsers.
textjoinFormula :: [ Atto.Parser a ] -> Atto.Parser [ a ]
textjoinFormula ps = do
  Atto.skipSpace
  Atto.skipMany ( Atto.asciiCI "_xlfn." ) -- some spreadsheet editors add this prefix
  _ <- Atto.asciiCI "TEXTJOIN" <?> "TEXTJOIN"
  Atto.skipSpace
  res <-
    list ( Atto.char '(' ) ( Atto.char ')' ) ( Atto.char ',' <|> Atto.char ';' )
      ( ( textSeparator $> undefined ) : ( boolean $> undefined ) : ps )
  Atto.skipSpace
  pure ( drop 2 res )
    where
      textSeparator :: Atto.Parser Text
      textSeparator = ( <?> "separator string" ) do
        Atto.skipSpace
        _ <- Atto.char '\"'
        sep <- Atto.takeTill ( == '\"' )
        _ <- Atto.anyChar
        Atto.skipSpace
        pure sep
      boolean :: Atto.Parser Bool
      boolean = ( ( Atto.asciiCI "TRUE" <|> Atto.asciiCI "1" ) $> True ) <|> ( ( Atto.asciiCI "FALSE" <|> Atto.asciiCI "0" ) $> False )
              <?> "Boolean value (True/False)"

-- | Given parsers for individual elements, parse a list of elements,
-- with given open/close parsers and a separator parser.
list :: Atto.Parser open -> Atto.Parser close -> Atto.Parser sep -> [ Atto.Parser a ] -> Atto.Parser [a]
list open close sep ps = do
  Atto.skipSpace
  _ <- open
  as <- go ps
  Atto.skipMany sep
  Atto.skipSpace
  _ <- close
  Atto.skipSpace
  pure as
  where
    go :: [ Atto.Parser a ] -> Atto.Parser [a]
    go [] = pure []
    go ( q : qs ) = do
      Atto.skipSpace
      a <- q
      Atto.skipSpace
      as <- ( ( sep *> go qs ) <|> pure [] )
      pure ( a : as )

-- | Obtain text from a cell.
--
-- Expects the cell to contain a constant plain text value, not rich text nor a formula.
parseText :: MonadError Error m => ( Int, Int ) -> Map ( Int, Int ) Xlsx.Cell -> m Text
parseText loc cells
  | Just ( TextCell text ) <- Map.lookup loc cells
  = pure text
  | otherwise
  = throwError ( SheetParseError $ "Could not parse text in cell " <> located loc <> "." )

-- | Obtain the task duration from a cell, in number of columns.
--
-- Expects the cell to contain a constant numeric value, not a formula.
parseTaskDuration :: MonadError Error m => ( Int, Int ) -> Map ( Int, Int ) Xlsx.Cell -> m ( Delta Column )
parseTaskDuration loc cells
  | Just ( Xlsx.Cell { Xlsx._cellValue = Just ( Xlsx.CellDouble d ) } ) <- Map.lookup loc cells
  = pure $ Delta ( Column ( round d ) )
  | otherwise
  = throwError ( SheetParseError $ "Could not parse task duration expected in cell " <> located loc <> "." )

-- | Obtain the makespan constraints for a given staff member.
--
-- This information should be specified in the spreadsheet with a formula of the form:
--
--  - @ TEXTJOIN(" | ";False; TEXTJOIN("-";False;D6;CU6;36); TEXTJOIN("-";False;EB6;HS6;48) )@
--
-- In this example, this formula specifies two makespan constraints:
--  - one in columns @D:CU@, with a maximum makespan of @36@ columns,
--  - one in columns @EB:HS@, with a maximum makespan of @48@ columns.
parseMakespanConstraints :: forall m. MonadError Error m => ( Int, Int ) -> Xlsx.Cell -> m [ ( Interval Column, Delta Column ) ]
parseMakespanConstraints loc ( SimpleFormulaCell formula ) =
  case Atto.parseOnly ( makespanParser <* Atto.endOfInput ) formula of
    Left  err -> throwError ( SheetParseError $ "Could not parse makespan constraint in cell " <> located loc <> ":\n" <> Text.pack err )
    Right res -> go res
  where
    makespanParser :: Atto.Parser [ [ Int ] ]
    makespanParser = textjoinFormula ( repeat $ textjoinFormula [ snd <$> location, snd <$> location, Atto.decimal ] )
    go :: [ [ Int ] ] -> m [ ( Interval Column, Delta Column ) ]
    go [] = pure []
    go ( [ s, e, d ] : rest ) = ( ( coerce s :<=..<= coerce ( e + 1 ), coerce d ) :) <$> go rest
    go _ = throwError $ SheetParseError $
      "Could not parse makespan constraint in cell " <> located loc <> ": expecting a triple start-end-maximum makespan."
parseMakespanConstraints loc _ =
  throwError ( SheetParseError $ "Could not parse makespan constraint in cell " <> located loc <> ":\n\
                                 \  - cell does not appear to contain a simple formula."
             )

-------------------------------------------------------------------------------
-- Updating spreadsheet data.

-- | Update the spreadsheet availability information by filling in
-- unavailable task time slots with the value @0@.
updateSpreadsheet
  :: SchedulingRanges
  -> ImmutableTaskInfos taskData Column
  -> Boxed.Vector StaffMemberData
  -> Xlsx.Xlsx
  -> Xlsx.Xlsx
updateSpreadsheet ( SchedulingRanges { .. } ) ( TaskInfos { taskNames, taskAvails } ) staff =
  over _cells ( Map.unionWith setCellText staffTasks . Map.mapWithKey makeCellUnavailable )
  where
    makeCellUnavailable :: ( Int,Int ) -> Xlsx.Cell -> Xlsx.Cell
    makeCellUnavailable ( r, c ) cell
      |  r < firstTaskRow
      || r > lastTaskRow
      || c < firstScheduleColumn
      || c > lastScheduleColumn
      = cell
      | let 
          taskAvail :: Intervals Column
          taskAvail = taskAvailability $ taskAvails Boxed.Vector.! ( r - firstTaskRow )
      , coerce c `insideLax` taskAvail && coerce ( c + 1 ) `insideLax` taskAvail
      = cell
      | otherwise
      = cell { Xlsx._cellValue = Just ( Xlsx.CellDouble 0 ) }
    staffTasks :: Map ( Int, Int ) Xlsx.Cell
    staffTasks = Map.fromList
      [ ( ( i, 1 ), Xlsx.Cell Nothing ( Just ( Xlsx.CellText $ staffTaskText ( i - firstStaffRow ) ) ) Nothing Nothing )
      | i <- [ firstStaffRow .. lastStaffRow ]
      ]
    staffTaskText :: Int -> Text
    staffTaskText i = Text.intercalate " + " names <> " = " <> Text.pack ( show totalDuration )
      where
        taskNbs :: Set Int
        taskNbs = memberAssignedTasks ( staff Boxed.Vector.! i )
        names :: [ Text ]
        names = map
          ( \ taskNb ->
          let
            name :: Text
            name = taskNames Boxed.Vector.! taskNb
            duration :: Int
            duration = coerce $ taskDuration ( taskAvails Boxed.Vector.! taskNb )
          in
            name <> " (" <> Text.pack ( show duration ) <> ")"
          )
          $ toList taskNbs
        totalDuration :: Int
        totalDuration = coerce $ foldMap ( \ taskNb -> taskDuration ( taskAvails Boxed.Vector.! taskNb ) ) taskNbs
    setCellText :: Xlsx.Cell -> Xlsx.Cell -> Xlsx.Cell
    setCellText ( TextCell text ) cell = cell { Xlsx._cellValue = Just ( Xlsx.CellText text ) }
    setCellText _ cell = cell

-------------------------------------------------------------------------------
-- Error handling.

note :: MonadError e m => e -> Maybe a -> m a
note _ ( Just a ) = pure a
note e _          = throwError e

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

-------------------------------------------------------------------------------
-- Command line arguments.

-- | Record of expected command line arguments.
data Args
  = Args
  { inputSpreadsheetPath   :: !FilePath
  , outputSpreadsheetPath  :: !FilePath
  , constraintLoggingPath  :: !(Maybe FilePath)
  , useSearch              :: !Bool
  , useMakespanConstraints :: !Bool
  }
  deriving stock Show

-- | Parse command line arguments: filename of input and output spreadsheets,
-- and whether to perform constraint propagation (if so, provide a filename for logging output).
parseArgs :: ExceptT Error IO Args
parseArgs = do
  args <- lift getArgs
  case OptParse.execParserPure parserPrefs parserInfo args of
    OptParse.Success res -> pure res
    OptParse.CompletionInvoked compl -> throwError ( Completion compl )
    OptParse.Failure err -> do
      progName <- lift getProgName
      let
        ( msg, _ ) = OptParse.renderFailure err progName
      throwError ( ArgsError msg )

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
            <> Pretty.hardline <> Pretty.hardline <>
            "Makespan constraints for staff members can also be specified in column B," <> Pretty.linebreak <>
            "on the same row as the task (requires the --makespan flag)." <> Pretty.hardline <>
            "The format is as follows:" <> Pretty.hardline <>
              ( Pretty.indent 4 "TEXTJOIN(delim,bool,TEXTJOIN(delim,bool,start1,end1,makespan1),TEXTJOIN(delim,bool,start2,end2,makespan2)...)" )
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
      { OptParse.infoParser      = OptParse.helper <*> ( Args <$> inputArg <*> outputArg <*> logArg <*> searchArg <*> makespanArg )
      , OptParse.infoFullDesc    = True
      , OptParse.infoProgDesc    = OptParse.Chunk ( Just desc )
      , OptParse.infoHeader      = OptParse.Chunk ( Just header )
      , OptParse.infoFooter      = OptParse.Chunk ( Just usageInfo )
      , OptParse.infoFailureCode = 255
      , OptParse.infoPolicy      = OptParse.Intersperse
      }

    inputArg :: OptParse.Parser FilePath
    inputArg =
      OptParse.strArgument
        (  OptParse.metavar "INPUTFILE"
        <> OptParse.help    "Read scheduling data from XLSX spreadsheet INPUTFILE"
        )

    outputArg :: OptParse.Parser FilePath
    outputArg =
      OptParse.strOption
        (  OptParse.long    "output"
        <> OptParse.short   'o'
        <> OptParse.metavar "OUTPUTFILE"
        <> OptParse.value   "output.xlsx"
        <> OptParse.help    "Write scheduling data to XLSX spreadsheet OUTPUTFILE"
        )

    logArg :: OptParse.Parser ( Maybe FilePath )
    logArg =  ( \ b fp -> if b then Nothing else Just fp )
          <$> OptParse.switch
                (  OptParse.long "no-prop"
                <> OptParse.help "Disable constraint propagation"
                )
          <*> OptParse.strOption
                (  OptParse.long    "log"
                <> OptParse.short   'l'
                <> OptParse.metavar "LOGFILE"
                <> OptParse.value   "log.txt"
                <> OptParse.help    "Log constraint solving information to LOGFILE"
                )

    searchArg :: OptParse.Parser Bool
    searchArg =
      OptParse.flag True False
        (  OptParse.long "no-search"
        <> OptParse.help "Disable search"
        )

    makespanArg :: OptParse.Parser Bool
    makespanArg =
      OptParse.switch
        (  OptParse.long  "makespan"
        <> OptParse.short 'm'
        <> OptParse.help  "Enable makespan constraints (experimental)"
        )
