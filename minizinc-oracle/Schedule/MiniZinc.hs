{-# LANGUAGE ScopedTypeVariables #-}

-- | A MiniZinc-backed oracle for unary-scheduling, intended for benchmarking
-- against the Chuffed lazy-clause-generation solver.
--
-- Unlike the Z3 oracle (which links the solver in-process via FFI), this driver
-- shells out to the @minizinc@ executable: it renders the instance to a @.dzn@
-- data file, runs it against a fixed @.mzn@ model with the requested solver, and
-- parses the solver's status and statistics back out. No solver bindings are
-- involved, only the standard MiniZinc command-line toolchain.
module Schedule.MiniZinc
  ( -- * Encoding
    unaryModel
  , renderInstanceData
    -- * Solver invocation
  , MiniZincOptions(..), defaultMiniZincOptions
  , MiniZincStatus(..), MiniZincOutcome(..)
  , MiniZincError(..)
  , minizincFeasible
  )
  where

-- base
import Control.Exception
  ( Exception, bracket, throwIO )
import Data.Char
  ( isSpace )
import Data.Coerce
  ( Coercible, coerce )
import Data.Foldable
  ( toList )
import Data.List
  ( dropWhileEnd, isInfixOf, stripPrefix )
import Data.Maybe
  ( listToMaybe, mapMaybe )
import System.IO
  ( hClose, hPutStr, openTempFile )
import System.IO.Error
  ( catchIOError )
import Text.Read
  ( readMaybe )

-- containers
import Data.IntSet
  ( IntSet )
import qualified Data.IntSet as IntSet
  ( fromList, toAscList, unions )

-- directory
import System.Directory
  ( getTemporaryDirectory, removeFile )

-- process
import System.Exit
  ( ExitCode )
import System.Process
  ( readProcessWithExitCode )

-- text
import Data.Text
  ( Text )
import qualified Data.Text as Text
  ( intercalate, pack, unlines, unpack )

-- unary-scheduling
import Schedule.Interval
  ( intervals, intervalIntBounds )
import Schedule.Task
  ( Task(..) )
import Schedule.Time
  ( Delta(..) )

--------------------------------------------------------------------------------
-- The fixed model.

-- | The unary-scheduling MiniZinc model.
--
-- Each task gets an integer start variable confined to its set of admissible
-- start positions (the union of @[release, deadline - duration]@ over its
-- availability windows), and a single 'disjunctive' global enforces the unary
-- resource. The @output@ item echoes the start vector so a feasible schedule
-- can be parsed back; see 'parseStarts'.
unaryModel :: String
unaryModel = unlines
  [ "include \"globals.mzn\";"
  , "int: n;"
  , "array[1..n] of int: dur;"
  , "array[1..n] of set of int: starts;"
  , "array[1..n] of var int: s;"
  , "constraint forall(i in 1..n)(s[i] in starts[i]);"
  , "constraint disjunctive(s, dur);"
  , "solve satisfy;"
  , "output [ \"s=\", show(s) ];"
  ]

--------------------------------------------------------------------------------
-- Instance encoding.

-- | Render an instance as MiniZinc @.dzn@ data for 'unaryModel': the task count,
-- the per-task durations, and the per-task sets of admissible start positions.
renderInstanceData :: forall task t. Coercible t Int => [ Task task t ] -> Text
renderInstanceData tasks =
  Text.unlines
    [ "n = " <> tshow ( length tasks ) <> ";"
    , "dur = [" <> commaSep ( map ( tshow . fst ) entries ) <> "];"
    , "starts = [" <> commaSep ( map ( renderSet . snd ) entries ) <> "];"
    ]
  where
    entries :: [ ( Int, IntSet ) ]
    entries = map taskEntry tasks

    -- A task's duration together with its set of admissible start positions.
    taskEntry :: Task task t -> ( Int, IntSet )
    taskEntry ( Task { taskAvailability, taskDuration } ) =
      let dur = coerce taskDuration :: Int
      in  ( dur
          , IntSet.unions
              [ IntSet.fromList [ s .. e - dur ]
              | ival <- toList ( intervals taskAvailability )
                -- 'intervalIntBounds' returns half-open bounds [s, e), so the
                -- last start that still fits a duration-@dur@ task is @e - dur@.
              , let ( s, e ) = intervalIntBounds ival
              ]
          )

    renderSet :: IntSet -> Text
    renderSet s = "{" <> commaSep ( map tshow ( IntSet.toAscList s ) ) <> "}"

    commaSep :: [ Text ] -> Text
    commaSep = Text.intercalate ", "

    tshow :: Int -> Text
    tshow = Text.pack . show

--------------------------------------------------------------------------------
-- Solver invocation.

-- | How to invoke MiniZinc.
data MiniZincOptions
  = MiniZincOptions
  { minizincExe :: !FilePath
    -- ^ path to the @minizinc@ executable
  , solver      :: !String
    -- ^ solver identifier passed to @--solver@ (e.g. @\"chuffed\"@)
  , timeLimitMs :: !Int
    -- ^ overall wall-clock budget in milliseconds (@--time-limit@)
  , freeSearch  :: !Bool
    -- ^ pass @-f@ to let the solver ignore the model's (absent) search
    -- annotation and use its own default search
  }
  deriving stock ( Eq, Show )

-- | Defaults: the @minizinc@ on @PATH@, the bundled Chuffed solver, a 60-second
-- budget, and fixed (non-free) search.
defaultMiniZincOptions :: MiniZincOptions
defaultMiniZincOptions =
  MiniZincOptions
    { minizincExe = "minizinc"
    , solver      = "chuffed"
    , timeLimitMs = 60_000
    , freeSearch  = False
    }

-- | The decided status of a feasibility query.
data MiniZincStatus
  = Feasible !( Maybe [ Int ] )
    -- ^ a feasible schedule was found; @Just starts@ when the start vector could
    -- be parsed from the solver's output
  | Infeasible
    -- ^ the solver proved the instance infeasible
  | Unknown
    -- ^ the solver hit the time limit without deciding
  deriving stock ( Eq, Show )

-- | The result of a feasibility query, together with the solver-reported timings
-- (in seconds). 'solveTime' isolates search/propagation and /excludes/ the
-- MiniZinc flattening step reported by 'flatTime', so it is the figure
-- comparable to the in-process LCG timing.
data MiniZincOutcome
  = MiniZincOutcome
  { status    :: !MiniZincStatus
  , solveTime :: !( Maybe Double )
  , flatTime  :: !( Maybe Double )
  }
  deriving stock ( Eq, Show )

-- | Thrown when @minizinc@ produces no recognisable status line, e.g. on a model
-- or flattening error. Carries the process output for diagnosis.
data MiniZincError
  = MiniZincError
  { exitCode :: !ExitCode
  , stdout   :: !String
  , stderr   :: !String
  }
  deriving stock Show
  deriving anyclass Exception

-- | Decide feasibility of a unary-scheduling instance by invoking MiniZinc.
--
-- Throws 'MiniZincError' if the solver output cannot be interpreted (rather than
-- silently reporting a bogus verdict).
minizincFeasible
  :: forall task t
  .  Coercible t Int
  => MiniZincOptions
  -> [ Task task t ]
  -> IO MiniZincOutcome
minizincFeasible opts tasks =
  withTempFiles unaryModel ( Text.unpack ( renderInstanceData tasks ) ) \ modelPath dataPath -> do
    let args =
          [ "--solver", solver opts
          , "--statistics"
          , "--time-limit", show ( timeLimitMs opts )
          ]
          ++ [ "-f" | freeSearch opts ]
          ++ [ modelPath, dataPath ]
    ( code, out, err ) <- readProcessWithExitCode ( minizincExe opts ) args ""
    let ls = lines out
    case parseStatus ls of
      Nothing  -> throwIO ( MiniZincError code out err )
      Just stat ->
        pure MiniZincOutcome
          { status    = stat
          , solveTime = statValue "solveTime" ls
          , flatTime  = statValue "flatTime"  ls
          }

--------------------------------------------------------------------------------
-- Output parsing.

-- | Interpret MiniZinc's standard status markers. 'Nothing' signals output we
-- don't recognise (treated as an error by 'minizincFeasible').
parseStatus :: [ String ] -> Maybe MiniZincStatus
parseStatus ls
  | hasMarker "=====UNSATISFIABLE=====" = Just Infeasible
  | hasMarker "=====UNKNOWN====="       = Just Unknown
  | hasMarker "=====ERROR====="         = Nothing
  | any ( ( "----------" == ) . trim ) ls = Just ( Feasible ( parseStarts ls ) )
  | otherwise                           = Nothing
  where
    hasMarker marker = any ( ( marker `isInfixOf` ) . trim ) ls

-- | Parse the start vector echoed by the model's @output@ item, of the form
-- @s=[1, 4, 7]@.
parseStarts :: [ String ] -> Maybe [ Int ]
parseStarts ls =
  listToMaybe
    [ ints
    | l <- ls
    , Just rest <- [ stripPrefix "s=" ( trim l ) ]
    , Just ints <- [ parseIntList rest ]
    ]
  where
    parseIntList :: String -> Maybe [ Int ]
    parseIntList s = do
      inner <- stripPrefix "[" ( trim s ) >>= stripSuffix "]" . trim
      traverse ( readMaybe . trim ) ( splitCommas inner )

    stripSuffix :: String -> String -> Maybe String
    stripSuffix suf xs = reverse <$> stripPrefix ( reverse suf ) ( reverse xs )

-- | Read a numeric @%%%mzn-stat:@ line such as
-- @%%%mzn-stat: solveTime=0.001@.
statValue :: String -> [ String ] -> Maybe Double
statValue key ls =
  listToMaybe $ mapMaybe lineValue ls
  where
    lineValue l = do
      rest   <- stripPrefix "%%%mzn-stat:" ( trim l )
      valStr <- stripPrefix ( key ++ "=" ) ( trim rest )
      readMaybe ( trim valStr )

--------------------------------------------------------------------------------
-- Small helpers.

-- | Strip surrounding whitespace, including the trailing @\\r@ left by Windows
-- line endings after 'lines'.
trim :: String -> String
trim = dropWhileEnd isSpace . dropWhile isSpace

-- | Split on commas, dropping empty fields (so @\"\"@ yields @[]@).
splitCommas :: String -> [ String ]
splitCommas s =
  case break ( == ',' ) s of
    ( field, ',' : rest ) -> field : splitCommas rest
    ( "",    _          ) -> []
    ( field, _          ) -> [ field ]

-- | Write the model and data to temporary files, run the action, then delete
-- them. The @.mzn@/@.dzn@ extensions are preserved so MiniZinc recognises each
-- file's role.
withTempFiles :: String -> String -> ( FilePath -> FilePath -> IO a ) -> IO a
withTempFiles modelTxt dataTxt action = do
  dir <- getTemporaryDirectory
  withTempFile dir "unary-sched-.mzn" modelTxt \ modelPath ->
    withTempFile dir "unary-sched-.dzn" dataTxt \ dataPath ->
      action modelPath dataPath
  where
    withTempFile :: FilePath -> String -> String -> ( FilePath -> IO a ) -> IO a
    withTempFile dir template content k =
      bracket
        ( do ( path, h ) <- openTempFile dir template
             hPutStr h content
             hClose h
             pure path )
        ( \ path -> removeFile path `catchIOError` \ _ -> pure () )
        k
