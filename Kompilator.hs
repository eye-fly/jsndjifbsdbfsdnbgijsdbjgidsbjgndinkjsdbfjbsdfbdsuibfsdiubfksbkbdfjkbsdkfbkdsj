-- File generated by the BNF Converter (bnfc 2.9.5).

-- | Program to test parser.

module Main where

import Prelude
  ( ($), (.)
  , Either(..)
  , Int, (>)
  , String, (++), concat, unlines
  , Show, show
  , IO, (>>), (>>=), mapM_, putStrLn
  , FilePath
  , getContents, readFile
  )
import System.IO  
import Control.Monad
import System.Environment ( getArgs )
import System.Exit        ( exitFailure )
import Control.Monad      ( when )
import Data.Maybe

import Util
import TypeChecker
import Runner

import AbsGramar  
import LexGramar   ( Token, mkPosToken )
import ParGramar   ( pProgram, myLexer )
import PrintGramar ( Print, printTree )
import SkelGramar  ()


-- prase :: FilePath -> Err AbsGramar.Program
-- prase f = do
--     handle <- openFile f ReadMode
--     contents <- hGetContents handle
--     pProgram (myLexer contents)
-- -- -- f= "filesTest/good/0.cpp"
-- --

runFile :: FilePath -> IO ()
runFile f = putStrLn f >> readFile f >>= run 

run:: String -> IO ()
run content =  do
  -- putStrLn $ show $ pProgram (myLexer content)

  case (prase content) of
    (Just s,_) -> do
       hPutStrLn  stderr ("Compile error " ++ s)
    (Nothing, Just (ret, io)) -> do
      (putStrLn "Pre run check Sucsessful\n") >>io >> putStrLn ("program ended with "++(show ret)) 

prase :: String -> (Err, Maybe (Int,IO()))
prase contents = 
    case pProgram (myLexer contents) of
    (Right tree) ->
      let (Program pos topDefs) = tree in
      case TypeChecker.typeChecker topDefs of
        Nothing ->  (Nothing,Just (runer topDefs))
        err -> (err, Nothing)
    (Left err) -> (Just err, Nothing)
  --   -- Print handle
  --   -- Nothing

usage :: IO ()
usage = do
  putStrLn $ unlines
    [ "usage: Call with one of the following argument combinations:"
    , "  --help          Display this help message."
    , "  (no arguments)  Parse stdin verbosely."
    , "  (files)         Parse content of files verbosely."
    , "  -s (files)      Silent mode. Parse content of files silently."
    ]

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["--help"] -> usage
    []         -> getContents >>= run 
    "-s":fs    -> mapM_ runFile fs
    fs         -> mapM_ runFile fs


-- f= "filesTest/typeChecker/bad/same_function_ident.cpp"
-- contents <- readFile f
-- prase contents
-- p = pProgram (myLexer handle)
-- (Right tree) = p
-- (Program pos topDefs) = tree














-- 0988888888888888888888888
-- f= "filesTest/good/0.cpp"
-- handle <- openFile f ReadMode
-- contents <- hGetContents handle
-- p = pProgram (myLexer contents)
-- (Right tree) = p
