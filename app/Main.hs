{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}

module Main where

import Control.Monad (when)
import qualified Control.Monad.Parallel as Par
import Data.Aeson
import Data.Aeson.Types
import Data.Char
import Data.FileEmbed (embedFile)
import Data.List (delete, isPrefixOf, partition)
import Data.Maybe
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Monoid ((<>))
import Data.Version
import Control.Monad.Supply
import Control.Monad.Supply.Class
import Text.Printf

import System.Environment
import System.Directory (createDirectoryIfMissing, doesDirectoryExist, doesFileExist, getModificationTime)
import System.FilePath ((</>), joinPath, splitDirectories, takeDirectory)

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import qualified Data.Text.Lazy as L
import qualified Data.Text.Lazy.Encoding as L
import qualified Data.ByteString as B

import Development.GitRev

import Language.PureScript.AST.Literals
import Language.PureScript.CoreFn
import Language.PureScript.CoreFn.FromJSON
import Language.PureScript.Externs
import Language.PureScript.Environment

import CodeGen.IL
import CodeGen.IL.Common
import CodeGen.IL.Printer

import Tests

parseJson :: Text -> Value
parseJson text
  | Just fileJson <- decode . L.encodeUtf8 $ L.fromStrict text = fileJson
  | otherwise = error "Bad json"

jsonToModule :: Value -> Module Ann
jsonToModule value =
  case parse moduleFromJSON value of
    Success (_, r) -> r
    _ -> error "failed"                  

readExtFile :: FilePath -> IO ExternsFile
readExtFile path = do
  m <- decodeFileStrict' path
  case m of
    Just e -> return e
              --if (externsIsCurrentVersion e) 
              --then return e
              --else error $ "Version mismatch for " <> path
    _ -> error $ "Error loading " <> path
    
main :: IO ()
main = do
  args <- getArgs
  if null args
    then return ()
    else do
      let (opts, files) = partition (isPrefixOf "--") args
          opts' = (map . map) toLower opts
      if "--tests" `elem` opts'
        then runTests
        else do
          when ("--makefile" `elem` opts') $
            B.writeFile "Makefile" $(embedFile "support/Makefile")
          when ("--help" `elem` opts') $
            putStrLn help
          when ("--version" `elem` opts') $ do
            let branch = $(gitBranch)
                details | branch == "master" = "master, commit: " ++ $(gitHash)
                        | otherwise = branch
            putStrLn $ details ++ if $(gitDirty) then " (DIRTY)" else ""
          when (not $ null files) $ do
            let filepath = takeDirectory (head files)
                baseOutpath = joinPath $ (init $ splitDirectories filepath) ++ [outdir]
            writeRuntimeFiles $ baseOutpath </> rtdir
            Par.mapM (generateCode opts' $ baseOutpath </> mddir) files
            return ()
          return ()

generateCode :: [String] -> FilePath -> FilePath -> IO ()
generateCode opts baseOutpath cfnJsonFile = do
  let filepath = takeDirectory cfnJsonFile
      extJsonFile = filepath </> "externs.json"
      dirparts = splitDirectories $ filepath
      mname = (\c -> if c == '.' then '_' else c) <$> last dirparts
      basedir = joinPath $ init dirparts
      possInterfaceFilename = basedir </> outdir </> mddir </> interfaceFileName mname
  exists <- doesFileExist possInterfaceFilename
  cfnJsonModTime <- getModificationTime cfnJsonFile
  extJsonModTime <- getModificationTime extJsonFile
  if exists
    then do
      modTime <- getModificationTime possInterfaceFilename
      when ((modTime < cfnJsonModTime) || (modTime < extJsonModTime)) $
        transpile opts baseOutpath cfnJsonFile extJsonFile
    else transpile opts baseOutpath cfnJsonFile extJsonFile

emptyEnvironment :: Environment
emptyEnvironment = Environment M.empty M.empty M.empty M.empty M.empty M.empty S.empty

transpile :: [String] -> FilePath -> FilePath -> FilePath -> IO ()
transpile opts baseOutpath cfnJsonFile extJsonFile = do
  cfnJsonText <- T.decodeUtf8 <$> B.readFile cfnJsonFile
  extFile <- readExtFile extJsonFile
  let module' = jsonToModule $ parseJson cfnJsonText
      env = applyExternsFileToEnvironment extFile emptyEnvironment 
  ((interface, foreigns, asts, implHeader, implFooter), _) <- runSupplyT 5 (moduleToIL module' env)
  let mn = moduleNameToIL $ moduleName module'
      implementation = prettyPrintIL asts
      interfacePath = baseOutpath </> interfaceFileName (T.unpack mn)
      implPath = baseOutpath </> implFileName mn
  putStrLn interfacePath
  createDirectoryIfMissing True baseOutpath
  B.writeFile interfacePath $ T.encodeUtf8 $ conv interface
  putStrLn implPath
  B.writeFile implPath $ T.encodeUtf8 $ conv (implHeader <> implementation <> implFooter)
  where
  conv :: Text -> Text
  conv
    | "--ucns" `elem` opts = toUCNs
    | otherwise = id

writeRuntimeFiles :: FilePath -> IO ()
writeRuntimeFiles baseOutpath = do
  createDirectoryIfMissing True baseOutpath
  let runtimeHeader = baseOutpath </> "purescript.h"
      runtimeSource = baseOutpath </> "purescript.cpp"
      fn = baseOutpath </> "functions.h"
      dict = baseOutpath </> "dictionary.h"
      recur = baseOutpath </> "recursion.h"
  runtimeExists <- doesFileExist runtimeHeader
  when (not runtimeExists) $ do
    B.writeFile runtimeHeader $(embedFile "runtime/purescript.h")
    B.writeFile runtimeSource $(embedFile "runtime/purescript.cpp")
    B.writeFile fn  $(embedFile "runtime/functions.h")
    B.writeFile dict $(embedFile "runtime/dictionary.h")
    B.writeFile recur $(embedFile "runtime/recursion.h")

outdir :: FilePath
outdir = "../cpp"

rtdir :: FilePath
rtdir = "runtime"

mddir :: FilePath
mddir = "modules"

interfaceFileName :: String -> FilePath
interfaceFileName mn = mn <> ".h"

implFileName :: Text -> FilePath
implFileName mn = T.unpack $ mn <> ".cpp"

escape :: Text -> Text
escape = T.concatMap go
  where
  go :: Char -> Text
  go c = T.pack $ printf "0x%04x," (ord c)


toUCNs :: Text -> Text
toUCNs = T.pack . concatMap toUCN . T.unpack

toUCN :: Char -> String
toUCN c | isAscii c = [c]
toUCN c = printf "\\U%08x" $ ord c

help :: String
help = "Usage: pscpp OPTIONS COREFN-FILES\n\
       \  PureScript-to-C++ compiler\n\n\
       \Available options:\n\
       \  --help                  Show this help text\n\n\
       \  --version               Show the version number\n\n\
       \  --makefile              Generate a GNU Makefile which can be used for compiling\n\
       \                          a PureScript program and libraries to a native binary via\n\
       \                          purs corefn output and C++\n\n\
       \  --ucns                  Use UCN encoding of unicode characters in literals and\n\
       \                          strings in generated C++ code (for compilers that do not\n\
       \                          support unicode literals, such as gcc)\n\n\
       \  --tests                 Run test cases (under construction)\n\n\
       \See also:\n\
       \  purs compile --help\n"
