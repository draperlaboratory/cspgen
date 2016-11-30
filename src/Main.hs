module Main where

import Data.Maybe (fromMaybe)

import System.Console.GetOpt
import System.Environment
import System.FilePath.Posix (takeBaseName)
import System.Exit (ExitCode(..), exitWith)

import Control.Monad (when)

import qualified CodeGen.C.DriverC as FM
import qualified CodeGen.LLVM.DriverLLVM as LL
import qualified CodeGen.Driver as D
import qualified Tests.CSPGenTest.CSPGenTest as Test
import qualified Tests.CParseTest.CParseTest as PTest
import qualified Tests.LLVMTest.LLVMTest as LTest

data Options = Options {optOutput       :: Maybe FilePath,
                        optDumpAST      :: Bool,
                        optDumpC        :: Bool,
                        optExternals    :: Maybe FilePath,
                        optRuntime      :: Maybe FilePath,
                        optTest         :: Bool,
                        optTestLLVM     :: Bool,
                        optCPP          :: String,
                        optWarn         :: Bool,
                        optIntermediate :: Bool,
                        optLLVM         :: Bool
                       }


defaultOpts :: Options
defaultOpts = Options {optOutput       = Nothing,
                       optDumpAST      = False,
                       optDumpC        = False,
                       optRuntime      = Nothing,
                       optExternals    = Nothing,
                       optTest         = False,
                       optTestLLVM     = False,
                       optCPP          = "",
                       optWarn         = True,
                       optIntermediate = False,
                       optLLVM         = False
                      }


-- A list of options consisting of:
-- * a short name
-- * a long name
-- * an options transformer
-- * a short description of the option
optionList :: [(Char, String, ArgDescr (Options -> Options), String)]
optionList = [('o', "output", ReqArg (\s o -> o {optOutput=Just s}) "FILE",
                      "Output destination"),
              ('l', "llvm",
                 NoArg (\o -> o {optLLVM=True,
                                 optRuntime=case optRuntime o of
                                              Nothing -> Just "runtimeLLVM.csp"
                                              Just s  -> Just s}),
                      "Take in LLVM IR rather than C"),
              ('d', "dump", NoArg (\o -> o {optDumpAST=True}),
                      "Dump the AST representation of the C-Flat code"),
              ('c', "emit-c", NoArg (\o -> o {optDumpC=True}),
                      "Output the parsed C code"),
              ('e', "externals", ReqArg (\s o -> o {optExternals=Just s}) "FILE",
                      "External function specifications"),
              ('r', "runtime", ReqArg (\s o -> o {optRuntime=Just s}) "FILE",
                      "Runtime file"),
              ('p', "cpp-opts", ReqArg (\s o -> o {optCPP = s}) "STRING",
                      "Options to be passed to cpp"),
              ('t', "test", NoArg (\o -> o {optTest=True}),
                      "Run test files"),
              ('u', "lltest", NoArg (\o -> o {optTestLLVM=True}),
                      "Run LLVM tests only"),
              ('w', "warn", NoArg (\o -> o {optWarn=False}),
                      "Hide warnings"),
              ('i', "intermediate", NoArg (\o -> o {optIntermediate=True}),
                      "Show intermediate results")
             ]

options :: [OptDescr (Options -> Options)]
options = map (\(a, b, c, d) -> Option [a] [b] c d) optionList

optionPrint :: String
optionPrint = concat $ map (\(x,_,_,_) -> [' ','-',x]) optionList

main :: IO ()
main = do
  argv <- getArgs
  case getOpt Permute options argv of
    (opts,ifiles,[]) -> do
      let Options {optOutput, optDumpAST, optDumpC, optLLVM,
                   optExternals, optRuntime, optTest, optTestLLVM, optCPP, 
                   optWarn, optIntermediate} = 
              foldl (\o f -> f o) defaultOpts opts
      when (1 < (length $ filter id [optDumpAST,optTest,optTestLLVM])) $
           error $ usage ["Please specify only one of -d, -t, or -u."]
      when optTest $ do PTest.runtests
                        Test.runtests
                        LTest.runtests
                        exitWith ExitSuccess
      when optTestLLVM $ LTest.runtests >> exitWith ExitSuccess
      when (length ifiles == 0) $
           error $ usage ["Please specify an input file."]
      when (length ifiles > 1) $ do 
           writeFile tmpFile ""
           mapM_ addFile ifiles

      let ifile, ofile, rfile, efile :: FilePath
          ifile 
           | length ifiles <  2 = head ifiles 
           | otherwise          = tmpFile -- if more than 1 use temp file
          ofile =
            case (optOutput,ifiles) of
              (Just f,_) -> f
              (_,   [f]) -> (takeBaseName f) ++ ".csp"
              _          -> "cspgenModel.csp"
          rfile = fromMaybe "runtime.csp" optRuntime
          efile = fromMaybe (if optLLVM then "externalsLLVM" else "externals") optExternals
      let driver :: D.Driver 
          driver = if optLLVM then LL.genCSP else
                     if optDumpAST then FM.genAST else
                       if optDumpC then FM.genCPretty else
                           FM.genCSP
          
          di = D.DriverInput {D.diFilename=ifile,
                              D.diCPPOpts=optCPP,
                              D.diRuntime=rfile,
                              D.diExternals=efile,
                              D.diWarn=optWarn,
                              D.diIntermediate=optIntermediate,
                              D.diInputList=ifiles}
      output <- D.runDriver driver di
      D.toFile di (D.outputLocs ofile) output
    (_,_,errs) -> error $ usage errs
  where
    header = "Usage: cspgen [OPTIONS] FILE"
    usage errs = concat errs ++ "\n" ++ usageInfo header options
    tmpFile = "tmp___001"
    
    addFile :: String -> IO ()
    addFile fin = do
      contents <- readFile fin
      appendFile tmpFile $ "#line 1 \"" ++ fin ++ "\"\n" ++ contents
