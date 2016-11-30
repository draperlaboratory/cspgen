module Tests.LLVMTest.LLVMTest where

import Data.List (isInfixOf)
-- import Control.Monad (when)
import Control.Monad.Except (runExceptT)

import System.Exit (ExitCode(..))
import System.Process (readProcessWithExitCode)

import qualified CodeGen.LLVM.DriverLLVM as L
import qualified CodeGen.Driver as D

-- import HSH.Command

import qualified Test.Tasty as T
import qualified Test.Tasty.HUnit as H

testPath :: FilePath
testPath = "examples/basic/"

cTestNames :: [String]
cTestNames = (map (\i -> "test_00" ++ show i) ([1..9] :: [Int]))
          ++ (map (\i -> "test_0" ++ show i) ([10..59] :: [Int]))

cppTestNames :: [String]
cppTestNames = map (\i -> "cpp_test_00" ++ show i) ([1..8] :: [Int])

globVarDecsLoc :: FilePath
globVarDecsLoc = testPath ++ "globVarDecs.csp"

stubLoc :: FilePath
stubLoc = testPath ++ "stubs.csp"


runtimeLLVM :: FilePath
runtimeLLVM = "runtimeLLVM.csp"

data TestInfo = TestInfo {testSuffix :: String,
                          testCompiler :: String,
                          testFlags :: [String]}

runTest :: TestInfo -> String -> IO Bool 
runTest (TestInfo {testSuffix,testCompiler,testFlags}) testname = do
  let cFilename = testPath ++ testname ++ testSuffix
      diFilename = testPath ++ testname ++ ".ll"
      -- compileCmd = ShellCommand $ "clang -emit-llvm -S " ++ diFilename
      di = D.DriverInput {D.diFilename,D.diCPPOpts="",D.diRuntime=runtimeLLVM,
                          D.diExternals="examples/basic/externalsLLVM",
                          D.diWarn=False,D.diIntermediate=False,D.diInputList=[]}

      outputFile = testPath ++ testname ++ ".csp"
      driver = L.genCSP
  putStrLn $ "Processing " ++ testname ++ " for LLVMTest..."
  putStrLn "Compiling LLVM from source..."
  -- runIo compileCmd
  (_, _, _) <- readProcessWithExitCode
                    testCompiler
                    (testFlags ++ ["-m32","-emit-llvm","-S","-o",diFilename,cFilename])
                    ""
  putStrLn "Generating CSP ..." 
  result <- runExceptT $ D.genCode driver di
  case result of 
    Left err -> do putStrLn $ "FAILED\n" ++ err
                   return False
    Right o -> do 
      D.toFile di ((D.outputLocs outputFile){D.memModelLoc = globVarDecsLoc,
                                             D.stubLoc = stubLoc}) o
      putStrLn "Checking refinement ..."
      (e2, out2, err2) <- readProcessWithExitCode "refines"
                          [testPath ++ testname ++ ".lltest.csp", "-q", "--format=plain"] ""
      case e2 of 
        ExitFailure _ -> do putStrLn $ "FAILED\n" ++ err2
                            return False
        ExitSuccess -> if "Failed" `isInfixOf` out2
                       then
                         do putStrLn $ "FAILED\n" ++
                                       "In file " ++ outputFile ++ "\nFailed assertion:\n" ++ out2
                            return False
                       else
                         do putStrLn "SUCCESS"
                            return True

makeTest :: (String, Bool) -> T.TestTree
makeTest (file, result) = H.testCase file $ H.assertBool "Result" result

cTestResults :: [IO Bool]
cTestResults = map (runTest tinfo) cTestNames
  where
    tinfo = TestInfo {testSuffix=".c",
                      testCompiler="clang",
                      testFlags=[]}

cppTestResults :: [IO Bool]
cppTestResults = map (runTest tinfo) cppTestNames
  where
    tinfo = TestInfo {testSuffix=".cpp",
                      testCompiler="clang++",
                      testFlags=["-fno-rtti"]}

allTests :: IO T.TestTree
allTests = do
  cresults <- sequence cTestResults
  cppresults <- sequence cppTestResults
  let zippedResult = zip (cTestNames ++ cppTestNames)
                         (cresults ++ cppresults)
  let tests = T.testGroup "DriverLLVM Tests" $ fmap makeTest zippedResult
  return tests

runtests, runtestsuite :: IO ()
runtestsuite = do
  tests <- allTests
  T.defaultMain tests

runtests = do 
  exits <- sequence (cTestResults ++ cppTestResults)
  let total = length exits
      wins = length (filter id exits)
  putStrLn $ "Passed " ++ show wins ++ " of " ++ show total ++ " tests.\n"

