module Tests.CSPGenTest.CSPGenTest where

import Data.List (isInfixOf)
import Control.Monad.Except (runExceptT)

import System.Exit (ExitCode(..))
import System.Process (readProcessWithExitCode)

import qualified CodeGen.C.DriverC as C
import qualified CodeGen.Driver as D

import qualified Test.Tasty as T
import qualified Test.Tasty.HUnit as H

testPath :: FilePath
testPath = "examples/basic/"

globVarDecsLoc :: FilePath
globVarDecsLoc = testPath ++ "globVarDecs.csp"

stubLoc :: FilePath
stubLoc = testPath ++ "stubs.csp"

runtimeLoc :: FilePath
runtimeLoc = "runtime.csp"

runtimePTLoc :: FilePath
runtimePTLoc = "runtimePThread.csp"


runtimeAlt :: FilePath
runtimeAlt = "runtimeChans.csp"

externalsLoc :: FilePath
externalsLoc = testPath ++ "externals"

refinesOpts :: [String]
refinesOpts = ["-q", "--format=plain"]

data TestCase = TestCase
  {tcSource  :: FilePath,
   tcDest    :: FilePath,
   tcSpec    :: FilePath,
   tcRuntime :: FilePath}

testCases :: [TestCase]
testCases = map (tc runtimeLoc) [1..36]
         ++ map (tc runtimePTLoc) [37..38]
         ++ map (tc runtimeLoc) [39..47]
         ++ map (tc runtimePTLoc) [48..49]
         ++ map (tc runtimeLoc) [50..54]
  where
    tc :: FilePath -> Int -> TestCase
    tc rt n = TestCase {tcSource=testName ++ ".c",
                        tcDest  =testName ++ ".csp",
                        tcSpec  =testName ++ ".ctest.csp",
                        tcRuntime=rt} 
      where
        ns = show n
        testName = "test_" ++ (replicate (3 - length ns) '0') ++ ns
      

process :: TestCase -> IO Bool
process (TestCase {tcSource,tcDest,tcSpec,tcRuntime}) = do
  let di = D.DriverInput {D.diFilename=testPath ++ tcSource,
                          D.diRuntime=tcRuntime,
                          D.diCPPOpts = "", 
                          D.diExternals=externalsLoc,
                          D.diWarn=False, D.diIntermediate=False, 
                          D.diInputList=[]}
              
      ofile = testPath ++ tcDest
      driver = C.genCSP
  putStrLn $ "Processing " ++ tcSource ++ "..."
  result <- runExceptT $ D.genCode driver di
  case result of 
    Left err -> do putStrLn $ "FAILED\n" ++ err
                   return False
    Right o -> do 
      D.toFile di ((D.outputLocs ofile) {D.memModelLoc = globVarDecsLoc,
                                         D.stubLoc = stubLoc}) o
      (e, out, err) <- readProcessWithExitCode "refines" 
                       [testPath ++ tcSpec, "-q", "--format=plain"] ""
      case e of
        ExitFailure _ -> do putStrLn $ "FAILED\n" ++ err
                            return False
        ExitSuccess -> if "Failed" `isInfixOf` out
                       then 
                         do putStrLn $ "FAILED\n" ++
                                       "In file " ++ ofile ++ "\nFailed assertion:\n" ++ out
                            return False
                       else 
                         do putStrLn "SUCCESS" 
                            return True

makeTest :: (TestCase, Bool) -> T.TestTree
makeTest (TestCase {tcSource}, result) = H.testCase tcSource $ H.assertBool "Result" result

processedTests :: [IO Bool]
processedTests = map process testCases

allTests :: IO T.TestTree
allTests = do
  results <- sequence processedTests
  let zippedResult = zip testCases results
  let tests = T.testGroup "CSPGen Tests" $ fmap makeTest zippedResult
  return tests

runtests, runtestsuite :: IO ()
runtestsuite = do 
  tests <- allTests
  T.defaultMain tests

runtests = do
  exits <- sequence $ map process testCases
  let total = length exits
      wins = length (filter id exits)
  putStrLn $ "Passed " ++ show wins ++ " of " ++ show total ++ " tests.\n"
