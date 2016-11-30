module Tests.CParseTest.CParseTest where

import CodeGen.Driver (DriverInput(..))
import CodeGen.C.Parser
import qualified CodeGen.C.Pretty as CPretty
import Language.C
import qualified Test.Tasty as T
import qualified Test.Tasty.HUnit as H
import Control.Monad.Except (runExceptT)

testPath :: FilePath
testPath = "examples/basic/"

testFiles :: [String]
testFiles = "SysModel"
          : (map (\i -> "test_00" ++ show i) ([1..9] :: [Int]))
         ++ (map (\i -> "test_0" ++ show i) ([10..54] :: [Int]))

process :: FilePath -> IO Bool
process file = do
  let diFilename = testPath ++ file ++ ".c"
      di = DriverInput {diFilename,diCPPOpts="",diRuntime="runtime.csp",
                        diExternals="externals",diWarn=False,
                        diIntermediate=False,diInputList=[]}
  putStrLn $ "Processing " ++ file ++ "..."
  input <- runExceptT $ cppParseSanity di builtins
  case input of
    Left err -> do putStrLn $ "FAILED\n" ++ show err
                   return False
    Right (_,code) -> do
      let tempFile = "/tmp/" ++ file ++ ".c.bootstrap"
      writeFile tempFile $ CPretty.emitTransUnit code
      input' <- runExceptT $ cppParseSanity (di {diFilename=tempFile}) builtins
      case input' of
        Left err    -> do putStrLn $ "FAILED\n" ++ show err
                          return False
        Right (_,code') -> 
            let result = code == code' in
            do if result then putStrLn "PASSED"
                         else do putStrLn "FAILED: ASTs don't match"
                                 print code
                                 print code'

               return result

  where
    builtins = [builtinIdent "send",
                builtinIdent "echo",
                builtinIdent "recv"]

makeTest :: (String, Bool) -> T.TestTree
makeTest (fname, result) = H.testCase fname $ H.assertBool "Result" result

processedTests :: [IO Bool]
processedTests = map process testFiles

allTests :: IO T.TestTree
allTests = do
    results <- sequence processedTests
    let zippedResult = zip testFiles results
    let tests = T.testGroup "CParse Tests" $ fmap makeTest zippedResult
    return tests

runtests, runtestsuite  :: IO ()
runtestsuite = do 
    tests <- allTests
    T.defaultMain tests


runtests = do -- runs command line tests
  exits <- sequence $ processedTests
  let total = length exits
      wins = length (filter id exits)
  putStrLn $ "Passed " ++ show wins ++ " of " ++ show total ++ " tests."
