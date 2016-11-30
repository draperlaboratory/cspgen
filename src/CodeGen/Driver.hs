module CodeGen.Driver where

import Control.Monad.Except

data Output = Output {memModel :: String, 
                      stubs    :: Maybe String,
                      code     :: String}
type DriverM a = ExceptT String IO a

data DriverInput = DriverInput {diFilename     :: String,
                                diCPPOpts      :: String,
                                diRuntime      :: String,
                                diExternals    :: String,
                                diWarn         :: Bool,
                                diIntermediate :: Bool,
                                diInputList    :: [String]}

data Driver = Driver {genCode :: DriverInput -> DriverM Output}

runDriver :: Driver -> DriverInput -> IO Output
runDriver d di = do
  mOutput <- runExceptT $ genCode d di
  case mOutput of
    Left err     -> error err
    Right output -> return output

data OutputLocs = OutputLocs {memModelLoc :: FilePath,
                              stubLoc     :: FilePath, 
                             codeLoc     :: FilePath}

defaultDriver :: Driver
defaultDriver = Driver $ \DriverInput {diFilename} -> do
  ftxt <- liftIO $ readFile diFilename
  return $ Output {memModel = "",
                   stubs = Nothing,
                   code = ftxt}

outputLocs :: FilePath -> OutputLocs
outputLocs codeLoc = OutputLocs {
    memModelLoc = "globVarDecs.csp",
    stubLoc     = "stubs.csp",
    codeLoc
  }


-- Transformer that adds the given filepath to the head of FDR output
addHeaders :: [FilePath] -> String -> String
addHeaders fps s = concatMap hdr fps ++ s
  where
    hdr fp = "include " ++ show fp ++ "\n"

toStdOut :: Output -> IO ()
toStdOut (Output {memModel,stubs,code}) = putStrLn strOutput
  where
    strOutput = 
          (   "--- begin memory model ---\n" 
           ++ memModel
           ++ "\n--- end memory model ---\n")
       ++ (case stubs of
             Nothing -> ""
             Just stubtxt -> 
                 "--- begin stubs ---\n" 
              ++ stubtxt
              ++ "\n--- end stubs ---\n")
       ++ code

-- Input, variable declarations and output file
toFile :: DriverInput -> OutputLocs -> Output -> IO ()
toFile (DriverInput {diRuntime})
       (OutputLocs {memModelLoc,stubLoc,codeLoc})
       (Output {memModel,stubs,code})                        =
  do case stubs of
       Just stubCode -> do
         writeFile codeLoc (addHeaders [diRuntime,stubName] code) 
         writeFile stubLoc stubCode
       Nothing ->
         writeFile codeLoc (addHeaders [diRuntime] code)
     writeFile memModelLoc memModel 
  where
    stubName        = "stubs.csp"
