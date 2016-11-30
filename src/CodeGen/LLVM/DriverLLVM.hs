{- |
   Module      :  CodeGen.LLVM.DriverLLVM
   Description :  Driver for LLVM translation to CSP
   
   Author      :  Chris Casinghino
   
   This module contains the high level "Driver" used by main to invoke the LLVM
   translation to CSP.
-}
module CodeGen.LLVM.DriverLLVM where

import qualified LLVM.General as L
import qualified LLVM.General.Context as L
import qualified LLVM.General.AST as LA (Name(..))
import qualified LLVM.General.Diagnostic as Diag

-- import qualified LLVM.General.PassManager as PM

import           Control.Monad.Except

import           CodeGen.Driver
import           CodeGen.LLVM.CGMonad
import           CodeGen.LLVM.TransModule
import           CodeGen.LLVM.Externals (getExternals,ExternalsInfo(..))

import           Data.List (intercalate)
import qualified Language.CSPM.Syntax as T
import qualified Language.CSPM.Pretty as Pretty

processModule :: ExternalsInfo -> L.Module -> IO (Either String CspModules, [Warning])
processModule (ExternalsInfo {funcInfo,minInt,maxInt}) lm = do
--  How to run LLVM passes
--  _ <- runExceptT $ L.writeLLVMAssemblyToFile (L.File "modBefore") lm
--  b <- PM.withPassManager (PM.defaultCuratedPassSetSpec {PM.optLevel = Just 3})
--           (\pm -> PM.runPassManager pm lm)
--  _ <- runExceptT $ L.writeLLVMAssemblyToFile (L.File "modAfter") lm
  lam <- L.moduleAST lm
  let extFunc :: (String,BaseType,[BaseType]) -> (LA.Name,GlobFuncInfo)
      extFunc (nm,ret,args) = (LA.Name nm,
                               GFInfo {ftid=T.Fixed nm,
                                       fret=ret,
                                       fargs=args,
                                       ftag=T.Fixed ("FP_" ++ nm),
                                       fdef=True})

      state = initState (minInt,maxInt) $ map extFunc funcInfo
  return $ runCG state (transModule lam)

driver :: DriverInput -> DriverM Output
driver (DriverInput {diFilename,diWarn,diExternals}) = do
  ext <- getExternals diExternals
  result <-
    liftIO $ L.withContext $ \c ->
      runExceptT $ L.withModuleFromLLVMAssembly c file (processModule ext)
  (output,warnings) <-
    case result of
      Left (Left s)  -> throwError s
      Left (Right d) -> throwError $ Diag.diagnosticDisplay d
      Right o        -> return o
  when diWarn $ liftIO $ putStrLn $ intercalate "\n" $ map show warnings
  CspModules {cmGlobalState,cmStubs,cmCode} <-
    case output of
      Left err -> throwError ("Compilation Error:\n" ++ err)
      Right o  -> do
        liftIO $ putStrLn "Code generation successful"
        return o
  -- XXX factor out everything from here on down - it's identical in C version
  modules <-                             
    case cmStubs of
      Nothing -> return [cmGlobalState,cmCode]
      Just stubMod -> do 
        liftIO $ putStrLn $ 
             "Warning: " ++ show (length $ T.topLevels stubMod) 
          ++ " functions were "
          ++ "declared but not defined.  Stubs for these functions "
          ++ "will be included in the generated CSP."
        return [cmGlobalState,stubMod,cmCode]
  let (txt,warns) = Pretty.emitMods modules
  when (not $ null warns) $ liftIO $ do
    putStrLn "The pretty printer warns that:"
    mapM_ putStrLn warns
  case txt of
    (gtxt:codetxt:[]) -> 
      return $
        Output {memModel = gtxt,
                stubs = Nothing,
                code = codetxt}
    (gtxt:stubtxt:codetxt:[]) ->
      return
        Output {memModel = gtxt,
                stubs = Just stubtxt,
                code = codetxt}
    _ -> error "Internal Error: emitMods returned incorrect number of modules."
  where
    file = L.File diFilename

genCSP :: Driver
genCSP = Driver driver
