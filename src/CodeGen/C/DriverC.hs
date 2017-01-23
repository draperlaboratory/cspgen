module CodeGen.C.DriverC where

import           CodeGen.C.Parser (cppParseSanity)
import qualified Language.CSPM.Pretty as Pretty
import           CodeGen.C.CodeGen
import qualified CodeGen.C.Pretty as CPretty
import qualified CodeGen.C.CFGPretty as GPretty
import           CodeGen.C.CFGLiveness (Mode(..))
import           CodeGen.C.ASTtoCFG (cfgTransUnit)
import           CodeGen.C.CGMonad
import           CodeGen.Driver

import           CodeGen.C.SimplifyLoop (sLoopTransUnit)
import           CodeGen.C.SimplifyLValues (sLValTransUnit)
import           CodeGen.C.SimplifyReferences (sRefTransUnit)

import           CodeGen.C.HedgeTrimmer

import           CodeGen.C.Externals (getExternals,ExternalsInfo(..))

import           Data.List (intercalate)
import qualified Data.Map as M

-- only needed for send/recv hack
import qualified Language.CSPM.Syntax as T
import qualified CodeGen.C.Syntax as S
import qualified Language.C as C

import           Control.Monad.Except

genCodeE :: DriverInput -> DriverM Output
genCodeE di@(DriverInput {diFilename,diIntermediate,diExternals,
                          diInputList,diWarn}) = do
    liftIO $ do 
      putStrLn $ "Translating " ++ diFilename ++ " to CSPm."
      putStrLn $ "Step 1: Parsing..."
    ExternalsInfo{funcInfo=externalDefs,minInt,maxInt} <- getExternals diExternals
    let externalCNames = map (\(nm,_,_) -> C.builtinIdent nm) externalDefs
    (sids,code) <- cppParseSanity di externalCNames 
    liftIO $ do 
      putStrLn $ "        Parsing successful (" ++ show (ltu code) 
              ++ " top-level declarations)"
      when diIntermediate $
        writeFile (diFilename ++ ".step1" ) (CPretty.emitTransUnit code)
      putStrLn "Step 2: Trimming the hedges..."
    let trimmedCode = trim (diFilename:diInputList) code
    liftIO $ do
      putStrLn $ "        Trimming succesful (" ++ show (ltu trimmedCode)
              ++ " top-level declarations remain)"
      putStrLn "Step 3: Generating CSP..."
      when diIntermediate $
        writeFile (diFilename ++ ".step2") (CPretty.emitTransUnit trimmedCode)
    let
      -- Initial CG context, computed from parsed external definitions config
      -- file and the corresponding identifiers.
      externalFInfos :: [(S.Id,FInfo)]
      externalFInfos = zip sids $ map externalFInfo externalDefs
        where
          externalFInfo :: (String,[Mode],BaseType) -> FInfo
          externalFInfo (nm,modes,fret) =
            FInfo {ftid = T.Fixed nm,
                   fret,
                   fargs = map (\_ -> UnknownType internal) modes,
                   fvararg = False,
                   fdef = True}
    
      state = initState (minInt,maxInt) externalFInfos
              
      -- A list of the preprocessing stuff we run directly on the C AST.
      -- The must be applied from left to right.
      simplifications = [sRefTransUnit,sLoopTransUnit,sLValTransUnit]
    
      -- A list with the itermediate steps to print via command option -i
      simplifiedCode :: S.TransUnit
      steps :: [S.TransUnit]
      (simplifiedCode,steps) = 
        foldl (\(curCode,acc) opt -> (opt curCode, curCode : acc)) 
              (trimmedCode,[]) simplifications

    when diIntermediate $ liftIO $ do
      let codeString = map (CPretty.emitTransUnit) steps
      writeTUFiles diFilename codeString
    
    let
      -- the argument modes of the external functions from the config file
      modes :: M.Map S.Id [Mode]
      modes = M.fromList $ 
                 map (\(fsid,(_,mode,_)) -> (fsid,mode)) 
                     (zip sids externalDefs)
    

      cfgAndCsp :: CG (String, CspModules)
      cfgAndCsp = do cfg <- cfgTransUnit modes simplifiedCode
                     (GPretty.ppCFG cfg,) <$> transGen cfg

    ((cfgString,CspModules {cmGlobalState,cmStubs,cmCode}),cgWarnings) <-
      case runCG state cfgAndCsp of
        (Left err,_)  ->
          -- XXX in this case we discard the warnings.  It would be nice to show
          -- them.
          throwError ("Compilation Error:\n" ++ err)
        (Right val,w) -> return (val,w)
    liftIO $ do
      when diIntermediate $
        writeFile (diFilename ++ ".step" ++ cfgStepNum steps) cfgString
      putStrLn "        Code generation successful."
      when diWarn $ putStrLn $ intercalate "\n" $ map show cgWarnings

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
    writeTUFiles :: String -> [String] -> IO ()
    writeTUFiles fname tu =
      mapM_ (\(x,y) -> writeFile (fname ++ ".step" ++ show y) x) 
            (zip tu ([3..] :: [Int]))

    cfgStepNum :: [a] -> String
    cfgStepNum x = show $ 3 + (length x)

    ltu :: S.TransUnit -> Int
    ltu = length . S.exts

genCSP :: Driver
genCSP = Driver genCodeE

-- TODO: change (Maybe String, String) to a built-in type
genAST :: Driver
genAST = Driver $ \di -> do
  (_,code) <- cppParseSanity di []
  return $ 
    Output {memModel = "",
            stubs = Nothing,
            code = show code}

genCPretty :: Driver
genCPretty = Driver $ \di -> do
  (_,code) <- cppParseSanity di []
  return $ 
    Output {memModel = "",
            stubs = Nothing,
            code = CPretty.emitTransUnit code}
