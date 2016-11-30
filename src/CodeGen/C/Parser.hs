{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{- necessary due to a bug in this version of GHC -}

{- |
Module      :  CodeGen.C.Parser
Description :  Parser for C-flat
Copyright   :  Draper Laboratories

Author      :  Chris Casinghino

This parses and sanity-checks C files.  We use the Language.C haskell library
for the parsing, then we translate the resulting AST into a simpler internal
AST, throwing an error if we encounter syntactic forms we don't handle.

-}

module CodeGen.C.Parser (cppParseSanity) where

import Language.C.Parser
import Language.C.Data.Position

import qualified Data.ByteString as B
import Data.List (intercalate)

import qualified Language.C as S
import qualified CodeGen.C.Syntax as T
import CodeGen.C.SyntaxSimplifier (simplifyTranslUnit,SimplResult(..))
import CodeGen.Driver (DriverInput(..))

import System.Process
import System.Exit (ExitCode(..))
import System.FilePath

import Control.Monad.Except


cLangParser :: MonadError String m => B.ByteString -> Position -> m S.CTranslUnit
cLangParser contents pos = 
  case parseC contents pos of
    Left perr -> throwError $ show perr
    Right ctu -> return ctu

data InputError = CPPError | CParseError String | SanityError String

instance Show InputError where
  show CPPError = "Error during preprocessing"
  show (CParseError s) = "Error during parsing: " ++ s
  show (SanityError s) = "Error while sanity-checking the parsed code: " ++ s

-- Does all three phases
cppParseSanity :: (MonadError String m, MonadIO m) => 
    DriverInput -> [S.Ident] -> m ([T.Id],T.TransUnit)
cppParseSanity (DriverInput {diFilename,diCPPOpts,diWarn}) lib = do
  let tempfile = "/tmp/" ++ takeFileName diFilename ++ ".cpp"
      args = [diCPPOpts,"-w","-o " ++ tempfile, diFilename]
  cppECode <- liftIO $ system ("cpp " ++ intercalate " " args)
  case cppECode of
    ExitSuccess -> do
      preprocessedC <- liftIO $ B.readFile tempfile
      cAST <- cLangParser preprocessedC (initPos diFilename)
      case simplifyTranslUnit cAST lib of
        Left err -> throwError $ show $ SanityError err
        Right (SR {srWarnings,srResult,srLibIds})  -> do
          when diWarn $ liftIO $ mapM_ putStrLn srWarnings
          return (srLibIds,srResult)
    _ -> throwError $ "Error during preprocessing"
