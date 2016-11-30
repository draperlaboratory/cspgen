{- |
Module      :  CodeGen.C.Externals
Description :  Parser for external function specs
Copyright   :  Draper Laboratories

This parses configuration files for cspgen.  The files have two sections and may
contain comments in Haskell style.  The high-level format is:

    @section FUNCTIONS {
    
      <function_list>
    
    }
    
    @section SETTINGS {
    
      <settings_list>
    
    }

-----

The FUNCTIONS section contains a list of functions which are used in the C code
but whose implementations are expected to be provided by the cspgen runtime.
The format for these files is a list of declarations of the form:

@
    returnType name(argMode_1,...,argMode_n);
@

Here, @returnType@ is the return type of the function (currently the grammar for
these is quite limited).  @name@ is the function's name, which must match both
the name used in the C code and the name in the csp runtime.  The function must
have @n@ arguments, and @argMode@ is defined by:

@
   argMode ::=  in  |  out  | inout
@

This specifies the mode of the argument.  "@in@" indicates a normal argument
used as an input to the function.  "@out@" indicates an "output" argument, for
example when a pointer is passed to a function as a location to write some data
to.  "@inout@" is an argument that is read from and then written to.  This
information is necessary for the control flow analysis done by cspgen.

-----

The SETTINGS section contains a list of options and the values assigned to them.
The format is a list of declarations of the form:

      settingName = value;

Currently the only "settingName"s supported are "minimumCVal" and "maximumCVal".
The value must be an integer.

-----

XXX One flaw in the current system is that types are not supported very well.
We only handle a few basic return types to avoid needing a full C parser here,
and we don't handle argument types at all.


-}

module CodeGen.C.Externals (getExternals,ExternalsInfo(..)) where

import Text.Parsec
import Text.Parsec.Token
import Text.Parsec.Language (haskellStyle)

import Control.Monad.Except

import System.Directory (doesFileExist)

import CodeGen.C.CFGLiveness (Mode(..))
import CodeGen.C.CGMonad (BaseType(..))
import qualified CodeGen.C.Syntax as S (SPos(..))

-- holds nput from parser 
data Setting = MinInt Int | MaxInt Int | NoValue

-- holds output 
data ExternalsInfo = 
  ExternalsInfo {
    funcInfo :: [(String,[Mode],BaseType)],
    minInt :: Int,
    maxInt :: Int
}

defaultExternalsInfo :: ExternalsInfo
defaultExternalsInfo =
  ExternalsInfo {
    funcInfo = [],
    minInt   = 0,
    maxInt   = 4
  }

-- Setting up tokenizer
externalsStyle :: LanguageDef st
externalsStyle = haskellStyle {reservedNames   = ["in","out","inout",
                                                  "void","int","bool","pid",
                                                  "minimumCVal","maximumCVal"],
                               reservedOpNames = ["=", "section"]}

exCommaSep :: Parsec String u a -> Parsec String u [a]
exIdentifier :: Parsec String u String
exParens :: Parsec String u a -> Parsec String u a
exReserved :: String -> Parsec String u ()
exReservedOp :: String -> Parsec String u ()
exWhiteSpace :: Parsec String u ()
exSemi :: Parsec String u String
exInteger :: Parsec String u Integer
exBraces :: Parsec String u a -> Parsec String u a
exSymbol :: String -> Parsec String u String
TokenParser {commaSep   = exCommaSep,
             reserved   = exReserved,
             reservedOp = exReservedOp,
             identifier = exIdentifier,
             parens     = exParens,
             whiteSpace = exWhiteSpace,
             semi       = exSemi,
             integer    = exInteger,
             braces     = exBraces,
             symbol     = exSymbol} 
  = makeTokenParser externalsStyle

getPos :: Monad m => ParsecT s u m S.SPos
getPos = do
  sourcePos <- getPosition
  return $ S.SPos {S.sourceName = sourceName sourcePos,
                   S.sourceLine = sourceLine sourcePos,
                   S.sourceColumn = sourceColumn sourcePos}

-------------------------------------
--- FUNCTIONS section parsing
-------------------------------------

-- Parsec parser definitions
typeParser :: Parsec String () BaseType
typeParser = do
  pos <- getPos
  choice $ typeParsers pos
  where
    types :: [(String,S.SPos -> BaseType)]
    types = [("int",IntType),
             ("bool",BoolType),
             ("void",UnknownType),
             ("pid",PIDType)
            ]

    typeParsers :: S.SPos -> [Parsec String () BaseType]
    typeParsers pos = map (\(s,t) -> exReserved s >> return (t pos))
                          types

modeParser :: Parsec String () Mode
modeParser = 
      (exReserved "in" >> return MInput)
  <|> (exReserved "out" >> return MOutput)
  <|> (exReserved "inout" >> return MUnknown)

externalFuncParser :: Parsec String () (String,[Mode],BaseType)
externalFuncParser = do
  eType <- typeParser
  eName <- exIdentifier
  eModes <- exParens $ exCommaSep modeParser
  return (eName,eModes,eType)


-------------------------------------
--- SETTINGS section parsing
-------------------------------------

settingNameParser :: String -> Parsec String () String
settingNameParser name = do 
  exReserved name 
  return name 

externalSettingParser :: Parsec String () Setting
externalSettingParser = do
  eName  <- settingNameParser "minimumCVal" <|> settingNameParser "maximumCVal" 
  exReservedOp "="
  eValue <- exInteger
  let setting = case eName of 
        "minimumCVal" -> MinInt (min (fromInteger eValue) 0)
        "maximumCVal" -> MaxInt (max (fromInteger eValue) 1)
        _             -> NoValue
  return setting


-- Updates the provided ExternalsInfo with any explicit settings that appeared
-- in the configuation file.
settingsExtractor :: ExternalsInfo -> [Setting] -> ExternalsInfo
settingsExtractor = foldr handleSetting
  where
    handleSetting :: Setting -> ExternalsInfo -> ExternalsInfo
    handleSetting NoValue      ei = ei
    handleSetting (MinInt val) ei = ei {minInt=val}
    handleSetting (MaxInt val) ei = ei {maxInt=val}


-----------------------------------
---- Top level parser and interface
-----------------------------------

missingExternalWarning :: String -> String
missingExternalWarning fname =
     "Warning: \"" ++ fname ++ "\" not found.  Proceeding with "
  ++ "no external functions."

sectionParser :: String -> Parsec String () a -> Parsec String () [a] 
sectionParser name p = do 
  _ <- exSymbol "@section"
  _ <- exSymbol name
  info <- exBraces $ sepEndBy p exSemi
  return info

externalsParser :: Parsec String () ExternalsInfo
externalsParser = do
  exWhiteSpace 
  externals <- sectionParser "FUNCTIONS" externalFuncParser
  values <- sectionParser "SETTINGS" externalSettingParser
  optional exWhiteSpace
  eof
  let ei = settingsExtractor (defaultExternalsInfo {funcInfo=externals})
                             values
  return ei


getExternals :: (MonadError String m, MonadIO m) => FilePath -> m ExternalsInfo
getExternals fileName = do
  externalsExists <- liftIO $ doesFileExist fileName
  if externalsExists then do
    cfgFileContents <- liftIO $ readFile fileName
    let result = parse externalsParser fileName cfgFileContents
    case result of
      Left parseError -> throwError $ show parseError
      Right externals -> return externals
  else do
    liftIO $ putStrLn $ missingExternalWarning fileName
    return defaultExternalsInfo
