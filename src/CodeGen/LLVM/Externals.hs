{- |
Module      :  CodeGen.LLVM.Externals
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
    returnType name(argType1,...,argType2);
@

Here, @returnType@ is the return type of the function (currently the grammar for
these is quite limited).  @name@ is the function's name, which must match the
LLVM name.  For now, this means the mangled name must occur here.

Currently supported types are:

  ty := int | bool | ty* | <name> | void

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

XXX this is mostly a copy of the C version.  Factor out this functionality if
it doesn't diverge substantially.

XXX


-}

module CodeGen.LLVM.Externals (getExternals,ExternalsInfo(..)) where

import Text.Parsec
import Text.Parsec.Token
import Text.Parsec.Expr
import Text.Parsec.Language (haskellStyle)

import Control.Monad.Except

import System.Directory (doesFileExist)

import CodeGen.LLVM.CGMonad (BaseType(..))

-- holds input from parser 
data Setting = MinInt Int | MaxInt Int | NoValue

-- holds output 
data ExternalsInfo = 
  ExternalsInfo {
    funcInfo :: [(String,BaseType,[BaseType])],
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
externalsStyle = haskellStyle {reservedNames   = ["void","int","bool","pid",
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

-------------------------------------
--- FUNCTIONS section parsing
-------------------------------------

-- Parsec parser definitions
typeParser :: Parsec String () BaseType
typeParser = buildExpressionParser table simpleType
  where
--    table :: OperatorTable String () a BaseType
    table =
      [[Postfix $ do _ <- char '*'
                     return PointerType]]

    simpleType :: Parsec String () BaseType
    simpleType = choice knownTypes

    knownTypes :: [Parsec String () BaseType]
    knownTypes =  map (\(n,b) -> exReserved n >> return b)
       [("int",IntType),
        ("bool",BoolType),
        ("void",VoidType),
        ("pid",PIDType)
       ]

--    typeName :: Parsec String () BaseType
--    typeName = NamedType <$> T.Fixed exIdentifier

externalFuncParser :: Parsec String () (String,BaseType,[BaseType])
externalFuncParser = do
  eRetType <- typeParser
  eName <- exIdentifier
  eArgTypes <- exParens $ exCommaSep typeParser
  return (eName,eRetType,eArgTypes)


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
