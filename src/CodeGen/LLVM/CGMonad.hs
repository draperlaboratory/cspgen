{- |
   Module      :  CodeGen.LLVM.CGMonad
   Description :  State/Error/... monad used by translation passes.
   
   Author      :  Chris Casinghino
   
   This module defines the "CG" monad which is used by the translation passes to
   manage state and error conditions.  It additionally defines a number of basic
   datatypes, primarily related to information recorded by the monad.

-}

module CodeGen.LLVM.CGMonad
  (ErrMsg,
   GlobInfo(..),GlobVarInfo(..),GlobVarLayout(..),
   GlobFuncInfo(..),
   TypeInfo(..),DataInfo(..),FirstClassInfo(..),StructInfo(..),
   BaseType (..),ppBaseType,btFirstFirstClass,isPointerLike,dataInfoFirstFCI,
   Warning(..),
   initState,CG,-- Abstract
   freshGlobVar,freshGlobMem,DataRep(..),
   freshFunc,setFuncDefined,lookupFPtrDeref,allFPtrDerefs,
   addAlias,
   lookupRepType,
   freshSSA,freshBlockSSA,freshTid,clearSSAVars,addSSAType,SSAVarInfo(..),
   addCtor,addDtor,getCtors,getDtors,
   lookupTypeDef,lookupTypeDefFail,lookupTypeInfo,
   lookupGlobal,lookupSSA,lookupSSAName,
   addTypeDef,transType,
   allGlobals,allFunctions,allTypeInfos,
   setCurrentLoc,clearCurrentLoc,getCurrentLoc,
   runCG,
   intTypeInfo,boolTypeInfo,floatTypeInfo,mutexTypeInfo,
   intFCInfo,boolFCInfo,floatFCInfo,mutexFCInfo,pidFCInfo,
   fptrTypeInfo,fptrFCInfo,
   getIntRange,addWarning,getWarnList,

   --- below here, to be moved
   prettyLLVMName, MemInfo(..)
  )
where

import           Control.Monad (ap,foldM,unless,when)

import qualified Language.CSPM.Syntax as T
import qualified LLVM.General.AST as S

import           Data.Char (toLower)
import           Data.List (intercalate)
import qualified Data.Map.Strict as M
import           Data.Maybe (fromMaybe)

import CodeGen.LLVM.ModelIdentifiers

type ErrMsg = String

---------------------------------------------
--- Types for representing memory

-- XXX GlobVarInfo and its pieces contain a lot of redundant
-- information.  This was convenient for efficient lookup of relevant
-- identifiers and during the construction of the MemInfo in
-- TransModule, but I bet there is a cleaner way to do things.

data GlobVarLayout = GVCell T.Exp
                   | GVAgg [GlobVarInfo]
  deriving (Show)
           
-- GlobVarInfo records information about the structure of memory at a
-- particular location.  It's the analogue of "DataRep", but with more
-- type and naming information.
--
-- In the case of aggregate types, the T.Id should be the target name for the
-- "first" cell in the and the BaseType should be the type of the whole
-- array/substructure.
data GlobVarInfo =
  GVInfo {gvtid :: T.Id,
          gvtype :: BaseType,
          gvlayout :: Maybe GlobVarLayout}
  deriving (Show)

data GlobFuncInfo =
  GFInfo {ftid  :: T.Id,
          -- The name of this function's CSP implementation, for when it is
          -- called in other bits of code.

          fret  :: BaseType,
          -- The return type, to help checking type information when this function is
          -- called in other bits of code.

          fargs :: [BaseType],
          -- The types of its arguments, which allow us to typecheck uses of this
          -- function or to produce a stub for it in the event it is never defined.

          ftag :: T.Id,
          -- ftag is the constructor in the FPtr datatype that corresponds to
          -- this particular function.

          fdef  :: Bool
          -- Whether this function has been defined.
         }
  deriving (Show)

-- In LLVM, the global namespace contains both global variables and functions.
-- We try to keep track of which is which in the state monad.
data GlobInfo = GlobVar GlobVarInfo
              | GlobFunc GlobFuncInfo
  deriving Show                      

type GMap = M.Map S.Name GlobInfo

-- LLVM allows global aliases - essentially multiple names for the same global
-- or function.  We keep track of these in a separate map, which we check before
-- looking up a global.  XXX This is not the most effiecient way to handle
-- aliases.
type AMap = M.Map S.Name S.Name

-- SSA var map: from in-scope SSA vars to target names.  The intention is that
-- the map will be initialized with names for all the SSA vars when entering a
-- function.  As we translate the blocks, type information is added.  Then the
-- map is cleared when we finish the function.
--
-- It is useful to store the representation type, since it sometimes differs
-- from the LLVM type annotations.  However, it is a bit tricky to calculate
-- this type up front, since it depends on our translation of instructions.  For
-- now, we just add the information to the SMap when convenient.  In the future,
-- we will probably want a more concerted effort to calculate this up front.
data SSAVarInfo = SVInfo {svname :: T.Id,
                          svreptype :: Maybe BaseType}
  deriving (Eq,Show)

type SMap = M.Map S.Name SSAVarInfo

-- Function pointer map.  It maps function types to the names of helper
-- functions that "dereference" function pointers at those types and applies
-- the resulting function.  For example, for a function like:
--
--    int foo(int x, int* y)
--
-- The helper function will have a type like:
--
--        (FPtrTag,CInt,CIntLoc,Stack,StackAddr,PID,
--         (Stack,StackAddr,PID,Int) -> Proc)
--     -> Proc
--
-- So, this function takes: the function pointer, the arguments to the function,
-- and the normal stack/stack pointer/pid/continuation stuff, where the
-- continuation expects to be given the return value of the function.
--
-- One minor trick is that the keys in the map are not BaseTypes, because often
-- different basetypes have the same representations (pointers to two classes
-- where one is a subclass of the other).  Instead we the csp name of the
-- representation type.
type FPtrMap = M.Map ([T.Id],T.Id) T.Id

data BaseType =
    IntType
        -- Any "integer" type, including chars and longs

  | BoolType
        -- Bools, handled separately because we can model them more precisely.

  | FloatType
        -- Any floating point type, including floats, doubles, etc.

  | MutexType
      -- A special case for any C types that we want to interpret as mutexes.

  | PIDType
      -- A special case for any C types that we want to interpret as thread ids.

  | VoidType

  | StructType [BaseType]
     -- These are LLVM's "literal" structure types, which means they are
     -- identified only by their contents.

  | NamedType S.Name
     -- We need named types for a few reasons (for example, breaking recursion
     -- in struct definitions).  This breaks our previous promise that equality
     -- on BaseType was just structural equality.

  | PointerType BaseType
  | ArrayType BaseType Int

  -- Functions and function pointers.  These are in weird special case limbo
  -- land right now, as they aren't really supported.
  | FunctionType
  | FPtrType
  deriving (Show,Eq,Ord)
-- XXX this derived notion of Eq doesn't correspond with LLVM's "structural
-- typing" idiom

ppBaseType :: BaseType -> String
ppBaseType BoolType          = "bool"
ppBaseType IntType           = "int"
ppBaseType FloatType         = "float"
ppBaseType MutexType         = "MUTEX"
ppBaseType PIDType           = "PID"
ppBaseType VoidType          = "void"
ppBaseType (StructType typs) =
  "{" ++ intercalate ", " (map ppBaseType typs) ++ "}"
ppBaseType (NamedType n)     = '%' : prettyLLVMName n
ppBaseType (PointerType bt)  = ppBaseType bt ++ "*"
ppBaseType (ArrayType bt sz) = ppBaseType bt ++ "[" ++ show sz ++ "]"
ppBaseType FunctionType      = "<function type>"
ppBaseType FPtrType          = "<function pointer>"

-- Here "first-class" means roughly "takes up one cell in memory".  Note that
-- this function isn't totally faithful - in particular, NamedTypes are not
-- considered first class, but really we can't tell without looking up their
-- definition.
btIsFirstClass :: BaseType -> CG Bool
btIsFirstClass BoolType         = return True
btIsFirstClass IntType          = return True
btIsFirstClass FloatType        = return True
btIsFirstClass MutexType        = return True
btIsFirstClass PIDType          = return True
btIsFirstClass VoidType         = return True
btIsFirstClass (StructType _)   = return False
btIsFirstClass (NamedType nm)    = do
  stype <- lookupTypeDefFail nm "btIsFirstClass"
  btype <- transType stype
  btIsFirstClass btype
btIsFirstClass (PointerType _)  = return True
btIsFirstClass (ArrayType _ _)  = return False
btIsFirstClass FunctionType     = return False
btIsFirstClass FPtrType         = return True

-- If the provided BaseType is first-class, this is the identity.  Otherwise, it
-- finds the base type of the first memory cell of the composite type.
btFirstFirstClass :: BaseType -> CG (Maybe BaseType)
btFirstFirstClass (StructType (b:_))   = return $ Just b
btFirstFirstClass (ArrayType b _)      = return $ Just b
btFirstFirstClass (NamedType nm)       = do
  stype <- lookupTypeDefFail nm "btFirstFirstClass"
  btype <- transType stype
  btFirstFirstClass btype
btFirstFirstClass bt = do
  isFC <- btIsFirstClass bt
  if isFC then return (Just bt) else
    fail $ "Internal error: btFirstFirstClass called on unsupported type "
        ++ ppBaseType bt

-- returns inner type, if basetype is array or pointer.  Is in CG to deal with
-- named type lookup.  String is location for good error message in event of
-- typedef lookup failure.
isPointerLike :: BaseType -> String -> CG (Maybe BaseType)
isPointerLike (PointerType bt) _ = return $ Just bt
isPointerLike (ArrayType bt _) _ = return $ Just bt
isPointerLike (NamedType n)    s = do
  stype <- lookupTypeDefFail n s
  btype <- transType stype
  isPointerLike btype s
isPointerLike  _ _ = return Nothing

data TypeInfo = 
   TypeInfo {tiNameHint :: String,
               -- A string to use in name calculations and error messages 

             tiLocType :: T.Id, -- the type of locations that store this type
             
             tiGlobalLocType :: T.Id,  -- the type of global locations that store this type
             
             -- The next four are tags used in the datatype representing
             -- locations of this type, which looks like:
             --   data FooLoc = tiNullLoc | tiUnknown
             --    .          | tiLocalLocTag stackAddress
             --    .          | tiGlobalLocTag tiGlobalLocType
             tiLocalLocTag :: T.Id,
             tiGlobalLocTag :: T.Id,
             tiNullLoc :: T.Id,
             tiUnknownLoc :: T.Id,

             -- In the implenentation of getElementPtr, we need to manipulate
             -- "Maybe tiLocType"s.  Sadly, CSPm has no built in Maybe type
             -- constructor.  So, we define the Maybe type and the maybe
             -- function for each location type.  Here we store the relevant
             -- names.
             tiLocMaybeType :: T.Id,
             tiLocMaybeJust :: T.Id,
             tiLocMaybeNothing :: T.Id,
             tiLocMaybeElim :: T.Id,

             -- Sometimes pointers are checked for equality (e.g., checking for
             -- a null pointer).  Since each kind of pointer in our model has
             -- its own representation type, we need a custom equality function
             -- too.  Its type is: (FooLoc,FooLoc) -> CInt.  It always returns
             -- 0, 1 or unknown.  Here, we record its name.
             tiLocEqCheck :: T.Id,

             -- A function used by the memory model to calculate addresses when
             -- indexing into arrays that hold this kind of data.  Used in the
             -- implementation of getElementPtr.
             --
             -- The type of the function is, roughly: (FooLoc,Int) -> FooLocMaybe
             tiArrayIndexer :: T.Id,

             tiBase    :: BaseType,
               -- It is convenient to record the BaseType that was used to
               -- create this TypeInfo here.

             tiDataInfo :: DataInfo
               -- Info about the how to deal with data of this type.  Either
               -- it's a first class type, which has an explicit data
               -- representation, or it's a struct and we record names for the
               -- functions that calculate the addresses of its fields info (and
               -- the FCI of the base type in the first position, for
               -- convenience).
            }
   deriving (Show,Eq,Ord)

data DataInfo = DIFirstClass FirstClassInfo
              | DIStruct StructInfo
              | DIArray ArrayInfo
  deriving (Show,Eq,Ord)

data ArrayInfo = ArrayInfo {
  aiElementFCI :: FirstClassInfo
  -- This is the fci for whatever "first-class" data element is at the beginning
  -- of the array.  So, if it's an array of ints, it's the FCI for int.  If it's
  -- an array of structs, it's the FCI for whatever is in the very first cell of
  -- the struct. This is sometimes useful as when a load or store happens at an
  -- array location.
}
  deriving (Show,Eq,Ord)

data StructInfo = StructInfo {
    siFirstFCI :: FirstClassInfo,
    -- This is the fci for whatever "first-class" data element is first in the struct.
    -- I.e., the FCI drawn from the type of whatever is in the first 32-bit
    -- memory cell.  This is sometimes useful as when a load or store happens at
    -- a struct location.
  
    siGetFieldPtrs :: [T.Id]
    -- These are the names of functions used in the implementation of
    -- getElementPtr.  For each field after the first, we define a function
    -- which takes the address of a struct in memory and calculates the
    -- address of the field.  A few notes:
    --
    --   - This isn't necessary for the first field because its address is the
    --     same as the outer struct.
    --
    --   - These names are only stored for the top-level fields of the
    --     structs, not the subfields of those fields.  We index one level at
    --     a time and to go deeper we'll get the typeinfo for the relevant
    --     substructure.
    --
    --   - The type of the function is, roughly:
    -- 
    --          fieldPtr :: (FooLoc) -> Maybe BarLoc
    --
    --     Here, FooLoc is the type of pointers to the struct (really the type
    --     of pointers to its first field), and BarLoc is the type of pointers
    --     to data of this field's type.  We return a Maybe because this might
    --     fail in the event that the provided pointer doesn't go to a struct
    --     or there is a stack underflow.
  }
  deriving (Show,Eq,Ord)
  

data FirstClassInfo =
       FirstClassInfo {
         fciRepType :: T.Id,
            -- the type we use to represent this in CSP
         
         fciReaderChan  :: T.Id,
            -- the name of the channel that communicates reads of global vars of
            -- this type.  (i.e., a locType => repType => Event)

         fciWriterChan :: T.Id,
            -- the name of the channel that communicates writes of gvars of this
            -- type.
             
         fciReader :: T.Id,
         fciWriter :: T.Id,
           -- The names of CSPm functions that read and write values of this
           -- type in memory.
           -- 
           -- types:
           -- fooReader :: (LocalState,PIDTyp,fooLoc,
           --                  (LocalState,PIDTyp,FooTyp) -> Proc) -> Proc
           -- fooWriter :: (LocalState,PIDTyp,fooLoc,FooTyp,
           --                  (LocalState,PIDTyp,FooTyp) -> Proc) -> Proc
           -- 
           -- In both cases, the final argument is a continuation telling us
           -- what to do after reading or writing, taking a potentially
           -- updated state map along with the value read or written
           -- (necessary in the former case, a convenience/concession to
           -- uniformity in the latter).

         fciVarCellBuilder :: T.Id,
            -- The name of the CSPm definition that builds variable cells
            -- holding data of this type.

         fciVarCells :: T.Id,
            -- The name of the CSPm definition representing the segment of
            -- memory holding all global variables of this type.

         fciStackValTag :: T.Id,
            -- The tag to put something into the stack tagged union
         
         fciStackValProj :: T.Id
            -- Projects a value of this type out of the tagged union used on the
            -- stack, (or fails).  XXX We may actually want this moved up to the
            -- type info when we add support for composite types.
         }
  deriving (Show,Eq,Ord)

-- Given a DataInfo for some type, this finds the FCI for the first cell of that
-- type.  If the type is first class, it's just that type's FCI.  If the type is
-- composite, we dig deeper.
dataInfoFirstFCI :: DataInfo -> FirstClassInfo
dataInfoFirstFCI (DIFirstClass fci) = fci
dataInfoFirstFCI (DIStruct si)      = siFirstFCI si
dataInfoFirstFCI (DIArray ai)       = aiElementFCI ai

-- Types
--
-- Our memory model is typed - rather than a collection of 32- or 64-bit cells,
-- the way data is stored depends on the type of that data.  This helps keep the
-- possible space of values for each individual cell low, which helps with model
-- checking time.  In the future, we probably want to do even more, with the
-- data representation in each memory "cell" depending on some prior static
-- analysis of the possible range of values.
--
-- This model requires us to keep track of several pieces of information for
-- each LLVM type.  For example, we need the CSPm type of "locations" that hold
-- each LLVM type, as well as channels to communicate reads and writes at these
-- locations.  That information is contained in a TypeInfo, which is constructed
-- the first time we encounter a particular type in the translation.  We keep
-- track of these in the map TImpMap, which maps BasicTypes to TypeInfos.
--
-- This is slightly inefficient, in that some different BasicTypes actually have
-- similar TypeInfos (arrays of different lengths, for example).  But the
-- penalty for duplicating this stuff seems low compared to the complexity of
-- reorganizing this map.
type TImpMap = M.Map BaseType TypeInfo   -- Type implementations

-- Typedefs
--
-- TMap maps type names from source files to types.
type TDefMap = M.Map S.Name S.Type       -- Type defs

-- We allow the range of values represented by some base types to be configured 
-- by the user. In order to do so, we require several pieces of information:
--
-- A constant that refers to the minimum possible value.
--
-- A constant that refers to the maximum possible value.
data RInfo = RInfo {rmin  :: Int,
                    rmax  :: Int
                   }

data Ranges = Ranges {intRange :: RInfo}

-- The cspgen tool has the ability to provide warnings to the user in cases 
-- where the design decisions have led to compromises that the user might want
-- to be aware of. 
-- 
-- The warnings consist of a short identifier string and a longer, more 
-- descriptive string with detailed information.
data Warning = Warning {warnName :: String, 
                        warnInfo :: String
                       }

instance (Show Warning) where
  show (Warning {warnName,warnInfo}) =
    "Warning: " ++ warnName ++ " - " ++ warnInfo

data CGEnv = 
  CGEnv {
    uniq :: Int,     -- for fresh name generation

    currentLoc :: Maybe String,
      -- In the C version, bits of syntax come with their location.  So, there,
      -- we made a wrapper around the standard monadic "fail" to print this
      -- location.
      --
      -- In the LLVM version, no such locations are provided (and it's not clear
      -- they would make much sense, as you aren't intended to be working
      -- directly with the LLVM).  Instead, we ask the user of this monad (i.e.,
      -- transModule), to periodically update this currentLoc variable to
      -- something sensible (e.g., the name of the function currently being
      -- translated), so that we can provide this location in the event of
      -- failure.
      --
      -- This is ugly and error prone.  But, I think, better than nothing.  In
      -- my first pass at an LLVM version I instead made the programmer supply a
      -- location to any monadic accessor that could fail.  The overhead there
      -- was too high.

    typedefs :: TDefMap,  -- Info about typdefs from the source
                          -- program and their definition

    types    :: TImpMap,  -- Info about our CSP implementation of
                          -- LLVM types.

    globals  :: GMap,    -- Mapping from global source identifiers to
                         -- target variable info.

    aliases  :: AMap,    -- Mapping from global aliases to their "real" name

    
    ssas     :: SMap,    -- Mapping from SSA variable source identifiers to
                         -- target identifiers.

    fptrs    :: FPtrMap, -- This stores information used in our model of
                         -- function pointers.  In particular, it's a map from
                         -- function types to the names of helper functions that
                         -- dereference pointers of those types.

    ranges   :: Ranges,  -- Info about the range of available values for various
                         -- types. Currently used only for C integers, but made 
                         -- generically so that it could also be used for pids, 
                         -- mutexes, etc.

    -- ctors and dtors ("constructors" and "destructors") are the names given to
    -- initialization code that must run before Main, and tear-down code to run
    -- after main, respectively.  They are lists of pairs - the int is a
    -- priority and the name should be the name of a "void ()" function.  The
    -- priorities are, annoying, handled differently for each - for ctors, the
    -- lowest one is run first, and for dtors the highest one is run first.
    ctors    :: [(Int,S.Name)],
    dtors    :: [(Int,S.Name)],

    warnings :: [Warning]
  }

--------------------------------------------------------------------
------- Base Type definitions
--------------------------------------------------------------------

-- This is a helper function for creating the "built-in" TypeInfos.  It takes in
-- the base type and the RepType name (as a string) and constructs fixed names
-- for the other TypeInfo fields in a regular way.
fixedTypeInfoBuilder :: BaseType -> String -> (TypeInfo,FirstClassInfo)
fixedTypeInfoBuilder btyp unm =
  (TypeInfo {
     tiNameHint      = unm,
     tiLocType       = T.Fixed $ unm ++ "Loc",
     tiGlobalLocType = T.Fixed $ unm ++ "GLoc",

     tiLocalLocTag   = T.Fixed $ unm ++ "LLocTag",
     tiGlobalLocTag  = T.Fixed $ unm ++ "GLocTag",
     tiNullLoc       = T.Fixed $ unm ++ "Loc_Null",
     tiUnknownLoc    = T.Fixed $ unm ++ "Loc_Unknown",

     tiLocMaybeType  = T.Fixed $ unm ++ "LocMaybe",
     tiLocMaybeJust  = T.Fixed $ unm ++ "LocJust",
     tiLocMaybeNothing = T.Fixed $ unm ++ "LocNothing",
     tiLocMaybeElim  = T.Fixed $ "maybe" ++ unm ++ "Loc",

     tiLocEqCheck    = T.Fixed $ unm ++ "LocEq",
     
     tiArrayIndexer  = T.Fixed $ unm ++ "GEPArray",
     
     tiDataInfo      = DIFirstClass fci,
     tiBase          = btyp
   },
   fci)
  where
    lnm :: String
    lnm = case unm of
            [] -> []
            (c:cs) -> toLower c : cs

    fci :: FirstClassInfo
    fci = FirstClassInfo {
        fciRepType        = T.Fixed unm,
        fciReaderChan     = T.Fixed $ lnm ++ "Read_c",
        fciWriterChan     = T.Fixed $ lnm ++ "Write_c",
        fciReader         = T.Fixed $ lnm ++ "Reader",
        fciWriter         = T.Fixed $ lnm ++ "Writer",
        fciVarCellBuilder = T.Fixed $ unm ++ "_VAR",
        fciVarCells       = T.Fixed $ unm ++ "_VARS",
        fciStackValTag    = T.Fixed $ unm ++ "StackTag",
        fciStackValProj   = T.Fixed $ unm ++ "StackProj"
      }

intTypeInfo :: TypeInfo
intFCInfo :: FirstClassInfo
(intTypeInfo,intFCInfo) = fixedTypeInfoBuilder IntType "CInt"

boolTypeInfo :: TypeInfo
boolFCInfo :: FirstClassInfo
(boolTypeInfo,boolFCInfo) = fixedTypeInfoBuilder BoolType "CBool"

floatTypeInfo :: TypeInfo
floatFCInfo :: FirstClassInfo
(floatTypeInfo,floatFCInfo) = fixedTypeInfoBuilder FloatType "CFloat"

mutexTypeInfo :: TypeInfo
mutexFCInfo :: FirstClassInfo
(mutexTypeInfo,mutexFCInfo) = fixedTypeInfoBuilder MutexType "Mutex"

pidTypeInfo :: TypeInfo
pidFCInfo :: FirstClassInfo
(pidTypeInfo,pidFCInfo) = fixedTypeInfoBuilder PIDType "TIDTyp"

fptrTypeInfo :: TypeInfo
fptrFCInfo :: FirstClassInfo
(fptrTypeInfo,fptrFCInfo) = fixedTypeInfoBuilder FPtrType "FPtr"

-- XXX generalize to take in all the parameters
initState :: (Int,Int) ->  [(S.Name,GlobFuncInfo)] -> CGEnv
initState (cmin,cmax) fs =
    CGEnv {uniq      = 0,
           currentLoc = Nothing,
           typedefs  = M.empty,
           types     = M.fromList [(IntType,intTypeInfo),
                                   (BoolType,boolTypeInfo),
                                   (FloatType,floatTypeInfo),
                                   (MutexType,mutexTypeInfo),
                                   (PIDType,pidTypeInfo),
                                   (FPtrType,fptrTypeInfo)],
           globals   = M.fromList (map (\(n,gf) -> (n,GlobFunc gf)) fs),
           aliases   = M.empty,
           ssas      = M.empty,
           fptrs     = M.empty,
           ranges    = Ranges {intRange = RInfo {rmin=cmin,rmax=cmax}},
           ctors     = [],
           dtors     = [],
           warnings  = []
          }

newtype CG a = CG (CGEnv -> (CGEnv,Either ErrMsg a))

unCG :: CG a -> CGEnv -> (CGEnv,Either ErrMsg a)
unCG (CG m) = m

instance Functor CG where
  fmap f m = CG (\env -> case unCG m env of
                           (cgp,e) -> (cgp,fmap f e))

instance Monad CG where
  return x = CG (\pst -> (pst,Right x))

  fail err = CG (\pst -> (pst, Left $
     case currentLoc pst of
       Nothing -> err
       Just l  -> err ++ " (Location: " ++ l ++ ")"))

  m >>= k  = CG (\env -> case unCG m env of
                          (pst,Left err) -> (pst,Left err)
                          (pst,Right v) -> unCG (k v) pst)

instance Applicative CG where
  pure  = return
  (<*>) = ap

runCG :: CGEnv -> CG a -> (Either ErrMsg a, [Warning])
runCG pst (CG cg) =
  case cg pst of
    (CGEnv {warnings},r) -> (r,warnings)

extendGlobal :: S.Name -> GlobInfo -> CG ()
extendGlobal sid ginfo =
  CG (\pst -> (pst {globals=M.insert sid ginfo (globals pst)},Right ()))

addAlias :: S.Name -> S.Name -> CG ()
addAlias alias realname =
  CG (\pst -> (pst {aliases=M.insert alias realname (aliases pst)},Right ()))

extendSSA    :: S.Name -> SSAVarInfo -> CG ()
extendSSA sid svinfo =
  CG (\pst -> (pst {ssas=M.insert sid svinfo (ssas pst)},Right ()))

clearSSAVars :: CG ()
clearSSAVars =
  CG (\pst -> (pst {ssas=M.empty},Right()))
  
--extendFunction :: S.Name -> FInfo -> CG ()
--extendFunction sid finfo =
--  CG (\pst -> 
--          (pst {functions=M.insert sid finfo (functions pst)},
--           Right ()))

extendType :: BaseType -> TypeInfo -> CG ()
extendType bt tinfo = 
  CG (\pst -> (pst {types=M.insert bt tinfo (types pst)},
               Right ()))

addTypeDef :: S.Name -> S.Type -> CG ()
addTypeDef sid td =
  CG (\pst ->
        (pst {typedefs=M.insert sid td (typedefs pst)},
         Right ()))

getGlobals :: CG GMap
getGlobals = CG (\pst -> (pst,Right $ globals pst))

getAliases :: CG AMap
getAliases = CG (\pst -> (pst,Right $ aliases pst))

getSSAs :: CG SMap
getSSAs = CG (\pst -> (pst,Right $ ssas pst))

getTypeInfos :: CG TImpMap
getTypeInfos = CG (\pst -> (pst,Right $ types pst))

getTypedefs :: CG TDefMap
getTypedefs = CG (\pst -> (pst,Right $ typedefs pst))

getUniq :: CG Int
getUniq = CG (\pst -> (pst {uniq = 1 + (uniq pst)}, Right $ uniq pst))
 
getRanges :: CG Ranges
getRanges = CG (\pst -> (pst,Right $ ranges pst ))

getIntRange :: CG (Int,Int)
getIntRange = do
  allRanges <- getRanges
  let ranges = intRange allRanges
  return (rmin ranges, rmax ranges)

getFPtrs :: CG FPtrMap
getFPtrs = CG (\pst -> (pst,Right $ fptrs pst))

extendFPtrs :: [T.Id] -> T.Id -> T.Id -> CG ()
extendFPtrs args ret nm =
  CG (\pst -> (pst {fptrs=M.insert (args,ret) nm (fptrs pst)}, Right ()))

addCtor :: (Int,S.Name) -> CG ()
addCtor p = CG (\pst -> (pst {ctors=p:ctors pst},Right ()))

addDtor :: (Int,S.Name) -> CG ()
addDtor p = CG (\pst -> (pst {dtors=p:dtors pst},Right ()))

getCtors :: CG [(Int,S.Name)]
getCtors = CG (\pst -> (pst, Right $ ctors pst))

getDtors :: CG [(Int,S.Name)]
getDtors = CG (\pst -> (pst, Right $ dtors pst))

----------
---------- Warning interface
----------

addWarning :: String -> String -> CG () 
addWarning warnName warnInfo = 
  CG (\pst -> (pst {warnings=newWarning : warnings pst}, Right ()))
  where 
    newWarning = Warning {warnName,warnInfo}

getWarnList :: CG [Warning]
getWarnList = CG (\pst -> (pst, Right $ warnings pst))


-------
------- Location interface
-------

setCurrentLoc :: String -> CG ()
setCurrentLoc s = CG (\pst -> (pst {currentLoc=Just s},Right ()))

clearCurrentLoc :: CG ()
clearCurrentLoc = CG (\pst -> (pst {currentLoc=Nothing},Right ()))

getCurrentLoc :: CG (Maybe String)
getCurrentLoc = CG (\pst -> (pst,Right $ currentLoc pst))


-------------
------------- Interface for looking up variables
-------------

lookupTypeInfo :: BaseType -> CG TypeInfo
lookupTypeInfo bt =
  case bt of
    FunctionType -> fail "Internal error: lookupTypeInfo called on FunctionType"
    _ -> do
      tinfos <- getTypeInfos
      case M.lookup bt tinfos of
        Just ti -> return ti
        Nothing ->
          -- This is just for error messages
          case bt of
            IntType -> 
                fail "Internal error: no typeinfo found for Int base type"
            BoolType -> 
                fail "Internal error: no typeinfo found for Bool base type"
            MutexType -> 
                fail "Internal error: no typeinfo found for Mutex base type"
            PIDType -> 
                fail "Internal error: no typeinfo found for PID base type"
            FPtrType -> 
                fail "Internal error: no typeinfo found for FPtr dummy base type"
            _ ->
              -- derived types like foo* and foo[] are not explicitly declared
              -- before using them, so we generate typeinfos the first time we
              -- encounter them.  And in LLVM, structs need not be pre-declared
              -- either.
              buildNewTypeInfo bt Nothing

-- Generate the fresh names for a new type info, given the field
-- types, and a hint for good name generation.
freshTypeInfoNames :: String -> BaseType
                   -> DataInfo
                   -> CG TypeInfo
freshTypeInfoNames nm tiBase tiDataInfo = do
  tiLocType         <- freshTid (Just $ nm ++ "Loc")
  tiGlobalLocType   <- freshTid (Just $ nm ++ "GLoc")
  tiNullLoc         <- freshTid (Just $ nm ++ "Loc_Null")
  tiUnknownLoc      <- freshTid (Just $ nm ++ "Loc_Unknown")
  tiGlobalLocTag    <- freshTid (Just $ nm ++ "GLocTag")
  tiLocalLocTag     <- freshTid (Just $ nm ++ "LLocTag")
  tiLocMaybeType    <- freshTid (Just $ nm ++ "LocMaybeType")
  tiLocMaybeJust    <- freshTid (Just $ nm ++ "LocMaybeJust")
  tiLocMaybeNothing <- freshTid (Just $ nm ++ "LocMaybeNothing")
  tiLocMaybeElim    <- freshTid (Just $ "maybe" ++ nm ++ "Loc")
  tiLocEqCheck      <- freshTid (Just $ nm ++ "LocEq")
  tiArrayIndexer    <- freshTid (Just $ nm ++ "GEPArray")
  return $ TypeInfo {tiNameHint=nm,tiLocType,
                     tiGlobalLocType,tiNullLoc,tiUnknownLoc,
                     tiGlobalLocTag,tiLocalLocTag,
                     tiLocMaybeType,tiLocMaybeJust,
                     tiLocMaybeNothing,tiLocMaybeElim,
                     tiLocEqCheck, tiArrayIndexer,
                     tiDataInfo,tiBase}

-- Generate the fresh names for a new fcInfo, given the reptype
freshFirstClassInfoNames :: String -> T.Id -> CG FirstClassInfo
freshFirstClassInfoNames nm fciRepType = do
  fciReaderChan     <- freshTid (Just $ (map toLower nm) ++ "_read_c")
  fciWriterChan     <- freshTid (Just $ (map toLower nm) ++ "_write_c")
  fciReader         <- freshTid (Just $ (map toLower nm) ++ "Reader")
  fciWriter         <- freshTid (Just $ (map toLower nm) ++ "Writer")
  fciVarCellBuilder <- freshTid (Just $ nm ++ "_VAR")
  fciVarCells       <- freshTid (Just $ nm ++ "_VARS")
  fciStackValTag    <- freshTid (Just $ nm ++ "StackTag")
  fciStackValProj   <- freshTid (Just $ nm ++ "StackProj")
  return $ FirstClassInfo {fciRepType,
                           fciReaderChan, fciWriterChan,
                           fciReader, fciWriter,
                           fciVarCellBuilder, fciVarCells,
                           fciStackValTag,fciStackValProj}

-- buildNewTypeInfo creates a new TypeInfo for a provided BaseType.  This
-- primarily consists of generating fresh names and ensuring that TypeInfos
-- already exist for any components of the BaseType, in the case of
-- structs/unions.
buildNewTypeInfo :: BaseType -> Maybe String -> CG TypeInfo
buildNewTypeInfo FunctionType _ =
  fail "Internal Error: Encountered FunctionType in buildNewTypeInfo"
buildNewTypeInfo IntType _ =
  fail "Internal Error: Encountered IntType in buildNewTypeInfo"
buildNewTypeInfo BoolType _ =
  fail "Internal Error: Encountered BoolType in buildNewTypeInfo"
buildNewTypeInfo FloatType _ =
  fail "Internal Error: Encountered FloatType in buildNewTypeInfo"
buildNewTypeInfo MutexType _ =
  fail "Internal Error: Encountered MutexType in buildNewTypeInfo"
buildNewTypeInfo PIDType _ =
  fail "Internal Error: Encountered PIDType in buildNewTypeInfo"
buildNewTypeInfo VoidType _ =
  fail "Internal Error: Encountered VoidType in buildNewTypeInfo"
buildNewTypeInfo FPtrType _ =
  fail "Internal Error: Encountered FPtrType in buildNewTypeInfo"
buildNewTypeInfo (PointerType bt) _ = do
  -- This case is a little tricky.  There are multiple different base types that
  -- share location types.  That is, even though there is no typeinfo stored for
  -- (PointerType bt), there might be one already made for some (PointerType
  -- bt') where bt and bt' share location types.  For example, bt and bt' might
  -- be Int and {Int,Float}.  The location of each is an Int*.
  --
  -- We don't want to generate 8 names for int*.  So, here's the trick: bt and
  -- bt' share locations just when the first memory "cell" of a bt and a bt'
  -- have the same type.  Individual memory cells always have first-class types.
  -- So, to make a new typeinfo for (PointerType bt), we check if it's first
  -- class.  If not, we get the typeinfo for (PointerType bt') where bt' is the
  -- type of its first cell (this may itself involve building a new type info).
  isFC <- btIsFirstClass bt
  tinfo <- 
    if isFC then do
      baseTInfo <- lookupTypeInfo bt
      let fciRepType = tiLocType baseTInfo 
          nm = T.namePart fciRepType
      fcInfo <- freshFirstClassInfoNames nm fciRepType
      tinfo <- freshTypeInfoNames nm (PointerType bt) (DIFirstClass fcInfo)
      return tinfo
    else do
      mFirstCellBT <- btFirstFirstClass bt
      firstCellBT <- 
        case mFirstCellBT of
          Nothing -> fail $
               "Internal error: buildNewTypeInfo encountered unsupported type "
            ++ ppBaseType (PointerType bt)
          Just fcBT -> return fcBT
      firstCellTInfo <- lookupTypeInfo (PointerType firstCellBT)
      return firstCellTInfo
  extendType (PointerType bt) tinfo
  return tinfo
buildNewTypeInfo bt@(StructType flds) mhint =
  -- Here we are playing a little trick.  Most pieces of information that
  -- appear in the typeinfo for a struct have to do with memory locations.
  -- But a pointer to a struct is also a pointer to the first thing in that
  -- struct.  So, we find the first thing in the struct and just reuse its
  -- information, rather than having a new kind of pointers.
  --
  -- The only other thing to calculate is the struct info, containing
  -- the names for the field pointer calculators.
  case flds of
    [] -> fail $ "Unsupported: empty struct type in buildNewTypeInfo"
              ++ maybe "" (\s -> " (" ++ s ++ ")") mhint
    (firstBT : btTail) -> do
      firstTInfo <- lookupTypeInfo firstBT
      let hint = fromMaybe "anonStruct_" mhint
      tailGetPtrTids <-
        mapM (\i -> freshTid (Just $ hint ++ "_GEP_" ++ show i))
             [1..(length btTail)]
      tiArrayIndexer <- freshTid $ Just $ hint ++ "GEPArray"
      let structInfo =
            StructInfo {siFirstFCI=dataInfoFirstFCI (tiDataInfo firstTInfo),
                        siGetFieldPtrs=tailGetPtrTids}
          tInfo = firstTInfo {tiNameHint = hint,
                              tiArrayIndexer,
                              tiBase = bt,
                              tiDataInfo = DIStruct structInfo}
      extendType bt tInfo
      return tInfo
buildNewTypeInfo bt@(ArrayType btElements len) nmHint = do
  -- Arrays are a lot like structs.  We only handle fixed-length arrays, so they
  -- are just some contiguous memory cells that all happen to have the same
  -- type.
  --
  -- An array value has the same representation, roughly, as an element of that
  -- array.  For example, if I've got a pointer to 3 contiguous ints in memory,
  -- what I've really got is a poitner to an int. Unlike structs, we don't have
  -- to bother with GEP accessors for each individual element of the array.
  -- Rather, there is one GEP helper for each type of array.
  tinfo@TypeInfo {tiNameHint=elementNmHint} <- lookupTypeInfo btElements
  let tiNameHint = fromMaybe (elementNmHint ++ "Arr" ++ show len) nmHint
  tiArrayIndexer <- freshTid $ Just $ tiNameHint ++ "GEPArray"
  let ainfo = ArrayInfo {aiElementFCI = dataInfoFirstFCI $ tiDataInfo tinfo}
      tInfo = tinfo {tiNameHint = tiNameHint,
                     tiArrayIndexer,
                     tiBase = bt,                                 
                     tiDataInfo = DIArray ainfo}
  extendType bt tInfo
  -- This just ensures the type info for the pointer to btElements exists as
  -- well, as we sometimes use its infrastructure.
  _ <- lookupTypeInfo (PointerType btElements)
  return tInfo
buildNewTypeInfo (NamedType n) _ = do
  mty <- lookupTypeDef n
  sty <- case mty of
           Nothing -> fail $
                "Internal error: missing definition for named type "
             ++ prettyLLVMName n ++ " in buildNewTypeInfo."
           Just t -> return t
  bty <- transType sty
  tinfos <- getTypeInfos
  case M.lookup bty tinfos of
    Just tinfo -> extendType (NamedType n) tinfo >> return tinfo
    Nothing -> do
    -- Here, we'd like to just build a new TypeInfo for bty.  But there's a
    -- problem: if bty contains (NamedType n) itself (for example, because n is a
    -- recursive struct), we'll come right back here and end up in an infinite
    -- loop.
    --
    -- Looking through buildNewTypeInfo, we see that the only calls to
    -- lookupTypeInfo are on the inner type of PointerType and on the first field
    -- of a struct.  For now, we just consider those cases unsupported (see
    -- allowedTypeRecursion).
    --
    -- XXX do something smarter when I have more time.
      unless (allowedTypeRecursion n bty) $ fail $
           "Unsupported: the recursion in the definition of type "
        ++ prettyLLVMName n ++ " is too complicated for my pitiful brain."
        ++ "  Moving recursive occurances out of the first field of structs"
        ++ " may help."
      tinfo <- buildNewTypeInfo bty (Just $ prettyLLVMName n)
      extendType (NamedType n) tinfo
      return tinfo
  where
    -- XXX We probably need to check the definition of encountered NamedTypes,
    -- too, to avoid unsupported mutually recursive definitions
    allowedTypeRecursion :: S.Name -> BaseType -> Bool
    allowedTypeRecursion recName (NamedType n') = not $ recName == n'
    allowedTypeRecursion recName (PointerType bt') =
      allowedTypeRecursion recName bt'
    allowedTypeRecursion recName (StructType (bt':_)) =
      allowedTypeRecursion recName bt'
    allowedTypeRecursion _ _ = True
                      

-- transType translates a source type to a BaseType.  This used to also generate
-- a TypeInfo if we hadn't done that yet, but I don't believe it is necessary,
-- since lookupTypeInfo does it.
transType :: S.Type -> CG BaseType
transType S.VoidType        = return VoidType
transType (S.IntegerType {S.typeBits}) =
  return $ if typeBits == 1 then BoolType else IntType
transType (S.PointerType {S.pointerReferent}) =
  case pointerReferent of
    S.FunctionType {} -> return FPtrType
    _ -> PointerType <$> transType pointerReferent
transType (S.FloatingPointType {}) = return FloatType
transType (S.FunctionType {})      = return FunctionType
transType (S.VectorType {})        = fail "Unsupported: vector types"
transType (S.StructureType {S.elementTypes}) =
  StructType <$> mapM transType elementTypes
transType (S.ArrayType {S.nArrayElements,S.elementType}) = do
  -- XXX this, or checkForAndCreateTypeInfo, is what needs to be fixed to
  -- support statically sized arrays.
  ArrayType <$> transType elementType <*> pure (fromIntegral nArrayElements)
transType (S.NamedTypeReference n) = do
 -- This is just sanity checking.  May need to ditch it (for example, to support
 -- mutually recursive type definitions)
  mty <- lookupTypeDef n
  case mty of
    Nothing -> fail $ "Unknown type name " ++ prettyLLVMName n
                   ++ " encountered in transType"
    Just _ -> return $ NamedType n
transType S.MetadataType =
  fail "Unimplemented: MetadataType encountered in transType"

lookupTypeDef :: S.Name -> CG (Maybe S.Type)
lookupTypeDef n = do
  env <- getTypedefs
  return $ M.lookup n env

lookupTypeDefFail :: S.Name -> String -> CG S.Type
lookupTypeDefFail n hint = do
  env <- getTypedefs
  case M.lookup n env of
    Nothing -> fail $ "Missing definition for named type "
                   ++ prettyLLVMName n ++ " (in " ++ hint ++ ")"
    Just sty -> return sty

-- Finds the name of the function that translates function pointer tags into
-- actual functions, for functions with the supplied argument and return types.
-- This checks the stored in the monad to see if we've already come up with a
-- name for this particular combo, and makes a fresh name if not.
lookupFPtrDeref :: [BaseType] -> BaseType -> CG T.Id
lookupFPtrDeref args ret = do
  fpmap <- getFPtrs
  argReps <- mapM lookupRepType args
  retRep <- lookupRepType ret
  case M.lookup (argReps,retRep) fpmap of
    Nothing -> do
      nm <- freshTid $ Just "fptrDeref"
      extendFPtrs argReps retRep nm
      return nm
    Just nm -> return nm

allFPtrDerefs :: CG [(([T.Id],T.Id),T.Id)]
allFPtrDerefs = M.toList <$> getFPtrs

-- This finds the CSP name of the type we use to represent this basetype.  This
-- can be useful because different BaseTypes can have the same representation
-- (like int* and int[3]), so equality on basetypes isn't always useful.
lookupRepType :: BaseType -> CG T.Id
lookupRepType VoidType = return unitRepId
lookupRepType bt = do
  tinfo <- lookupTypeInfo bt
  return $ fciRepType $ dataInfoFirstFCI $ tiDataInfo tinfo


------------
------------ Fresh name generation
------------


-- We do one check: C variables can begin with "_", but CSP variables can't, so
-- in the event of leading underscores we add a "u" at the front.
freshTid :: Maybe String -> CG T.Id
freshTid mhint = do
  i <- getUniq
  return $ T.Id (sanitizedHint,i)
  where
    hint = case mhint of
             Just s@('_':_) -> 'u':s
             Just s -> s
             Nothing -> "x"

    -- Both "." and ":" can occur in a llvm identifiers, but are not legal in
    -- cspm.  We replace them with underscores.
    sanitizedHint :: String
    sanitizedHint = map (\c -> if (c == '.') || (c == ':') then '_' else c) hint
  

-------------
------------- Interface for adding state
-------------

-- Data representation
--
-- The CSP model has no types representing "aggregate" values in LLVM, like
-- structs and arrays.  Instead, it deals only with the individual components
-- of those types.  As a result, sometimes the translation of an LLVM
-- expression or constant is not a single CSP expression or constant.  We use
-- the following type instead:
data DataRep = DRValue T.Exp
             | DRAgg [DataRep]
  deriving (Show)

-- This function is called by the translation when it needs a name for
-- a new global variable.  Names are added in a first pass before we
-- translate initializers or function bodies, so this does not need to
-- worry about creating space in the memory model.
freshGlobVar :: S.Name -> BaseType -> CG ()
freshGlobVar sid gvtype = do
  tinfo <- lookupTypeInfo gvtype
  let snm = prettyLLVMName sid
      locNm = T.namePart $ tiLocType tinfo
      nm = locNm ++ "_" ++ snm
  gvtid <- freshTid (Just nm)
  let gvInfo = GVInfo {gvtid,gvtype,gvlayout=Nothing}
  extendGlobal sid $ GlobVar gvInfo

-- This is the function called by the translation when processing the
-- initializer for a global variable.  It creates the layout of the
-- memory associated with the variable.  Globals in LLVM are obligated
-- to come with initializers, which are provided here as a DataRep.
-- freshGlobMem is responsible for breaking down the type of the new
-- variable, making sure it corresponds with the provided DataRep, and
-- recording information about the resulting memory layout to the
-- monad.
--
-- freshGlobVar should already have been called for this variable.
-- So, it should already be recorded in the monad, but without an
-- initializer.
freshGlobMem :: S.Name -> BaseType -> DataRep -> CG ()
freshGlobMem sid bt dr = do
  mGInfo <- lookupGlobal sid
  gvinfo <-
    case mGInfo of
      Nothing ->
        fail $ "Internal error: freshGlobMem called on previously "
            ++ "unencountered variable " ++ prettyLLVMName sid
      Just (GlobFunc _) ->
        fail $ "Internal error: freshGlobMem called on variable "
            ++ prettyLLVMName sid
            ++ ", which was previously added as a function."
      Just (GlobVar gvi) -> do
        unless (gvtype gvi == bt) $
          fail $ "Internal error: freshGlobMem called on variable "
              ++ prettyLLVMName sid ++ " at type " ++ show bt
              ++ ", but this variable was previously added at type "
              ++ show (gvtype gvi)
        return gvi
  let snm = prettyLLVMName sid

      -- We provide naming "hints" to the memory layout routine.
      -- There is a special case, which is that the very first cell of
      -- memory associated with this variable has already been given a
      -- name.  To deal with this, the hints are either a String hint
      -- or a T.Id, indicating a fixed name has already been chosen.
      -- Only the very first "hint" should be a T.Id
      nameHints :: [Either String T.Id]
      nameHints = Right (gvtid gvinfo)
                : [Left (snm ++ "_" ++ show i) | i <- [(1::Int)..]]
  (gvinfo',_) <- layoutGlobalMem bt dr nameHints
  extendGlobal sid (GlobVar gvinfo')

showHint :: Either String T.Id -> String
showHint (Left s) = s
showHint (Right t) = T.namePart t

-- Helper for freshGlobMem.  Third argument is a list of name hints.
layoutGlobalMem :: BaseType -> DataRep -> [Either String T.Id]
                -> CG (GlobVarInfo,[Either String T.Id])
layoutGlobalMem _ _ [] = fail "Internal Error: layoutGlobalMem out of names"
layoutGlobalMem structBT@(StructType bts) (DRAgg reps) hints@(h:_) = do
  when (length bts /= length reps) $
    fail $ "Illegal: in layoutGlobalMem allocation of " ++ showHint h
        ++ " initializer has different number of fields than type ("
        ++ ppBaseType structBT ++ ")"
  (revInfos,hints') <-
    foldM (\(agg,hs) (bt,rep) -> do
             (gmInfo,hs') <- layoutGlobalMem bt rep hs
             return (gmInfo:agg,hs'))
          ([],hints)
          (zip bts reps)
  let gmInfos = reverse revInfos
  firstName <-
    case gmInfos of
      [] -> fail $ "Illegal: in layoutGlobalmem allocation of " ++ showHint h
                ++ ", the struct is empty (" ++ ppBaseType structBT
                ++ ")"
      (v1:_) -> return $ gvtid v1
  let gvinfo = GVInfo {gvtid = firstName,
                       gvtype = structBT,
                       gvlayout = Just $ GVAgg gmInfos}
  return (gvinfo, hints')
layoutGlobalMem (NamedType n) dr hs = do
  mty <- lookupTypeDef n
  case mty of
    Nothing -> fail $ "Missing definition for type " ++ prettyLLVMName n
                   ++ " in layoutGlobalMem"
    Just sty -> do {bty <- transType sty; layoutGlobalMem bty dr hs}
layoutGlobalMem FunctionType _ (hint:_) =
  fail $ "Unsupported: global variable of function type encountered "
      ++ "during layoutGlobalMem allocation of " ++ showHint hint
layoutGlobalMem arrBT@(ArrayType bt len) (DRAgg reps) hints@(h:_) = do
  when (len /= length reps) $
    fail $ "Illegal: in layoutGlobalMem allocation of " ++ showHint h
        ++ " initializer has different number of fields than type ("
        ++ ppBaseType arrBT ++ ")"
  (revInfos,hints') <-
    foldM (\(agg,hs) rep -> do
             (gmInfo,hs') <- layoutGlobalMem bt rep hs
             return (gmInfo:agg,hs'))
          ([],hints) reps
  let gmInfos = reverse revInfos
  firstName <-
    case gmInfos of
      [] -> fail $ "Illegal: in layoutGlobalmem allocation of " ++ showHint h
                ++ ", the arrau is empty (" ++ ppBaseType arrBT
                ++ ")"
      (v1:_) -> return $ gvtid v1
  let gvinfo = GVInfo {gvtid = firstName,
                       gvtype = arrBT,
                       gvlayout = Just $ GVAgg gmInfos}
  return (gvinfo, hints')
layoutGlobalMem bt (DRAgg _) (hint: _) =
  fail $ "Unsupported: in layoutGlobalMem allocation of " ++ showHint hint
      ++ ", composite initializer provided for first-class type "
      ++ ppBaseType bt
layoutGlobalMem bt (DRValue e) (hint:hs) = do
  isfc <- btIsFirstClass bt
  if isfc then do
    gvtid <-
      case hint of
        Right t -> return t
        Left s -> do tinfo <- lookupTypeInfo bt
                     let locNm = T.namePart $ tiLocType tinfo
                         nm = locNm ++ "_" ++ s
                     freshTid (Just nm)
    let gvlayout = Just $ GVCell e
    return (GVInfo {gvtid,gvtype=bt,gvlayout},hs)
  else
    fail $ "Unsupported: in layoutGlobalMem allocation of " ++ showHint hint
        ++ ", first-class initializer provided for aggregate type "
        ++ ppBaseType bt

freshFunc :: S.Name -> BaseType -> [BaseType] -> Bool -> CG ()
freshFunc sid fret fargs fdef = do
  ftid <- freshTid (Just $ prettyLLVMName sid)
  ftag <- freshTid (Just $ "FP_" ++ prettyLLVMName sid)
  extendGlobal sid $ GlobFunc $ GFInfo {ftid,fret,fargs,ftag,fdef}

setFuncDefined :: S.Name -> CG ()
setFuncDefined sid = CG (\pst ->
  let oldGlobs = globals pst in
  case M.lookup sid (globals pst) of
    Nothing ->
      (pst, Left $ "Internal error: setFuncDefined encountered unknown "
                ++ "function " ++ prettyLLVMName sid)
    Just (GlobVar _) ->
      (pst, Left $ "Internal error: setFuncDefined called on glob variable "
                ++ prettyLLVMName sid)
    Just (GlobFunc finfo) ->
      (pst {globals=M.insert sid (GlobFunc finfo {fdef=True}) oldGlobs},
       Right ()))

-- Like fresh SSA, but with prettier names for blocks.
freshBlockSSA :: String -> S.Name -> CG T.Id
freshBlockSSA fname sid = do
  let hint = fname ++ "_block_" ++ prettyLLVMName sid
  tid <- freshTid $ Just hint
  extendSSA sid (SVInfo {svname=tid,svreptype=Nothing})
  return tid

freshSSA :: S.Name -> CG T.Id
freshSSA sid = do
  tid <- freshTid $ Just $ prettyLLVMName sid
  extendSSA sid (SVInfo {svname=tid,svreptype=Nothing})
  return tid

addSSAType :: S.Name -> BaseType -> CG ()
addSSAType sid btype = do
  svinfo <- lookupSSA sid
  extendSSA sid (svinfo {svreptype=Just btype})

----------
---------- More state accessors
----------

lookupSSA :: S.Name -> CG SSAVarInfo
lookupSSA nm = do
  ssas <- getSSAs
  case M.lookup nm ssas of
    Nothing ->
      fail $
           "Internal error: SSA variable " ++ prettyLLVMName nm
        ++ " not found."
    Just svinfo -> return svinfo

lookupSSAName :: S.Name -> CG T.Id
lookupSSAName nm = do
  ssas <- getSSAs
  case M.lookup nm ssas of
    Nothing ->
      fail $
           "Internal error: SSA variable " ++ prettyLLVMName nm
        ++ " not found."
    Just svinfo -> return $ svname svinfo


-- XXX This is inelegant, and slow.  Come up with a better way to deal with aliases.
lookupGlobal :: S.Name -> CG (Maybe GlobInfo)
lookupGlobal n = do
  aliases <- getAliases
  let gname = fromMaybe n (M.lookup n aliases)
  M.lookup gname <$> getGlobals

allGlobals :: CG [(S.Name,GlobInfo)]
allGlobals = M.toList <$> getGlobals

allFunctions :: CG [(S.Name,GlobFuncInfo)]
allFunctions = do
  globs <- allGlobals
  return $ [(nm,gfi) | (nm,GlobFunc gfi) <- globs]

allTypeInfos :: CG [TypeInfo]
allTypeInfos = M.elems <$> getTypeInfos



-------
------- XXX Doesn't really belong here
-------
------- In particular, we should just have a "types" file imported by everything
------- where this kind of stuff and the type definitions at the top of this
------- file live.

prettyLLVMName :: S.Name -> String
prettyLLVMName (S.Name s) = s
prettyLLVMName (S.UnName w) = 'u' : show w

-- The meminfo is used in a few places for tracking all the memory cells we
-- need.  We break this down by first class variables, structs, and arrays.
--
-- In the struct case, the TypeInfo key is the struct.  In the array case, the
-- TypeInfo key is the type of elements in the array (since arrays of different
-- lengths have different slightly different typeInfos).
data MemInfo = MInfo {
    firstClassMInfo :: [(TypeInfo,[GlobVarInfo])],
    structMInfo     :: [(TypeInfo,[GlobVarInfo])],
    arrayMInfo      :: [(TypeInfo,[GlobVarInfo])]
  }
