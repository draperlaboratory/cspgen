module CodeGen.C.CGMonad
  (ErrMsg,GlobInfo(..),LocalInfo(..),StructInfo(..),TypeInfo(..),FieldInfo(..),
   VarInfo (..),FInfo(..),ArrayLocs(..),
   BaseType (..),Warning(..),
   initState,CG,-- Abstract
   freshLocalNew,freshLocalsNew,freshLocal,freshLocalArrayCells,
   freshGlobal,freshFunction,freshLocation,
   setFunctionDefined,
   lookupVar,lookupLocalVar,lookupTypeDef,lookupTypeInfo,lookupFunction,lookupFunctionByName,
   globalExists,addGlobalInitializer,
   clearLocalState,
   localStateType,localStateCon,localStateEmpty,
   voidStarRepType,voidStarNullTest,voidStarNullCon,voidStarUnknownCon,
   memoryName,runInMemoryName,hideMemoryName,
   addTypeDef,transType,
   allGlobals,allLocals,allTypeInfos,allFunctions,allArrays,
   runCG,
   failBase,failGlob,failPos,failDecln,failStmt,failExp,failType,failExternal,
   cIntBaseType,cIntTypeInfo,cBoolBaseType,cBoolTypeInfo,cFloatBaseType,
   cFloatTypeInfo,mutexTypeInfo,
   unitTypeInfo,unitValCon,
   cIntKnownCon,cIntUnknownCon,
   cBoolTrueCon, cBoolFalseCon, cBoolUnknownCon,
   cFloatUnknownCon,
   cIntToBool,cBoolToInt,cIntToFloat,cFloatToInt,
   mutexInitCon, mutexUnInitCon,pidTypId,pidKnownCon,pidUnknownCon,
   cTernary,
   ppBaseType,internal,
   getCIntRange,addWarning,getWarnList,
   localProjErrorChanId,arrayIndexErrorChanId
  )
where

import           Control.Monad (ap,unless)

import           Compiler.Hoopl (UniqueMonad(..),freshLabel,Label,CheckpointMonad(..))

import qualified Language.CSPM.Syntax as T
import qualified CodeGen.C.Syntax as S
import           CodeGen.C.Pretty (emitId,emitExternalDecln)

import           Data.Char (toLower,toUpper)
import           Data.List (find)
import qualified Data.Map.Strict as M
import           Data.Maybe (isJust)

-- The CG monad contains maps "globals" and "locals" for variables,
-- along with a list of reserved names.  Both maps are use to keep
-- track of the correspondence between source language names and
-- target language names and types.  In the case of "globals", we also
-- track an initialization value for each variable.
--
-- It used to be that we "globals" was state and "locals" was handled like a
-- reader monad, but as we've switched to a lower-level IR, that's no longer
-- feasible.

type ErrMsg = String

-- Global map is : Source ID  -> Target Id, Type, Maybe (Inital value)
data GlobInfo = GInfo {gtid  :: T.Id,
                       gtype :: BaseType,
                       ginit :: (Maybe T.Exp),
                       gdeclpos :: S.SPos}
  deriving Show                      

type GMap = M.Map S.Id GlobInfo

-- For locals we just need the target language id (the key into the map of
-- locals) and the type of this local.  T.Id's are guaranteed to never be
-- shadowed by our sanity checker, so we don't need to keep track of scope
-- information.
data LocalInfo = LInfo {ltid  :: T.Id,
                        ltype :: BaseType}
type LMap = M.Map S.Id LocalInfo

data BaseType =
    IntType S.SPos
        -- Any "integer" type, including chars and longs

  | BoolType S.SPos
        -- Bools, handled separately because we can model them more precisely.

  | FloatType S.SPos
        -- Any floating point type, including flots, doubles, etc.

  | ChannelType S.SPos
       -- A special case for any C types that we want to interpret at CSP
       -- channels.

  | MutexType S.SPos
      -- A special case for any C types that we want to interpret as mutexes.

  | PIDType S.SPos
      -- A special case for any C types that we want to interpret as thread ids.

  | UnitType S.SPos
       -- Unit.  Sometimes used to represent.

  | StructType S.SPos S.Id
      -- struct and union BaseTypes do not record information about their
      -- fields.  Instead, that information is stored int he TypeInfo associated
      -- with the struct, since it has to do only with the data representation
      -- and not the identity of the type.

  | UnionType S.SPos S.Id
      -- Similar to structs.  Our CSP representation is actually just like a
      -- struct's.  We have one CSP constructor with a field for each possible
      -- union element.  When one field is set, we change the others to
      -- "unknown".
      --
      -- The more natural representation would be a datatype with a separate
      -- constructor for each possible union element, but this way we can
      -- reuse a lot of the code for structs.

  | PointerType S.SPos BaseType (Maybe Integer)
    -- The "Maybe Integer" is an optional length for statically-sized arrays.
    -- It is ignored in comparisons.

  | VoidStarType S.SPos
    -- We treat a void* differently than other pointers, since we don't know
    -- what type of data it points to.  In particular, we represent it as a tagged
    -- union of the pointer represenations for every type.

  | FunctionType S.SPos 
      -- Don't need any more info right now... but probably eventually, especially
      -- if I'm going to handle function pointers
  
  | UnknownType S.SPos
  deriving (Show)

ppBaseType :: BaseType -> String
ppBaseType (BoolType _)         = "bool"
ppBaseType (IntType _)          = "int"
ppBaseType (FloatType _)        = "float"
ppBaseType (ChannelType _)      = "CHAN"
ppBaseType (MutexType _)        = "MUTEX"
ppBaseType (PIDType _)          = "PID"
ppBaseType (UnitType _)         = "Unit"
ppBaseType (StructType _ sid)   = "struct " ++ emitId sid
ppBaseType (UnionType _ sid)    = "union " ++ emitId sid
ppBaseType (PointerType _ bt _) = ppBaseType bt ++ "*"
ppBaseType (VoidStarType _)     = "void*"
ppBaseType (FunctionType _)     = "<function type>"
ppBaseType (UnknownType _)      = "<unknown type>"

instance Eq (BaseType) where
  (==) (IntType _) (IntType _) = True
  (==) (BoolType _) (BoolType _) = True
  (==) (FloatType _) (FloatType _) = True
  (==) (ChannelType _) (ChannelType _) = True
  (==) (MutexType _) (MutexType _) = True
  (==) (PIDType _)  (PIDType _) = True
  (==) (UnitType _) (UnitType _) = True
  (==) (StructType _ sid1) (StructType _ sid2) = sid1 == sid2
  (==) (UnionType _ sid1) (UnionType _ sid2)   = sid1 == sid2
  (==) (PointerType _ bt1 _) (PointerType _ bt2 _) = bt1 == bt2
  (==) (VoidStarType _) (VoidStarType _)         = True
  (==) (FunctionType _) (FunctionType _) = True -- XXX
  (==) (UnknownType _) (UnknownType _) = True   -- XXX
  (==) _ _ = False

-- I have no idea if this is the most efficient way to implement compare.
instance Ord (BaseType) where
  compare (IntType _)           (IntType _)           = EQ
  compare (IntType _)           _                     = LT
  compare _                     (IntType _)           = GT
  compare (BoolType _)          (BoolType _)          = EQ
  compare (BoolType _)           _                    = LT
  compare _                     (BoolType _)          = GT
  compare (FloatType _)         (FloatType _)         = EQ
  compare (FloatType _)         _                     = LT
  compare _                     (FloatType _)         = GT
  compare (ChannelType _)       (ChannelType _)       = EQ
  compare (ChannelType _)       _                     = LT
  compare _                     (ChannelType _)       = GT
  compare (MutexType _)         (MutexType _)         = EQ
  compare (MutexType _)         _                     = LT
  compare _                     (MutexType _)         = GT
  compare (PIDType _)           (PIDType _)           = EQ
  compare (PIDType _)           _                     = LT
  compare _                     (PIDType _)           = GT
  compare (UnitType _)          (UnitType _)          = EQ
  compare (UnitType _)          _                     = LT
  compare _                     (UnitType _)          = GT
  compare (StructType _ sid1)   (StructType _ sid2)   = compare sid1 sid2
  compare (StructType _ _)      _                     = LT
  compare _                     (StructType _ _)      = GT
  compare (UnionType _ sid1)    (UnionType _ sid2)    = compare sid1 sid2
  compare (UnionType _ _)       _                     = LT
  compare _                     (UnionType _ _)       = GT
  compare (PointerType _ bt1 _) (PointerType _ bt2 _) = compare bt1 bt2
  compare (PointerType _ _ _)   _                     = LT
  compare _                     (PointerType _ _ _)   = GT
  compare (VoidStarType _)      (VoidStarType _)      = EQ
  compare (VoidStarType _)      _                     = LT
  compare _                     (VoidStarType _)      = GT
  compare (FunctionType _)      (FunctionType _)      = EQ
  compare (FunctionType _)      _                     = LT
  compare _                     (FunctionType _)      = GT
  compare (UnknownType _)       (UnknownType _)       = EQ


locBaseType :: BaseType -> S.SPos
locBaseType (IntType sp)         = sp
locBaseType (BoolType sp)        = sp
locBaseType (FloatType sp)       = sp
locBaseType (ChannelType sp)     = sp
locBaseType (MutexType sp)       = sp
locBaseType (PIDType sp)         = sp
locBaseType (UnitType sp)        = sp
locBaseType (StructType sp _)    = sp
locBaseType (UnionType sp _)     = sp
locBaseType (PointerType sp _ _) = sp
locBaseType (VoidStarType sp)    = sp
locBaseType (FunctionType sp)    = sp
locBaseType (UnknownType sp)     = sp

data TypeInfo = 
   TypeInfo {tiRepType :: T.Id,  -- the type we use to represent this in CSP

             tiLocType :: T.Id, -- the type of locations that store this type

             tiGlobalLocType :: T.Id,  -- the type of global locations that store this type
             tiLocalLocType :: T.Id,   -- the same, for locals
             
             -- The next four are tags used in the datatype representing
             -- locations of this type, which looks like:
             --   data FooLoc = tiNullLoc | tiUnknown
             --    .          | tiLocalLocTag liLocalLocType
             --    .          | tiGlobalLocTag tiGlobalLocType
             tiLocalLocTag :: T.Id,
             tiGlobalLocTag :: T.Id,
             tiNullLoc :: T.Id,
             tiUnknownLoc :: T.Id,
             
             tiLocalsProj :: T.Id, -- The name of the CSPm function which
                                   -- projects the locals of this type
                                   -- from the larger LocalState type.

             -- The next four are used in conjunction with our representation of
             -- void*.  The value stored for a void* is an element of a tagged
             -- union containng all location types.  tiVoidStarLTag and
             -- tiVoidStarGTag are the names of the constructors for local and
             -- global locations of this type, respectively, in the tagged union
             -- (so they should have type "tiLocalLocType -> VoidStarRep" and
             -- "tiGlobalLocType -> VoidStarRep").  tiVoidStarProj projects a
             -- location of this type out of the void* union (so it should have
             -- type "VoidStarRep -> tiLocType"), and tiVoidStarInj injects a
             -- location of this type into the union.
             tiVoidStarLTag :: T.Id,
             tiVoidStarGTag :: T.Id,
             tiVoidStarProj :: T.Id,
             tiVoidStarInj :: T.Id,

             
             tiLocalsUpdate :: T.Id,
               -- The name of the CSPm function which, given the current
               -- LocalState, a local variable of this type and a corresponding
               -- value, produces the updated LocalState.

             tiLocalsDelete :: T.Id,
               -- The name of the CSPm function which, given the current
               -- LocalState and the name of a variable of this type, produces a
               -- LocalState where the variable has been deleted from the map.
             
             tiArrayLocs :: T.Id,
             -- The name of the cspm function that handles memory locality.  Its
             -- type is:
             --
             -- tiArrayLocs :: (btLoc,CIntRep) -> <btLoc>
             --
             -- For a location that corresponds to a statically-allocated array,
             -- it will return either a one-element list containing the nth
             -- subsequent location, or an empty list if (a) the input location
             -- is not an array, (b) the arrays is too short, or (c) the input
             -- number is unknown.  Here we're just using lists as a proxy for
             -- Maybe, since CSPm doesn't have it.
             
             tiReader :: T.Id,
             tiWriter :: T.Id,
               -- The names of CSPm functions that read from and write to
               -- variables of this type.
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

             tiReaderChan  :: T.Id,  -- the name of the channel that communicates
                                     --    reads of global vars of this type.
                                     --    (i.e., a   locType => repType => Event)

             tiWriterChan :: T.Id,   -- the name of the channel that communicates
                                     -- writes of gvars of this type.
             
             tiVarCellBuilder :: T.Id,
                -- The name of the CSPm definition that builds variable cells
                -- holding data of this type.

             tiVarCells :: T.Id,
                -- The name of the CSPm definition representing the segment of
                -- memory holding all global variables of this type.


             tiBase    :: BaseType,
               -- It is convenient to have a record of the BaseType that was
               -- used to create this TypeInfo here.

             tiDataInfo :: (Either StructInfo String)
               -- Info about the how to deal with data of this type.  This is
               -- either a StructInfo for struct types, or just a name to use
               -- in the global reader/writers for vars of this type.
            }
   deriving (Show,Eq,Ord)

data StructInfo =
    StructInfo {siConName :: T.Id,  -- the name of this type's lone data constructor
                siFields :: [FieldInfo] -- Info about the struct's fields.
               }
  deriving (Show,Eq,Ord)

data FieldInfo =
  FieldInfo {fiSourceName :: String,          
             -- The source name of the field

             fiTargetNameHint :: String,
             -- the target name of the field, used only in generating
             -- the memory process.

             fiReaderChan :: T.Id,
             -- the name of the channel that reads this field

             fiWriterChan :: T.Id,
             -- the name of the channel that writes this field

             fiReader :: T.Id,
             fiWriter :: T.Id,
             -- the name of the CSPm functions that read from and write to
             -- just this field of the struct
             --
             -- the types are the same as tiReader and tiWriter above.

             fiFieldProj :: T.Id,
             -- The name of a CSPm function that projects this field out when
             -- provided with the whole struct.

             fiFieldInj :: T.Id,
             -- The name of a CSPm function that takes a struct of this type and
             -- a new value for this particular field, and produces an updated
             -- struct value.

             fiSubfields  :: [FieldInfo],
             -- If this field contains another struct, we need info
             -- about the fields of that struct too (for accessors).
             
             fiType       :: BaseType
             -- The type of this field's data.
            }
  deriving (Show,Eq,Ord)

-- Types
--
-- Our memory model is unusual in that it keeps track of and uses the types of
-- C data to model how things are stored.  For example, structs are stored as
-- a whole, with channels to communicate modifying their individual parts.
--
-- This model requires us to keep track of several pieces of information for
-- each C type.  For example, we need the CSPm type of "locations" that hold
-- each C type, as well as channels to communicate reads and writes at these
-- locations.  That information is contained in a TypeInfo, which is
-- constructed the first time we come accross a particular C type in the
-- translation.  We keep track of these in the map TImpMap, which maps basic C
-- types to TypeInfos.
type TImpMap = M.Map BaseType TypeInfo   -- Type implementations

-- Typedefs
--
-- TMap maps type names from source files to types.
--
-- Typedefs are treated as global.  We don't support local typedef or
-- struct declarations.
type TDefMap = M.Map S.Id BaseType

-- In C, functions are their own namespace.  For each source function, we record:
-- 
-- - The name of its CSP implementation, for when this function is called in
--   other bits of code.
--
-- - The return type, to help checking type information when this function is
--   called in other bits of code.
-- 
-- - The types of its arguments, which allow us to typecheck uses of this
--   function or to produce a stub for it in the event it is never defined.
-- 
-- - Whether this function has been defined.
--
-- We DO NOT record the names of the function's arguments.  That information is
-- not needed until we translate the function's implementation, and recording it
-- early can result in problems with the local variable scope.
data FInfo = FInfo {ftid  :: T.Id,
                    fret  :: BaseType,
                    fargs :: [BaseType],
                    fdef  :: Bool
                   }

type FMap = M.Map S.Id FInfo

-- We allow the range of values represented by some base types to be configured 
-- by the user. In order to do so, we require several pieces of information:
--
-- An ID string to help us refer to this effective range.
--
-- The base type that this range refers to.
--
-- A constant that refers to the minimum possible value.
--
-- A constant that refers to the maximum possible value.
data RInfo = RInfo {rmin  :: Int,
                    rmax  :: Int
                   }

data Ranges = Ranges {intRange :: RInfo}

-- This map keeps track of information about statically-sized arrays. 
--
-- For each statically allocated array of this type, we record the list of
-- corresponding locations here, as well as whether the array is local or global,
type AMap = M.Map BaseType [ArrayLocs]

data ArrayLocs = ALLocal [T.Id]
               | ALGlobal [T.Id]
  
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

    typedefs :: TDefMap,  -- Info about typdefs from the source
                          -- program and their definition

    types    :: TImpMap,  -- Info about our CSP implementation of
                          -- C types.

    globals  :: GMap,    -- Mapping from global source identifiers to
                         -- target variable info.

    locals   :: LMap,    -- Mapping form local source identifiers to target
                         -- variable info

    ranges   :: Ranges,  -- Info about the range of available values for various
                         -- types. Currently used only for C integers, but made 
                         -- generically so that it could also be used for pids, 
                         -- mutexes, etc.
                
    functions :: FMap,   -- Map source function names to target function
                         -- names.

    arrays :: AMap,      -- Map basetypes to info about any statically-allocated
                         -- arrays of that type.

    localAddresses :: [LocalInfo],
                         -- We need source locals to be globally unique for
                         -- the 'state map'.  This is actually a slight lie -
                         -- we could get away with only keeping track of
                         -- locals whose address is taken (this would also be
                         -- a big performance win), but for now we're doing
                         -- the simple thing.

    warnings :: [Warning]
  }

internal :: S.SPos
internal = S.initialPos "INTERNAL"

--------------------------------------------------------------------
------- Base Type definitions
--------------------------------------------------------------------

-- All IDs used here must be avoided during name generation in the monad.  This
-- happens automatically, now, because these are "Fixed" ids and the monad generated
-- non-fixed ones.

cIntBaseType :: BaseType
cIntBaseType = IntType internal

cBoolBaseType :: BaseType
cBoolBaseType = BoolType internal

cFloatBaseType :: BaseType
cFloatBaseType = FloatType internal

unitBaseType :: BaseType
unitBaseType = UnitType internal

cIntKnownCon,cIntUnknownCon :: T.Id
cIntKnownCon   = T.Fixed "CIntKnown"
cIntUnknownCon = T.Fixed "CIntUnknown"

cFloatUnknownCon :: T.Id
cFloatUnknownCon = T.Fixed "CFloatUnknown"

cBoolTrueCon, cBoolFalseCon, cBoolUnknownCon :: T.Id
cBoolTrueCon    = T.Fixed "CBoolTrue"
cBoolFalseCon   = T.Fixed "CBoolFalse"
cBoolUnknownCon = T.Fixed "CBoolUnknown"

unitValCon :: T.Id
unitValCon = T.Fixed "UnitVal"

cIntToBool, cBoolToInt :: T.Id
cIntToBool = T.Fixed "intToBool"
cBoolToInt = T.Fixed "boolToInt"

cIntToFloat, cFloatToInt :: T.Id
cIntToFloat = T.Fixed "intToFloat"
cFloatToInt = T.Fixed "floatToInt"

cTernary :: T.Id
cTernary = T.Fixed "cond"

mutexInitCon, mutexUnInitCon :: T.Id
mutexInitCon = T.Fixed "MutCSP"
mutexUnInitCon = T.Fixed "MutCSP_UNINITIALIZED"

pidTypId :: T.Id
pidTypId = T.Fixed "PIDTyp"

pidKnownCon, pidUnknownCon :: T.Id
pidKnownCon = T.Fixed "PID"
pidUnknownCon = T.Fixed "PIDUnknown"



-- This is a helper function for creating the "built-in" TypeInfos.  It takes in
-- the base type and the RepType name (as a string) and constructs fixed names
-- for the other TypeInfo fields in a regular way.
fixedTypeInfoBuilder :: BaseType -> String -> TypeInfo
fixedTypeInfoBuilder btyp unm =
  TypeInfo {
    tiRepType        = T.Fixed unm,
    tiLocType        = T.Fixed $ unm ++ "Loc",
    tiLocalLocType   = T.Fixed $ unm ++ "LLoc",
    tiGlobalLocType  = T.Fixed $ unm ++ "GLoc",
    tiReaderChan     = T.Fixed $ lnm ++ "Read_c",
    tiWriterChan     = T.Fixed $ lnm ++ "Write_c",

    tiVarCellBuilder = T.Fixed $ unm ++ "_VAR",
    tiVarCells       = T.Fixed $ unm ++ "_VARS",

    tiVoidStarLTag   = T.Fixed $ unm ++ "_VoidLTag",
    tiVoidStarGTag   = T.Fixed $ unm ++ "_VoidGTag",
    tiVoidStarProj   = T.Fixed $ lnm ++ "_VoidLocProj",
    tiVoidStarInj    = T.Fixed $ lnm ++ "_VoidLocInj",
    
    tiLocalsProj     = T.Fixed $ lnm ++ "LocalsProj",
    tiLocalsUpdate   = T.Fixed $ lnm ++ "LocalsUpd",
    tiLocalsDelete   = T.Fixed $ lnm ++ "LocalsDel",

    tiArrayLocs      = T.Fixed $ lnm ++ "ArrayLocs",

    tiReader        = T.Fixed $ lnm ++ "Reader",
    tiWriter        = T.Fixed $ lnm ++ "Writer",

    tiLocalLocTag   = T.Fixed $ unm ++ "LLocTag",
    tiGlobalLocTag  = T.Fixed $ unm ++ "GLocTag",
    tiNullLoc       = T.Fixed $ unm ++ "Loc_Null",
    tiUnknownLoc    = T.Fixed $ unm ++ "Loc_Unknown",
    tiDataInfo      = Right $ lnm ++ "_data_info",
    tiBase          = btyp
  }
  where
    lnm :: String
    lnm = case unm of
            [] -> []
            (c:cs) -> toLower c : cs


cIntTypeInfo :: TypeInfo
cIntTypeInfo = fixedTypeInfoBuilder cIntBaseType "CInt"

cBoolTypeInfo :: TypeInfo
cBoolTypeInfo = fixedTypeInfoBuilder cBoolBaseType "CBool"

cFloatTypeInfo :: TypeInfo
cFloatTypeInfo = fixedTypeInfoBuilder cFloatBaseType "CFloat"

voidStarTypeInfo :: TypeInfo
voidStarTypeInfo = fixedTypeInfoBuilder (VoidStarType internal) "VoidStar"

unitTypeInfo :: TypeInfo
unitTypeInfo = fixedTypeInfoBuilder unitBaseType "Unit"

-- XXX this is horrid
chanTypeInfo :: TypeInfo
chanTypeInfo = ti {tiRepType = T.Fixed "ChannelNames"}
  where
    ti :: TypeInfo
    ti = fixedTypeInfoBuilder (ChannelType internal) "Chan"
                               
mutexTypeInfo :: TypeInfo
mutexTypeInfo = fixedTypeInfoBuilder (MutexType internal) "MutexCSP"

pidTypeInfo :: TypeInfo
pidTypeInfo = fixedTypeInfoBuilder (PIDType internal) "PIDTyp"



------
------ Other IDs
------
localProjErrorChanId, arrayIndexErrorChanId :: T.Id
localProjErrorChanId = T.Fixed "localProj_ERROR"
arrayIndexErrorChanId = T.Fixed "arrayIndex_ERROR"


------------------------------------------------------------
----- Memory Model definitions
------------------------------------------------------------


-- The next few definitions are just unique names that we refer to in the
-- memory model.  They don't really belong here in the monad, but the module
-- boundry between these two parts of the code is already awfully weak.
--
-- "localStateType" is the name of local state map type.  "localStateCon" is its
-- sole constructor.  "localStateEmpty" is the name of an initial, empty local
-- state defined in globVarDecs for convenience.
localStateType, localStateCon, localStateEmpty :: T.Id
localStateType  = T.Fixed "LocalState"
localStateCon   = T.Fixed "LSMaps"
localStateEmpty = T.Fixed "emptyLocalState"

-- The name of the datatype that models values with C type void*, the name of
-- the channel we use to signal errors related to void* casts, and the name of
-- the function that tests void* for null.
voidStarRepType, voidStarNullTest, voidStarNullCon, voidStarUnknownCon :: T.Id
voidStarRepType    = T.Fixed "VoidStar"
voidStarNullTest   = T.Fixed "voidStarNullTest"
voidStarNullCon    = T.Fixed "VoidStarNull"
voidStarUnknownCon = T.Fixed "VoidStarUnknown"

-- These are three unique process names that we build in the memory model.
memoryName, runInMemoryName, hideMemoryName :: T.Id
memoryName = T.Fixed "MEMORY"
runInMemoryName = T.Fixed "runInMemory"
hideMemoryName = T.Fixed "hideMemory"

-- XXX generalize to take in all the parameters
initState :: (Int,Int) ->  [(S.Id,FInfo)] -> CGEnv
initState (cmin,cmax) fs =
    CGEnv {uniq      = 0,
           typedefs  = M.empty,
           types     = M.fromList [(cIntBaseType,cIntTypeInfo),
                                   (cBoolBaseType,cBoolTypeInfo),
                                   (cFloatBaseType,cFloatTypeInfo),
                                   (VoidStarType internal,voidStarTypeInfo),
                                   (unitBaseType,unitTypeInfo),
                                   (ChannelType internal,chanTypeInfo),
                                   (MutexType internal,mutexTypeInfo),
                                   (PIDType internal,pidTypeInfo)],
           globals   = M.empty,
           locals    = M.empty,
           arrays    = M.empty,
           ranges    = Ranges {intRange = RInfo {rmin=cmin,rmax=cmax}},
           functions = M.fromList fs,
           localAddresses = [],
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

  fail err = CG (\pst -> (pst,Left err))

  m >>= k  = CG (\env -> case unCG m env of
                          (pst,Left err) -> (pst,Left err)
                          (pst,Right v) -> unCG (k v) pst)

instance Applicative CG where
  pure  = return
  (<*>) = ap

instance UniqueMonad CG where
  freshUnique = getUniq

instance CheckpointMonad CG where
  type Checkpoint CG = CGEnv
  
  checkpoint = CG (\env -> (env,Right env))
  restart m  = CG (\_-> (m,Right ()))

freshLocation :: String -> CG (Label,T.Id)
freshLocation nmHint = do
  label <- freshLabel
  tid <- freshTid $ Just $ nmHint ++ "_" ++ show label
  return (label,tid)

runCG :: CGEnv -> CG a -> (Either ErrMsg a, [Warning])
runCG pst (CG cg) =
  case cg pst of
    (CGEnv {warnings},r) -> (r,warnings)

extendGlobal :: S.Id -> GlobInfo -> CG ()
extendGlobal sid ginfo =
  CG (\pst -> (pst {globals=M.insert sid ginfo (globals pst)},Right ()))

extendFunction :: S.Id -> FInfo -> CG ()
extendFunction sid finfo =
  CG (\pst -> 
          (pst {functions=M.insert sid finfo (functions pst)},
           Right ()))

extendLocalAddresses :: LocalInfo -> CG ()
extendLocalAddresses linfo =
  CG (\pst -> (pst {localAddresses=linfo:localAddresses pst},
               Right ()))

extendType :: BaseType -> TypeInfo -> CG ()
extendType bt tinfo = 
  CG (\pst -> (pst {types=M.insert bt tinfo (types pst)},
               Right ()))

extendLocal :: S.Id -> LocalInfo -> CG ()
extendLocal sid linfo =
  CG (\pst -> 
        (let oldLocals = locals pst in
         pst {locals = M.insert sid linfo oldLocals},
         Right ()))

clearLocalState :: CG ()
clearLocalState = 
  CG (\pst -> (pst {locals = M.empty},Right ()))

addTypeDef :: S.Id -> BaseType -> CG ()
addTypeDef sid td =
  CG (\pst ->
        (pst {typedefs=M.insert sid td (typedefs pst)},
         Right ()))

getGlobals :: CG GMap
getGlobals = CG (\pst -> (pst,Right $ globals pst))

getFunctions :: CG FMap
getFunctions = CG (\pst -> (pst,Right $ functions pst))

getArrays :: CG AMap
getArrays = CG (\pst -> (pst,Right $ arrays pst))

getLocalAddresses :: CG [LocalInfo]
getLocalAddresses = CG (\pst -> (pst,Right $ localAddresses pst))

getLocals :: CG LMap
getLocals = CG (\pst -> (pst,Right $ locals pst))

getTypeInfos :: CG TImpMap
getTypeInfos = CG (\pst -> (pst,Right $ types pst))

getTypedefs :: CG TDefMap
getTypedefs = CG (\pst -> (pst,Right $ typedefs pst))

getUniq :: CG Int
getUniq = CG (\pst -> (pst {uniq = 1 + (uniq pst)}, Right $ uniq pst))
 
getRanges :: CG Ranges
getRanges = CG (\pst -> (pst,Right $ ranges pst ))

getCIntRange :: CG (Int,Int)
getCIntRange = do
  allRanges <- getRanges
  let cIntRange = intRange allRanges
  return (rmin cIntRange, rmax cIntRange)

addArray :: BaseType -> ArrayLocs -> CG ()
addArray bt arr = CG (\pst@(CGEnv {arrays}) ->
  case M.lookup bt arrays of
    Nothing ->   (pst {arrays = M.insert bt [arr] arrays},Right ())
    Just arrs -> (pst {arrays = M.insert bt (arr:arrs) arrays},Right ()))

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

-------------
------------- Interface for looking up data
-------------

-- This type is used to answer variable lookup requests
data VarInfo = Global GlobInfo
             | Local LocalInfo
             | NotBound

-- lookupVarInfo :: S.Id -> CG VarInfo
-- lookupVarInfo n = do
--   locals <- getLocals
--   case M.lookup n locals of
--     Just linfo -> return $ Local linfo
--     Nothing -> do
--       globals <- getGlobals
--       case M.lookup n globals of
--         Just ginfo -> return $ Global ginfo
--         Nothing -> return NotBound

lookupLocalVar :: S.Id -> CG (Maybe LocalInfo)
lookupLocalVar sid = do
  locals <- getLocals
  return $ M.lookup sid locals

globalExists :: S.Id -> CG Bool
globalExists sid = do
  globals <- getGlobals
  return $ isJust $ M.lookup sid globals

addGlobalInitializer :: S.Id -> T.Exp -> CG ()
addGlobalInitializer sid initval = do
  globals <- getGlobals
  case M.lookup sid globals of
    Nothing -> fail $ "Internal error in translation: attempt to add "
                   ++ "initializer for undeclared global " ++ show sid
    Just (GInfo {ginit=Just _}) -> fail $
         "Error: encountered initializer for variable " ++ show sid
      ++ " but this variable has already been initialized."
    Just ginfo -> extendGlobal sid (ginfo {ginit=Just initval})


lookupVar :: S.Id -> CG (Maybe (T.Exp,BaseType,TypeInfo))
lookupVar n = do
  locals <- getLocals
  case M.lookup n locals of
    Just (LInfo {ltid,ltype}) -> do
      tinfo <-  lookupTypeInfo ltype
      return $ Just (T.EDot (T.EId $ tiLocalLocTag tinfo) [T.EId ltid],
                     ltype,tinfo)
    Nothing -> do
      globals <- getGlobals
      case M.lookup n globals of
        Just (GInfo {gtid,gtype}) -> do 
          tinfo <- lookupTypeInfo gtype
          return $ Just (T.EDot (T.EId $ tiGlobalLocTag tinfo) [T.EId gtid],
                         gtype,tinfo)
        Nothing -> return Nothing

lookupFunction :: S.Id -> CG (Maybe FInfo)
lookupFunction f = M.lookup f <$> getFunctions

lookupFunctionByName :: String -> CG (Maybe FInfo)
lookupFunctionByName nm = do
  fs <- M.toList <$> getFunctions
  return $ fmap snd $ find (\(S.Id nm' _ _,_) -> nm == nm') fs

hasTypeInfo :: BaseType -> CG Bool
hasTypeInfo bt = do
  tinfos <- getTypeInfos
  return $ isJust $ M.lookup bt tinfos

lookupTypeInfo :: BaseType -> CG TypeInfo
lookupTypeInfo bt =
  case bt of
    FunctionType _ -> failBase bt "Internal error: lookupTypeInfo called on FunctionType"
    UnknownType _ -> failBase bt "Internal error: lookupTypeInfo called on UnknownType"
    _ -> do
      tinfos <- getTypeInfos
      case M.lookup bt tinfos of
        Just ti -> return ti
        Nothing ->
          -- This is just for error messages
          case bt of
            IntType _ -> 
                failBase bt "Internal error: no typeinfo found for Int base type"
            BoolType _ -> 
                failBase bt "Internal error: no typeinfo found for Bool base type"
            ChannelType _ -> 
                failBase bt "Internal error: no typeinfo found for Chan base type"
            MutexType _ -> 
                failBase bt "Internal error: no typeinfo found for Mutex base type"
            PIDType _ -> 
                failBase bt "Internal error: no typeinfo found for PID base type"
            StructType _ _ -> 
                failBase bt "Unsupported: Struct type used before declaration"
            UnionType _ _ -> 
                failBase bt "Unsupported: Union type used before declaration"
            _ ->
              -- derived types like foo* and foo[] are not explicitly declared
              -- before using them, so we generate typeinfos the first time we
              -- encounter them.
              buildNewTypeInfo bt Nothing

lookupTypeDef :: S.Id -> CG (Maybe BaseType)
lookupTypeDef n = do
  env <- getTypedefs
  return $ M.lookup n env

-------------
------------- Interfaces for adding data
-------------

-- Generate the fresh names for a new type info, given the RepType, the field
-- types, and a hint for good name generation.
freshTypeInfoNames :: String -> T.Id -> BaseType -> Either StructInfo String
                 -> CG TypeInfo
freshTypeInfoNames nm tiRepType tiBase tiDataInfo = do
  tiLocType        <- freshTid (Just $ nm ++ "Loc")
  tiLocalLocType   <- freshTid (Just $ nm ++ "LLoc")
  tiGlobalLocType  <- freshTid (Just $ nm ++ "GLoc")
  tiReaderChan     <- freshTid (Just $ map toLower $ nm ++ "_read_c")
  tiWriterChan     <- freshTid (Just $ map toLower $ nm ++ "_write_c")
  tiNullLoc        <- freshTid (Just $ nm ++ "Loc_Null")
  tiUnknownLoc     <- freshTid (Just $ nm ++ "Loc_Unknown")
  tiGlobalLocTag   <- freshTid (Just $ nm ++ "GLocTag")
  tiLocalLocTag    <- freshTid (Just $ nm ++ "LLocTag")
  tiVoidStarLTag   <- freshTid (Just $ nm ++ "VoidStarLTag")
  tiVoidStarGTag   <- freshTid (Just $ nm ++ "VoidStarGTag")
  tiVoidStarProj   <- freshTid (Just $ (map toLower nm) ++ "VoidLocProj")
  tiVoidStarInj    <- freshTid (Just $ (map toLower nm) ++ "VoidLocInj")
  tiLocalsProj     <- freshTid (Just $ (map toLower nm) ++ "LocalsProj")
  tiLocalsUpdate   <- freshTid (Just $ (map toLower nm) ++ "LocalsUpd")
  tiLocalsDelete   <- freshTid (Just $ (map toLower nm) ++ "LocalsDel")
  tiArrayLocs      <- freshTid (Just $ (map toLower nm) ++ "ArrayLocs")
  tiReader         <- freshTid (Just $ (map toLower nm) ++ "Reader")
  tiWriter         <- freshTid (Just $ (map toLower nm) ++ "Writer")
  tiVarCellBuilder <- freshTid (Just $ nm ++ "_VAR")
  tiVarCells       <- freshTid (Just $ nm ++ "_VARS")
  return $ TypeInfo {tiRepType,tiLocalLocType,tiGlobalLocType,
                     tiLocType,tiReaderChan,tiWriterChan,
                     tiVoidStarLTag,tiVoidStarGTag,
                     tiVoidStarProj,tiVoidStarInj,
                     tiLocalsProj,tiLocalsUpdate,tiLocalsDelete,
                     tiArrayLocs,tiNullLoc,tiUnknownLoc,
                     tiGlobalLocTag,tiLocalLocTag,
                     tiReader,tiWriter,
                     tiVarCellBuilder,tiVarCells,
                     tiDataInfo,tiBase}

-- buildNewTypeInfo creates a new TypeInfo for a provided BaseType.  This
-- primarily consists of generating fresh names and ensuring that TypeInfos
-- already exist for any components of the BaseType, in the case of
-- structs/unions.
buildNewTypeInfo :: BaseType -> Maybe S.StructFields -> CG TypeInfo
buildNewTypeInfo bt@(FunctionType _) _ =
  failBase bt "Internal Error: Encountered FunctionType in buildNewTypeInfo"
buildNewTypeInfo bt@(UnknownType _) _ =
  failBase bt "Internal Error: Encountered UnknownType in buildNewTypeInfo"
buildNewTypeInfo bt@(IntType _) _ =
  failBase bt "Internal Error: Encountered IntType in buildNewTypeInfo"
buildNewTypeInfo bt@(BoolType _) _ =
  failBase bt "Internal Error: Encountered BoolType in buildNewTypeInfo"
buildNewTypeInfo bt@(FloatType _) _ =
  failBase bt "Internal Error: Encountered FloatType in buildNewTypeInfo"
buildNewTypeInfo bt@(UnitType _) _ =
  failBase bt "Internal Error: Encountered UnitType in buildNewTypeInfo"
buildNewTypeInfo bt@(ChannelType _) _ =
  failBase bt "Internal Error: Encountered ChannelType in buildNewTypeInfo"
buildNewTypeInfo bt@(MutexType _) _ =
  failBase bt "Internal Error: Encountered MutexType in buildNewTypeInfo"
buildNewTypeInfo bt@(PIDType _) _ =
  failBase bt "Internal Error: Encountered PIDType in buildNewTypeInfo"
buildNewTypeInfo bt@(PointerType _ _ _) (Just _) =
  failBase bt $ "Internal Error: Encountered PointerType with StructFields "
             ++ "in buildNewTypeInfo"
buildNewTypeInfo (PointerType sp bt _) Nothing = do
  -- We assume transType has already been called on bt, so its TypeInfo must
  -- exist.  We do not consider the length, in the case of a statically-sized array.
  baseTInfo <- lookupTypeInfo bt
  let tiRepType = tiLocType baseTInfo 
      nm = T.namePart tiRepType
      tiFieldName = map toLower nm
  tinfo <- freshTypeInfoNames nm tiRepType (PointerType sp bt Nothing)
                              (Right tiFieldName)
  extendType (PointerType sp bt Nothing) tinfo
  return tinfo
buildNewTypeInfo bt@(VoidStarType _) _ =
  failBase bt $ "Internal Error: Encountered VoidStarType in buildNewTypeInfo"
buildNewTypeInfo bt@(StructType _ snm) Nothing =
  failBase bt $ "Unsupported: use of struct " ++ emitId snm
             ++ " occurs before its definition"
buildNewTypeInfo tbt@(StructType _ snm) (Just flds) =
  buildNewStructUnionTypeInfo tbt snm flds
buildNewTypeInfo bt@(UnionType _ snm) Nothing =
  failBase bt $ "Unsupported: use of union " ++ emitId snm
             ++ " occurs before its definition"
buildNewTypeInfo tbt@(UnionType _ snm) (Just flds) =
  buildNewStructUnionTypeInfo tbt snm flds

-- XXX type StructFields = [(Maybe String, Type, Maybe Integer)]


-- A subcase of buildNewTypeInfo that deals with structs and unions
buildNewStructUnionTypeInfo :: BaseType -> S.Id -> S.StructFields -> CG TypeInfo
buildNewStructUnionTypeInfo bt sid flds = do
  -- We begin with a bit of a hack.  We need to translate this struct or union's
  -- fields.  But the struct may be recursive.  In that case, when transType
  -- encounters the recursive variable it will cause an error since no type info
  -- for the current struct exists yet.
  --
  -- The solution is to add a "dummy" TypeInfo for this struct or union to the
  -- TypeInfo map, so that transType doesn't complain.  Then, after we've
  -- assembled the real TypeInfo, we replace the dummy.
  --
  -- This "dummy" can't just be any old TypeInfo.  In particular, its important
  -- that the names it uses are the correct ones, since they might be needed if,
  -- for example, a pointer to this struct or union is encountered.  However,
  -- its description of its own subfields is unimportant, because the current
  -- struct is only allowed to reference itself indirectly (according to the C
  -- spec, the current struct is an "incomplete" type during its own
  -- declaration, which you can't have a field of this type, though you can have
  -- a field that is a pointer to this type).  TODO: It would be nice to give a
  -- good error in the case that the user has an improper use of an incomplete
  -- type, but it seems a little tricky.
  let nm = S.stringPart sid
  tiRepType <- freshTid $ Just $ nm ++ "Typ"
  dummyTInfo <- freshTypeInfoNames nm tiRepType bt
                                   (Right "INTERNAL_RECURSIVE_STRUCT_DUMMY")
  extendType bt dummyTInfo

  --having inserted the dummy, we translate the fields:
  tfields <- mapM transField flds
  siFields <- mapM (buildFieldInfo nm) tfields

  -- now we build the real tinfo (keeping the names from the dummy) and replace
  -- the dummy in the TypeInfo map
  siConName <- freshTid $ Just nm
  let
    realStructInfo = StructInfo {siConName,siFields}
    realTInfo = dummyTInfo {tiDataInfo = Left realStructInfo}
  extendType bt realTInfo
  return realTInfo
  where
    transField :: (Maybe String, S.Type, Maybe Integer) -> CG (String,BaseType)
    transField (mfnm,ty,_) = do
      tty <- transType ty
      fnm <- case mfnm of
              Just fsid -> return fsid
              Nothing  -> do i <- getUniq
                             return $ "anonField" ++ show i
      return (fnm,tty)

    buildFieldInfo :: String -> (String,BaseType) -> CG FieldInfo
    buildFieldInfo _ (_,fbt@(FunctionType _)) =
      failBase fbt "Unsupported: Struct or union containing function"
    buildFieldInfo _ (_,fbt@(UnknownType _)) =
      failBase fbt $ "Internal Error: UnknownType encountered in "
                 ++ "struct or union field in buildFieldInfo"
    buildFieldInfo pre (fnm,fbt) = do
      ftinfo <- lookupTypeInfo fbt    -- Make sure the field's type is sane
      let pre' = pre ++ ('_' : map toLower fnm)
      fiReaderChan <- freshTid $ Just $ map toLower $ pre' ++ "_read_c"
      fiWriterChan <- freshTid $ Just $ map toLower $ pre' ++ "_write_c"
      fiReader <- freshTid $ Just $ map toLower $ pre' ++ "Reader"
      fiWriter <- freshTid $ Just $ map toLower $ pre' ++ "Writer"
      fiFieldProj <- freshTid $ Just $ map toLower $ pre' ++ "Proj"
      fiFieldInj <- freshTid $ Just $ map toLower $ pre' ++ "Inj"
      fiSubfields <- 
        let subfields =
              case tiDataInfo ftinfo of
                Right _ -> []
                Left (StructInfo {siFields}) ->
                  map (\FieldInfo {fiSourceName,fiType} -> (fiSourceName,fiType))
                      siFields
         in
        mapM (buildFieldInfo pre') subfields
      return $ FieldInfo {fiSourceName = fnm,
                          fiTargetNameHint = fnm, fiReaderChan, fiWriterChan,
                          fiReader,fiWriter,fiFieldProj,fiFieldInj,
                          fiSubfields, fiType = fbt
                         }


-- This checks to see if a TypeInfo for a particular BaseType already exists,
-- and creates the BaseType if not.  It takes an optional "S.StructFields"
-- argument, the BaseType for a struct does not carry information about its
-- fields.  It returns the provided BaseType, just for convenience.
checkForAndCreateTypeInfo :: BaseType -> Maybe S.StructFields -> CG BaseType
checkForAndCreateTypeInfo (PointerType _ bt@(FunctionType _) _) _ = return bt
checkForAndCreateTypeInfo bt msf = do
  hasTInfo <- hasTypeInfo bt
  unless hasTInfo $ do {_ <- buildNewTypeInfo bt msf; return ()}
  return bt

-- transType translates a source type to a BaseType.  If this is the first time
-- we've encountered the source type, we also generate a TypeInfo for it.
transType :: S.Type -> CG BaseType
transType (S.BoolType sp)         = return $ BoolType sp
transType (S.VoidType sp)         = return $ UnknownType sp
transType (S.Integral sp _)       = return $ IntType sp
transType (S.Floating sp _)       = return $ FloatType sp
transType (S.PointerType sp (S.VoidType _)) =
  -- special case for void*, which isn't handled like normal pointers.
  return $ VoidStarType sp
transType (S.PointerType sp t)    = do
  bt <- PointerType sp <$> transType t <*> pure Nothing
  checkForAndCreateTypeInfo bt Nothing
transType (S.ArrayType sp t sz)    = do
  bt <- PointerType sp <$> transType t <*> pure sz
  checkForAndCreateTypeInfo bt Nothing
transType (S.Struct sp mnm mfs)   = do
  nm <- 
    case mnm of
      Nothing -> do i <- getUniq  -- XXX just fail here because this is hanled in sanity checking?
                    return $ S.Id ("anonStruct" ++ show i) S.VSGlobal ( -1) -- XXX
      Just sid -> return sid
  checkForAndCreateTypeInfo (StructType sp nm) mfs
--  let btyp = StructType sp nm
--  mtinfo <- lookypTypeInfo btyp
--  case (mtinfo,mfs) of
--   (Just _,_)        -> return btyp
--   (Nothing,Nothing) -> failBase btyp $ "Occurence of struct " ++ show nm
--                                     ++ " occurs before definition."
--   (Nothing,Just fs) -> do
--     
--  
--  
--  tfields <- case mfs of
--               Nothing -> return []
--               Just fs -> mapM transField fs
--  let ty = StructType sp nm tfields
--  _ <- lookupTypeInfo ty  -- Just to make sure any names we just created get
--                          -- added to state
--  return yt
transType (S.Union sp mnm mfs)     = do
  nm <- 
    case mnm of
      Nothing -> do i <- getUniq  -- XXX just fail here becuase this is handled in sanity checking?
                    return $ S.Id ("anonUnion" ++ show i) S.VSGlobal ( -1)-- XXX
      Just sid -> return sid
  checkForAndCreateTypeInfo (UnionType sp nm) mfs
--  let ty = UnionType sp nm tfields
--  tfields <- case mfs of
--               Nothing -> return []
--               Just fs -> mapM transField fs
--  _ <- lookupTypeInfo ty  -- Just to make sure any names we just created get
--                          -- added to state
--  return ty
transType (S.Func sp _ _ _)         = return $ FunctionType sp
transType tt@(S.TypeDef _ tnm)      = do
  mtd <- lookupTypeDef tnm 
  case mtd of
    Nothing -> failType tt (   "Undefined type identifier " ++ emitId tnm
                            ++ " in transType ")
    Just td -> return td
transType tt@(S.Enum _ _ _)      = failType tt "transType called on enum"

------------
------------ Fresh name generation
------------


-- We do one check: C variables can begin with "_", but CSP variables can't, so
-- we strip any opening underscores from the name hint.
freshTid :: Maybe String -> CG T.Id
freshTid mhint = do
  i <- getUniq
  return $ T.Id (hint,i)
  where
    hint = case mhint of
             Just s -> dropWhile (== '_') s
             Nothing -> "x"

-------------
------------- Interface for adding state
-------------

-- Generate a new lvar name guaranteed to be fresh for the current context.  The
-- string input is a naming "hint".  This local has no analogue in the source,
-- so we don't record it in the map of C locals.
freshLocalNew :: String -> CG T.Id
freshLocalNew nm = freshTid $ Just nm

freshLocalsNew :: [String] -> CG [T.Id]
freshLocalsNew nms = mapM (freshTid . Just) nms

-- Generate a new local variable corresponding to some local variable from the
-- C.
freshLocal :: S.Id -> BaseType -> CG T.Id
freshLocal sid typ = do
  nm' <- unm
  tid <- freshTid (Just nm')
  let lcl = LInfo {ltid=tid,ltype=typ}
  extendLocalAddresses lcl
  extendLocal sid lcl
  return tid
  where
    unm :: CG String
    unm = case S.stringPart sid of
            [] -> fail "Empty name in freshLocal"
            (c:cs) -> return $ toUpper c : cs    

-- This creates n new local locations, and is meant to be used when we find a
-- local declaration of a statically-sized array.  It takes a name hint, the
-- base type of the array elements, and the length of the array.  It returns all
-- the locations in the array, which are likely used by the caller to set up the
-- local state map with the new locations and to initialize the array variable
-- itself.
--
-- Note that it will actually only build min(length,maxInt+1) cells, since any
-- more could never be used.
freshLocalArrayCells :: String -> BaseType -> Integer -> CG [T.Id]
freshLocalArrayCells nmHint bt len = do
  (_,maxInt) <- getCIntRange
  let cellCount = min (fromIntegral len) (1+maxInt)
  tids <- mapM (\i -> freshTid (Just $ nmHint ++ "_c" ++ show i))
               [0..(cellCount-1)]
  mapM_ (\ltid -> extendLocalAddresses (LInfo {ltid,ltype=bt})) tids
  addArray bt $ ALLocal tids
  return tids


freshGlobal :: S.Id -> BaseType -> Maybe T.Exp -> S.SPos -> CG T.Id
freshGlobal sid typ initval sp = do
  case typ of -- XXX for good error message.  Want to handle global channels one day.
    ChannelType _ ->
      failPos sp "Unsupported: global variable of channel type"
    _ -> return ()
  tinfo <- lookupTypeInfo typ
  let locnm = T.namePart $ tiLocType tinfo
      nm = S.stringPart sid
  tid <- freshTid (Just (locnm ++ "_" ++ nm))
  ginit <-
    case typ of
      PointerType _ bt (Just len) -> do
        TypeInfo {tiGlobalLocTag} <- lookupTypeInfo bt
        gloc <- freshArrayGlobals nm sp bt len
        return $ Just $ T.EDot (T.EId tiGlobalLocTag) [gloc]
      _ -> return initval
  extendGlobal sid (GInfo {gtid=tid,
                           gtype=typ,
                           ginit=ginit,
                           gdeclpos=sp})
  return tid

-- like freshArrayLocals - this allocates global cells for each element of a
-- statically-allocated array.
freshArrayGlobals :: String -> S.SPos -> BaseType -> Integer -> CG T.Exp
freshArrayGlobals nmHint gdeclpos bt len = do
  (_,maxInt) <- getCIntRange
  let cellCount =  min (fromIntegral len) (1+maxInt)
  tids <- mapM (\i -> freshTid (Just $ nmHint ++ "_c" ++ show i))
               [0..(cellCount-1)]
  mapM_ (\gtid -> extendGlobal (S.Fixed $ "__anon_glbl_" ++ T.namePart gtid)
                    (GInfo {gtid,gtype=bt,ginit=Nothing,gdeclpos}))
        tids
  addArray bt $ ALGlobal tids
  case tids of
    (tid:_) -> return $ T.EId tid
    []      -> failPos gdeclpos "Unsupported: 0-length array"

-- This generates a fresh name for a function, the types of its arguments, and
-- the function's return type.
freshFunction :: S.Id -> [BaseType] -> BaseType -> CG FInfo
freshFunction sid fargs fret = do
  let nm = S.stringPart sid
  tid <- freshTid (Just nm)
  let finfo = FInfo {ftid=tid,fargs,fret,fdef=False}
  extendFunction sid finfo
  return finfo

-- This records the information that a previously declared function also had a
-- definition.
setFunctionDefined :: S.Id -> S.SPos -> CG ()
setFunctionDefined f sp = do
  fs <- getFunctions
  case M.lookup f fs of
    Nothing -> failPos sp $ "Internal error: setFunctionDefined called on "
                         ++ "undeclared function " ++ show f
    Just finfo -> extendFunction f (finfo {fdef = True})


----------
---------- More state accessors
----------

allGlobals :: CG [(S.Id,GlobInfo)]
allGlobals = M.toList <$> getGlobals

allFunctions :: CG [(S.Id,FInfo)]
allFunctions = M.toList <$> getFunctions

allLocals :: CG [LocalInfo]
allLocals = getLocalAddresses

allArrays :: CG [(BaseType,[ArrayLocs])]
allArrays = M.toList <$> getArrays

allTypeInfos :: CG [TypeInfo]
allTypeInfos = M.elems <$> getTypeInfos

----------
---------- failure functions with locations
----------
-- XXX These should include the actual Decln/Stmt/Exp, except that we don't
-- have a pretty printer for C and the derived output is too big.  Come
-- back and include relevant bit of C in error when we do.

failBase :: BaseType -> String -> CG a
failBase bt err = fail $ err ++ " at :" ++ show (locBaseType bt) ++ "."

failGlob :: GlobInfo -> String -> CG a
failGlob g err = fail $ err ++ " at :" ++ show (gdeclpos g) ++ "."

failPos :: S.SPos -> String -> CG a
failPos sp err = fail $ err ++ " at :" ++ show sp ++ "."

failDecln :: S.Decln -> ErrMsg -> CG a
failDecln d msg = fail $ "Error in translation: " ++ msg ++ ", at "
                      ++ show (S.locDecln d) ++ "."

failStmt :: S.Statement -> ErrMsg -> CG a
failStmt s msg = fail $ "Error in translation: " ++ msg ++ ", at "
                      ++ show (S.locStmt s) ++ "."

failExp :: S.Exp -> ErrMsg -> CG a
failExp e msg = fail $ "Error in translation: " ++ msg ++ ", at "
                     ++ show (S.locExp e) ++ "."

failType :: S.Type -> ErrMsg -> CG a
failType t msg = fail $ "Error in translation: " ++ msg ++ ", at "
                     ++ show (S.locType t) ++ "."

failExternal :: S.ExternalDecln -> ErrMsg -> CG a
failExternal e msg = 
  fail $ "Error in translation: " ++ msg 
      ++ ".\n  In external declaration: " ++ emitExternalDecln e
      ++ ".\n  At location: " ++ show (S.locExternal e) ++ "."
