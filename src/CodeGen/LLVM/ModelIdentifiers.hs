{- |

   Module      :  CodeGen.LLVM.ModelIdentifiers
   Description :  This module holds the fixed identifiers used by the model
   
   Author      :  Chris Casinghino
   
-}

module CodeGen.LLVM.ModelIdentifiers where

import qualified Language.CSPM.Syntax as T

----------------------------------------------
---- Basic datatype representation identifiers

-- Ints
knownIntCon,unknownIntCon :: T.Id
knownIntCon   = T.Fixed "CIntKnown"
unknownIntCon = T.Fixed "CIntUnknown"

minIntId, maxIntId :: T.Id
minIntId = T.Fixed "minimumCVal"
maxIntId = T.Fixed "maximumCVal"


-- Floats
unknownFloatCon :: T.Id
unknownFloatCon = T.Fixed "CFloatUnknown"

-- Bools
boolTrueCon, boolFalseCon, unknownBoolCon :: T.Id
boolTrueCon    = T.Fixed "CBoolTrue"
boolFalseCon   = T.Fixed "CBoolFalse"
unknownBoolCon = T.Fixed "CBoolUnknown"

-- Mutex IDs
midTypId :: T.Id
midTypId = T.Fixed "MutexID"

midConId :: T.Id
midConId = T.Fixed "M_ID"

maxMidId :: T.Id
maxMidId = T.Fixed "maximumMID"

-- Mutex IDs and Mutexes themselves
mutexInitCon, mutexUnInitCon :: T.Id
mutexInitCon = T.Fixed "Mut"
mutexUnInitCon = T.Fixed "Mut_UNINITIALIZED"


-- Unit
unitRepId :: T.Id
unitRepId = T.Fixed "Unit"

unitValCon :: T.Id
unitValCon = T.Fixed "UnitVal"

--Function pointers
fptrRepId :: T.Id
fptrRepId = T.Fixed "FPtr"

fptrNullCon :: T.Id
fptrNullCon = T.Fixed "FPtr_NULL"

fptrUnknownCon :: T.Id
fptrUnknownCon = T.Fixed "FPtr_UNKNOWN"

fptrErrorName :: T.Id
fptrErrorName = T.Fixed "fptr_deref_ERROR"

----------------------------------------------
--- Identifiers related to thread IDs

tidTypId :: T.Id
tidTypId = T.Fixed "TIDTyp"

tidKnownCon, tidUnknownCon :: T.Id
tidKnownCon = T.Fixed "TID"
tidUnknownCon = T.Fixed "TIDUnknown"

maxTidId :: T.Id
maxTidId = T.Fixed "maximumTID"

----------------------------------------------
---- Datatype conversion identifiers

cIntToBool, cBoolToInt :: T.Id
cIntToBool = T.Fixed "intToBool"
cBoolToInt = T.Fixed "boolToInt"

cIntToFloat, cFloatToInt :: T.Id
cIntToFloat = T.Fixed "intToFloat"
cFloatToInt = T.Fixed "floatToInt"

----------------------------------------------
---- Stack representation and manipulators

stackType :: T.Id
stackType = T.Fixed "Stack"

stackAddrType,stackAddrCon :: T.Id
stackAddrType = T.Fixed "StackAddr"
stackAddrCon  = T.Fixed "SA"

maxStackAddr :: T.Id
maxStackAddr  = T.Fixed "maxStackAddr"

-- read or write from/to a stack variable, or push a new variable
readFromStackId,writeToStackId,pushOnStackId :: T.Id
readFromStackId = T.Fixed "readFromStack"
writeToStackId  = T.Fixed "writeToStack"
pushOnStackId   = T.Fixed "pushOnStack"

-- stack data
stackValType :: T.Id
stackValType = T.Fixed "StackVal"

stackFrameCon :: T.Id
stackFrameCon = T.Fixed "StackFrameBoundary"

-- stack frame manipulation
pushStackFrameId, popStackFrameId :: T.Id
pushStackFrameId = T.Fixed "pushStackFrame"
popStackFrameId  = T.Fixed "popStackFrame"

-- stackErrors
stackOverflowErrorId, stackUnderflowErrorId :: T.Id
stackOverflowErrorId = T.Fixed "stackOverflowError"
stackUnderflowErrorId = T.Fixed "stackUnderflowError"

stackMisprojErrorId :: T.Id
stackMisprojErrorId = T.Fixed "stackMisprojectionError"

----------------------------------------------
---- Top-level memory model identifiers

memoryName, runInMemoryName, hideMemoryName :: T.Id
memoryName = T.Fixed "MEMORY"
runInMemoryName = T.Fixed "runInMemory"
hideMemoryName = T.Fixed "hideMemory"

--getElementPtr errors
gepErrorName :: T.Id
gepErrorName = T.Fixed "gepERROR"

----------------------------------------
-- Runtime names

selectId :: T.Id
selectId = T.Fixed "selectLLVM"


---------------------------
--- Top-level program stuff

runAsMainName :: T.Id
runAsMainName = T.Fixed "runAsMain"

runName :: T.Id
runName = T.Fixed "run"
