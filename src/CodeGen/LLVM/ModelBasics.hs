{- |

   Module      :  CodeGen.LLVM.ModelBasics
   Description :  Basic CSP data representations and common definitions
   
   Author      :  Chris Casinghino
   
   This contains the data representations for basic parts of the model (for
   example, Unit, Int and Float).  It also contains some basic csp defintions used in
   other parts of the model (like zero and one).
-}

module CodeGen.LLVM.ModelBasics where

import Language.CSPM.Syntax as T

import CodeGen.LLVM.ModelIdentifiers
import CodeGen.LLVM.CGMonad



-------------------------------------------------
--- Integers

-- representation definition
minIntDef, maxIntDef :: Int -> T.Definition
minIntDef x = T.DVar (T.PId minIntId) $ T.EConst $ T.CInt $ toInteger x
maxIntDef x = T.DVar (T.PId maxIntId) $ T.EConst $ T.CInt $ toInteger x

intDataRep :: T.Definition
intDataRep = 
  T.DDataType (fciRepType intFCInfo)
              [(knownIntCon,[T.ESetFromTo (T.EId minIntId) 
                                          (T.EId maxIntId)]),
               (unknownIntCon,[])]

-- Helpers
unknownInt :: T.Exp
unknownInt = T.EDot (T.EId unknownIntCon) []

knownInt :: Integer -> T.Exp
knownInt i = T.EDot (T.EId knownIntCon) [T.EConst $ T.CInt i]

intZero, intOne :: T.Exp
intZero = knownInt 0
intOne  = knownInt 1


--------------------------------------------------------
--- Booleans

--- XXX do we need this in LLVM verison?

cBoolDataRep :: T.Definition
cBoolDataRep =
  T.DDataType (fciRepType boolFCInfo)
              [(boolTrueCon,[]),
               (boolFalseCon,[]),
               (unknownBoolCon,[])]

unknownBool :: T.Exp
unknownBool = T.EDot (T.EId unknownBoolCon) []

boolFalse :: T.Exp
boolFalse = T.EDot (T.EId boolFalseCon) []

boolTrue :: T.Exp
boolTrue = T.EDot (T.EId boolTrueCon) []

--------------------------------------------------------
--- Floats

cFloatDataRep :: T.Definition
cFloatDataRep =
  T.DDataType (fciRepType floatFCInfo)
              [(unknownFloatCon,[])]

unknownFloat :: T.Exp
unknownFloat = T.EDot (T.EId unknownFloatCon) []

--------------------------------------------------------
--- Unit

unitDataRep :: T.Definition
unitDataRep =
  T.DDataType unitRepId [(unitValCon,[])]

cspUnit :: T.Exp
cspUnit = T.EDot (T.EId unitValCon) []


--------------------------------------------------------
--- Thread IDs

-- The data representation for process IDs.  The MAX should be configurable, but
-- is not currently.
maxTidDef :: T.Definition
maxTidDef = T.DVar (T.PId maxTidId) $ T.EConst $ T.CInt 6

tidDataRep :: T.Definition
tidDataRep =
  T.DDataType tidTypId
              [(tidKnownCon, [T.ESetFromTo (T.EConst (T.CInt 0))
                                           (T.EId maxTidId)]),
               (tidUnknownCon, [])]

tidZero :: T.Exp
tidZero = T.EDot (T.EId tidKnownCon) [T.EConst (T.CInt 0)]

--------------------------------------------------------
--- Mutex IDs

maxMidDef :: T.Definition
maxMidDef = T.DVar (T.PId maxMidId) $ T.EConst $ T.CInt 5

midDataRep :: T.Definition
midDataRep =
  T.DDataType midTypId
              [(midConId, [T.ESetFromTo (T.EConst (T.CInt 0))
                                        (T.EId maxMidId)])]

--------------------------------------------------------
--- Mutexes


-- A mutex is represented essentially as a (Maybe MutexID).  "Nothing" indicates
-- this mutex has not been initialized.

mutDataRep :: T.Definition
mutDataRep = 
  T.DDataType (fciRepType mutexFCInfo)
              [(mutexInitCon,[T.EDot (T.EId midTypId) []]),
               (mutexUnInitCon,[])]

uninitializedMutex :: T.Exp
uninitializedMutex = T.EDot (T.EId mutexUnInitCon) []


--------------------------------------------------------
--- Assorted common CSP idioms

-- used repeatedly
noId :: T.Id
noId = T.Fixed "_"
