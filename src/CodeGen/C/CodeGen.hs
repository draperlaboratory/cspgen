{- |
   Module      :  CodeGen.C.CodeGen
   Description :  CSP code generation
   Copyright   :  Draper Laboratories
   
   Author      :  Chris Casinghino
   
   This is the main module for generating CSP code from a CFG.

-}

module CodeGen.C.CodeGen
    (transGen,
     inFnTy,inUnTy,
     buildMemoryModel, -- XXX temp for warnings
     stubOut,
     transInitializer, uninitializedGlobal, -- for CFG generation
     CspModules (..)
    )
where

import Prelude hiding (init)
--import Data.Char (ord)
import qualified CodeGen.C.Syntax as S -- Source
import qualified CodeGen.C.CFG as S
import Compiler.Hoopl hiding ((<*>))

import qualified Language.CSPM.Syntax as T -- Target

import CodeGen.C.CGMonad

import qualified Data.Map as M
import Data.List (find,foldl',foldl1',tails)
import Control.Monad (when,unless,foldM,zipWithM)
import Data.Maybe (mapMaybe,catMaybes,fromMaybe)

--import CodeGen.C.Pretty (emitId)

-- import System.IO.Unsafe (unsafePerformIO)

-------------------------------------------
-----------  TODO now in stdlib Data.Either
-------------------------------------------

isLeft :: Either a b -> Bool
isLeft (Left _)  = True
isLeft (Right _) = False

-----------
----------- Common failure cases
-----------

failMissingLoc :: Label -> (String -> CG a) -> CG a
failMissingLoc l mfail = mfail $ "Internal error: missing tid for label " ++ show l

lookupLoc :: Label -> M.Map Label T.Id -> (String -> CG T.Id) -> CG T.Id
lookupLoc l m mfail = 
  case M.lookup l m of
    Nothing -> failMissingLoc l mfail
    Just tid -> return tid

-----------
----------- Useful to have a dummy location around
-----------

inFnTy :: BaseType
inFnTy = FunctionType internal

--inIntTy :: BaseType
--inIntTy = IntType internal

inUnTy :: BaseType
inUnTy = UnknownType internal


---------------------------------------------------------------------
----------- Base type hacks
---------------------------------------------------------------------
-- cIntMin, cIntMax :: T.Const
-- cIntMin = T.CInt 0
-- cIntMax = T.CInt 4

cIntZero :: T.Exp
cIntZero = T.EDot (T.EId cIntKnownCon) [T.EConst $ T.CInt 0]

cIntOne :: T.Exp
cIntOne = T.EDot (T.EId cIntKnownCon) [T.EConst (T.CInt 1)]

cIntUnknown :: T.Exp
cIntUnknown = T.EDot (T.EId cIntUnknownCon) []

cFloatUnknown :: T.Exp
cFloatUnknown = T.EDot (T.EId cFloatUnknownCon) []

cBoolUnknown :: T.Exp
cBoolUnknown = T.EDot (T.EId cBoolUnknownCon) []

cBoolFalse :: T.Exp
cBoolFalse = T.EDot (T.EId cBoolFalseCon) []

-- And here we have the actual datatype declarations for our base types.
-- These are used below in the memory model.
minCIntId, maxCIntId :: T.Id
minCIntId = T.Fixed "minimumCVal"
maxCIntId = T.Fixed "maximumCVal"

minCIntDef, maxCIntDef :: Int -> T.Definition
minCIntDef x = T.DVar (T.PId minCIntId) $ T.EConst $ T.CInt $ toInteger x
maxCIntDef x = T.DVar (T.PId maxCIntId) $ T.EConst $ T.CInt $ toInteger x

cIntDataRep :: T.Definition
cIntDataRep = 
  T.DDataType (tiRepType cIntTypeInfo)
              [(cIntKnownCon,[T.ESetFromTo (T.EId minCIntId) 
                                           (T.EId maxCIntId)]),
               (cIntUnknownCon,[])]

cBoolDataRep :: T.Definition
cBoolDataRep =
  T.DDataType (tiRepType cBoolTypeInfo)
              [(cBoolTrueCon,[]),
               (cBoolFalseCon,[]),
               (cBoolUnknownCon,[])]

cFloatDataRep :: T.Definition
cFloatDataRep =
  T.DDataType (tiRepType cFloatTypeInfo) [(cFloatUnknownCon,[])]

cUnitDataRep :: T.Definition
cUnitDataRep =
  T.DDataType (tiRepType unitTypeInfo) [(unitValCon,[])]

cspUnit :: T.Exp
cspUnit = T.EDot (T.EId unitValCon) []

-- The data representation for process IDs.  The MAX should be configurable, but
-- is not currently.
maxPidId :: T.Id
maxPidId = T.Fixed "maximumPID"

maxPidDef :: T.Definition
maxPidDef = T.DVar (T.PId maxPidId) $ T.EConst $ T.CInt 6

pidDataRep :: T.Definition
pidDataRep =
  T.DDataType pidTypId
              [(pidKnownCon, [T.ESetFromTo (T.EConst (T.CInt 0))
                                           (T.EId maxPidId)]),
               (pidUnknownCon, [])]

-- The data representation for Mutexes.  A mutex is represented essentially as a
-- (Maybe MutexID).  "Nothing" indicates this mutex has not been initialized.
midTypId :: T.Id
midTypId = T.Fixed "MutexIDCSP"

midConId :: T.Id
midConId = T.Fixed "MCSP_ID"

maxMidId :: T.Id
maxMidId = T.Fixed "maximumCSPMID"

maxMidDef :: T.Definition
maxMidDef = T.DVar (T.PId maxMidId) $ T.EConst $ T.CInt 5

midDataRep :: T.Definition
midDataRep =
  T.DDataType midTypId
              [(midConId, [T.ESetFromTo (T.EConst (T.CInt 0))
                                        (T.EId maxMidId)])]

mutDataRep :: T.Definition
mutDataRep = 
  T.DDataType (tiRepType mutexTypeInfo)
              [(mutexInitCon,[T.EDot (T.EId midTypId) []]),
               (mutexUnInitCon,[])]

uninitializedMutex :: T.Exp
uninitializedMutex = T.EDot (T.EId mutexUnInitCon) []



--------------------------------------------------------------------
-----------------  Read/Write process builders for global memory
--------------------------------------------------------------------

-- gread c pid x y   builds   c!pid!x?y
gread :: T.Id -> T.Exp -> T.Exp -> T.Id -> T.Exp -> T.Exp
gread channel pid location binder =
  T.EPrefix
    (T.EId channel)
    [T.CFOutput pid,
     T.CFOutput location,
     T.CFInput $ T.PId binder]

-- gwrite wchan pid x v   builds   wchan!pid!x!v
gwrite :: T.Id -> T.Exp -> T.Id -> T.Exp -> T.Exp -> T.Exp
gwrite wchan pid location binder =
  T.EPrefix
    (T.EId wchan)
    [T.CFOutput pid,
     T.CFOutput $ T.EId location,
     T.CFOutput binder]

--------------------------------------------------------------------
---------------- Basic csp builders
--------------------------------------------------------------------


-- "returnExp e" builds (\(st,pid,k) . k (st,pid,e)).
returnExp :: T.Exp -> CG T.Exp
returnExp e =
  expOuterLambda $ \st pid k ->
    return $ T.EApp (T.EId k) [T.EId st,T.EId pid,e]

-- Expressions are translated as CSPm functions of type
--     (VarMap,PID,(VarMap,PID,a) -> Proc)) -> Proc
--
-- (where 'a' is the type of the expression).
--
-- Thus, the translations of statements often begin with the pattern
--    \(state,pid,k) @ .....
--
-- This just constructs that lambda, given a way to define the body from the
-- binder names.  The extra 'a' return parmeter is there in case we need to
-- return any state computed with these variables in scope.
expOuterLambdaState :: (T.Id -> T.Id -> T.Id -> CG (T.Exp,a)) -> CG (T.Exp,a)
expOuterLambdaState body = do
  stBnd <- freshLocalNew "StBndr"
  pidBnd <- freshLocalNew "pidBndr"
  kBnd <- freshLocalNew "eContBndr"
  (te,st) <- body stBnd pidBnd kBnd
  return (T.ELambda [T.PId stBnd, T.PId pidBnd, T.PId kBnd] te,st)

expOuterLambda :: (T.Id -> T.Id -> T.Id -> CG T.Exp) -> CG T.Exp
expOuterLambda body = 
  fst <$> expOuterLambdaState (\a b c -> (,()) <$> body a b c)

-- Expressions are translated as CSPm functions of type
--     (VarMap,PID,(VarMap,PID,a) -> Proc)) -> Proc
--
-- (where 'a' is the type of the expression).
--
-- Often we need to explicitly build the inner lambda that the translation of
-- an exp will be applied to.  That is, the (VarMap,PID,a) -> Proc.
--
-- This constructs that lambda, given a way to define the body from the binder
-- names.  Similar to expOuterLambda, but separated for better variable names
-- and because the (CSPm) types are different.
expInnerLambda :: (T.Id -> T.Id -> T.Id -> CG T.Exp) -> CG T.Exp
expInnerLambda body =
  fst <$> expInnerLambdaState (\a b c -> (,()) <$> body a b c)

expInnerLambdaState :: (T.Id -> T.Id -> T.Id -> CG (T.Exp,a)) -> CG (T.Exp,a)
expInnerLambdaState body = do
  stBnd <- freshLocalNew "iStBndr"
  pidBnd <- freshLocalNew "iPidBndr"
  evBnd <- freshLocalNew "iValBndr"
  (te,st) <- body stBnd pidBnd evBnd
  return (T.ELambda [T.PId stBnd, T.PId pidBnd, T.PId evBnd] te, st)

-- Statements are translated as CSPm functions of type
--     (VarMap,PID,(VarMap,PID,a) -> Proc)) -> Proc
--
-- Thus, the translations of statements often begin with the patternL
--    \(state,pid,k) @ .....
--
-- This just constructs that lambda, given a way to define the body from the
-- binder names.
--
-- (Right now this is identical to expOuterLambda, but they might be different when
-- we keep track of function type information).
stmtLambda :: (T.Id -> T.Id -> T.Id -> CG T.Exp) -> CG T.Exp
stmtLambda body = do
  stBnd <- freshLocalNew "sStBndr"
  pidBnd <- freshLocalNew "sPidBndr"
  kBnd  <- freshLocalNew "sContBndr"
  T.ELambda [T.PId stBnd, T.PId pidBnd, T.PId kBnd] <$> body stBnd pidBnd kBnd

-- Check if a var is present in a CSPm state map
cspMapMember :: T.Id -> T.Id -> T.Exp
cspMapMember st loc = 
    T.EApp (T.EId (T.Fixed "mapMember"))
           [T.EId st, T.EId loc]

-- Read from the CSPm state map.
cspMapLookup :: T.Id -> T.Id -> T.Exp
cspMapLookup st loc = 
    T.EApp (T.EId (T.Fixed "mapLookup"))
           [T.EId st, T.EId loc]

-- Write to the CSPm state map.
cspMapUpdate :: T.Exp -> T.Id -> T.Exp -> T.Exp
cspMapUpdate st loc val =
    T.EApp (T.EId (T.Fixed "mapUpdate"))
           [st,T.EId loc,val]

-----------------------------------------
-----------------------------------------

-- Helper code that should go elsewhere, once CG monad has been
-- generalized to not refer specifically to C and CSP

-- calculates the variables mentioned in a pattern.
patternVars :: T.Pat -> [T.Id]
patternVars (T.PId v)           = [v]
patternVars (T.PConcat p1 p2)   = (patternVars p1) ++ (patternVars p2)
patternVars (T.PDot p1 p2)      = (patternVars p1) ++ (concatMap patternVars p2)
patternVars (T.PDouble p1 p2)   = (patternVars p1) ++ (patternVars p2)
patternVars (T.PList ps)        = concatMap patternVars ps
patternVars (T.PConst _)        = []
patternVars T.PEmptySet         = []
patternVars (T.PSingletonSet p) = patternVars p
patternVars (T.PTuple ps)       = concatMap patternVars ps
patternVars T.PWildCard         = []

-- calculates the variables defined by a definition
definedVars :: T.Definition -> [T.Id]
definedVars (T.DVar p _)       = patternVars p
definedVars (T.DFun nm _)      = [nm]
definedVars (T.DAnnot _ _)     = []
definedVars (T.DDataType _ _)  = []
definedVars (T.DChan nms _)    = nms
definedVars (T.DInclude _)     = []
definedVars (T.DExternal x)    = [x]
definedVars (T.DTransparent x) = [x]
definedVars (T.DSubType f _)   = [f]
definedVars (T.DAssert _ _)    = []

-- (subst a x b) computes the substitution of a for x in b.  That is, [a/x]b.
-- We assume variable capture can not happen, because of the fresh name
-- generation used by the monad.  (This substantially improves the performance
-- of subst over earlier versions which considered variable capture)
subst :: T.Exp -> T.Id -> T.Exp -> T.Exp
subst a x b = sub b
  where
    sub :: T.Exp -> T.Exp
    sub (T.EId v)                = if x == v then a else (T.EId v)
    sub (T.ELambda ys e) = T.ELambda ys $ 
      if x `elem` concatMap patternVars ys then e else sub e
    sub (T.EApp e1 es)        = T.EApp (sub e1) (map sub es)
    sub (T.ELet defs e2) = 
      if x `elem` concatMap definedVars defs
         then T.ELet defs e2
         else T.ELet (map subDef defs) (sub e2)
    sub (T.EIfThenElse e1 e2 e3) = T.EIfThenElse (sub e1) (sub e2) (sub e3)
    sub (T.EUOp uop e)        = T.EUOp uop (sub e)
    sub (T.EBinOp e1 bop e2)  = T.EBinOp (sub e1) bop (sub e2)
    sub (T.EDot (T.EId c) es)        = T.EDot (T.EId c) (map sub es)
    sub (T.EConst c)          = T.EConst c
    sub (T.EError err)        = T.EError err

    sub (T.EDot e1 e2)        = T.EDot (sub e1) (map sub e2)
    sub (T.EExtChoice e1 e2)  = T.EExtChoice (sub e1) (sub e2)
    sub (T.EGuarded e1 e2)    = T.EGuarded (sub e1) (sub e2)
    sub (T.EHide e1 e2)       = T.EHide (sub e1) (sub e2)
    sub (T.EIntChoice e1 e2)  = T.EIntChoice (sub e1) (sub e2)
    sub (T.EPrefix e1 cs e2)  =
      let (cs',e2') = subCommFields cs e2 in
      T.EPrefix (sub e1) cs' e2'
    sub (T.EProject e1 e2)    = T.EProject (sub e1) (sub e2)
    sub (T.ERename e1 es)     = 
      T.ERename (sub e1) (map (\(el,er) -> (sub el,sub er)) es)

    sub (T.EAlphaParallel e1 e2 e3 e4) =
      T.EAlphaParallel (sub e1) (sub e2) (sub e3) (sub e4)
    sub (T.EGenParallel e1 e2 e3) = T.EGenParallel (sub e1) (sub e2) (sub e3)
    sub (T.EInterleave e1 e2) = T.EInterleave (sub e1) (sub e2)

    sub (T.EException e1 e2 e3) = T.EException (sub e1) (sub e2) (sub e3)
    sub (T.EInterrupt e1 e2) = T.EInterrupt (sub e1) (sub e2)
    sub (T.ESeq e1 e2) = T.ESeq (sub e1) (sub e2)
    sub (T.ELinkedParallel e1 eps e2) = 
      T.ELinkedParallel e1 (map (\(el,er) -> (sub el, sub er)) eps) e2
    sub (T.ETimeout e1 e2) = T.ETimeout (sub e1) (sub e2)
    sub (T.ESyncExtChoice e1 e2 e3) =
      T.ESyncExtChoice (sub e1) (sub e2) (sub e3)
    sub (T.ESyncInterrupt e1 e2 e3) =
      T.ESyncInterrupt (sub e1) (sub e2) (sub e3)

    -- In the expressions with comprehensions, we don't check for capture at
    -- all.  sub assumes all names are unique, so this is allowed.
    sub (T.ERepAlphaParallel css e1 e2) =
      T.ERepAlphaParallel (map subCompStmt css) (sub e1) (sub e2)
    sub (T.ERepExtChoice css e) =
      T.ERepExtChoice (map subCompStmt css) (sub e)
    sub (T.ERepGenParallel e1 css e2) =
      T.ERepGenParallel (sub e1) (map subCompStmt css) (sub e2)
    sub (T.ERepInterleave css e) =
      T.ERepInterleave (map subCompStmt css) (sub e)
    sub (T.ERepIntChoice css e) =
      T.ERepIntChoice (map subCompStmt css) (sub e)
    sub (T.ERepLinkedParallel eps css e) =
      T.ERepLinkedParallel eps' (map subCompStmt css) (sub e)
      where
        eps' = map (\(el,er) -> (sub el,sub er)) eps
    sub (T.ERepSeq css e) = T.ERepSeq (map subCompStmt css) (sub e)
    sub (T.ERepSyncExtChoice e1 css e2) =
      T.ERepSyncExtChoice (sub e1) (map subCompStmt css) (sub e2)

    sub (T.EList es)          = T.EList (map sub es)
    sub (T.EListComp es css)  = T.EListComp (map sub es) (map subCompStmt css)
    sub (T.EListFrom e)       = T.EListFrom (sub e)
    sub (T.EListFromComp e css) =
      T.EListFromComp (sub e) (map subCompStmt css)
    sub (T.EListFromTo e1 e2) = T.EListFromTo (sub e1) (sub e2)
    sub (T.EListFromToComp e1 e2 css) =
      T.EListFromToComp (sub e1) (sub e2) (map subCompStmt css)
    sub (T.EListConcat e1 e2) = T.EListConcat (sub e1) (sub e2)
    sub (T.EListLength e)     = T.EListLength (sub e)

    sub (T.ETuple es)         = T.ETuple (map sub es)
                                
    sub (T.ESet es)           = T.ESet (map sub es)
    sub (T.ESetComp es css)   = T.ESetComp (map sub es) (map subCompStmt css)
    sub (T.ESetFrom e)        = T.ESetFrom (sub e)
    sub (T.ESetFromComp e css) = T.ESetFromComp (sub e) (map subCompStmt css)
    sub (T.ESetFromTo e1 e2)  = T.ESetFromTo (sub e1) (sub e2)
    sub (T.ESetFromToComp e1 e2 css) =
      T.ESetFromToComp (sub e1) (sub e2) (map subCompStmt css)
    sub T.ESetInt             = T.ESetInt
    sub T.ESetBool            = T.ESetBool
    
    sub (T.EEnumSet es)         = T.EEnumSet $ map sub es
    sub (T.EEnumSetComp es css) =
      T.EEnumSetComp (map sub es) (map subCompStmt css)

    sub (T.EMap eps)          = T.EMap (map (\(e1,e2) -> (sub e1, sub e2)) eps)

    -- again: not checking for capture in the patterns within comprehensions.
    -- Incorrect generally, but allowed due to our unique names requirement.
    subCompStmt :: T.CompStmt -> T.CompStmt
    subCompStmt (T.CSGen p e) = T.CSGen p (sub e)
    subCompStmt (T.CSPred e)  = T.CSPred e

    -- not checking for capture
    subDef :: T.Definition -> T.Definition
    subDef (T.DVar p e) = T.DVar p (sub e)
    subDef (T.DFun nm clauses) = T.DFun nm (map (\(ps,e) -> (ps,sub e)) clauses)
    subDef d = d

    -- We're not checking for capture.  If we were, this one would be a little
    -- tricky, since if we bind over the var in one of the commfields we should
    -- not perform the substitution in the subsequent fields or the expression.
    subCommFields :: [T.CommField] -> T.Exp -> ([T.CommField],T.Exp)
    subCommFields cs e = (map subCF cs, sub e)
      where
        subCF (T.CFPlain e1) = T.CFPlain $ sub e1
        subCF (T.CFInput p) = T.CFInput p
        subCF (T.CFOutput e1) = T.CFOutput $ sub e1
        subCF (T.CFNDInput p) = T.CFNDInput p

-- squash eliminates "administrative redexes" that are introduced
-- unnecessarily by the CPS translation.  In particular, it performs
-- the following local reduction:
--
-- (\x1,..,xn . a) (v1,..,vn)     --->   [vn/xn]...[v1/x1]a
--
-- When v1...vn are values.
--
-- Note again that we IGNORE CAPTURE here, relying on the producer of the CSP
-- AST to not reuse names.

squash :: T.Exp -> CG T.Exp
squash (T.EApp (T.ELambda bnds a) args) = do
  args' <- mapM squash args
  case allVars bnds of
    Just vs | length vs == length args' && all valish args ->
      beta vs args' a
    _ -> do
      a' <- squash a
      return $ T.EApp (T.ELambda bnds a') args'
  where
    allVars :: [T.Pat] -> Maybe [T.Id]
    allVars [] = Just []
    allVars (T.PId v : es) = fmap (v:) $ allVars es
    allVars _  = Nothing

    -- XXX should expand this with more val forms, but I don't generate them and
    -- am lazy
    valish (T.EId _)       = True
    valish (T.ELambda _ _) = True
    valish (T.EConst _)    = True
    valish (T.EDot e es)   = all valish (e:es)
    valish (T.ETuple es)   = all valish es
    valish _               = False

    beta :: [T.Id] -> [T.Exp] -> T.Exp -> CG T.Exp
    beta [] [] e = squash e
    beta (x:xs) (v:vs) e =
      let e' = subst v x e in
        beta xs vs e'
    beta _ _ _ = fail "Internal Error: beta encountered unequal length lists."
squash (T.EId x)             = return $ T.EId x
squash (T.ELambda bvs e)     = T.ELambda bvs <$> squash e
squash (T.EApp e1 es)        = T.EApp <$> squash e1 <*> mapM squash es
squash (T.ELet defs e2)      = T.ELet <$> mapM squashDef defs <*> squash e2
squash (T.EIfThenElse e1 e2 e3) = 
    T.EIfThenElse <$> squash e1 <*> squash e2 <*> squash e3
squash (T.EUOp u e)          = T.EUOp u <$> squash e
squash (T.EBinOp e1 b e2)    = T.EBinOp <$> squash e1 <*> return b <*> squash e2
squash (T.EDot (T.EId bv) es)       = T.EDot (T.EId bv) <$> mapM squash es
squash (T.EConst c)          = return $ T.EConst c
squash (T.EError s)          = return $ T.EError s

squash (T.EDot e ces)        = T.EDot <$> squash e <*> mapM squash ces
squash (T.EExtChoice e1 e2)  = T.EExtChoice <$> squash e1 <*> squash e2
squash (T.EGuarded e1 e2)    = T.EGuarded <$> squash e1 <*> squash e2
squash (T.EHide e1 e2)       = T.EHide <$> squash e1 <*> squash e2
squash (T.EIntChoice e1 e2)  = T.EIntChoice <$> squash e1 <*> squash e2
squash (T.EPrefix e1 cs e2)  = 
  T.EPrefix <$> squash e1 <*> mapM squashCF cs <*> squash e2
  where
    squashCF :: T.CommField -> CG T.CommField
    squashCF (T.CFPlain e)   = T.CFPlain <$> squash e
    squashCF (T.CFInput p)   = return $ T.CFInput p
    squashCF (T.CFOutput e)  = T.CFOutput <$> squash e
    squashCF (T.CFNDInput p) = return $ T.CFNDInput p
squash (T.EProject e1 e2)    = T.EProject <$> squash e1 <*> squash e2
squash (T.ERename e1 eps)    = 
    T.ERename <$> squash e1 
              <*> mapM (\(el,er) -> (,) <$> squash el <*> squash er) eps

squash (T.EAlphaParallel e1 e2 e3 e4) =
  T.EAlphaParallel <$> squash e1 <*> squash e2
                   <*> squash e3 <*> squash e4
squash (T.EGenParallel e1 e2 e3) =
  T.EGenParallel <$> squash e1 <*> squash e2 <*> squash e3
squash (T.EInterleave e1 e2) = T.EInterleave <$> squash e1 <*> squash e2

squash (T.EException e1 e2 e3) =
  T.EException <$> squash e1 <*> squash e2 <*> squash e3
squash (T.EInterrupt e1 e2) = T.EInterrupt <$> squash e1 <*> squash e2
squash (T.ESeq e1 e2)       = T.ESeq <$> squash e1 <*> squash e2
squash (T.ELinkedParallel e1 es e2) =
  T.ELinkedParallel <$> squash e1
                    <*> mapM (\(el,er) -> (,) <$> squash el <*> squash er) es
                    <*> squash e2
squash (T.ETimeout e1 e2)   = T.ETimeout <$> squash e1 <*> squash e2
squash (T.ESyncExtChoice e1 e2 e3) =
  T.ESyncExtChoice <$> squash e1 <*> squash e2 <*> squash e3
squash (T.ESyncInterrupt e1 e2 e3) =
  T.ESyncInterrupt <$> squash e1 <*> squash e2 <*> squash e3

squash (T.ERepAlphaParallel css e1 e2) =
  T.ERepAlphaParallel <$> mapM squashCompStmt css
                      <*> squash e1 <*> squash e2
squash (T.ERepExtChoice css e) =
  T.ERepExtChoice <$> mapM squashCompStmt css
                  <*> squash e
squash (T.ERepGenParallel e1 css e2) =
  T.ERepGenParallel <$> squash e1
                    <*> mapM squashCompStmt css
                    <*> squash e2
squash (T.ERepInterleave css e) =
  T.ERepInterleave <$> mapM squashCompStmt css
                   <*> squash e
squash (T.ERepIntChoice css e) =
  T.ERepIntChoice <$> mapM squashCompStmt css
                  <*> squash e
squash (T.ERepLinkedParallel eps css e) =
  T.ERepLinkedParallel <$> mapM (\(el,er) -> (,) <$> squash el <*> squash er) eps
                       <*> mapM squashCompStmt css
                       <*> squash e
squash (T.ERepSeq css e) =
  T.ERepSeq <$> mapM squashCompStmt css <*> squash e
squash (T.ERepSyncExtChoice e1 css e2) =
  T.ERepSyncExtChoice <$> squash e1
                      <*> mapM squashCompStmt css
                      <*> squash e2

squash (T.EList es)          = T.EList <$> mapM squash es
squash (T.EListComp es css)  = T.EListComp <$> mapM squash es
                                           <*> mapM squashCompStmt css
squash (T.EListFrom e)       = T.EListFrom <$> squash e
squash (T.EListFromComp e css) =
  T.EListFromComp <$> squash e <*> mapM squashCompStmt css
squash (T.EListFromTo e1 e2) = T.EListFromTo <$> squash e1 <*> squash e2
squash (T.EListFromToComp e1 e2 css) =
  T.EListFromToComp <$> squash e1 <*> squash e2
                    <*> mapM squashCompStmt css
squash (T.EListConcat e1 e2) = T.EListConcat <$> squash e1 <*> squash e2
squash (T.EListLength e)     = T.EListLength <$> squash e

squash (T.ETuple es)         = T.ETuple <$> mapM squash es

squash (T.ESet es)           = T.ESet <$> mapM squash es
squash (T.ESetComp es css)   = T.ESetComp <$> mapM squash es
                                          <*> mapM squashCompStmt css
squash (T.ESetFrom e)        = T.ESetFrom <$> squash e
squash (T.ESetFromComp e css) =
  T.ESetFromComp <$> squash e <*> mapM squashCompStmt css
squash (T.ESetFromTo e1 e2) = T.ESetFromTo <$> squash e1 <*> squash e2
squash (T.ESetFromToComp e1 e2 css) =
  T.ESetFromToComp <$> squash e1 <*> squash e2
                   <*> mapM squashCompStmt css
squash T.ESetInt    = return T.ESetInt
squash T.ESetBool   = return T.ESetBool

squash (T.EEnumSet es) = T.EEnumSet <$> mapM squash es
squash (T.EEnumSetComp es css) = 
  T.EEnumSetComp <$> mapM squash es <*> mapM squashCompStmt css

squash (T.EMap eps)          =
    T.EMap <$> mapM (\(e1,e2) -> (,) <$> squash e1 <*> squash e2) eps


--Ignoring shadowing
squashCompStmt :: T.CompStmt -> CG T.CompStmt
squashCompStmt (T.CSGen p e) = T.CSGen p <$> squash e
squashCompStmt (T.CSPred e)  = T.CSPred <$> squash e


squashDef :: T.Definition -> CG T.Definition
squashDef (T.DVar nm e) = T.DVar nm <$> squash e
squashDef (T.DFun nm clauses) =
  T.DFun nm <$> mapM (\(ps,e) -> (ps,) <$> squash e) clauses
squashDef d = return d


-----------------------------------------
-----------------------------------------
-- helper functions for struct accesses


-- "traverseChain bi [x,y,z]"  Checks if k.x.y.z is a valid field
-- access for a variable k of type bi, and returns the appropriate
-- reader channel if so.
traverseDirSelChain :: [FieldInfo] -> [String] -> Maybe FieldInfo
traverseDirSelChain _ [] = Nothing   -- should never happen.
traverseDirSelChain flds (fn:fns) =
    case find (\f -> fn == fiSourceName f) flds of
      Just fi ->
        if null fns 
          then Just fi
          else traverseDirSelChain (fiSubfields fi) fns
      Nothing -> Nothing

-----------------------------------------
-----------------------------------------

-- buildApp f [e1...en] st pid k
-- builds:   |e1| (st,pid,\(st1,pid1,ev1) @ 
-- -           |e2| (st1,pid1,\(st2,pid2,ev2) @ ...
-- -              |en| (stn-1,pidn-1,\(stn,pidn,evn) @ f (ev1,...,evn,stn,pidn,k)))
--
-- buildApp also checks at each step that the argument has the appropriate type,
-- unless we don't know the type of the function's arguments (indicated by
-- "UnknownType").
-- 
-- TODO can this be consolidated with transStmts?
buildApp :: T.Exp -> [(BaseType,S.Exp)] -> T.Exp -> T.Exp -> T.Exp -> CG T.Exp  -- need foldrM?
buildApp f args outerst outerpid k = buildApp' args [] outerst outerpid
  where
    buildApp' [] argAcc st pid = do
      return $ T.EApp f $ map T.EId (reverse argAcc) ++ [st,pid,k]
    buildApp' ((t1,e1) : es) argAcc st pid = do
      (te1,t1') <- transExp e1
      case t1 of
        UnknownType _ -> return ()
        _ -> unless (t1 == t1') $ failExp e1 $
                  "Function argument has type " ++ ppBaseType t1'
               ++ " but an argument of type " ++ ppBaseType t1
               ++ " was expected"
      innerLam <- 
        expInnerLambda $ \stBnd pidBnd evBnd -> 
          buildApp' es (evBnd:argAcc) (T.EId stBnd) (T.EId pidBnd)
      return $ T.EApp te1 [st,pid,innerLam]

-- unlike other generated Exps, these do not expect a continuation.
-- They are just constants, so it's not needed.
transConst :: S.Const -> S.SPos -> CG (T.Exp,BaseType)
transConst cnst sp =
  case cnst of
    (S.CharConst  _)   -> do
      addWarning "Character constant" "Warning: Character constants are all represented as unknown ints"
      return $ (cIntUnknown, cIntBaseType)
    (S.StringConst  _) -> do 
      addWarning "String literal" "Warning: String literals are all represented as unknown strings" 
      return (T.EDot (T.EId $ tiUnknownLoc cIntTypeInfo) [],
              PointerType sp cIntBaseType Nothing)
    (S.FloatConst _)   -> return $ (cFloatUnknown,cFloatBaseType)
    (S.IntConst   i)   -> return $
       (if i < 0 then cIntUnknown
           else if i > 4 then cIntUnknown
                   else T.EDot (T.EId cIntKnownCon) [T.EConst $ T.CInt i],
        cIntBaseType)

-- transFunctionescriptor translates the expression being applied in a
-- function call.  According to the K&R any expression whose type is "a
-- pointer to a function" may be used here.  The common case of a function
-- itself is a kind of special case.
--
-- It's probably the case that we need to eventually handle a wide variety of
-- function descriptors, like function pointers, but for now we just demand a
-- function identifier.  When we generalize, the type of this function will
-- probably need to be generalized too.
transFunctionDescriptor :: S.Exp -> CG FInfo
transFunctionDescriptor e@(S.IdExp sid@(S.Id nm _ _) _) = do
  mf <- lookupFunction sid
  case mf of
    Just f  -> return f
    Nothing -> failExp e $ "Attempt to call unknown function " ++ nm
transFunctionDescriptor e = 
  failExp e "Unsupported: anything other than a variable being used as a function"


-- transExp translates an expression from C to CSP.
--
-- transExp returns a CSP function, since we're doing things in CPS.  Suppose
-- the input expression e has some type t and let |t| be the "csp version" of
-- that type.  Then e's translation will have type:
--
--     (VarMap,PID,(VarMap,PID,|t|) -> Proc) -> Proc
--
-- That is, e's translation is a function which takes in three arguments:
-- 
-- - The first argument, of type VarMap, tells us the current state of
--   any local variables when we translate this expression.
--
-- - The second arugment, of type PID, tells us the process id of the process
--   that is evaluating this expression.  This is needed to support mutual
--   exclusion.
--
-- - The third argument, of type "(VarMap,PID,|t|) -> Proc", tells us what to do
--   with the result of this expresion.  We will pass it an updated VarMap (in
--   case this expression modifies any local state) and the PID along with the
--   value of this expression.
--
-- transExp also attempts to compute the type of the expression it just
-- translated.  This information is needed, e.g., in the translation of binary
-- operators, since arithmetic operators mean different things for different
-- types of operands.
transExp :: S.Exp -> CG (T.Exp,BaseType)
transExp te@(S.IdExp sid sp)    = do
  -- we handle function pointers here as a very special case.
  mf <- lookupFunction sid
  case mf of
    Just finfo -> (,FunctionType sp) <$> returnExp (T.EId (ftid finfo))
    Nothing -> readFromLValue te
transExp (S.ConstExp c sp)     = do (tc,typ) <- transConst c sp
                                    (,typ) <$> returnExp tc
transExp se@(S.CommaExp ces _) =
--    e1,e2,...,en   
--  -->    
--    \st1,pid1,k @ [e1] (st1,pid1,
--        \st2,pid2,_ @ [e2] (st2,pid2
--           ...
--             \stn,pidn,_  @ [en] (stn,pidnk)
  expOuterLambdaState $ \st1 pid1 k -> transExps (T.EId st1) (T.EId pid1) (T.EId k) ces
  where
    -- transExps st k [s1,s2,s3] recursively builds the
    --             [s1] (st,pid,\(st',pid',_) . 
    --                [s2] (st',pid',\(st'',pid'',_) .
    --                   [s3] (st'',pid'', k)))
    -- part of what we saw above
    transExps :: T.Exp -> T.Exp -> T.Exp -> [S.Exp] -> CG (T.Exp,BaseType)
    transExps _  _    _      []  = failExp se "Unsupported: empty comma expression"
    transExps st pid outerk [e] = do
      (te,ty) <- transExp e
      return $ (T.EApp te [st, pid, outerk],ty)
    transExps st pid outerk (e : es) = do
      (te,_) <- transExp e
      (innerk,ty) <- expInnerLambdaState $ \st' pid' _ -> 
         transExps (T.EId st') (T.EId pid') outerk es
      return $ (T.EApp te [st,pid,innerk],ty)

transExp se@(S.Subscript _ _ _) = readFromLValue se
    
transExp (S.AssignExp S.Assign lv rv _) = do
  -- \(st,pid,k) @ [rv] (st,pid,
  --    \(st',pid',rvBnd) @ |lv| (st',pid',
  --       \(st'',pid'',lvloc) -> writer (st'',pid'',lvloc,typeConvert rvBnd,k))))
  -- 
  -- Here, |lv| is the expression computed by transLValue which is meant to
  -- compute the location corresponding to lv, and "writer" is the name of the
  -- function which writes to locations of the appropriate type (also computed
  -- by transLValue)
  --
  -- Note that assignments are expressions returning the value assigned.  So
  -- "k" here expected to be applied to both the updated state map and the
  -- value of rv.  On the other hand, "writer" expects to be passed a (StateMap -> Proc).
  -- So we pass it k, partially applied to rvBnd)
  -- 
  -- In C, implicit type conversions are allowed at assignments.  We don't support
  -- all the conversions C does, but a few are handled by implicitConvert
  expOuterLambdaState $ \st pid k -> do
    (trv,rvTyp) <- transExp rv
    (innerL,lvTyp) <- expInnerLambdaState $ \st' pid' rvBnd -> do
      (locComp,lvTyp,_,writer) <- transLValue lv
      rvBndTyped <- implicitConvert (S.locExp rv) (T.EId rvBnd) rvTyp lvTyp
      innerL' <- expInnerLambda $ \st'' pid'' lvloc ->
        return $ 
          T.EApp writer
             [T.EId st'',T.EId pid'',T.EId lvloc,rvBndTyped,
              T.EId k]
      return (T.EApp locComp [T.EId st',T.EId pid',innerL'],lvTyp)
    return (T.EApp trv [T.EId st,T.EId pid,innerL],lvTyp)
transExp sa@(S.AssignExp _ _ _ _)  =
  failExp sa "Modifying assignment operators (like +=) are not supported"
transExp sa@(S.FunCall f args _)   =
  -- Suppose args is [e1, ..., en] and the names of f's args are [x1,...,xn].
  -- Let |e| be (transExp e).  This builds:
  --
  --    \(st,pid,k). |e1| (st,\(st1,pid1,ev1). ... |en| (stn-1, pidn-1,
  --                             \(stn,pidn,evn). |f| (ev1,...evn,stn,pidn,k))))
  --
  -- Recall that the translation of a function takes two extra arguments: 
  -- 
  --   - st, which is the current local variable state (necessary since the
  --     address of a local might get passed into the function.
  --
  --   - k, a continuation that gets applied to the result of the function and
  --     an updated state (in case the function modifies anything via pointers
  --     to local data that were passed in).
  --
  -- In an effort to provide good error messages to the user, we typecheck the
  -- function's arguments against the function's prototype.  This function
  -- explicitly checks the number of arguments, and it calls buildApp which
  -- checks their types.  XXX In a few unfortunate situations (particularly the
  -- "externals" file) we don't have complete prototypes and therefore can't
  -- provide good errors in buildApp.
  expOuterLambdaState $ \st pid k -> do
    FInfo {ftid,fret,fargs} <- transFunctionDescriptor f
    when (length args /= length fargs) $ failExp sa $
         "Function is applied to " ++ show (length args) ++ " arguments, but "
      ++ "its prototype has " ++ show (length fargs) ++ " arguments"
    let typedArgs = zip fargs args
    (,fret) <$> buildApp (T.EId ftid) typedArgs (T.EId st) (T.EId pid) (T.EId k)
    
transExp te@(S.CompSel _ _ _ _) = readFromLValue te
transExp se@(S.Unary u e _) =
  -- XXX factor out this continuation pattern
  case u of
    S.Address -> 
      -- Idea: &e is only valid when e is an lvalue.
      --
      --    [[ &x ]] = \(st,pid,k) . |x| (st,pid,\(st',pid',xlocval) . k (st',pid',locval))
      --
      -- Here, |x| is the location computed by transLValue.  You get it by
      -- just looking up x and slapping on the appropriate local or global
      -- tag.
      --
      -- XXX WRONG FOR STRUCTS
      expOuterLambdaState $ \st pid k -> do
        (loc,btyp,_,_) <- transLValue e
        innerL <- expInnerLambda $ \st' pid' xlocval ->
          return $ T.EApp (T.EId k) [T.EId st',T.EId pid',T.EId xlocval]
        return $ (T.EApp loc [T.EId st,T.EId pid,innerL],
                  PointerType internal btyp Nothing)
    S.Indirection -> readFromLValue se
    S.UnaryPlus -> do
      (te,btyp) <- transExp e
      case btyp of
        IntType _   -> return (te,btyp)
        BoolType _  -> return (te,btyp)
        FloatType _ -> return (te,btyp)
        t -> failExp se $ "Unary plus unsupported on data of type " ++ ppBaseType t
    S.UnaryMinus -> 
      -- \ (st,pid,k) @ [e] (st,pid,\(st',pid',ev) @ k (st',pid',-ev))
      expOuterLambdaState $ \st pid k -> do
        (et,btyp) <- transExp e
        negation <-
          case btyp of
            IntType _   -> return $ T.Fixed "negate"
            BoolType _  -> return $ T.Fixed "negateBool"
            FloatType _ -> return $ T.Fixed "negateFloat"
            t -> failExp se $ "Unsupported: unary negation on data of type " 
                           ++ ppBaseType t
        innerLambda <- expInnerLambda $ \st' pid' ev ->
          let body = T.EApp (T.EId negation) [T.EId ev] in
          return $ T.EApp (T.EId k) [T.EId st',T.EId pid',body]
        return (T.EApp et [T.EId st, T.EId pid, innerLambda],btyp)
    S.BitwiseNot ->
      expOuterLambdaState $ \st pid k -> do
        (et,btyp) <- transExp e
        negation <-
          case btyp of
            IntType _ -> return $ T.EId $ T.Fixed "bwNot"
            _ -> failExp se $ "Unsupported: bitwise negation on data of type "
                           ++ ppBaseType btyp
        innerLambda <- expInnerLambda $ \st' pid' ev ->
          return $ T.EApp (T.EId k) 
                     [T.EId st', T.EId pid', T.EApp negation [T.EId ev]]
        return (T.EApp et [T.EId st, T.EId pid, innerLambda],btyp)
    S.LogicalNot ->
      -- \(st,pid,k) @ [e] (\(st',pid',ev) @ k (st',pid',not ev))
      expOuterLambdaState $ \st pid k -> do
        (et,btyp) <- transExp e
        lnot <- 
          case btyp of
            IntType _  -> return $ T.Fixed "lnot"
            BoolType _ -> return $ T.Fixed "lnotBool"
            t -> failExp se $ "Unsupported: logical \"not\" on data of type "
                           ++ ppBaseType t
        innerLambda <- expInnerLambda $ \st' pid' ev ->
          let negation = T.EApp (T.EId lnot) [T.EId ev] in
          return $ T.EApp (T.EId k) [T.EId st',T.EId pid', negation]
        return (T.EApp et [T.EId st, T.EId pid,innerLambda], btyp)
    uop ->
      case isIncDec uop of
        Nothing -> failExp se "Unsupported unary operator"
        Just (cspName,cspNameBool) ->
         -- \st,pid,k @ [e] (st, pid, runtimeIncDec (rdr,wtr,k))
         --
         -- Here: 
         -- 
         --  - [e] is the translation of "e" as an lvalue (it computes the
         --    corresponding location.
         --
         --  - "runtimeIncDec" is the name of the runtime function
         --    corresponding to this particular operator.  Note that it
         --    returns a function expecting three arguments, which is exactly
         --    what's needed as the argument to [e]
         expOuterLambdaState $ \st pid k -> do
           (loc,btyp,rdr,wtr) <- transLValue e
           fnm <-
             case btyp of
               IntType _  -> return cspName
               BoolType _ -> return cspNameBool
               _ -> failExp se $ "Unsupported: increment or decrement "
                              ++ "operator on data of type " ++ ppBaseType btyp
           return (T.EApp loc 
                     [T.EId st, T.EId pid,
                      T.EApp fnm [rdr,wtr,T.EId k]],
                   btyp)
  where
    isIncDec uop = fmap (\(a,b) -> (T.EId $ T.Fixed a, T.EId $ T.Fixed b)) $
      case uop of
        S.PreInc  -> Just ("preIncrement","preIncrementBool")
        S.PostInc -> Just ("postIncrement","postIncrementBool")
        S.PreDec  -> Just ("preDecrement","preDecrementBool")
        S.PostDec -> Just ("postDecrement","postDecrementBool")
        _         -> Nothing
        
             
transExp e@(S.Bin bop e1 e2 _) =
  -- Individual binary operations (like addition) mean different things for
  -- different types.  There are three main categories of types where
  -- arithmetic operators are sensible: integral types, floating point types,
  -- and pointer types.
  --
  -- What we do is to check the types of two operands and, if they are both
  -- ints or floats, use the appropriate runtime function for that type from
  -- the runtime.  Pointer arithmetic is completely unsupported.  We also do
  -- not support C's automatic type conversions, but in principle these would
  -- not be hard to add if they turn out to be needed.
  -- 
  -- We build:     
  --     \ (st,pid,k) @ 
  --         [e1] (st,pid,\(st',pid',ev1) @ 
  --             [e2] (st',pid',\(st'',pid'',ev2) @ k (st'',pid'',bop ev1 ev2)
  --
  -- where "bop" is the appropriate runtime function.
  expOuterLambdaState $ \st pid k -> do
    (te1,btyp1) <- transExp e1
    (e1LamArg,resultType) <- 
      expInnerLambdaState $ \st' pid' ev1 -> do
        (te2,btyp2) <- transExp e2
        (resultType,bopt,mconv1,mconv2) <- mbopt btyp1 btyp2
        (e2LamArg) <-
           expInnerLambda $ \st'' pid'' ev2 ->
             let
               useConv :: Maybe T.Exp -> T.Exp -> T.Exp
               useConv Nothing  oprnd = oprnd
               useConv (Just f) oprnd = T.EApp f [oprnd]
               
               operand1 = useConv mconv1 (T.EId ev1)
               operand2 = useConv mconv2 (T.EId ev2)
             in
             return $ T.EApp (T.EId k) 
                         [T.EId st'',T.EId pid'',
                          T.EApp bopt [operand1,operand2]]
        return (T.EApp te2 [T.EId st',T.EId pid',e2LamArg],resultType)
    return (T.EApp te1 [T.EId st,T.EId pid,e1LamArg],resultType)
  where
    binops =
      [((S.Multiply,          cIntBaseType)  , (cIntBaseType,"multiply")),
       ((S.Multiply,          cFloatBaseType), (cFloatBaseType,"multiplyFloat")),
       ((S.Divide,            cIntBaseType)  , (cIntBaseType,"divide")),
       ((S.Divide,            cFloatBaseType), (cFloatBaseType,"divideFloat")),
       ((S.Modulus,           cIntBaseType)  , (cIntBaseType,"mod")),
       ((S.Add,               cIntBaseType)  , (cIntBaseType,"plus")),
       ((S.Add,               cFloatBaseType), (cFloatBaseType,"plusFloat")),
       ((S.Subtract,          cIntBaseType)  , (cIntBaseType,"minus")),
       ((S.Subtract,          cFloatBaseType), (cFloatBaseType,"minusFloat")),
       ((S.LessThan,          cIntBaseType)  , (cIntBaseType,"lt")),
       ((S.LessThan,          cFloatBaseType), (cIntBaseType,"ltFloat")),
       ((S.GreaterThan,       cIntBaseType)  , (cIntBaseType,"gt")),
       ((S.GreaterThan,       cFloatBaseType), (cIntBaseType,"gtFloat")),
       ((S.LessThanOrEqual,   cIntBaseType)  , (cIntBaseType,"le")),
       ((S.LessThanOrEqual,   cFloatBaseType), (cIntBaseType,"leFloat")),
       ((S.GreaterThanOrEqual,cIntBaseType)  , (cIntBaseType,"ge")),
       ((S.GreaterThanOrEqual,cFloatBaseType), (cIntBaseType,"geFloat")),
       ((S.Equal,             cIntBaseType)  , (cIntBaseType,"eq")),
       ((S.Equal,             cFloatBaseType), (cIntBaseType,"eqFloat")),
       ((S.NotEqual,          cIntBaseType)  , (cIntBaseType,"neq")),
       ((S.NotEqual,          cFloatBaseType), (cIntBaseType,"neqFloat")),
       ((S.LogicalAnd,        cIntBaseType)  , (cIntBaseType,"land")),
       ((S.LogicalAnd,        cBoolBaseType) , (cIntBaseType,"landBool")),
       ((S.LogicalOr,         cIntBaseType)  , (cIntBaseType,"lor")),
       ((S.LogicalOr,         cBoolBaseType) , (cIntBaseType,"lorBool")),
       ((S.BitwiseAnd,        cIntBaseType)  , (cIntBaseType,"bwAnd")),
       ((S.BitwiseOr,         cIntBaseType)  , (cIntBaseType,"bwOr")),
       ((S.BitwiseXor,        cIntBaseType)  , (cIntBaseType,"bwXor")),
       ((S.LeftShift,         cIntBaseType)  , (cIntBaseType,"leftShift")),
       ((S.RightShift,        cIntBaseType)  , (cIntBaseType,"rightShift"))
      ]
    
    pointerBinops =
       [(S.Equal, (cIntBaseType,"eqPointer")),
        (S.NotEqual, (cIntBaseType,"neqPointer"))]
  

    -- mbopt does two things:
    --
    -- - First, if the operands have different types, it checks to see if one
    --   of these types can be implicitly converted to the other, following
    --   the C rules for promoting from smaller types to larger types.
    --   In the event that a conversion is necessary, it computes the appropriate
    --   cspm conversion function (these are the two "Maybe T.Exp"s returned.
    --
    -- - If the types were the same or could be unified, it checks to see
    --   if we know how to perform the requested operation on things of this type,
    --   and returns the appropriate cspm function if so.
    mbopt :: BaseType -> BaseType -> CG (BaseType,T.Exp,Maybe T.Exp,Maybe T.Exp)
    mbopt btyp1 btyp2 = do
      (bt,mconv1,mconv2) <- 
        case unifyTypes btyp1 btyp2 of
          Just u -> return u
          Nothing -> 
            failExp e $ "Binary operators must be applied to operands of "
                     ++ "compatible types, but here " ++ show bop ++ " is "
                     ++ "applied to operands of types \"" ++ ppBaseType btyp1
                     ++ "\" and \"" ++ ppBaseType btyp2 ++ "\""

      case lookup (bop,bt) binops of
        Just (rtyp,nm) -> return (rtyp,T.EId $ T.Fixed nm,mconv1,mconv2)
        Nothing -> 
          case (isPointerish bt, lookup bop pointerBinops) of
            (True, Just (rtyp,nm)) ->
              return (rtyp,T.EId (T.Fixed nm),mconv1,mconv2)
            _ -> 
              failExp e $ "Binary operator " ++ show bop ++ " is not "
                       ++ " supported on operands of type "
                       ++ ppBaseType bt
      where 
        isPointerish :: BaseType -> Bool
        isPointerish (PointerType _ _ _) = True
        isPointerish (VoidStarType _)    = True
        isPointerish _                   = False
transExp (S.SizeOfExp _ _) = (,cIntBaseType) <$> returnExp cIntUnknown
transExp (S.SizeOfTy _ _)  = (,cIntBaseType) <$> returnExp cIntUnknown
transExp (S.Cast t e sp)   = do
  -- right now we only support casts that could be implicit conversions
  (te,btyp) <- transExp e
  btyp' <- transType t
  if btyp' == btyp 
    then return (te,btyp') -- no conversion necessary
    else -- here we must eta expand te, so that we have someting to apply the
         -- conversion to.  That is:
         -- 
         -- \st,pid,k -> [e] (st,pid,\st',pid',ev -> k (st',pid',||ev||))
         --
         -- where by ||ev|| I mean the result of the implicit cast on ev.
      do expOuterLambdaState $ \st pid k -> do
           innerL <- expInnerLambda $ \st' pid' ev -> do
             ev' <- implicitConvert sp (T.EId ev) btyp btyp'
             return $ T.EApp (T.EId k) [T.EId st',T.EId pid',ev']
           return (T.EApp te [T.EId st,T.EId pid,innerL],btyp')
transExp te@(S.Cond escrut metrue efalse sp) = do
  -- [e ? e1 : e2]    
  --    ---->
  -- \st,pid,k -> [e] (st,pid,\st',pid',ev -> cond(st',pid',k,ev,[e1],[e2])
  -- 
  -- (with an implicit conversion from the type of "e" to int, if necessary
  -- and allowed, and a conversion to unify the types of e1 and e2, if
  -- necessary and allowed.
  expOuterLambdaState $ \st pid k -> do
    (tescrut,scrutTyp) <- transExp escrut
    (innerL,retType) <- expInnerLambdaState $ \st' pid' ev -> do
      (te1,btyp1) <-
        case metrue of
          Just ef -> transExp ef
          -- XXX unsupported: the scrutinee is to be used if the first argument is missing.
          Nothing -> failExp te "Unsupported: ternary operator with missing false case"
      (te2,btyp2) <- transExp efalse
      case unifyTypes btyp1 btyp2 of
        Nothing -> failExp te $
             "The branches of a conditional expression must have the same "
          ++ "type, but here one has type \"" ++ ppBaseType btyp1 ++ "\" and "
          ++ "the other has type \"" ++ ppBaseType btyp2 ++ "\""
        Just (retType,mconv1,mconv2) ->
          let
            -- we can't evaluate te1 or te2 before runtime (since we don't know
            -- which needs to be run).  So, in the event a type conversion is
            -- necessary, instead of evaluating them and then applying the
            -- conversion function, we have to wrap them in a lambda that will
            -- apply the conversion function when they are evaluated.  To wit:
            --
            --  \st,k @ [e] (st, \st',ev @ k (st',conv ev))
            useConv :: Maybe T.Exp -> T.Exp -> CG T.Exp
            useConv Nothing  oprnd = return oprnd
            useConv (Just f) oprnd =
              expOuterLambda $ \convSt convPid convK -> do
                innerL <- expInnerLambda $ \convSt' convPid' convEV ->
                  return $ T.EApp (T.EId convK) 
                              [T.EId convSt',T.EId convPid',T.EApp f [T.EId convEV]]
                return $ T.EApp oprnd [T.EId convSt,T.EId convPid,innerL]
          in do
            te1' <- useConv mconv1 te1
            te2' <- useConv mconv2 te2
            tev' <- implicitConvert sp (T.EId ev) scrutTyp (IntType sp)
            return (T.EApp (T.EId cTernary)
                               [T.EId st',T.EId pid',T.EId k,tev',te1',te2'],
                    retType)
    return (T.EApp tescrut [T.EId st,T.EId pid,innerL],retType)

  

--------------------------------------------------------------------
--------------- TYPE CONVERSIONS
--------------------------------------------------------------------

-- In C, some types may be implicitly converted to other types.
--
-- This assumes it is passed in a CSP exp that's the actual value, not
-- a CPS-converted one.  Args: pos exp fromType toType.
implicitConvert :: S.SPos -> T.Exp -> BaseType -> BaseType -> CG T.Exp
implicitConvert _ e t1 t2 | t1 == t2         = return e

implicitConvert _ e (IntType _) (BoolType _) = 
  return $ T.EApp (T.EId cIntToBool) [e]
implicitConvert _ e (BoolType _) (IntType _) =
  return $ T.EApp (T.EId cBoolToInt) [e]

implicitConvert _ e (FloatType _) (IntType _) =
  return $ T.EApp (T.EId cFloatToInt) [e]
implicitConvert _ e (IntType _) (FloatType _) =
  return $ T.EApp (T.EId cIntToFloat) [e]

implicitConvert _ e (PointerType _ bt _) (IntType _) = do
  tinfo <- lookupTypeInfo bt
  -- if e == NULL then CIntKnown.0 else CIntUnknown
  return $ T.EIfThenElse (T.EBinOp e T.BEq (T.EId $ tiNullLoc tinfo))
                         cIntZero cIntUnknown

implicitConvert _ e (IntType _) (PointerType _ bt _) = do
  tinfo <- lookupTypeInfo bt
  -- if e == 0 then NullPtr else UnknownPtr
  return $ T.EIfThenElse (T.EBinOp e T.BEq cIntZero)
                         (T.EId $ tiNullLoc tinfo)
                         (T.EId $ tiUnknownLoc tinfo)

-- Conversions between void* and other pointer types.  We don't lose any
-- information, because our representation for (void*) is just a tagged union of
-- all locations.
implicitConvert _ e (PointerType _ bt _) (VoidStarType _) = do
  tinfo <- lookupTypeInfo bt
  return $ T.EApp (T.EId $ tiVoidStarInj tinfo) [e]
implicitConvert _ e (VoidStarType _) (PointerType _ bt _) = do
  tinfo <- lookupTypeInfo bt
  return $ T.EApp (T.EId $ tiVoidStarProj tinfo) [e]

-- Conversions between void* and int types.  Null maps to 0 and everything else
-- is unknown.  As in the case of int and other pointers, it would be nice if we
-- had a way to represent non-zero ints.
implicitConvert _ e (IntType _) (VoidStarType _) =
  return $ T.EIfThenElse (T.EBinOp e T.BEq cIntZero)
                         (T.EId voidStarNullCon)
                         (T.EId voidStarUnknownCon)
implicitConvert _ e (VoidStarType _) (IntType _) =
  return $ T.EIfThenElse (T.EBinOp e T.BEq (T.EId voidStarNullCon))
                         cIntZero cIntUnknown

implicitConvert p _ t1 t2 =
  failPos p $ "An expression of type " ++ ppBaseType t2
           ++ " is required, but this expression has type "
           ++ ppBaseType t1

-- Sometimes (for example, at binary ops), we need to check if two types are
-- compatible and convert one to the other if so (e.g., adding an int to a
-- bool).
--
-- XXX this is meant to be a non-directional version of implicitConvert, for
-- situations in which the C compiler is expected to infer the direction of the
-- conversion.  But it doesn't handle very many cases now.
unifyTypes :: BaseType -> BaseType 
          -> Maybe (BaseType,Maybe T.Exp,Maybe T.Exp)
unifyTypes bt1 bt2 | bt1 == bt2         = Just (bt1,Nothing,Nothing)
unifyTypes bt1@(IntType _) (BoolType _) =
  Just (bt1,Nothing,Just $ T.EId cBoolToInt)
unifyTypes (BoolType _) bt2@(IntType _) =
  Just (bt2,Just (T.EId cBoolToInt),Nothing)
unifyTypes _ _ = Nothing


--------------------------------------------------------------------
--------------- LVALUES
--------------------------------------------------------------------


-- lvalues in C are complicated beasts.  K&R says an lvalue is anything that
-- refers to a named region of storage.  This suggests lots of crazy things
-- are lvalues.  For example, is the following code legal?
--
-- int x = 0;
-- int y,z;
-- (x?y:z) = 3;
--
-- By the definition above, yes!  Though GCC does seem to reject this.
-- In practice, we handle lvalues that fall into this grammar:
--
--   lv := x | *lv | lv -> label | lv . label | lv [e] | (t)lv
--
-- Now, the first thing to observe is that (lv -> label) is shorthand for
-- ((*lv).label), so we translate away '->'s early in the process of dealing
-- with lvalues (breakupLVal below).
--
-- This just leaves variables, dereferences, direct struct accesses, subscripts
-- and casts.  Every lvalue has one variable at the core and is then a sequence
-- of the other operations.  It is convenient for our internal representation to
-- group sequences of direct struct accesses together, so we represent the
-- accessor operations with the following datatype:

data VarAccess = VADeref | VADot [String]
               | VASubscript S.Exp | VACast S.Type

-- So, for example, if we had an lvalue like:
--
--    (*((*x)->l1).l2).l3.l4 = ...
--
-- We ditch the arrow, obtaining:
--
--    (*((**x).l1.l2)).l3.l4
-- 
-- And this series of operations is represented by:
--
--    [VADeref, VADeref, VADots [l1,l2], VADeref, VADots [l4,l4]]
--
-- The function breakupLVal below takes an expression and breaks it up into
-- this structure, also finding the variable at the core of the lvalue.
--
-- TODO: better error messages
breakupLVal :: S.Exp -> CG (S.Id,[VarAccess])
breakupLVal = bupLVAcc []
  where
    bupLVAcc vas (S.IdExp x _) = return (x,vas)
    bupLVAcc vas (S.Unary S.Indirection e _) =
      bupLVAcc (VADeref : vas) e
    bupLVAcc vas (S.CompSel e S.IndirSel lab _) =
      bupLVAcc (VADeref : VADot [lab] : vas) e
    bupLVAcc vas e@(S.CompSel _ S.DirSel _ _) =
      case e' of
        -- must check for an inner -> here for correct grouping of dots
        S.CompSel e'' S.IndirSel lab _ ->
          bupLVAcc (VADeref : VADot (lab:labs) : vas) e''
        _ -> bupLVAcc (VADot labs : vas) e'
      where
        (e',labs) = dirSels e []

        -- peel off all dots from the exp
        dirSels :: S.Exp -> [String] -> (S.Exp,[String])
        dirSels (S.CompSel v S.DirSel f _) acc = dirSels v (f:acc)
        dirSels f acc = (f,acc)
    bupLVAcc vas (S.Subscript elv eindex _ ) =
      bupLVAcc (VASubscript eindex : vas) elv
    bupLVAcc vas (S.Cast t elv _) =
      bupLVAcc (VACast t : vas) elv

    bupLVAcc _ e = failExp e $ "Invalid or unsupported lvalue"


-- LValues correspond to locations.  transLValue builds a CSPm process that
-- computes the location corresponding to some lvalue.  That is, for an lvalue
-- which refers to a location containing data of type Foo, transLValue builds a:
--
--    (VarMap,PID,(Varmap,PID,FooLoc) -> Proc) -> Proc
--
-- Here, "VarMap" is the local state map.  This CSPm type corresponds directly
-- to the way we translate expressions, since an lvalue is a kind of expression.
--
-- transLValue also returns three other pieces of data: the type of the data
-- that the lvalue points to, along with the CSPm functions that read and write
-- to this lvalue.  Our model is a little unusual in that there are several
-- distinct C lvalues which correspond to each location (for example, the
-- various fields of a struct).  This is why transLValue returns more than just
-- the location and type.
transLValue :: S.Exp -> CG (T.Exp,BaseType,T.Exp,T.Exp)
transLValue e = do
  (sid@(S.Id nm _ _),vas) <- breakupLVal e
  mvar <- lookupVar sid
  case mvar of
    Nothing -> failExp e $ "Unbound Variable " ++ nm ++ " in transLValue"
    Just (loc,binfo,tinfo) -> do
      initialLocExp <- returnExp loc
      foldM processVA 
        (initialLocExp,binfo,T.EId (tiReader tinfo),T.EId (tiWriter tinfo))
        vas
  where
    -- processVA gets folded over the "VarAccess"es, updating the information
    -- about the lvalue at each step.
    processVA :: (T.Exp,BaseType,T.Exp,T.Exp) -> VarAccess
               -> CG (T.Exp,BaseType,T.Exp,T.Exp)
    processVA (loc,PointerType _ bt _,reader,_) VADeref = do
      -- \(st,pid,k) @ loc (st,pid,
      --     \(st',pid',locVal) @ reader (st',pid',locBnd,pos,k))
      loc' <- 
        expOuterLambda $ \st pid k -> do
          innerL <- expInnerLambda $ \st' pid' locVal ->
            return $
              T.EApp reader
                [T.EId st',T.EId pid',T.EId locVal, T.EId k]
          return $ T.EApp loc [T.EId st,T.EId pid,innerL]
      tinfo <- lookupTypeInfo bt
      return (loc',bt,T.EId (tiReader tinfo),T.EId (tiWriter tinfo))
    processVA _ VADeref =
      failExp e "Attempt to dereference expression of non-pointer type"

    processVA (loc,bt,_,_) (VADot labels) = do
      tinfo <- lookupTypeInfo bt
      case tiDataInfo tinfo of
        Right _ -> failExp e "Attempt to access fields of non-struct type"
        Left (StructInfo {siFields}) ->
          case traverseDirSelChain siFields labels of
            Nothing -> failExp e $ "Attempt to access non-existant field (" ++ show labels ++ ")" ++ show siFields
            Just fi -> return (loc, fiType fi,
                               T.EId (fiReader fi), T.EId (fiWriter fi))

    -- Array access is a lot like pointer dereference, except there's an
    -- additional offset modelled by the tiArrayLocs function.  That function
    -- may return the empty list or a one-element list.  Empty means we couldn't
    -- figure out the offset, perhaps because the index is unknown or because
    -- the array isn't long enough, or whatever.  In that case we signal an
    -- error and deadlock the program to avoid being unsound.  Otherwise, the
    -- function returns the location at the appropriate offset, so we return it.
    processVA (loc, PointerType _ bt _, reader, _) (VASubscript index) = do
      -- \st,pid,k @ loc(st,pid,
      --   \st',pid',locVal @ reader (st',pid',locVal,
      --     \st'',pid'',arrayLoc @ [index] (st'', pid'',
      --       \st''',pid''',indexVal @
      --         let offsetLoc = tiArrayLocs(arrayLoc,indexVal) within
      --           if null(offsetLoc) then (arrayIndex_ERROR -> STOP)
      --                              else k(st''',pid''',head(offsetLoc)))))

      TypeInfo {tiArrayLocs,tiReader,tiWriter} <- lookupTypeInfo bt
      loc' <- expOuterLambda $ \st pid k -> do
        innerL1 <- expInnerLambda $ \st' pid' locVal -> do
          innerL2 <- expInnerLambda $ \st'' pid'' arrayLoc -> do
            innerL3 <- expInnerLambda $ \st''' pid''' indexVal -> do
              offsetLoc <- freshLocalNew "offsetLoc"
              return $
                T.ELet [T.DVar (T.PId offsetLoc)
                             $ T.EApp (T.EId tiArrayLocs)
                                    $ map T.EId [arrayLoc,indexVal]]
                       (T.EIfThenElse
                         (T.EApp (T.EId $ T.Fixed "null") [T.EId offsetLoc])
                         (T.EPrefix (T.EId arrayIndexErrorChanId) []
                                    (T.EConst T.CStop))
                         (T.EApp (T.EId k)
                                 [T.EId st''', T.EId pid''',
                                    T.EApp (T.EId $ T.Fixed "head")
                                           [T.EId offsetLoc]]))
            (te,_) <- transExp index
            return $ T.EApp te [T.EId st'', T.EId pid'', innerL3]
          return $ T.EApp reader [T.EId st',T.EId pid', T.EId locVal, innerL2]
        return $ T.EApp loc [T.EId st, T.EId pid, innerL1]
      return (loc', bt, T.EId tiReader, T.EId tiWriter)
    processVA _ (VASubscript _) = failExp e "Array access on object of non-array type"
    processVA (loc,bt,reader,writer) (VACast t) = do
    -- Here there is a cast on the lvalue.  The idea is that a cast doesn't
    -- change the location (loc) itself.  But, if you use reader or writer,
    -- you're now expecting a value of a different type.  So we wrap those guys
    -- in functions that apply "implicitConvert" to do the cast.
    --
    -- reader' =
    --    \st,pid,l,k @ reader (st,pid,l,
    --        \st',pid',v @ k (st',pid',implicitConvert v))
    --
    -- writer' =
    --    \st,pid,loc,val,k @ writer (st,pid,loc,val,implicitConvert k)
      bt' <- transType t
      reader' <- do
        st  <- freshLocalNew "st"
        pid <- freshLocalNew "pid"
        l   <- freshLocalNew "l"
        k   <- freshLocalNew "k"
        innerL <- expInnerLambda $ \st' pid' v -> do
          v' <- implicitConvert (S.locType t) (T.EId v) bt bt'
          return $ T.EApp (T.EId k) [T.EId st', T.EId pid', v']
        return $ T.ELambda (map T.PId [st,pid,l,k])
                  $ T.EApp reader ((map T.EId [st,pid,l]) ++ [innerL])

      writer' <- do
        st  <- freshLocalNew "st"
        pid <- freshLocalNew "pid"
        l   <- freshLocalNew "l"
        v   <- freshLocalNew "v"
        k   <- freshLocalNew "k"
        v'  <- implicitConvert (S.locType t) (T.EId v) bt bt'
        return $ T.ELambda (map T.PId [st,pid,l,v,k])
                  $ T.EApp writer ((map T.EId [st,pid,l,v]) ++ [v'])

      return (loc, bt', reader', writer')

-- Builds an expression that reads from a lvalue (and the type of the data
-- that will be read).  Used for variable access, etc.  This produces a CSP
-- expression of the same type as transExp:
--
--     (VarMap,PID,(VarMap,PID,Foo) -> Proc) -> Proc
-- 
-- Where "Foo" is the type of data stored in this location.
--
-- In particular, it builds:
--
--    \(st,pid,k) -> |e| (st,\(st',pid',eloc) -> read (st',pid',eloc,pos e,k)
--
-- Here, |e| is the expression which computes the location of e, 
-- implemented by transLValue.
readFromLValue :: S.Exp -> CG (T.Exp,BaseType)
readFromLValue e =
  expOuterLambdaState $ \st pid k -> do
    (loc,btyp,reader,_) <- transLValue e
    innerL <- expInnerLambda $ \st' pid' locBnd ->
      return $ 
        T.EApp reader [T.EId st',T.EId pid',T.EId locBnd, T.EId k]
    return $ (T.EApp loc [T.EId st,T.EId pid,innerL],btyp)

--------------------------------------------------------------------
----------- Procs!
--------------------------------------------------------------------

-- We'd like to translate each statment as a function that takes a
-- continuation, does its business, and calls the continuation.  Perhaps 
-- with the CSPm type:
-- 
--   Proc -> Proc
--
-- This works fine for a variety of statements, but it works poorly for
-- statements that update local variables, because there is no way to tell the
-- continuation that the value of some variable it uses has changed.
--
-- For example, consider the code:
--
--   int x = 5;
--   if (...) { x = 6; } else { x = 7; };
--   return x;
--
-- If we're translating statements as 'Proc -> Proc's, this is hard to model.
-- There's no way to signal to the continuation of the translation of the if
-- statement that the value of x has changed.
--
-- What we do instead is to pass around a map containing the value of any
-- local variables, updating it as we go.  So our next guess might be that a
-- statement has type:
--
--      (VarMap, VarMap -> Proc) -> Proc
--
-- That is: you tell me the current state of local variables and what to do
-- with the updated state, and I'll do my stuff then pass on the updated state
-- as specified.
--
-- To be more precise, "VarMap" is really (| LocVar => CType |) - a CSPm map
-- which associates the representation of some C value with each local
-- variable (or some superset of the local variables currently in scope).
--
-- This is almost right, but it turns out that code generation will be cleaner
-- (and more importantly, fdr will handle the generated code better) if we add
-- an extra argument to the continuation passed to a statement, making it:
--
--     (VarMap, (VarMap,a) -> Proc) -> Proc
--
-- We pick this type because it lines up better with the translation of
-- expressions, which are a kind of statement.  Expressions, unlike statements,
-- have a value, so the continuation takes this value.  Statements don't have a
-- value, so really it shouldn't matter what gets passed to this continuation.
-- However, we are able to generate cleaner code with fewer special cases, when
-- we have an expression statement or a return statement, we pass the associated
-- value to the continuation.
--
-- The final consideration is process IDs.  To support things like mutual
-- exclusion, each process in the C program must have a unique pid.  One option
-- would be to store this in the local state map, but a process shouldn't be
-- able to change its own pid.  So, we pass along the process of ID as a third
-- piece of information along with the VarMap and the continuation, resulting in
-- a final type of:
--
--   (VarMap, PID, (VarMap,PID,a) -> Proc) -> Proc

-- transInnerNodes translates the body of a basic block.  For example, in a block like:
--
--  blockLabel: 
--    int x = 3;
--    y = f(&x);
--    y++;
--    return y;
--
-- the "inner nodes" are "int x = 3; y = f(&x); y++"
--
-- We translate these nodes as a Proc.  For this, transInnerNodes takes three
-- extra arguments - the name of the state map at the beginning of the block,
-- the process ID, and the "exit continuation" - the translation of "return y".
-- Note that we actually take in the exit continuation as a monadic action,
-- since state built up during the translation of the body may be required for
-- the translation of the exit node (in particular, it may reference variables
-- defined in the previous blocks).
--
-- Each individual inner node is translated as a
--      (VarMap, PID,(VarMap,PID,a) -> Proc) -> Proc
--
-- That is, it takes three arguments: the current state, the process ID, and a
-- continuation which itself expects an updated state.  The third argument to
-- the continuation is ignored - it is there only for uniformity with the
-- translation of expressions.
--
-- Consider, then, the translation of a block like [s1;s2;s3;return].  We are provided
-- with:
--        - st, the name of the state map at the start of the block
--        - pid, the process id
--        - texit, which is a (VarMap,a) -> Proc
-- 
-- We produce:
--
--    [ s1; s2; s3; return ] 
-- -> [s1] (st,pid,\(st',pid',_) . 
--      [s2] (st',pid',\(st'',pid'',_) .
--         [s3] (st'',pid'',\(st''',pid''',_) . texit (st''',pid''',()))))
--
-- In the special cases of 0 and 1 statements, we have:
--
--         texit (st,pid,())    
--  and    [s] (st,pid,\(st',pid',_).texit(st',pid',()))
--
-- Though we can safely the third argument, or "return value" of each statement,
-- we can not ignore the updated process ids.  In the event at the statement is
-- "fork" or a similar multithreading operation, the process ids may change as
-- we go.
transInnerNodes :: [S.Insn O O] -> T.Id -> T.Id -> CG T.Exp -> CG T.Exp
transInnerNodes [] outerState outerPid exitCont = do
  texit <- exitCont
  return $ T.EApp texit [T.EId outerState,T.EId outerPid,cspUnit]
transInnerNodes [i] outerState outerPid exitCont = do
  ti   <- transInnerNode i
  texit <- exitCont
  return $ T.EApp ti [T.EId outerState, T.EId outerPid, texit]  -- XXX wrap texit?
transInnerNodes (i:is) outerState outerPid exitCont = do
  ti <- transInnerNode i
  innerk <- stmtLambda $ \st' pid' _ -> transInnerNodes is st' pid' exitCont
  return $ T.EApp ti [T.EId outerState,T.EId outerPid,innerk]

transInnerNode :: S.Insn O O -> CG T.Exp
transInnerNode (S.ICleanup sid) = stmtLambda $ \st pid k -> do
  st' <- removeVarsFromState internal (T.EId st) [sid]
  return $ T.EApp (T.EId k) [st',T.EId pid,cspUnit]
transInnerNode (S.IExp e) = stmtLambda $ \st pid k -> do
  -- When an expression is used as a statement, it is evaluated and then its
  -- value is thrown away.  But, owing to the types involved, the continuation
  -- passed to this statement expects some kind of value.  In principle, that
  -- value should never be used, so we pass unit.
  -- That is, we do:
  -- 
  --   [e;]  -->  \(st,pid,k) -> [e] (st,pid,\(st',pid',_) -> k (st',pid',()))
  (te,_) <- transExp e
  innerL <- expInnerLambda $ \st' pid' _ ->
    return $ T.EApp (T.EId k) [T.EId st',T.EId pid',cspUnit]
  return $ T.EApp te [T.EId st,T.EId pid,innerL]
transInnerNode (S.IDecl d) =
  -- here we have a declaration like:   "t x = e;".
  -- 
  -- We build:
  --     \st,pid,k @ [e] (st,pid,
  --         \(st',pid',ev) @ k (tLocalsUpdate st' x (convert xv),pid',())
  -- 
  -- "convert te" here indicates that we call implicitConvert because
  -- at declarations an implicit type conversion is allowed in C.
  case d of
    S.VarDecln (S.VDecln {S.vdIdent,S.vdType,S.vdInit}) p -> do
      lvTyp <- transType vdType
      (initializer,rvTyp) <-
        case lvTyp of
          -- we have a special case for Array types, because in that case the
          -- declared local is initialized to the first location of the array,
          -- and any initializer provided applies to the implicitly allocated
          -- array elements instead.
          PointerType _ bt (Just len) ->
            case vdInit of
              Just (S.SimpleInitializer _) ->
                failDecln d $ "Illegal initializer: statically sized arrays "
                           ++ "may only be given array initializers"
              Just (S.ListInitializer _) ->
                failDecln d $ "Unsupported: array initializer"
              Nothing -> do
                let nameHint = S.stringPart vdIdent
                arrayCells <- freshLocalArrayCells nameHint bt len
                TypeInfo {tiLocalLocTag,tiLocalsUpdate} <- lookupTypeInfo bt
                firstCell <-
                  case arrayCells of
                    [] -> failDecln d $ "Unsupported: 0-length local array"
                    (c:_) -> return $ T.EDot (T.EId tiLocalLocTag) [T.EId c]
                uninit <- uninitializedLocal bt
                -- \(st,pid,k) -> k(st {cell1=unknown,...,celln=unknown},
                --                      pid,firstCell)
                i <- expOuterLambda (\st pid k -> return $
                       T.EApp (T.EId k) $
                          let st' = foldl (\s c -> T.EApp (T.EId tiLocalsUpdate)
                                                          [s,T.EId c,uninit])
                                          (T.EId st) arrayCells
                           in [st', T.EId pid, firstCell])
                return $ (i,lvTyp)
          _ -> 
            case vdInit of
              Just (S.SimpleInitializer se) -> transExp se
              Just li@(S.ListInitializer _) -> do 
                initExp <- transInitializer lvTyp li uninitializedLocal p
                fmap (,lvTyp) $ returnExp initExp
              Nothing -> do
                uninit <- uninitializedLocal lvTyp
                fmap (,lvTyp) $ returnExp uninit
                -- returnExp to match with transExp, which produces a function.
      stmtLambda $ \st pid k ->
        T.EApp initializer <$> sequence [return (T.EId st),return (T.EId pid),
          expInnerLambda $ \st' pid' ev -> do
            vdtid <- freshLocal vdIdent lvTyp
            evTyped <- implicitConvert p (T.EId ev) rvTyp lvTyp
            TypeInfo {tiLocalsUpdate} <- lookupTypeInfo lvTyp
            let st'' = T.EApp (T.EId tiLocalsUpdate)
                         [T.EId st', T.EId vdtid, evTyped]
            return $ T.EApp (T.EId k) [st'',T.EId pid',cspUnit]]
    _ -> failDecln d "Unsupported declaration form in compound statement"



-- An exit node is translated as a ((VarMap,PID,a) -> Proc).
--
-- Unlike intermediate nodes, it doesn't take a continuation as an argument
-- because the node itself specifies where control goes next.  It could just be
-- a ((VarMap,PID) -> Proc), but we add an extra argument that's just ignored for
-- uniformity with expressions.
--
-- We do need to know the outer continuation (i.e., what to do after the current
-- function returns, in case this exit node is return).  So transExitNode takes
-- a (T.Exp,BaseType), specifying the return continuation and the type, if any,
-- that this function returns.
--
-- We also need to know the name of the function we are currently translating,
-- in the case of a tail call.  This is the T.Id argument.
--
-- Finally, note that each exit node carries along with it a list of variables
-- that go dead just before the control flow transfer.  We use the helper
-- function "removeVarsFromState" to take these out of the state map in each
-- case.
transExitNode :: S.Insn O C -> (T.Exp,BaseType) -> T.Id -> M.Map Label T.Id -> CG T.Exp
transExitNode insn (kr,rtyp) fname locs = do
  case insn of
    S.IGoto p vs gotoLabel -> do 
      gotoTarget <- T.EId <$> lookupLoc gotoLabel locs (failPos p)
      expInnerLambda $ \vmap pid _ -> do
         vmap' <- removeVarsFromState p (T.EId vmap) vs
         return $ T.EApp gotoTarget [vmap', T.EId pid, kr] 
    S.ITailCall p vs args -> expInnerLambda $ \vmap pid _ ->
        buildTailApp (T.EId fname) args (T.EId vmap) (T.EId pid) kr
      where
        -- XXX really ugly - this is basically a duplicated buildApp just to
        -- insert the "removeVarsFromState" bit.  As a result, they are out of
        -- sync. (in particular this one doesn't have the type checking)
        buildTailApp :: T.Exp -> [(S.Exp)] -> T.Exp -> T.Exp -> T.Exp -> CG T.Exp 
        buildTailApp f fargs outerst outerpid k = buildApp' fargs [] outerst outerpid
          where
            buildApp' [] argAcc st pid = do
              st' <- removeVarsFromState p st vs
              return $ T.EApp f $ map T.EId (reverse argAcc) ++ [st',pid,k]
            buildApp' (e1 : es) argAcc st pid = do
              (te1,_)  <- transExp e1
              innerLam <- 
                expInnerLambda $ \stBnd pidBnd evBnd -> 
                  buildApp' es (evBnd:argAcc) (T.EId stBnd) (T.EId pidBnd)
              return $ T.EApp te1 [st,pid,innerLam]
    S.ICond p vs1 vs2 cond thenLabel elseLabel -> expInnerLambda $ \vmap pid _ -> do
      --  \ st, pid, _ @ 
      --     [cond] (st, pid, \st',pid',condVal @
      --       branch (st',pid',castToInt condVal,thenLabel,elseLabel)
      thenTid <- lookupLoc thenLabel locs (failPos p)
      elseTid <- lookupLoc elseLabel locs (failPos p)
      (tcond,btyp) <- transExp cond
      innerLam <- expInnerLambda $ \vmap' pid' condVal -> do
        -- XXX As a very special case here, if(x) where x is a pointer is
        -- handled separately.  In particular, our normal implicit conversion
        -- from a pointer to an int will yield "unknown" when the pointer is
        -- not-null, which loses a lot of information.  The 'right' thing to do
        -- may be to expand the model of ints with a "not zero" constructor,
        -- modeling ints who are known to be non-zero but whose values aren't
        -- known.
        tcondInt <-
          let scrutinee = T.EId condVal in
          case btyp of
            PointerType _ btyp' _ -> do
              ptrinfo <- lookupTypeInfo btyp'
              -- [if e == NULL then CIntKnown.0
              --     else if e = UNKNOWN then CIntUnknown
              --         else CIntKnown.1]
              return $ T.EIfThenElse
                (T.EBinOp scrutinee T.BEq (T.EId $ tiNullLoc ptrinfo))
                cIntZero
                (T.EIfThenElse
                   (T.EBinOp scrutinee T.BEq (T.EId $ tiUnknownLoc ptrinfo))
                   cIntUnknown
                   cIntOne)
            VoidStarType _ ->
              return $ T.EApp (T.EId $ T.Fixed "lnot")
                          [T.EApp (T.EId voidStarNullTest) [T.EId condVal]]
            _ -> implicitConvert p scrutinee btyp (IntType internal)
        thenBranch <- if null vs1 then return (T.EId thenTid) else
           stmtLambda $ \vmap'' pid'' k -> do
              thenState <- removeVarsFromState p (T.EId vmap'') vs1
              return $ T.EApp (T.EId thenTid) [thenState,T.EId pid'',T.EId k]
        elseBranch <- if null vs2 then return (T.EId elseTid) else
           stmtLambda $ \vmap'' pid'' k -> do
              elseState <- removeVarsFromState p (T.EId vmap'') vs2
              return $ T.EApp (T.EId elseTid) [elseState,T.EId pid'',T.EId k]
        return $ T.EApp (T.EId (T.Fixed "ifthenelseProc"))
                    [tcondInt,thenBranch,elseBranch, T.EId vmap',T.EId pid',kr]
      return $ T.EApp tcond [T.EId vmap, T.EId pid, innerLam]
    S.IReturn p vs me -> expInnerLambda $ \vmap pid _ -> do
      -- When returning a value e of the right type: 
      --          \st pid k -> [e] (st,pid,kr)
      -- When returning a value e with an implicit type conversion:
      --          \st pid k -> [e] (st,pid,\st',pid',ev -> kr (st',pid',"conv" ev))
      -- When returning from void function:   \st k -> kr (st,Unit)
      case me of
        Nothing -> return $ T.EApp kr [T.EId vmap, T.EId pid, cspUnit]
        Just e  -> do
          (et,rtyp') <- transExp e
          returnCont <- 
            if rtyp == rtyp' then return kr
            else expInnerLambda $ \st' pid' ev -> do
                   ev' <- implicitConvert p (T.EId ev) rtyp' rtyp
                   st'' <- removeVarsFromState p (T.EId st') vs
                   return $ T.EApp kr [st'',T.EId pid',ev']
          return $ T.EApp et [T.EId vmap, T.EId pid, returnCont]

removeVarsFromState :: S.SPos -> T.Exp -> [S.Id] -> CG T.Exp
removeVarsFromState spos sids outere =
  foldM removeVarFromState sids outere
  where
    removeVarFromState :: T.Exp -> S.Id -> CG T.Exp
    removeVarFromState e sid = do
      mLoc <- lookupLocalVar sid
      case mLoc of
        Nothing -> failPos spos $
             "Internal error: out-of-scope or non-local var "
          ++ show sid 
          ++ " is removed from state."
        Just (LInfo {ltid,ltype}) -> do
          tinfo <- lookupTypeInfo ltype
          return $ T.EApp (T.EId $ tiLocalsDelete tinfo) [e, T.EId ltid]


-- transGraph does the work of actually pulling apart the graph representation
-- of function and translating its nodes.
transGraph :: S.Proc a -> CG [T.Definition]
transGraph p@(S.Proc {S.procDecln=FInfo {fret,ftid},
                      S.procEntry, S.procBody, S.procLocations}) =
  mapM transBlock blocks
  where
--    blocks :: [Block (S.AInsn a) C C]
    blocks = 
      case procBody of
        GMany NothingO body NothingO -> 
          postorder_dfs_from body procEntry

    -- transBlock translates a single basic block from a function.  the result
    -- is a top-level CSPm function which takes three arguments (the local state
    -- map, the process ID, and a return continuation for the outer function).
    transBlock :: Block (S.AInsn a) C C -> CG T.Definition
    transBlock block = do
      blockStateId <- freshLocalNew "blockState"
      blockPIDId   <- freshLocalNew "blockPID"
      blockContId  <- freshLocalNew "blockCont"
      tid <- lookupLoc entryLbl procLocations (S.failProc p)
      let texit = transExitNode exitNode (T.EId blockContId, fret) ftid procLocations
      tbody <- transInnerNodes bodyNodes blockStateId blockPIDId texit
      return $ T.DFun tid
                      [([T.PId blockStateId,T.PId blockPIDId,
                         T.PId blockContId],
                        tbody)]
      where
        entryNode :: S.Insn C O
        exitNode :: S.Insn O C
        bodyNodes :: [S.Insn O O]
        (aEntryNode,aBodyBlock,aExitNode) = blockSplit block
        entryNode = S.getInsn aEntryNode
        bodyNodes = map S.getInsn $ blockToList aBodyBlock
        exitNode  = S.getInsn aExitNode
        
        entryLbl :: Label
        S.ILabel _ entryLbl = entryNode
        
-- The translation of every C function take three extra arguments.
--
-- The first extra argument is the current local variable state.  This state
-- also contains any local variables that were in scope at the call site -
-- even though the function will not be able to directly refer to local
-- variables in scope at the call site, the function might be passed pointer
-- arguments that refer to these variables.  Thus, the local state at the call
-- site is needed in the function
--
-- The second extra argument is a process ID, indicating which process is
-- invoking this function.
--
-- The third extra argument is a continuation.  This tells us what to do when
-- the function returns.  The continuation has type
--
--    (VarMap,PID,a) -> Proc.
-- 
-- Here, VarMap is the type we are using for the local state map.  The
-- continuation must be passed this, because the function could have updated it
-- in the case where the function is passsed pointers to local variables.  The
-- process ID is also necessary, since the function make fork new processes.
-- "a" is the translation of the function's return type.  In the case of a
-- function with a void return type, we use Unit.
--
-- Function arguments are a particular complication.  In general, we don't use
-- CSPm variables to represent C variables.  Instead, C variables are
-- translated as tags that are looked up in the local state map.  So, we can't
-- just use CSPm function parameters directly to model C function parameters,
-- because in the body of the function these look like local variables.  What
-- we do is to add some extra code at the top of each translated function
-- which sticks any passed arguments into the local state map, where the body
-- of the function can access them.
--
-- An alternative would be to remove all the original function arguments and
-- require that before a function is called the values of its arguments are
-- added to the local state map (just like how C function arguments are
-- actually just pushed onto the stack).  This would probably be slightly
-- conceptually cleaner, but it has the substantial disadvantage of making our
-- handwritten runtime functions much more inconvenient to write.
--
-- So, in summary, we have:
--
--       t foo (t1 x1, ... , tn xn) { s }
--   ~~> foo(x1_arg,...,xn_arg,st,pid,kr) = 
--            (transGraph s kr) (st {x1 = x1_arg,...,xn = xn_arg})
--
-- XXX when delete gets added to FDR3, the translation of a function should
-- remove its arguments from the statemap that it passes to the continuation.
transProc :: S.Proc a -> CG [T.Definition]
transProc pr@(S.Proc {S.procDecln=FInfo {ftid},
                      S.procArgs, S.procEntry, S.procLocations}) = do
  -- stateArgNames are the names we use in the state map.  fargs are the names
  -- we use as function parameters.  The state we pass to the function body
  -- binds the former to the values of the latter.
  stateArgNames <- mapM (uncurry freshLocal) procArgs
  fargs <- mapM (\(sid,bt) -> (,bt) <$> freshLocalNew (S.stringPart sid)) procArgs
  argState <- freshLocalNew "funState"
  argPid   <- freshLocalNew "funPID"
  argCont  <- freshLocalNew "funCont"
  tblocks  <- transGraph pr

  -- The top-level CSP function updates the state map it is passed with the
  -- function's arguments, then goes to the entry block of the function.
  argInfos <- zipWithM (\xSt (xArg,btype) -> do
                         tinfo <- lookupTypeInfo btype
                         return $ (xSt,xArg,tinfo))
                       stateArgNames fargs
  entryTid <- lookupLoc procEntry procLocations (S.failProc pr)
  let updatedState =
        foldl' (\curSt (xSt,xArg,tinfo) ->
                   T.EApp (T.EId $ tiLocalsUpdate tinfo)
                     [curSt, T.EId xSt, T.EId xArg])
               (T.EId argState) argInfos
      body = T.EApp (T.EId entryTid) [updatedState,T.EId argPid,T.EId argCont]
  clearLocalState
  mapM squashDef $ (T.DFun ftid
          [(map T.PId $ map fst fargs ++ [argState,argPid,argCont],
            body)])
      : tblocks


-- Takes, as an argument, a strategy for generating values for uninitialized
-- subparts (which should be 0 in global scope and undefined in local scope).
transInitializer :: BaseType -> S.Initializer -> (BaseType -> CG T.Exp)
                 -> S.SPos -> CG T.Exp
transInitializer ty1 (S.SimpleInitializer e) _ sp = 
  case constish e of
    Just c  ->
      do (tc,ty2) <- transConst c sp
         implicitConvert sp tc ty2 ty1
    Nothing -> failPos sp $ "Unsupported: non-constant initializer"
  where
    constish :: S.Exp -> Maybe S.Const
    constish (S.ConstExp c _) = Just c
    constish (S.Cast _ e' _)  = constish e'
    constish _                = Nothing
transInitializer ty1 (S.ListInitializer li) uninit sp =
  case ty1 of
    -- "PointerType" should correspond to an array in this context.  We return
    -- the unknown location because we are not explicitly modeling arrays.
    PointerType _ ty1' _ -> do
      tinfo <- lookupTypeInfo ty1'
      return $ T.EId $ tiUnknownLoc tinfo

    StructType _ _ ->  do
      tinfo <- lookupTypeInfo ty1
      case tinfo of 
        TypeInfo {tiDataInfo=Left (StructInfo {siConName,siFields})} -> 
          T.EDot (T.EId siConName) <$> mapM (chooseExp li) siFields
            where 
              -- retrieves an expression via the initializer list or an 
              -- uninitialized expression for the member field
              chooseExp :: [([S.InitDesignator],S.Initializer)] -> FieldInfo -> CG T.Exp
              chooseExp [] fi = uninit $ fiType fi
              chooseExp (([S.MemberDesig md _],ini):lis) fi = do
                if md == fiSourceName fi then 
                  transInitializer (fiType fi) ini uninit sp 
                else 
                  chooseExp lis fi
              chooseExp _ fi = do
                addWarning "Unsupported initdesignator"
                  $ "Warning: Discarding initializer at " ++ show sp
                uninit $ fiType fi

        _ -> failBase ty1 $ "Internal Error: struct has no StructInfo."

    -- Also need to add support for unions
    _ -> failPos sp $ "Unsupported: Initializers for objects of type "
                   ++ ppBaseType ty1
    
baseTypeToType :: BaseType -> CG T.Type
baseTypeToType bt = T.TData . tiRepType <$> lookupTypeInfo bt


-----------------------------------------------------------------------------
--------- Uninitialized State
-----------------------------------------------------------------------------

-- According to K&R, uninitialized variables are handled differently depending
-- on whether they are global or local.  The memory corresponding to an
-- uninitialized global is zeroed out, while an uninitialized local may
-- contain garbage data.
--
-- We represent uninitialized globals using a combination of "zeroes" and
-- null locations.
--
-- We represent uninitialized locals using the "unknown" C value in the model.
uninitializedGlobal :: BaseType -> CG T.Exp
uninitializedGlobal (IntType _)   = return cIntZero
uninitializedGlobal (BoolType _)  = return cBoolFalse
uninitializedGlobal (FloatType _) = return cFloatUnknown
                                    -- I think this is known to bo Zero.  Am I unsound? XXX
uninitializedGlobal bt@(StructType _ _) = do
  tinfo <- lookupTypeInfo bt
  case tinfo of
    TypeInfo {tiDataInfo=Left (StructInfo {siConName,siFields})} ->
      T.EDot (T.EId siConName) <$> mapM (uninitializedGlobal . fiType) siFields
    _ -> failBase bt $ "Internal Error: translation of struct has no structinfo."
uninitializedGlobal (PointerType _ bt _) = do
  tinfo <- lookupTypeInfo bt
  return $ T.EId $ tiNullLoc tinfo
uninitializedGlobal (MutexType _)     = return uninitializedMutex
  -- Technically the pid is known to be 0, but unknown here is sound.
uninitializedGlobal (PIDType _)       = return $ T.EDot (T.EId pidUnknownCon) []
uninitializedGlobal (VoidStarType _)  = return $ T.EDot (T.EId voidStarNullCon) []
uninitializedGlobal t = fail $ "Internal Error: uninitializedGlobal "
                            ++ "called on unsupported type " ++ ppBaseType t 
                            ++ "."

uninitializedLocal :: BaseType -> CG T.Exp
uninitializedLocal (IntType _)   = return cIntUnknown
uninitializedLocal (BoolType _)  = return cBoolUnknown
uninitializedLocal (FloatType _) = return cFloatUnknown
uninitializedLocal bt@(StructType _ _) = do
  tinfo <- lookupTypeInfo bt
  case tinfo of
    TypeInfo {tiDataInfo=Left (StructInfo {siConName,siFields})} ->
      T.EDot (T.EId siConName) <$> mapM (uninitializedLocal . fiType) siFields
    _ -> failBase bt $ "Internal Error: translation of struct has no structinfo."
uninitializedLocal (PointerType _ bt _) = do
  tinfo <- lookupTypeInfo bt
  return $ T.EId $ tiUnknownLoc tinfo
uninitializedLocal (MutexType _)    = return uninitializedMutex
uninitializedLocal (PIDType _)      = return $ T.EDot (T.EId pidUnknownCon) []
uninitializedLocal (VoidStarType _) = return $ T.EDot (T.EId voidStarUnknownCon) []
uninitializedLocal t = fail $ "Internal Error: uninitializedLocal "
                            ++ "called on unsupported type " ++ ppBaseType t 
                            ++ "."

-----------------------------------------------------------------------------
----------- Stubs
-----------------------------------------------------------------------------

-- It is convenient to define "stubs" for functions that are declared but not
-- defined.  These are CSPm functions that accept the right number of
-- arguments and always return the "unknown" value of the appropriate type.
-- Note that these are unsound models, since they fail to account for any of
-- the effects of the actual functions.

stubOut :: FInfo -> CG T.Definition
stubOut (FInfo {ftid,fargs,fret,fdef}) = do
  undefinedRet <- 
    case fret of
      -- "unknown type" corresponds to void, in this case.
      -- XXX add proper void type.  This is realllllly rickety.
      (UnknownType _) -> return cspUnit
      (PointerType _ (UnknownType _) _) -> return cspUnit
      _ -> uninitializedLocal fret
  when fdef $ fail $
     "Internal Error: stubOut called on defined function " ++ T.namePart ftid
  st <- freshLocalNew "stubState"
  pid <- freshLocalNew "stubPID"
  k <- freshLocalNew "stubCont"
  return $ 
    T.DFun ftid
           [(map T.PId $ 
               (replicate (length fargs) (T.Fixed "_")) ++ [st,pid,k],
             T.EApp (T.EId k) [T.EId st, T.EId pid,undefinedRet])]
              
-----------------------------------------------------------------------------
----------- Memory model
-----------------------------------------------------------------------------

-- Here we define the various CSP components that represent the memory of a C
-- program, along with a number of helper accessor functions in CSP to make
-- other aspects of code generation easier.
--
-- Most of these functions are assumed to run after all the code has been
-- translated, and rely on the state that has been accumulated in the monad
-- during that process.


-- Rather than extracting all of the variable state from the monad in each
-- definition, we do this once and pass it around:
data TypeVars = TypeVars {tvGlobals :: [(T.Id,T.Exp)], -- it and init val
                          tvLocals  :: [T.Id],
                          tvArrays  :: [ArrayLocs]}

-- We use a list instead of a Map here becuse the ordering is important.
type MemInfo = [(TypeInfo,TypeVars)]


-- Run through the accumulated state and build the meminfo
createMemInfo :: CG MemInfo
createMemInfo = do
  globals  <- map snd <$> allGlobals
  locals   <- allLocals
  typinfs  <- allTypeInfos
  arrays   <- allArrays

  -- globalInits :: [(BaseType,T.Id,T.Exp)]
  -- Is a list of every global variable and its initial value.
  globalInits <- 
    let findGlobalInit :: GlobInfo -> CG (BaseType,T.Id,T.Exp)
        findGlobalInit gi@(GInfo {gtid,gtype,ginit}) = do
          -- This first bit is just for good error messages
          case gtype of
            FunctionType _ -> 
                failGlob gi $ "Global variables of function types are unsupported ("
                           ++ show gtid ++ ")"
            UnknownType _  -> 
                failGlob gi $ "Global variables of unknown types are unsupported ("
                           ++ show gtid ++ ")"
            ChannelType _  ->
                failGlob gi $ "Global variables of channel types are unsupported ("
                           ++ show gtid ++ ")"
            _ -> return ()
          initial <- case ginit of
                       Nothing -> uninitializedGlobal gtype
                       Just i  -> return i
          return (gtype,gtid,initial)
    in mapM findGlobalInit globals
  let groupedGlobals :: [(BaseType,[(T.Id,T.Exp)])]
      groupedGlobals = M.toList $
        foldl' (\m (bt,tid,tinit) ->
                   case M.lookup bt m of
                     Nothing  -> M.insert bt [(tid,tinit)] m
                     Just gvs -> M.insert bt ((tid,tinit):gvs) m)
                M.empty globalInits
  let groupedLocals :: [(BaseType,[T.Id])]
      groupedLocals = M.toList $
        foldl' (\m (LInfo {ltid,ltype}) ->
                   case M.lookup ltype m of
                     Nothing  -> M.insert ltype [ltid] m
                     Just gvs -> M.insert ltype (ltid:gvs) m)
               M.empty locals

  -- Build a (M.Map TypeInfo TypeVars) with just info about the globals.
  minfoGlobals <-
    foldM (\m (bt,tvGlobals) -> do
              tinfo <- lookupTypeInfo bt
              return $ M.insert tinfo (TypeVars {tvGlobals,tvLocals = [],
                                                 tvArrays = []}) m)
          M.empty groupedGlobals

  -- Add the info about locals to the previous map
  minfoAllVars <-
    foldM (\m (bt,tvLocals) -> do
             tinfo <- lookupTypeInfo bt
             return $
               case M.lookup tinfo m of
                 Nothing  ->
                   M.insert tinfo (TypeVars {tvLocals,tvGlobals=[],
                                             tvArrays = []}) m
                 Just tvs ->
                   M.insert tinfo (tvs {tvLocals}) m)
          minfoGlobals groupedLocals

  -- Add info about arrays to the previous map
  let minfoVarsAndArrays =
        M.mapWithKey (\(TypeInfo {tiBase}) tvs ->
                          tvs {tvArrays=fromMaybe [] (lookup tiBase arrays)})
                     minfoAllVars

  -- This last step just makes an entry for declared types which have no
  -- corresponding variables.
  let minfoMap =
        foldl' (\m ti -> case M.lookup ti m of
                           Nothing -> M.insert ti (TypeVars [] [] []) m
                           Just _  -> m)
               minfoVarsAndArrays typinfs
  return $ M.toList minfoMap
  
-- The current state of local variables is stored in a collection of maps,
-- organized by the type of the variable.  These maps are bundled together into
-- the "LocalState" type.  This defines that type, as well as an initial, empty
-- LocalState.
--
-- One hitch is that we need to be able to find the map corresponding to a
-- particular type.  The best thing would be to use some kind of record, but
-- CSPm doesn't have them.  Instead, we bless the randomish ordering of our
-- computed MemInfo - the nth type in the typedLocals list corresponds to the
-- nth argument to the LocalState constructor.  This means we need MemInfo
-- whenever we're building local variable accessors, and also that we should be
-- careful not to reorder the list in MemInfo.
buildLocalState :: MemInfo -> [T.Definition]
buildLocalState minfo =
  [T.DDataType localStateType
     [(localStateCon,
         map (\TypeInfo {tiLocalLocType,tiRepType} ->
                   T.EApp (T.EId $ T.Fixed "Map")
                      [T.EDot (T.EId tiLocalLocType) [], T.EDot (T.EId tiRepType) []])
             localTypes)],
   T.DVar (T.PId localStateEmpty)
          (T.EDot (T.EId localStateCon) $ replicate (length localTypes)
                                             (T.EId $ T.Fixed "emptyMap"))]
  where
    localTypes :: [TypeInfo]
    localTypes = [tinfo | (tinfo,TypeVars {tvLocals}) <- minfo,
                          not $ null tvLocals]

-- buildLocations builds the datatypes representing the memory locations.
--
-- For each type, we build two datatypes of addresses: one represents all the
-- local variables of this type in the program, and the other all the globals.
--
--   data FooLocals  = Foo_x | Foo_y | ... 
--   data FooGlobals = Foo_z1 | Foo_z2 | ...
--
-- These list a unique address for every local and global of the appropriate
-- type.
--
-- A location of a particular type is either null, unknown, or one of these
-- locals or globals.  So for each type we build a location data type, e.g.:
--
--   data FooLoc = FooLoc_Null | FooLoc_Unknown
-- .             | FooLocal FooLocals | FooGlobal FooGlobals
--
-- In the special case that there are no locals or no globals of this type, we
-- do not define FooLocals/FooGlobals, and omit the relevant constructors from
-- FooLoc.
buildLocations :: MemInfo -> [T.Definition]
buildLocations minfo =
    concatMap (\p -> allLocations p : buildLocLists p) minfo
  where
    buildLocLists :: (TypeInfo,TypeVars)
                  -> [T.Definition]
    buildLocLists (TypeInfo {tiLocalLocType,tiGlobalLocType},
                   TypeVars {tvGlobals,tvLocals}) =
      catMaybes $
        [if null tvLocals then Nothing
           else Just (T.DDataType tiLocalLocType localCons),
         if null tvGlobals then Nothing
           else Just (T.DDataType tiGlobalLocType globalCons)]
      where
        localCons = map (,[]) tvLocals
        globalCons = map ( (,[]) . fst ) tvGlobals

    allLocations :: (TypeInfo,TypeVars) -> T.Definition
    allLocations (tinfo,TypeVars {tvLocals,tvGlobals}) = 
      T.DDataType (tiLocType tinfo) $
          (tiNullLoc tinfo,[]) 
        : (tiUnknownLoc tinfo,[]) 
        : (if null tvLocals then [] else [localCon])
       ++ (if null tvGlobals then [] else [globalCon])
      where
        localCon = (tiLocalLocTag tinfo,[T.EDot (T.EId $ tiLocalLocType tinfo) []])
        globalCon = (tiGlobalLocTag tinfo,[T.EDot (T.EId $ tiGlobalLocType tinfo) []])

-- buildVoidStarRep builds the representation of C data of type void*.  In
-- particular, void* is modeled as a tagged union of all the location types.
-- Additionally:
--
--  - for each individual type, we build a function that projects out of this
--    union into locations for that type (if the wrong tag is encountered it
--    returns the "unknown" value, which I believe is sound).
--
--  - Our model of void* is a bit messy in that there are many different
--    representations of the null pointer (since each individual type has its
--    own null pointer in the model).  We define a "is_null" helper function to
--    check if a pointer is null.
buildVoidStarRep :: MemInfo -> CG [T.Definition]
buildVoidStarRep minfo = do
  injections <- voidStarInjections
  projections <- voidStarProjections
  return $ voidStarRep : voidStarIsNull : injections ++ projections
  where
    voidStarRep :: T.Definition
    voidStarRep = T.DDataType voidStarRepType $
        (voidStarNullCon,[])
      : (voidStarUnknownCon,[])
      : concatMap tinfoCons minfo
      where
        tinfoCons :: (TypeInfo,TypeVars) -> [(T.Id,[T.Exp])]
        tinfoCons (tinfo,tv) = catMaybes
          [if null (tvLocals tv) then Nothing else Just
             (tiVoidStarLTag tinfo, [T.EId $ tiLocalLocType tinfo]),
           if null (tvGlobals tv) then Nothing else Just 
             (tiVoidStarGTag tinfo, [T.EId $ tiGlobalLocType tinfo])]

    -- For each type, we build a projection from the tagged union of all locations.
    -- For example, for a type Foo:
    --
    -- fooVoidStarProj :: VoidStarRep -> FooLocType
    -- fooVoidStarProj (FooVoidStarLTag.t) = FooLocalLocTag.t
    -- fooVoidStarProj (FooVoidStarGTag.t) = FooGlobalLocTag.t
    -- fooVoidStarProj VoidStarNull = FooNullLoc
    -- fooVoidStarProj _ = FooUnknownLoc
    --
    -- The only hitch is that we shouldn't generate the local or globals case in
    -- the event there aren't variables of those kinds for this type.
    voidStarProjections :: CG [T.Definition]
    voidStarProjections = do
      locBndr <- freshLocalNew "loc"
      return $ map (voidStarProjection locBndr) minfo

    voidStarProjection :: T.Id -> (TypeInfo,TypeVars) -> T.Definition
    voidStarProjection bndr (tinfo,tv) = T.DFun (tiVoidStarProj tinfo)$ 
      catMaybes
        [if null (tvLocals tv) then Nothing else Just
           ([T.PDot (T.PId $ tiVoidStarLTag tinfo) [T.PId bndr]],
            T.EDot (T.EId $ tiLocalLocTag tinfo) [T.EId bndr]),
         
         if null (tvGlobals tv) then Nothing else Just
           ([T.PDot (T.PId $ tiVoidStarGTag tinfo) [T.PId bndr]],
            T.EDot (T.EId $ tiGlobalLocTag tinfo) [T.EId bndr]),
  
         Just ([T.PId voidStarNullCon],T.EId $ tiNullLoc tinfo),
  
         Just ([T.PId (T.Fixed "_")], T.EId $ tiUnknownLoc tinfo)]

    -- For each type, we build an injection from the tagged union of all
    -- locations.  For example, for a type Foo:
    --
    -- fooVoidStarInj :: FooLocType -> VoidStarRep
    -- fooVoidStarInj FooNullLoc          = VoidStarNullCon
    -- fooVoidStarInj FooUnknownLoc       = VoidStarUnknownCOn
    -- fooVoidStarInj (FooGlobalLocTag.l) = FooVoidStarGTag.l
    -- fooVoidStarInj (FooLocalLocTag.l)  = FooVoidStarLTag.l
    --
    -- The only hitch is that we shouldn't generate the local or globals case in
    -- the event there aren't variables of those kinds for this type.
    voidStarInjections :: CG [T.Definition]
    voidStarInjections = do
      locBndr <- freshLocalNew "loc"
      return $ map (voidStarInjection locBndr) minfo

    voidStarInjection :: T.Id -> (TypeInfo,TypeVars) -> T.Definition
    voidStarInjection bndr (tinfo,tv) = T.DFun (tiVoidStarInj tinfo) $
      catMaybes 
        [Just ([T.PId $ tiNullLoc tinfo],T.EId voidStarNullCon),
  
         Just ([T.PId $ tiUnknownLoc tinfo],T.EId voidStarUnknownCon),
  
         if null (tvGlobals tv) then Nothing else Just
           ([T.PDot (T.PId $ tiGlobalLocTag tinfo) [T.PId bndr]],
            T.EDot (T.EId $ tiVoidStarGTag tinfo) [T.EId bndr]),
  
         if null (tvLocals tv) then Nothing else Just
           ([T.PDot (T.PId $ tiLocalLocTag tinfo) [T.PId bndr]],
            T.EDot (T.EId $ tiVoidStarLTag tinfo) [T.EId bndr])]
          
    -- This functions checks if an element of the void union is null.
    -- It looks like:
    --
    -- void_is_null :: VoidStarRep -> CInt
    -- void_is_null VoidStarNullCon     = CInt.1
    -- void_is_null VoidStarUnknownCon  = CIntUnknown
    -- void_is_null _                   = CInt.0

    voidStarIsNull :: T.Definition
    voidStarIsNull = T.DFun voidStarNullTest 
      [([T.PId voidStarNullCon],cIntOne),
       ([T.PId voidStarUnknownCon],cIntUnknown),
       ([T.PId (T.Fixed "_")],cIntZero)]

-- buildCspChannels builds the CSP channel declarations that list all the
-- channels we'll use to read and write to global variables.  Types for which
-- there are no global variables do not get channels.
--
-- For example, for a struct like:
--   
--   struct foo {int x;}
-- 
-- This builds the channels:
--
-- channel foo_read    : PIDTyp.Foo_GLoc.Foo_Typ
-- channel foo_write   : PIDTyp.Foo_GLoc.Foo_Typ
-- channel foo_x_read  : PIDTyp.Foo_GLoc.CValTyp
-- channel foo_x_write : PIDTyp.Foo_GLoc.CValTyp
--
-- These channels permit reading or writing the whole struct or any subfield
-- of the struct.  The first PIDTyp argument is a process ID.
--
-- The monad is used here only to look up the TypeInfo associated with the
-- BaseTypes of any subfields.
buildCspChannels :: MemInfo -> CG [T.Definition]
buildCspChannels minfo =
  concat <$> mapM typChans minfo
  where
    -- type communicated over the channel (e.g., PIDTyp.Foo_GLoc.Foo_Typ)
    chanArgs :: TypeInfo -> [T.Type]
    chanArgs tinfo = [T.TData pidTypId,
                      T.TData (tiGlobalLocType tinfo),
                      T.TData (tiRepType tinfo)]

    -- The channels for reading and writing subfields
    fieldChans tinfo (FieldInfo {fiReaderChan=fr,
                                 fiWriterChan=fw,
                                 fiSubfields=fsubs,
                                 fiType=binfo}) = do
       typ <- baseTypeToType binfo
       subs <- concat <$> mapM (fieldChans tinfo) fsubs
       return $
         [T.DChan [fr] [T.TData pidTypId,
                        T.TData (tiGlobalLocType tinfo),
                        typ],
          T.DChan [fw] [T.TData pidTypId,
                        T.TData (tiGlobalLocType tinfo),
                        typ]]
         ++ subs

    typChans :: (TypeInfo,TypeVars) -> CG [T.Definition]
    typChans (_,TypeVars {tvGlobals=[]}) = return []
    typChans (tinfo,_) = do
      fldChans <- 
        case tiDataInfo tinfo of
          Right _ -> return []
          Left (StructInfo {siFields}) ->
             concat <$> mapM (fieldChans tinfo) siFields
      return $
           [T.DChan [tiReaderChan tinfo] (chanArgs tinfo)
           ,T.DChan [tiWriterChan tinfo] (chanArgs tinfo)]
        ++ fldChans

-- dataPattern is a useful helper function that builds a CSPm pattern which
-- binds all the fields of the datatype corresponding to a C
-- struct.  For example, consider the C declarations:
--
-- struct Bar {
--   int z;
-- }
--
-- struct Foo {
--   int x;
--   struct Bar y;
-- }
--
-- In this case, calling dataPattern on the representation of Bar creates the
-- pattern:
--
--    Bar.z
--
-- And calling dataPattern on the representation of Foo creates the pattern:
--
--    Foo.x.(Bar.z)
--
-- We represent the patterns using this simple datatype.  The (T.Id,T.Id)
-- pairs are meant to be the names of the reader and writer channels.
data Pattern = PVar T.Id            
             -- A leaf of the struct, with a fresh name to use for binding
             | PData T.Id [(FieldInfo,Pattern)]

-- Takes a pattern turns it into a CSP Pat like "Foo.x.(Bar.z)", suitable for
-- use as a binder pattern
patternToPat :: Pattern -> T.Pat
patternToPat (PVar vnm) = T.PId vnm
patternToPat (PData constructor fields) = 
  T.PDot (T.PId constructor) $ map (patternToPat . snd) fields

-- Takes a pattern turns it into a CSP Exp like "Foo.x.(Bar.z)".
patternToExp :: Pattern -> T.Exp
patternToExp (PVar vnm) = T.EId vnm
patternToExp (PData constructor fields) = 
  T.EDot (T.EId constructor) $ map (patternToExp . snd) fields

dataPattern :: StructInfo -> CG Pattern
dataPattern (StructInfo {siConName,siFields}) =
  fieldPatterns siFields [] $ \subfields -> return $ PData siConName subfields
  where
    fieldPatterns :: [FieldInfo] -> [(FieldInfo,Pattern)] 
                  -> ([(FieldInfo,Pattern)] -> CG a) -> CG a
    fieldPatterns [] pats f = f $ reverse pats
    fieldPatterns (finfo@FieldInfo {fiSourceName,fiTargetNameHint,
                                    fiSubfields,fiType} : fis)
                  pats f = do
      TypeInfo {tiDataInfo} <- lookupTypeInfo fiType
      case (tiDataInfo,null fiSubfields) of
        (Right _, True) -> do
          tid <- freshLocalNew fiTargetNameHint
          fieldPatterns fis ((finfo,PVar tid) : pats) f
        (Left sinfo, False) -> do
          pat <- dataPattern (sinfo {siFields = fiSubfields})
          fieldPatterns fis ((finfo,pat) : pats) f
        -- There is a little trick here: we looked up the TypeInfo
        -- corresponding to this field of the struct, but we replace the
        -- subfields of its StructInfo.  The reason is that we use
        -- _different_ field names when a struct appears at the top level vs
        -- when it appears as a subfield.

        (Right _, False) -> fail $ 
              "Internal Error in building pattern for struct "
           ++ show siConName ++ ".  The representation of field " 
           ++ show fiSourceName ++ " has subfields, but its type does not."
        (Left _, True) -> fail $ 
              "Internal Error in building pattern for struct "
           ++ show siConName ++ ".  The representation of field " 
           ++ show fiSourceName ++ " has no subfields, but its type does."

-- varCellBuilders constructs, for each type, a CSPm function that builds
-- global variable cells of that type.  The function has type:
--
--     Typ_VAR :: (tiGlobalLocType tinfo) -> (tyRepType tinfo) -> Proc
--
-- which builds process representing a global variable of the appropriate
-- type.  Once again, we only do this for types which have global variables.
buildVarCellBuilders :: MemInfo -> CG [T.Definition]
buildVarCellBuilders minfo =
  mapM buildChan [ti | (ti,TypeVars {tvGlobals}) <- minfo, not (null tvGlobals)]
  where
    -- This is a wrapper for dataPattern, additionally handling the case where
    -- we're building a var cell for a base type and not a struct.
    buildPattern :: TypeInfo -> CG Pattern
    buildPattern (TypeInfo {tiDataInfo}) =
      case tiDataInfo of
        Right s -> PVar <$> freshLocalNew s
        Left sinfo -> dataPattern sinfo


    buildChan :: TypeInfo -> CG T.Definition
    buildChan tinfo@(TypeInfo {tiVarCellBuilder}) = do
      topPattern <- buildPattern tinfo
      vLoc <- freshLocalNew "vLoc"
      let
        -- the top pattern, converted to a pat
        topPat :: T.Pat
        topPat = patternToPat topPattern

        topExp :: T.Exp
        topExp = patternToExp topPattern

        -- builds the reader/writer pair for a particular field, given the
        -- pattern corresponding to that field.
        rwPrefixRecurse :: (T.Id,T.Id) -> Pattern -> [T.Exp]
        rwPrefixRecurse (rdrChan,wtrChan) pat =
          [readerOrWriter rdrChan (T.CFOutput $ patternToExp pat),
           readerOrWriter wtrChan (T.CFInput $ patternToPat pat)]
          where
            -- reader?_!loc!data -> VAR(loc,topExp)
            -- or
            -- writer?_!loc?data -> VAR(loc,topExp)   (where topExp mentions the vars of data)
            readerOrWriter :: T.Id -> T.CommField -> T.Exp
            readerOrWriter cname cf =
              T.EPrefix (T.EId cname)
                 [T.CFInput (T.PId $ T.Fixed "_"), -- XXX ignored process ID
                  T.CFOutput (T.EId vLoc),
                  cf]
                 (T.EApp (T.EId tiVarCellBuilder) [T.EId vLoc,topExp])
  
        -- This builds all the readers and writers associated with a
        -- pattern.
        patRWs :: (T.Id,T.Id) -> Pattern -> [T.Exp]
        patRWs rwChans pat@(PVar _) = rwPrefixRecurse rwChans pat
        patRWs rwChans pat@(PData _ fields) = 
             rwPrefixRecurse rwChans pat 
          ++ concatMap (\(finfo,fpat) -> patRWs (fiReaderChan finfo,
                                                 fiWriterChan finfo) fpat)
                       fields
      return $ T.DFun tiVarCellBuilder
         -- VAR(loc,D.x.(C.y.z)) =
         --     reader?_!loc!D.x.(C.y.z) -> VAR(loc,D.x.(C.y.z))
         --  [] writer?_!loc?D.x.(C.y.z) -> VAR(loc,D.x.(C.y.z))
         --  [] reader_x?_!loc!x         -> VAR(loc,D.x.(C.y.z))
         --  [] writer_x?_!loc?x         -> VAR(loc,D.x.(C.y.z))
         --  [] reader_C?_!loc!C.y.z     -> VAR(loc,D.x.(C.y.z))
         --  [] writer_C?_!loc?C.y.z     -> VAR(loc,D.x.(C.y.z))
         --  [] reader_C_y?_!loc!y       -> VAR(loc,D.x.(C.y.z))
         --  [] writer_C_y?_!loc?y       -> VAR(loc,D.x.(C.y.z))
         --  [] ...
          [([T.PId vLoc, topPat],
            foldl1' (\cell rw -> T.EExtChoice cell rw) 
                    (patRWs (tiReaderChan tinfo, tiWriterChan tinfo)
                            topPattern))]


-- buildTypedMemory builds a CSP process representing all the memory
-- associated with data of a particular type.  This process is just:
-- 
--   Foo_VAR(nm1,init1) ||| ... ||| Foo_VAR(nmk,initk)
-- 
-- for each global variable of type Foo.
--
-- XXX would it be more efficient to do this with renaming?
buildTypedMemory :: MemInfo -> [T.Definition]
buildTypedMemory minfo = 
  mapMaybe buildTypMem $ map (\(ti,tvs) -> (ti,tvGlobals tvs)) minfo
  where
    buildTypMem :: (TypeInfo,[(T.Id,T.Exp)]) -> Maybe T.Definition
    buildTypMem (_,[])     = Nothing
    buildTypMem (TypeInfo {tiVarCellBuilder,tiVarCells},gvars) =
        Just $ T.DVar (T.PId tiVarCells) (buildCells gvars)
      where
        buildCells :: [(T.Id,T.Exp)] -> T.Exp
        buildCells [] = error "INTERNAL ERROR: buildCells on empty list"
        buildCells [(gv,gi)] =
          T.EApp (T.EId tiVarCellBuilder) [T.EDot (T.EId gv) [],gi]
        buildCells ((gv,gi):gs) =
          T.EInterleave
            (T.EApp (T.EId tiVarCellBuilder) [T.EDot (T.EId gv) [],gi])
            (buildCells gs)


-- memoryProcs comprises three convenient CSPm definitions related to running
-- processes in memory.
--
-- The first, MEMORY, is the interleaving of all the memory cells together.
--
-- The second, runInMemory, runs another process in generalized parallel
-- with memory, allowing them to interact only on reads and writes. 
--
-- The third, hideMemory, hides any communications related to global memory in a
-- process.
memoryProcs :: MemInfo -> [T.Definition]
memoryProcs minfo =
 [ T.DVar (T.PId memoryName) $ buildMemory tinfosWithVars,
   T.DFun runInMemoryName
          [([T.PId $ T.Fixed "procToRun"],runInMemory)],
   T.DFun hideMemoryName
          [([T.PId $ T.Fixed "procToRun"],hideMemory)]
 ]
 where
   tinfosWithVars :: [TypeInfo]
   tinfosWithVars = [ti | (ti,TypeVars {tvGlobals}) <- minfo, not (null tvGlobals)]

   buildMemory :: [TypeInfo] -> T.Exp
   buildMemory [] = T.EConst T.CSkip
     -- In this case there are no globals

   buildMemory [TypeInfo {tiVarCells}] = T.EId tiVarCells

   buildMemory (TypeInfo {tiVarCells}:vs) = 
     T.EInterleave (T.EId tiVarCells)
                   (buildMemory vs)

   memTypeChans :: TypeInfo -> [T.Exp]
   memTypeChans TypeInfo {tiReaderChan,tiWriterChan,tiDataInfo} =
     (T.EId tiReaderChan):(T.EId tiWriterChan):dataChans tiDataInfo
     where
       dataChans (Right _) = []
       dataChans (Left (StructInfo {siFields})) =
           concatMap (map T.EId . fieldChans) siFields

       fieldChans :: FieldInfo -> [T.Id]
       fieldChans (FieldInfo {fiReaderChan,fiWriterChan,fiSubfields}) =
           [fiReaderChan,fiWriterChan] ++ concatMap fieldChans fiSubfields

     
   hideMemory =
     T.EHide (T.EId $ T.Fixed "procToRun")
             (T.EEnumSet $ concatMap memTypeChans tinfosWithVars)
              
   runInMemory =
     T.EGenParallel (T.EId $ memoryName)
                    (T.EEnumSet $ concatMap memTypeChans tinfosWithVars)
                    (T.EId (T.Fixed "procToRun"))

-- buildDataReps constructs the datatypes representing the actual C types
--
-- The data representation for built-in C types are special cases defined
-- elsewhere and included in the list generated here.
buildDataReps :: MemInfo -> CG [T.Definition]
buildDataReps minfo = do
  standardReps <- mapM buildDataRep baseStructTypes
  (cIntMin,cIntMax) <- getCIntRange
  return $ (minCIntDef cIntMin):(maxCIntDef cIntMax):baseTypes ++ standardReps
  where
    baseStructTypes :: [TypeInfo]
    baseStructTypes = [ti | (ti,_) <- minfo, isLeft (tiDataInfo ti)]

    buildDataRep :: TypeInfo -> CG T.Definition
    buildDataRep (TypeInfo {tiRepType=rt,
                            tiDataInfo=Left (StructInfo {siConName,
                                                         siFields})}) = do
        tfields <- mapM (tName . fiType) siFields
        return $ T.DDataType rt [(siConName,tfields)]
      where
        tName :: BaseType -> CG T.Exp
        tName bt = T.EDot . T.EId . tiRepType <$> lookupTypeInfo bt <*> pure []
    buildDataRep ti = fail $ "Internal Error: buildDataRep called on non-struct type "
                          ++ show ti

    baseTypes = [cIntDataRep, cBoolDataRep, cFloatDataRep, cUnitDataRep, 
                 maxPidDef, pidDataRep, maxMidDef, midDataRep, mutDataRep]

-- buildLSProjections builds CSP functions for dealing with our LocalState
-- map.  In particular, imagine our program uses local variables of three types:
-- int, bar and baz.  Then LocalState will look like
--
--    data LocalState = LS.(|intLoc => intRep|)
--                        .(|barLoc => barRep|)
--                        .(|bazLoc => bazRep|)
--
-- For each of int, bar, and baz, we build a function to look up a local
-- variable of the appropriate type.  If the variable is absent, we emit a
-- failure event and deadlock.  
--
--    channel proj_error
--
--    intLocalsProj :: LocalState -> intLoc -> (intRep -> Proc) -> Proc
--    intLocalsProj (LS.st._._) v k =
--      if mapMember(st,v) then k(mapLookup(st,v))
--                         else proj_error -> STOP
-- 
--    barLocalsProj :: LocalState -> barLoc -> (barRep -> Proc) -> Proc
--    barLocalsProj (LS._.st._) v k =
--      if mapMember(st,v) then k(mapLookup(st,v))
--                         else proj_error -> STOP
--
-- and so on, for each type.
--
-- It's mandatory that we check if the key is present before calling mapLookup
-- here.  If it's called with a missing key, FDR will fail completely and stop
-- evaluating the model.  This can happen even if the program doesn't actually
-- reach this error state, because of the way FDR eagerly evaluates processes
-- for all possible inputs.
--
-- TODO: It would be cleaner to just have this function return a "maybe" instead
-- of returning a Proc, and do the error case where it is called.  But I don't
-- think FDR3 has polymorphic datatypes, and I'm too lazy to define a maybe type
-- for each thing in a map.
buildLSProjections :: MemInfo -> CG [T.Definition]
buildLSProjections minfo = do
  stv  <- freshLocalNew "locProjSt"
  locv <- freshLocalNew "locProjLoc"
  kv   <- freshLocalNew "locProjk"
  return $ errorChan : buildProjections (stv,locv,kv) 0 typesWithLocals []
  where
    errorChan :: T.Definition
    errorChan = T.DChan [localProjErrorChanId] []
    
    typesWithLocals :: [TypeInfo]
    typesWithLocals = [ti | (ti,TypeVars {tvLocals}) <- minfo,
                            not $ null tvLocals]

    -- args: names to use in binding the state map and the location argument,
    -- the number of previous typeinfos, the remaining typeinfos, the
    -- accumulated projections so far.
    buildProjections :: (T.Id,T.Id,T.Id) -> Int -> [TypeInfo] -> [T.Definition]
                     -> [T.Definition]
    buildProjections _ _ [] acc = acc
    buildProjections (stv,locv,kv) count (ti:tis) acc =
      buildProjections (stv,locv,kv) (1+count) tis
                       (buildProj ti : acc)
      where
        uid :: T.Id
        uid = T.Fixed "_"

        buildProj :: TypeInfo -> T.Definition
        buildProj (TypeInfo {tiLocalsProj}) =
          T.DFun tiLocalsProj
            [([T.PDot (T.PId localStateCon)
                      (map T.PId $ replicate count uid
                                ++ stv : replicate (length tis) uid),
               T.PId locv,
               T.PId kv],
              T.EIfThenElse (cspMapMember stv locv)
                (T.EApp (T.EId kv) [cspMapLookup stv locv])
                (T.EPrefix (T.EId localProjErrorChanId) [] (T.EConst T.CStop))
              )]

-- buildLSProjections builds CSP functions for updating our LocalState.
-- In particular, imagine our program uses local variables of three types:
-- int, bar and baz.  Then LocalState will look like
--
--    data LocalState = LS.(|intLoc => intRep|)
--                        .(|barLoc => barRep|)
--                        .(|bazLoc => bazRep|)
--
-- For each of int, bar, and baz, we build a function to update a local variable
-- of the appropriate type and to delete a local variable of the appropriate
-- type.  That is, functions:
--
--    intLocalsUpd :: LocalState -> intLoc -> intRep -> LocalState
--    intLocalsUpd (LS.st1.st2.st3) v d = LS.mapUpdate(st1,v,d).st2.st3
--
--    intLocalsDel :: LocalState -> intLoc -> LocalState
--    intLocalsDel (LS.st1.st2.st3) v = LS.mapDelete(st1,v).st2.st3
--
-- and so on, for each type.
buildLSUpdaters :: MemInfo -> CG [T.Definition]
buildLSUpdaters minfo = do
  locv <- freshLocalNew "locProjLoc"
  valv <- freshLocalNew "locProjVal"
  stvs <- freshLocalsNew $ map ("st"++) $ map show [1..(length typesWithLocals)]
  let namedTypes  = zip (map T.EId stvs) typesWithLocals
      stateBinder = T.PDot (T.PId localStateCon) $ map T.PId stvs
  return $ buildUpdaters (stateBinder,locv,valv) [] namedTypes []
  where
    typesWithLocals :: [TypeInfo]
    typesWithLocals = [ti | (ti,TypeVars {tvLocals}) <- minfo,
                            not $ null tvLocals]

    -- args: names to use for (the state map, the location, the value), the list
    -- of binders for state maps we've already done, the typeinfos
    -- left to do and their binders, and the accumulated updaters so far.
    buildUpdaters :: (T.Pat,T.Id,T.Id) -> [T.Exp] -> [(T.Exp,TypeInfo)]
                  -> [T.Definition] -> [T.Definition]
    buildUpdaters _ _ [] acc = acc
    buildUpdaters (stBnd,locv,valv) oldSts
                  ((stn,TypeInfo {tiLocalsUpdate,tiLocalsDelete}):tis)
                  acc =
      buildUpdaters (stBnd,locv,valv) (oldSts ++ [stn]) tis
                    (updater : deleter : acc)
      where
        updater :: T.Definition
        updater =
          T.DFun tiLocalsUpdate
            [([stBnd,T.PId locv,T.PId valv],
              T.EDot (T.EId localStateCon)
                   $ oldSts ++ cspMapUpdate stn locv (T.EId valv)
                             : map fst tis)]

        deleter :: T.Definition
        deleter =
          T.DFun tiLocalsDelete
            [([stBnd,T.PId locv],
              T.EDot (T.EId localStateCon)
                   $ oldSts ++ (T.EApp (T.EId $ T.Fixed "mapDelete")
                                       [stn,T.EId locv])
                             : map fst tis)]

-- buildArrayLocLookup builds the CSP functions that are used to check if a
-- location is a statically-sized array.  Imagine for some type Foo there are
-- two arrays:
--
--   foo x[2], y[3];
--
-- When these declarations are handled, the following lists of addresses will
-- get generated and added to the monad:
--
--   fooArrays = [[x_c0,x_c1],[y_c0,y_c1,y_c2]]
--
-- Supposing this is a local definition, we'll then build the following for
-- tiArrayLocs:
--
--   fooArrayLocs (FooLocLTag.x_c0,CIntKnown.0) = <FooLocLTag.x_c0>
--   fooArrayLocs (FooLocLTag.x_c0,CIntKnown.1) = <FooLocLTag.x_c1>
--   fooArrayLocs (FooLocLTag.x_c1,CIntKnown.0) = <FooLocLTag.x_c1>
--
--   fooArrayLocs (FooLocLTag.y_c0,CIntKnown.0) = <FooLocLTag.y_c0>
--   fooArrayLocs (FooLocLTag.y_c0,CIntKnown.1) = <FooLocLTag.y_c1>
--   fooArrayLocs (FooLocLTag.y_c0,CIntKnown.2) = <FooLocLTag.y_c2>
--   fooArrayLocs (FooLocLTag.y_c1,CIntKnown.0) = <FooLocLTag.y_c1>
--   fooArrayLocs (FooLocLTag.y_c1,CIntKnown.1) = <FooLocLTag.y_c2>
--   fooArrayLocs (FooLocLTag.y_c2,CIntKnown.0) = <FooLocLTag.y_c2>
--
--   fooArrayLocs _                             = <>
--
-- If these were global definitions, the only difference would be the use of 
-- FooLocalGTag instead of FooLocalLTag.
buildArrayLocLookup :: MemInfo -> [T.Definition]
buildArrayLocLookup minfo =
    (T.DChan [arrayIndexErrorChanId] [])
  : (mapMaybe (\(tinfo,TypeVars {tvArrays}) ->
                if null tvArrays then Nothing
                                 else Just $ arrLookups tinfo tvArrays)
              minfo)
  where
    arrLookups :: TypeInfo -> [ArrayLocs] -> T.Definition
    arrLookups (tinfo@(TypeInfo{tiArrayLocs=nm})) arrs =
      T.DFun nm (   (concatMap (arrLookupClauses tinfo) arrs)
                 ++ [([T.PId (T.Fixed "_"),T.PId (T.Fixed "_")],T.EList [])])

    
    arrLookupClauses :: TypeInfo -> ArrayLocs -> [([T.Pat],T.Exp)]
    arrLookupClauses (TypeInfo {tiLocalLocTag}) (ALLocal locs) =
      concatMap (oneLocClauses tiLocalLocTag) (tails locs)
    arrLookupClauses (TypeInfo {tiGlobalLocTag}) (ALGlobal locs) =
      concatMap (oneLocClauses tiGlobalLocTag) (tails locs)


    -- args: the local/global tag.  A list of locations.
    oneLocClauses :: T.Id -> [T.Id] -> [([T.Pat],T.Exp)]
    oneLocClauses _   []            = []
    oneLocClauses tag locs@(loc0:_) =
      map (\(locn,n) -> ([T.PDot (T.PId tag) [T.PId loc0],
                          T.PDot (T.PId cIntKnownCon) [T.PConst $ T.CInt n]],
                         T.EList [T.EDot (T.EId tag) [T.EId locn]]))
          (zip locs [0..])


-- buildLocationReaders builds a CSPm function that reads data from a memory
-- address.  This is a little complicated because the memory address might
-- come in any of four forms: Null, Unknown, a global address, or a local address.
--
--   - In the case of Null or Unknown, we deadlock.    (XXX also send an alert signal?)
--
--   - In the case of a global address, we communicate with the appropriate
--     variable process.
--
--   - In the case of a local address, we read from the local state map.
--
-- We determine which case we are in by pattern matching on the provided
-- address.
--
-- The generated CSPm function is meant to look like:
--
--  readFoo :: (LocalState, PIDTyp, FooLoc, (LocalState,PIDTyp,FooTyp) -> Proc) 
--          -> Proc
-- 
--  readFoo(_,pid,(FooGlobalTag.loc),k) = readFoo!pid!x?v -> k(v)
--  readFoo(st,_(FooLocalTag.loc),k)    = fooLocalsProj (st,loc,\val @ k (st,pid,val))
--  readFoo(_,_,FooNullLoc,_)           = STOP
--  readFoo(_,_,FooUnknownLoc,_)        = STOP
-- 
-- The first three two arguments are the current local state map, the current
-- process ID, and the location we are meant to read from.  The last argument is
-- a continuation, which tells us what to do with the value stored in the
-- location once we find it.
-- 
-- It's necessary to use CPS here instead of just returning a FooTyp, because
-- a CSPm function with that return type would have no way to read from the
-- variable cells in the case of a global variable.
--
-- We also build readers that pull just one field out of struct stored at some
-- location.  See the comment above buildLocationReader below.
--
-- There is one small additional complication: For types with no global
-- variables, we do not generate the channels that would be used to read or
-- write those global variables.  So, in that case, we must also not generate
-- the clause of this definition that would access global variables.  Similarly,
-- for types with no local variables, there is no corresponding data in
-- LocalState, so we omit that clause.
buildLocationReaders :: MemInfo -> CG [T.Definition]
buildLocationReaders minfo =
  concat <$> mapM typeReaders minfo
  where
    typeReaders :: (TypeInfo,TypeVars) -> CG [T.Definition]
    typeReaders (TypeInfo {tiLocalLocTag,tiGlobalLocTag,tiNullLoc,tiUnknownLoc,
                           tiLocalsProj,tiReader,tiReaderChan,tiDataInfo},
                 TypeVars {tvGlobals,tvLocals}) = do
        fieldReaders <- 
          mapM (\(fiReader,fiReaderChan,fiFieldProj) -> 
                    buildLocationReader fiReader tiNullLoc tiUnknownLoc
                           (fmap (\(gltag,_) -> (gltag,fiReaderChan)) ginfo)
                           (if null tvLocals then Nothing else
                              Just (tiLocalLocTag,tiLocalsProj,
                                    Just $ T.EId fiFieldProj)))
               fields
        structReader <- buildLocationReader tiReader tiNullLoc tiUnknownLoc ginfo 
                           (if null tvLocals then Nothing else
                              Just (tiLocalLocTag,tiLocalsProj,Nothing))
        return $ structReader : fieldReaders
      where
        ginfo :: Maybe (T.Id,T.Id)
        ginfo = case tvGlobals of
                  []    -> Nothing
                  (_:_) -> Just (tiGlobalLocTag,tiReaderChan)

        fields :: [(T.Id,T.Id,T.Id)]
        fields =
          case tiDataInfo of
            Right _ -> []
            Left (StructInfo {siFields}) -> transFields siFields
              where
                transFields :: [FieldInfo] -> [(T.Id,T.Id,T.Id)]
                transFields flds = concatMap field flds
                
                field :: FieldInfo -> [(T.Id,T.Id,T.Id)]
                field f = (fiReader f, fiReaderChan f, fiFieldProj f)
                        : transFields (fiSubfields f)

    -- Build location reader is a little tricky.  We've defined it in a fairly
    -- abstract way in order to use the same definition both for reading
    -- everything at a location and for reading just one field of a struct at
    -- a location.  Its arguments are.
    --
    -- - The name of the cspm function we are defining.
    -- 
    -- - The name of the "null" and "unknown" locations associated with this
    --   type.
    --
    -- - If there are global variables of this type: the "tag" for global
    --   variable locations and the cspm channel to read from.
    -- 
    -- - If there are local variables of this type: the tag for local variables
    --   of this type, the function that projects data of this type out of the
    --   LocalState, and optionally a function to apply to the result we get
    --   from the state map (to support getting just one field of a struct).
    buildLocationReader :: T.Id -> T.Id -> T.Id -> Maybe (T.Id,T.Id) 
                        -> Maybe (T.Id,T.Id,Maybe T.Exp) -> CG T.Definition
    buildLocationReader fnm nullLoc unknownLoc ginfo linfo = do
      sBnd <- freshLocalNew "st" 
      pBnd <- freshLocalNew "pid"
      lBnd <- freshLocalNew "loc"
      kBnd <- freshLocalNew "k"  
      vBnd <- freshLocalNew "v"  
      return $ T.DFun fnm $
             -- readFoo(st,pid,FooNullLoc,k) = STOP
             ([T.PId sBnd,T.PId pBnd,T.PId nullLoc,T.PId kBnd],
              T.EConst T.CStop)
             -- readFoo(st,pid,FooUnknownLoc,k) = STOP
           : ([T.PId sBnd,T.PId pBnd,T.PId unknownLoc,T.PId kBnd],
              T.EConst T.CStop)
           : -- readFoo(st,pid,(FooLocalTag.loc),k) =
             --     fooProj (st,x,\val @ k (st,pid,val))
             -- (with an extra projection in the case of a struct)
             case linfo of
               Nothing -> []
               Just (ltag,lLocalProj,mlStructProj) ->
                 [([T.PId sBnd,T.PId pBnd,T.PDot (T.PId ltag) [T.PId lBnd],
                    T.PId kBnd],
                   T.EApp (T.EId lLocalProj)
                     [T.EId sBnd, T.EId lBnd, T.ELambda [T.PId vBnd] kApp])]
                 where
                   kApp = 
                    T.EApp (T.EId kBnd) (case mlStructProj of
                                             Nothing -> map T.EId [sBnd,pBnd,vBnd]
                                             Just e  -> [T.EId sBnd,T.EId pBnd,
                                                         T.EApp e [T.EId vBnd]])
           ++ case ginfo of
               Nothing -> []
               Just (gtag,gchan) ->
                 [([T.PId sBnd, T.PId pBnd, T.PDot (T.PId gtag) [T.PId lBnd],
                    T.PId kBnd],
                  gread gchan (T.EId pBnd) (T.EId lBnd) vBnd
                   (T.EApp (T.EId kBnd) [T.EId sBnd,T.EId pBnd,T.EId vBnd]))]

-- buildLocationWriters is an awful lot like buildLocationReaders (see above),
-- so I'll give the cliffs notes.  I'm sure these two definitions could be
-- combined in some elegant way, but they are already getting a little
-- unwieldly, so I skipped it.
--
-- The writers have this type:
--
--  writeFoo :: (LocalState, PidTyp, FooLoc, FooType, (LocalState,PIDTyp,Foo) -> Proc)
--           -> Proc
--
-- The primary difference is that the caller must supply the value to be
-- written.  We could have chosen to make the continuation here just
-- ((LocalState,PIDTyp) -> Proc), since we're not reading any data that needs to be
-- passed on in this case.  But, for convenience and uniformity with other
-- statements, we pass along the value that was written (much like how "x = e"
-- is an expression that evaluates to e in C).
-- 
--  writeFoo(st,pid,(FooGlobalTag.loc),v,k) = writeFoo!pid!x!v -> k(st,pid,v)
--  writeFoo(st,(FooLocalTag.loc),v,k)      = k (fooLocalsUpdate st loc v,pid,v)
--  writeFoo(_,_,FooNullLoc,_,_)            = STOP
--  writeFoo(_,_,FooUnknownLoc,_,_)         = STOP
--
-- The case for modifying just a subfield of a struct in the case of a local
-- variable is a bit more complicated, in that we must read the whole struct
-- and then store a slightly modified copy.  It looks like:
--
--   writeFoo(st,(FooLocalTag.loc),v,k) =
--     fooLocalsProj (st,loc,
--        \sval @ k (fooLocalsUpdate st loc (fieldInj sval v,pid,v)))
--
-- where fieldInj is a helper function defined elsewhere that just pattern
-- matches on a struct and modifies one field.
buildLocationWriters :: MemInfo -> CG [T.Definition]
buildLocationWriters minfo =
  concat <$> mapM typeWriters minfo
  where
    typeWriters :: (TypeInfo,TypeVars) -> CG [T.Definition]
    typeWriters (TypeInfo {tiLocalLocTag,tiGlobalLocTag,tiNullLoc,
                           tiUnknownLoc,tiWriter,tiWriterChan,tiDataInfo,
                           tiLocalsProj,tiLocalsUpdate},
                 TypeVars {tvGlobals,tvLocals}) = do
        fieldWriters <- 
          mapM (\(fiWriter,fiWriterChan,fiFieldInj) -> 
                    buildLocationWriter fiWriter tiNullLoc tiUnknownLoc
                           (fmap (\(gltag,_) -> (gltag,fiWriterChan)) ginfo)
                           (if null tvLocals then Nothing else
                              Just (tiLocalLocTag,tiLocalsUpdate,
                                    Just (tiLocalsProj,T.EId fiFieldInj))))
               fields
        structWriter <- buildLocationWriter tiWriter tiNullLoc tiUnknownLoc ginfo
                           (if null tvLocals then Nothing else
                             Just (tiLocalLocTag,tiLocalsUpdate,Nothing))
        return $ structWriter : fieldWriters
      where
        ginfo :: Maybe (T.Id,T.Id)
        ginfo = case tvGlobals of
                  []    -> Nothing
                  (_:_) -> Just (tiGlobalLocTag,tiWriterChan)

        fields :: [(T.Id,T.Id,T.Id)]
        fields =
          case tiDataInfo of
            Right _ -> []
            Left (StructInfo {siFields}) -> transFields siFields
              where
                transFields :: [FieldInfo] -> [(T.Id,T.Id,T.Id)]
                transFields flds = concatMap field flds
                
                field :: FieldInfo -> [(T.Id,T.Id,T.Id)]
                field f = (fiWriter f, fiWriterChan f, fiFieldInj f)
                        : transFields (fiSubfields f)


    -- Building a location writer is similar to building a location reader.
    -- The args are:
    -- 
    -- - The name of the function being defined.
    --
    -- - The null and unknown locations for this type.
    -- 
    -- - If there are global variables of this type: the tag used for their
    --   locations and the channel we use to write to them.
    -- 
    -- - If there are local variables of this type: the tag used for local
    --   locations of this type, the function that writes to the map for this
    --   type in the local state map, and, in the case where we're writing to
    --   just a field, the function that reads from the map of this type in the
    --   local state map and a function to update this field of the struct
    --   (should be of type "StructType -> FieldType -> StructType)".
    buildLocationWriter :: T.Id -> T.Id -> T.Id -> Maybe (T.Id,T.Id) 
                        -> Maybe (T.Id,T.Id,Maybe (T.Id,T.Exp)) -> CG T.Definition
    buildLocationWriter fnm nullLoc unknownLoc ginfo linfo = do
      sBnd <- freshLocalNew "st"
      pBnd <- freshLocalNew "pid"
      lBnd <- freshLocalNew "loc"
      kBnd <- freshLocalNew "k"
      vBnd <- freshLocalNew "v"
      svalBnd <- freshLocalNew "sval"
      return $ T.DFun fnm $
             -- writeFoo.st.FooNullLoc.v.k = STOP
             ([T.PId sBnd, T.PId pBnd, T.PId nullLoc, T.PId vBnd,
               T.PId kBnd],
              T.EConst T.CStop)
             -- writeFoo.st.FooUnknownLoc.v.k = STOP
           : ([T.PId sBnd, T.PId pBnd, T.PId unknownLoc, T.PId vBnd,
               T.PId kBnd],
              T.EConst T.CStop)
           : -- writeFoo(st,pid,(FooLocalTag.loc),v,k) = 
             --   k (fooLocalsUpdate st loc v,pid,v)
             -- 
             -- Or, in the case of a struct field update:
             --
             -- writeFoo(st,pid,(FooLocalTag.loc),v,k) =
             --   fooLocalsProj (st,loc,
             --     \sval @ k (fooLocalsUpdate st loc (fieldInj sval v),
             --                pid,v))
             case linfo of
               Nothing -> []
               Just (ltag,localsUpdate,mlStructInj) -> 
                 [([T.PId sBnd, T.PId pBnd, T.PDot (T.PId ltag) [T.PId lBnd],
                    T.PId vBnd, T.PId kBnd],
                   case mlStructInj of
                     Nothing -> kApp
                     Just (localsProj,_) ->
                       T.EApp (T.EId localsProj)
                         [T.EId sBnd, T.EId lBnd,
                          T.ELambda [T.PId svalBnd] kApp])]
                 where
                   kApp =
                     T.EApp (T.EId kBnd)
                       [T.EApp (T.EId localsUpdate)
                          [T.EId sBnd, T.EId lBnd,
                           case mlStructInj of
                             Nothing -> T.EId vBnd
                             Just (_,fieldInj) ->
                               T.EApp fieldInj [T.EId svalBnd,T.EId vBnd]],
                        T.EId pBnd, T.EId vBnd]
             -- writeFoo(st,pid,(FooGlobalTag.loc),v,k) = writeChan!pid!loc!v -> k(st,pid,v)
          ++ case ginfo of
               Nothing -> []
               Just (gtag,gchan) ->
                 [([T.PId sBnd, T.PId pBnd, T.PDot (T.PId gtag) [T.PId lBnd],
                    T.PId vBnd, T.PId kBnd],
                   gwrite gchan (T.EId pBnd) lBnd (T.EId vBnd)
                    (T.EApp (T.EId kBnd) [T.EId sBnd,T.EId pBnd,T.EId vBnd]))]

-- buildFieldProjInj builds a pair of functions corresponding to each field
-- of a struct declared in the source program.  Recall that a C Struct:
--
--   struct Foo {
--     int x;
--     bar y;
--     int z;
--   }
--
-- Is represented as a CSPm datatype:
--
--     datatype Foo = Foo.|int|.|bar|.|int|
--
-- Where |t| is the CSPm representation of the C type t.
--
-- We need two functions for each field of Foo: one to project out that field
-- given a Foo, and one to update that field given a Foo and new value.  For
-- example, for the field "x":
--
--    fieldProj_x (Foo.x._._) = x
--
--    fieldInj_x (Foo._.y.z) x = Foo.x.y.z
--
-- buildFieldProjInj constructs these two definitions.
buildFieldProjInj :: MemInfo -> CG [T.Definition]
buildFieldProjInj minfo = 
    concat <$> mapM buildPIs structs
  where
    structs :: [StructInfo]
    structs = foldl' (\sis (TypeInfo {tiDataInfo},_) ->
                         case tiDataInfo of
                           Left si -> si : sis
                           Right _ -> sis)
                     [] minfo
 
    buildPIs :: StructInfo -> CG [T.Definition]
    buildPIs si = do pat <- dataPattern si
                     buildSubpatternPIs pat
      where
        -- this builds projections/injections for any subfields of the
        -- provided pattern.
        buildSubpatternPIs :: Pattern -> CG [T.Definition]
        buildSubpatternPIs (PVar _) = return []
        buildSubpatternPIs (PData topnm subfields) =
            topLevelSubdefs [] subfields []
          where
            topLevelSubdefs :: [(FieldInfo,Pattern)] -> [(FieldInfo,Pattern)]
                            -> [T.Definition] -> CG [T.Definition]
            topLevelSubdefs _ [] defs = return defs
            topLevelSubdefs done ((fi,fp):todo) defs = do
              theseDefs <- 
                fldDef (\p -> PData topnm (done ++ (fi,p) : todo))
                       fp fi
              topLevelSubdefs (done ++ [(fi,fp)]) todo (theseDefs ++ defs)
              

        -- Give me a way to construct the top-level pattern if I change just
        -- this field's identifier, the fieldinfo corresponding to this
        -- subpattern, and I'll give you the tiFieldProj/tiFieldInj
        -- definitions for this field and its subfields
        fldDef :: (Pattern -> Pattern) -> Pattern -> FieldInfo -> CG [T.Definition]
        fldDef modPat pat 
               (FieldInfo {fiTargetNameHint, fiFieldProj, fiFieldInj}) = do
          fieldVar <- freshLocalNew fiTargetNameHint
          subfieldDefs <- subDefs
          return $ [projDef fieldVar, injDef fieldVar] ++ subfieldDefs
          where
            projDef, injDef :: T.Id -> T.Definition
            projDef fieldVar = 
              T.DFun fiFieldProj
                     [([patternToPat $ modPat $ PVar fieldVar],
                       T.EId fieldVar)]

            injDef fieldVar =
              T.DFun fiFieldInj
                     [([patternToPat $ modPat (PVar (T.Fixed "_")),T.PId fieldVar],
                       patternToExp (modPat (PVar fieldVar)))]

            subDefs :: CG [T.Definition]
            subDefs =
              case pat of
                PVar _ -> return []
                PData dataFInfo subfields ->
                  let 
                    subDefRec :: [(FieldInfo,Pattern)] 
                              -> [(FieldInfo,Pattern)]
                              -> [T.Definition]
                              -> CG [T.Definition]
                    subDefRec _ [] defs = return defs
                    subDefRec doneFs ((fi,fp):todoFs) doneDefs = do
                      theseDefs <- 
                        fldDef (\fp' -> modPat (PData dataFInfo 
                                                      (doneFs ++ (fi,fp') : todoFs)))
                               fp fi
                      subDefRec (doneFs ++ [(fi,fp)]) todoFs (theseDefs ++ doneDefs)
                  in 
                    subDefRec [] subfields []

-- This builds all the definitions related to the memory model.
buildMemoryModel :: CG [T.Definition]
buildMemoryModel = do
  minfo <- createMemInfo
  voidStarRep     <- buildVoidStarRep minfo
  cspChannels     <- buildCspChannels minfo
  varCellBuilders <- buildVarCellBuilders minfo
  dataReps        <- buildDataReps minfo
  localReaders    <- buildLSProjections minfo
  localWriters    <- buildLSUpdaters minfo
  let arrayIndexers = buildArrayLocLookup minfo
  locationReaders <- buildLocationReaders minfo
  locationWriters <- buildLocationWriters minfo
  fieldProjInjs   <- buildFieldProjInj minfo
  return $ concat [dataReps,
                   buildLocations minfo,
                   buildLocalState minfo,
                   voidStarRep,
                   cspChannels,
                   varCellBuilders,
                   buildTypedMemory minfo,
                   memoryProcs minfo,
                   localReaders,
                   localWriters,
                   fieldProjInjs,
                   arrayIndexers,
                   locationReaders,
                   locationWriters
                  ]

-----------------------------------------------------------------------------
----------- Main!
-----------------------------------------------------------------------------


mainGen :: T.Exp -> T.Definition
mainGen main = do
  let 
    upat = T.PId $ T.Fixed "_"
    mainExp =
      T.EApp (T.EId (T.Fixed "runInSystem"))
         [T.EApp main [T.EId localStateEmpty,
                       T.EDot (T.EId pidKnownCon) [T.EConst $ T.CInt 0],
                       (T.ELambda [upat,upat,upat]
                                  (T.EConst T.CSkip)) ]]
   in T.DVar (T.PId $ T.Fixed "runMain") mainExp

-- This translates a bunch of CFGs into CSP.  It assumes it is called
-- in a context where the appropriate type information, function
-- declarations, etc, have already been added to the monad.  (For
-- example, by calling ASTtoCFG.cfgTransUnit first)
data CspModules =
  CspModules {cmGlobalState :: T.FDRMod,
              cmStubs       :: Maybe T.FDRMod,
              cmCode        :: T.FDRMod}

  
transGen :: [S.Proc a] -> CG CspModules
transGen procs =
  do functionDefs <- concat <$> mapM transProc procs
     mmainNm <- lookupFunctionByName "main"
     let 
       upat = T.PId $ T.Fixed "_"
       mainNm =
         case mmainNm of
           Nothing -> 
             T.ELambda [upat, upat, upat] (T.EConst T.CSkip)
           Just m -> T.EId $ ftid m
       main = mainGen mainNm
     globalProcs <- buildMemoryModel
     -- hack for channel names right now XXX
     let cmGlobalState = T.FDRMod globalProcs
     functions <- allFunctions
     let undefinedFunctions = [fd | (_,fd) <- functions, not (fdef fd)]
     cmStubs <- 
        if null undefinedFunctions then return Nothing
         else Just . T.FDRMod <$> mapM stubOut undefinedFunctions
     return $ CspModules {cmGlobalState, cmStubs,
                          cmCode = T.FDRMod $ functionDefs ++ [main]}
