{- |

   Module      :  CodeGen.LLVM.TransModule
   Description :  Translation of LLVM Modules to CSP
   
   Author      :  Chris Casinghino
   
   This module handles the bulk of the compilation from LLVM IR to CSP.
-}

module CodeGen.LLVM.TransModule (transModule,CspModules(..)) where

import Prelude hiding (mapM)

import Control.Monad (foldM,unless,when,void)
import Data.Maybe (catMaybes,isJust,isNothing)
import Data.Traversable (mapM)
import Data.List (foldl',sortBy,zip4,(\\),groupBy)
import qualified Data.Map as M

import qualified LLVM.General.AST as L (Definition(..),Module(..),Name(..))
import qualified LLVM.General.AST.Global as L
import qualified LLVM.General.AST.Type as L
import qualified LLVM.General.AST.Float as L
import qualified LLVM.General.AST.AddrSpace as L
import qualified LLVM.General.AST.Operand as L
import qualified LLVM.General.AST.Instruction as LI
import qualified LLVM.General.AST.IntegerPredicate as LI
import qualified LLVM.General.AST.Constant as LC
import qualified LLVM.General.PrettyPrint as LP
import qualified Language.CSPM.Syntax as T

import CodeGen.LLVM.CGMonad
import CodeGen.LLVM.Analysis
import CodeGen.LLVM.ModelIdentifiers
import CodeGen.LLVM.ModelBasics
import CodeGen.LLVM.ModelStack

-------------------------------
--- std libraryish things
nth :: [a] -> Int -> Maybe a
nth []     _ = Nothing
nth (x:_)  n | n <= 0 = Just x
nth (_:xs) n = nth xs (n-1)

---------------------------------------------------------
---- XXX FIX THIS XXX
---- this is a copy of the C squash thing.  Should just be moved to CSPretty

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


---- END XXX FIX THIS XXX
---- this is a copy of the C thing.  Should just be moved to CSPretty
---------------------------------------------------------



-------------------------------------------------
-- General helpers

-- Many functions must pass around the CSP variables that currently refer to the
-- stack and other pieces of data.  We use this type for that.
data StateVars = StateVars {svStack    :: T.Id,
                            svStackPtr :: T.Id,
                            svThreadID :: T.Id}

-- Instructions are translated as CSPm functions of type
--     (Stack,StackPointer,TID,
--       (Stack,StackPointer,TID,a) -> Proc) -> Proc
--
-- Thus, the translations of statements often begin with the patternL
--    \(stck,sp,tid,k) @ .....
--
-- This just constructs that lambda, given a way to define the body from the
-- binder names.
insnOuterLambda :: (StateVars -> T.Id -> CG T.Exp) -> CG T.Exp
insnOuterLambda body = do
  svStack    <- freshTid $ Just "iStckBndr"
  svStackPtr <- freshTid $ Just "iSPBndr"
  svThreadID <- freshTid $ Just "iTIDBndr"
  kBnd       <- freshTid $ Just "iContBndr"
  T.ELambda (map T.PId [svStack, svStackPtr, svThreadID, kBnd])
    <$> body (StateVars {svStack,svStackPtr,svThreadID}) kBnd

-- As the comment for insnOuterLambda mentions, the translation of instructions
-- takes a continuation as an argument.  Sometimes we need to explicitly
-- construct those - this function does the required name generation.
--
-- The main difference from insnOuterLambda is that the name of the fourth
-- argument is taken as an argument, since it typically is the binding location
-- for an SSA variable and should not be generated fresh.
insnInnerLambda :: T.Id -> (StateVars -> CG T.Exp) -> CG T.Exp
insnInnerLambda ssa body = do
  svStack    <- freshTid $ Just "ikStckBndr"
  svStackPtr <- freshTid $ Just "ikSPBndr"
  svThreadID <- freshTid $ Just "ikTIDBndr"
  T.ELambda (map T.PId [svStack, svStackPtr, svThreadID, ssa])
     <$> body (StateVars {svStack,svStackPtr,svThreadID})


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

---------------------
-- Translation proper

-- Operands and Constants shold never require a memory access or other
-- side-effect to resolve.  Thus, our transConstant and transOperand function
-- return a DataRep which is not a function or a Proc - just a CSP value (or
-- collection of values) whose type is the translation of the returned btype.
transConstant :: LC.Constant -> CG (BaseType,DataRep)
transConstant (LC.Int {LC.integerValue,LC.integerBits=1}) = do
  let e = if integerValue == 0 then boolFalse
          else if integerValue == 1 then boolTrue
               else unknownBool
  return (BoolType,DRValue e)
transConstant (LC.Int {LC.integerValue}) = do
  let intValue = fromIntegral integerValue
  (intMin,intMax) <- getIntRange
  let e = if (intValue < intMin) || (intValue > intMax)
            then unknownInt
            else knownInt integerValue
  return (IntType,DRValue e)
transConstant (LC.GlobalReference ty nm) = do
  mginfo <- lookupGlobal nm
  -- XXX Here, we aren't checking our recorded type for global against the type
  -- stored in the GlobalReference.  Should we?
  case mginfo of
    Nothing -> fail $ "Error: unknown global var " ++ LP.showPretty nm
    Just (GlobFunc (GFInfo {ftag})) ->
      return (FPtrType,DRValue $ T.EId ftag)
    Just (GlobVar gvi) -> do
      bt <- transType ty
      globalTag <-
        case bt of
          PointerType bt' -> tiGlobalLocTag <$> lookupTypeInfo bt'
          _ -> fail $ "Global reference has non-pointer type "
                   ++ ppBaseType bt
      return (bt,DRValue $ T.EDot (T.EId globalTag) [T.EId $ gvtid gvi])
transConstant (LC.Null {LC.constantType}) = do
  btype <- transType constantType
  (btype,) <$> zeroedValue btype
transConstant (LC.Float {}) = return $
  (FloatType,DRValue $ T.EId unknownFloatCon)
transConstant (LC.GetElementPtr {LC.address,LC.indices}) = do
  -- I believe the only valid constant address is a global reference, so
  -- the code below assumes that's what "address" will be.
  locSName <- transConstAddrConstant address
  indexInts <- mapM transGEPConstant indices
  mGInfo <- lookupGlobal locSName
  case mGInfo of
    Nothing -> fail $ "Constant address " ++ prettyLLVMName locSName
                   ++ " not found."
    Just (GlobFunc _) -> fail $ "Function name " ++ prettyLLVMName locSName
                             ++ " used as address"
    Just (GlobVar gvinfo) -> do
      ixs <-
        case indexInts of
          [] -> fail "Illegal: getElementPtr with empty index list"
          (ix:_) | ix /= 0 -> fail $
               "Unsupported: static getElementPtr with non-zero initial intex ("
            ++ show ix ++ ")"
          (_:ixs) -> return ixs
      (btype,locTid) <- staticGEPIndex gvinfo ixs
      fieldTInfo <- lookupTypeInfo btype
      return (PointerType btype,
              DRValue $ T.EDot (T.EId $ tiGlobalLocTag fieldTInfo)
                               [T.EId locTid])
  where
    staticGEPIndex :: GlobVarInfo -> [Int] -> CG (BaseType,T.Id)
    staticGEPIndex gvinfo [] =
      return (gvtype gvinfo, gvtid gvinfo)
    staticGEPIndex (GVInfo {gvtype,gvlayout}) (ix:ixs) =
      case gvlayout of
        Nothing -> fail $ "Internal error: uninitialized global encountered "
                       ++ "in staticGEPIndex."
        Just (GVAgg cells) -> 
          case nth cells ix of
            Nothing -> fail $ "Index " ++ show ix ++ " invalid for type"
                           ++ ppBaseType gvtype
            Just gvinfo -> staticGEPIndex gvinfo ixs
        Just (GVCell _) ->
          fail $ "Illegal: static getElementPtr attempts to index into "
              ++ "non-aggregate type " ++ ppBaseType gvtype
transConstant (LC.Array {LC.memberType,LC.memberValues}) = do
  memberBType <- transType memberType
  drs <- mapM (\mv -> do (mvTyp,mvDR) <- transConstant mv
                         unless (mvTyp == memberBType) $ fail $
                              "Illegal: array member has different type "
                           ++ "than array: " ++ LP.showPretty mv
                         return mvDR)
              memberValues
  return (ArrayType memberBType (fromIntegral $ length drs),
          DRAgg drs)
transConstant (LC.BitCast {LC.operand0}) = transConstant operand0
transConstant c =
  fail $ "Unsupported constant: " ++ LP.showPretty c


transOperand :: L.Operand -> CG (BaseType,DataRep)
transOperand (L.MetadataStringOperand _) =
  fail $ "Unsupported: transOperand called on MetadataStringOperand."
transOperand (L.MetadataNodeOperand _) =
  fail $ "Unsupported: transOperand called on MetadataNodeOperand."
transOperand (L.LocalReference ty nm) = do
  SVInfo {svname,svreptype} <- lookupSSA nm
  btype <- case svreptype of
             Just btype -> return btype
             Nothing    -> transType ty
  return (btype, DRValue (T.EId svname))
transOperand (L.ConstantOperand c) = transConstant c

-- The indices used as arguments to getElementPtr can either be constant
-- integers or local references
transGEPOperand :: L.Operand -> CG (Either Int L.Name)
transGEPOperand (L.MetadataStringOperand _) = fail
  "Unsupported: int or local expected, but MetadataStringOperand found."
transGEPOperand (L.MetadataNodeOperand _) = fail 
  "Unsupported: int or local expected, but MetadataNodeOperand found."
transGEPOperand (L.LocalReference (L.IntegerType _) nm) =
  return $ Right nm
transGEPOperand (L.LocalReference t nm) =
  fail $ "Unsupported: Index " ++ prettyLLVMName nm ++ " to getElementPtr"
      ++ " has non-Int type " ++ LP.showPretty t
transGEPOperand (L.ConstantOperand c) = Left <$> transGEPConstant c

transGEPConstant :: LC.Constant -> CG Int
transGEPConstant (LC.Int {LC.integerValue}) =
  return $ fromIntegral integerValue
transGEPConstant c =
  fail $ "Unsupported: expected constant int but found " ++ LP.showPretty c

-- Sometimes, as when getElementPtr appears in a constant, we are presented with
-- a "constant" llvm value that must be interpreted as an address.  I believe
-- the only LLVM constant that can be an address is a reference to a global
-- variable.  This function checks to see if the constant has that form, and
-- returns the corresponding source name if so.
transConstAddrConstant :: LC.Constant -> CG L.Name
transConstAddrConstant (LC.GlobalReference _ nm) = return nm
transConstAddrConstant c = fail $
     "Unsupported: constant address expected, but encountered "
  ++ LP.showPretty c

-- translate an operand that must be a First-class value (i.e., not a composite
-- type).
transFCOperand :: L.Operand -> CG (BaseType,T.Exp)
transFCOperand o = do
  (t,dr) <- transOperand o
  case dr of
    DRValue v -> return (t,v)
    DRAgg _ -> fail $
         "Expected first-class value but found composite operanrd ("
      ++ LP.showPretty o ++ ")"

-- This takes a function operand and the translation of its arguments and builds
-- the application.  In the case where the operand is just the name of a
-- function, this is easy.  In the case where the operand is some location
-- holding a function pointer, it's somewhat trickier.
transFunctionApplication :: L.Operand -> [T.Exp] -> CG T.Exp
transFunctionApplication (L.ConstantOperand (LC.GlobalReference _ nm)) args = do
  mginfo <- lookupGlobal nm
  case mginfo of
    Just (GlobFunc (GFInfo {ftid})) -> return $ T.EApp (T.EId ftid) args
    Just (GlobVar gvi) -> do
      fail $ "Attempt to use non-function global " ++ T.namePart (gvtid gvi)
          ++ " in function application."
    Nothing -> 
      fail $ "Unknown global " ++ prettyLLVMName nm
          ++ "in function application."
transFunctionApplication (L.LocalReference ty nm) args = do
  -- For now, we only support function pointers when supplied as an ssa
  -- variable.  I am unsure if other things are used, but in principle they
  -- could be supported.  The primary reason for this restriction is that we
  -- need to know the type at which the function is used (for our function
  -- pointer infrastructure), but the way we have set up the type inference
  -- around operands infers the representation type instead, which may be
  -- different.
  (argTys,retTy) <-
    case ty of
      L.PointerType {L.pointerReferent=
            L.FunctionType {L.resultType, L.argumentTypes}} ->
        (,) <$> mapM transType argumentTypes <*> transType resultType
      _ -> fail $ "Expected variable " ++ prettyLLVMName nm ++ " to be a "
               ++ "function pointer, but it has type " ++ LP.showPretty ty
  SVInfo {svname} <- lookupSSA nm
  f <- lookupFPtrDeref argTys retTy
  return $ T.EApp (T.EId f) $ T.EId svname : args
transFunctionApplication o _ = do
  fail $ "Unsupported operand: " ++ LP.showPretty o
      ++ " in transFunctionApplication."

-- This maps each IntegerPredicate to the CSP identifier given in the runtime to
-- its implementation.
transIPredicate :: LI.IntegerPredicate -> T.Id
transIPredicate p = T.Fixed $
  case p of
    LI.EQ -> "eq"
    LI.NE -> "neq"
    LI.UGT -> "ugt"
    LI.UGE -> "uge"
    LI.ULT -> "ult"
    LI.ULE -> "ule"
    LI.SGT -> "sgt"
    LI.SGE -> "sge"
    LI.SLT -> "slt"
    LI.SLE -> "sle"

transBlocks :: [AnalyzedBlock] -> CG [T.Definition]
transBlocks = mapM transBlock

transBlock :: AnalyzedBlock -> CG T.Definition
transBlock aBlock@(AnalyzedBlock {abLabel,abLiveIn}) = do
  blockTid <- lookupSSAName abLabel 

  -- XXX not very efficient to create new ones each time.
  svStack    <- freshTid $ Just "blockStack"
  svStackPtr <- freshTid $ Just "blockSP"
  svThreadID <- freshTid $ Just "blockTID"
  let sv = StateVars {svStack,svStackPtr,svThreadID}
  blockCont  <- freshTid $ Just "blockCont"
  blockLiveTids <- mapM lookupSSAName abLiveIn
  blockBody <- transInsns aBlock sv blockCont
  return $ T.DFun blockTid $
      [(map T.PId $ blockLiveTids ++ [svStack,svStackPtr,svThreadID,blockCont],
        blockBody)]

-- ROUGHLY XXXXXXX
--    [ %1 = s1; s2; %3 = s3; trm ] 
-- -> [s1] (st,sp,tid,\(st',sp',tid',u1) . 
--      [s2] (st',sp',tid',\(st'',sp'',tid'',_) .
--         [s3] (st'',sp'',tid'',\(st''',sp''',tid''',u3) .
--                                    [trm] (st''',sp''',pid''',k))))
--
-- Note that transTerm does the application to (st''',sp''',pid''',k) itself, so
-- the brackets around [trm] are inaccurate.
--
-- XXX factor named terminator check into transTerm if possible.
transInsns :: AnalyzedBlock -> StateVars -> T.Id -> CG T.Exp
transInsns ab@(AnalyzedBlock {abInstructions}) topLevelSV topLevelCont =
  tis abInstructions topLevelSV
  where
    tis :: [LI.Named LI.Instruction] -> StateVars -> CG T.Exp
    tis [] sv = 
      transTerm ab sv topLevelCont
    tis (ninsn:is) (StateVars {svStack,svStackPtr,svThreadID}) = do
      (ins,resultBinder) <-
        case ninsn of
          LI.Do i -> return (i, T.Fixed "_")
          nm LI.:= i -> (i,) <$> lookupSSAName nm
      (mbty,ti) <- transInsn ins
      case (mbty,ninsn) of
        (Just bty, nm LI.:= _) -> addSSAType nm bty
        _ -> return ()
      innerk <- insnInnerLambda resultBinder $ \sv' ->
        case is of
          []  -> transTerm ab sv' topLevelCont
          _:_ -> tis is sv'
      return $ T.EApp ti [T.EId svStack, T.EId svStackPtr, T.EId svThreadID,
                          innerk]

-- This translates an individual LLVM instruction to CSP.  The type of the
-- resulting CSP expression should be, roughly:
--
-- (Stack,StackAddr,TID,(Stack,StackAddr,TID,Foo) -> Proc) -> Proc
--
-- That is, the instruction becomes a function which takes as arguments:
--   - The current stack,
--   - The current "stack pointer",
--   - The current thread ID,
--   - A continuation.
--
-- The continuation expects to be passed potentially updated versions of the
-- first three arguments, as well as the result computed by this instruction
-- (the "Foo").  For example, if the instruction looked like
--
--  %x = add %y %z
--
-- Foo would be Int, since add computes an Int.  In the case of "unnamed"
-- instructions that don't compute something, Foo will be unit.  transInsn
-- attempts to compute the type that will be returned by the instruction (if
-- any) but doesn't make any guarantees about getting that right.
transInsn :: LI.Instruction -> CG (Maybe BaseType,T.Exp)
transInsn (LI.Store {LI.address,LI.value}) = do
  (locBaseType,var) <- transFCOperand address
  mValBaseType <-
    case locBaseType of
      PointerType bt -> btFirstFirstClass bt
        -- The call to btFirstFirstClass here helps deal with the tricky case
        -- where address is a pointer to a composite type.  In that situation,
        -- the result should be to store into the first memory cell.  There's
        -- probably a bitcast in the llvm that changed type of this pointer
        -- correspondingly, but our transOperand function throw that information
        -- away.
      _ -> fail $ "Address used in store (" ++ LP.showPretty address
               ++ ") has non-pointer type " ++ show locBaseType
  valBaseType <-
    case mValBaseType of
      Just bt -> return bt
      Nothing -> fail $ "Unable to determine appropriate type for address "
                     ++ LP.showPretty address ++ " in Store"
  (_,tvalue) <- transFCOperand value
  TypeInfo {tiDataInfo} <- lookupTypeInfo valBaseType
  let writer = fciWriter $ dataInfoFirstFCI tiDataInfo
  fmap (Nothing,) $ insnOuterLambda $
    \(StateVars {svStack,svStackPtr,svThreadID}) k ->
      return $ T.EApp (T.EId writer)
                    $ [T.EId svStack, T.EId svStackPtr, T.EId svThreadID,
                       var, tvalue, T.EId k]
transInsn (LI.Load {LI.address}) = do
  -- Where address is a foo*:
  -- 
  -- \(st,sp,tid,k) -> fooReader(st,sp,tid,address,k)
  (locBaseType,var) <- transFCOperand address
  mValBaseType <- 
    case locBaseType of
      PointerType bt -> btFirstFirstClass bt
        -- See comment in LI.Store
      _ -> fail $ "Address used in load has non-pointer type "
               ++ show locBaseType
  valBaseType <-
    case mValBaseType of
      Just bt -> return bt
      Nothing -> fail $ "Unable to determine appropriate type for address "
                     ++ LP.showPretty address ++ " in Load"
  TypeInfo {tiDataInfo} <- lookupTypeInfo valBaseType
  let reader = fciReader $ dataInfoFirstFCI tiDataInfo
  fmap (Just valBaseType,) $ insnOuterLambda $
    \(StateVars {svStack,svStackPtr,svThreadID}) k ->
      return $ T.EApp (T.EId reader)
                      [T.EId svStack, T.EId svStackPtr, T.EId svThreadID,
                       var, T.EId k]
transInsn (LI.Add {LI.operand0,LI.operand1}) = do
  -- XXX this is WRONG for integer types smaller than our range of ints.
  transArithInsn operand0 operand1 (T.Fixed "plus") "add"
transInsn (LI.FAdd {LI.operand0,LI.operand1}) = do
  transArithInsn operand0 operand1 (T.Fixed "plus") "fadd"
transInsn (LI.Sub {LI.operand0,LI.operand1}) = do
  transArithInsn operand0 operand1 (T.Fixed "minus") "sub"
transInsn (LI.FSub {LI.operand0,LI.operand1}) = do
  transArithInsn operand0 operand1 (T.Fixed "minus") "fsub"
transInsn (LI.Mul {LI.operand0,LI.operand1}) = do
  transArithInsn operand0 operand1 (T.Fixed "multiply") "mul"
transInsn (LI.FMul {LI.operand0,LI.operand1}) = do
  transArithInsn operand0 operand1 (T.Fixed "multiply") "fmul"
transInsn (LI.UDiv {LI.operand0,LI.operand1}) = do
  transArithInsn operand0 operand1 (T.Fixed "divide") "udiv"
transInsn (LI.SDiv {LI.operand0,LI.operand1}) = do
  transArithInsn operand0 operand1 (T.Fixed "divide") "sdiv"
transInsn (LI.FDiv {LI.operand0,LI.operand1}) = do
  transArithInsn operand0 operand1 (T.Fixed "divide") "fdiv"
transInsn (LI.URem {LI.operand0,LI.operand1}) = do
  transArithInsn operand0 operand1 (T.Fixed "mod") "urem"
transInsn (LI.SRem {LI.operand0,LI.operand1}) = do
  transArithInsn operand0 operand1 (T.Fixed "mod") "srem"
transInsn (LI.FRem {LI.operand0,LI.operand1}) = do
  transArithInsn operand0 operand1 (T.Fixed "mod") "frem"
transInsn (LI.Shl {LI.operand0,LI.operand1}) = do
  transArithInsn operand0 operand1 (T.Fixed "leftShift") "shl"
transInsn (LI.LShr {LI.operand0,LI.operand1}) = do
  transArithInsn operand0 operand1 (T.Fixed "rightShift") "lshr"
transInsn (LI.AShr {LI.operand0,LI.operand1}) = do
  transArithInsn operand0 operand1 (T.Fixed "rightShift") "ashr"
transInsn (LI.And {LI.operand0,LI.operand1}) = do
  transArithInsn operand0 operand1 (T.Fixed "bwAnd") "and"
transInsn (LI.Or {LI.operand0,LI.operand1}) = do
  transArithInsn operand0 operand1 (T.Fixed "bwOr") "or"
transInsn (LI.Xor {LI.operand0,LI.operand1}) = do
  transArithInsn operand0 operand1 (T.Fixed "bwXor") "xor"
transInsn (LI.ZExt {LI.operand0,LI.type'}) = do
  -- XXX note this model is wrong for signed numbers, and we aren't checking the
  -- LLVM requirement that the original type has no more bits than the target
  -- type.
  (btype,e0) <- transFCOperand operand0
  btype' <- transType type'
  (resultTransformer,resultType) <-
    case (btype,btype') of
      -- sanity checking
      (IntType,IntType) -> return (id,IntType)
      (BoolType,IntType) -> return (\e -> T.EApp (T.EId cBoolToInt) [e], IntType)
      _ -> fail $ "Unsupported: non-integer types in ZExt instruction ("
               ++ ppBaseType btype ++ ") or (" ++ ppBaseType btype' ++ ")"
  fmap (Just resultType,) $ insnOuterLambda $ \(StateVars st sp tid) k -> return $
    T.EApp (T.EId k) [T.EId st, T.EId sp, T.EId tid, resultTransformer e0]
transInsn (LI.SExt {LI.operand0,LI.type'}) = do
  -- XXX right now, this always returns unknown because we aren't doing a good
  -- enough job keeping track of the size of ints to do better.
  --
  -- We also aren't checking the LLVM requirement that the original type has
  -- fewer bits than the target type.
  (btype,_) <- transFCOperand operand0
  btype' <- transType type'
  resultType <-
    case (btype,btype') of
      -- sanity checking
      (IntType,IntType) -> return IntType
      (BoolType,IntType) -> return IntType
      _ -> fail $ "Unsupported: non-integer types in SExt instruction ("
               ++ ppBaseType btype ++ ") or (" ++ ppBaseType btype' ++ ")"
  fmap (Just resultType,) $ insnOuterLambda $ \(StateVars st sp tid) k -> return $
    T.EApp (T.EId k) [T.EId st, T.EId sp, T.EId tid, unknownInt]
transInsn (LI.Trunc {LI.operand0,LI.type'}) = do
  (btype,e0) <- transFCOperand operand0
  bitsTarget <-
    case (btype,type') of
    -- sanity checking
      (IntType, L.IntegerType {L.typeBits}) -> return typeBits
      _ ->
        fail $ "Unsupported: non-integer types in Trunc instruction ("
            ++ ppBaseType btype ++ ") or (" ++ LP.showPretty type' ++ ")"
  (returnVal,retType) <-
    case bitsTarget of
      -- right now we support only truncating to 1,8 or 16 bits.
      1 -> return $ (T.EApp (T.EId $ T.Fixed "trunc1") [e0],BoolType)
      8 -> return $ (T.EApp (T.EId $ T.Fixed "trunc8") [e0],IntType)
      16 -> return $ (T.EApp (T.EId $ T.Fixed "trunc16") [e0],IntType)
      _ -> fail $ "Unsupported: truncation to " ++ show bitsTarget
               ++ "bits (only 1 and 8 supported currently)."
  fmap (Just retType,) $ insnOuterLambda $ \(StateVars st sp tid) k -> return $
    T.EApp (T.EId k) [T.EId st, T.EId sp, T.EId tid, returnVal]
transInsn (LI.Alloca {LI.allocatedType,LI.numElements}) = do
  when (isJust numElements) $ fail $
    "Unsupported: alloca with 'numElements' specifier."
  baseType <- transType allocatedType
  tinfo <- lookupTypeInfo baseType
  initVals <- reverse <$> unknownStackValues baseType
  -- Supposing we're pushing for type Foo, we make:
  --
  -- \(st,sp,tid,k) @ 
  --    pushOnStack (unknownFooData, st, sp, tid,
  --      \(st',sp',tid',loc) @ k (st',sp',tid',FooLocalLocTag.loc))
  fmap (Just (PointerType baseType),) $ insnOuterLambda $
    \(StateVars st sp tid) k -> do
      locVar <- freshTid $ Just "loc"
      innerL <- insnInnerLambda locVar $ \(StateVars st' sp' tid') ->
        return $ T.EApp (T.EId k)
                      [T.EId st', T.EId sp', T.EId tid',
                       T.EDot (T.EId $ tiLocalLocTag tinfo) [T.EId locVar]]
      return $ T.EApp (T.EId pushOnStackId)
                 [T.EList initVals,
                  T.EId st, T.EId sp, T.EId tid, innerL]
transInsn (LI.ICmp {LI.iPredicate,LI.operand0,LI.operand1}) = do
  (ty0,o0) <- transFCOperand operand0
  (ty1,o1) <- transFCOperand operand1
  fmap (Just BoolType,) $ case (ty0,ty1) of
    (IntType,IntType) -> do
      let f = transIPredicate iPredicate
      insnOuterLambda $ \(StateVars {svStack,svStackPtr,svThreadID}) k ->
        return $ T.EApp (T.EId k) [T.EId svStack, T.EId svStackPtr,
                                   T.EId svThreadID,
                                   T.EApp (T.EId f) [o0,o1]]
    (PointerType pr1, PointerType pr2) | pr1 == pr2 -> do
      -- Here we are being conservative, requiring pointer types (so not arrays)
      -- and requiring the subtypes be equal (rather than having the same
      -- representations).  XXX relax this eventually.  Also, if comparing
      -- function pointers, this will trigger a cspgen-time error in lookupTypeInfo.
      TypeInfo {tiLocEqCheck} <- lookupTypeInfo pr1
      let eqTerm = T.EApp (T.EId tiLocEqCheck) [o0,o1]
      resultTerm <-
        case iPredicate of
          LI.EQ -> return eqTerm
          LI.NE -> return $ T.EApp (T.EId $ T.Fixed "lnotBool") [eqTerm]
          _ -> fail $ "Unsupported: ICmp on pointers with predicate "
                   ++ LP.showPretty iPredicate
      insnOuterLambda $ \(StateVars st sp tid) k ->
        return $ T.EApp (T.EId k) [T.EId st, T.EId sp, T.EId tid, resultTerm]
    _ -> fail $ "Unsupported: ICmp used to compare type "
             ++ ppBaseType ty0 ++ " with " ++ ppBaseType ty1
transInsn (LI.Select {LI.condition',LI.trueValue,LI.falseValue}) = do
  -- [e ? e1 : e2]    
  --    ---->
  -- \(st,sp,tid,k) ->
  --     select(st,sp,tid,k,[e],[e1],[e2])
  --
  -- XXX the sanity checking here should probably be via "assignedLLVMType" and
  -- not the computed types from transOperand.
  (tyScrut,scrutVal) <- transFCOperand condition'
  (tyTrue,trueVal)   <- transFCOperand trueValue
  (tyFalse,falseVal) <- transFCOperand falseValue
  unless (tyScrut == BoolType) $
    fail $ "Illegal: scrutinee of Select operator has a type other than i1 ("
        ++ ppBaseType tyScrut ++ ")"
  repTypTrue <- lookupRepType tyTrue
  repTypFalse <- lookupRepType tyFalse
  unless (repTypTrue == repTypFalse) $
    fail $ "Illegal: branches of select operator have distinct types: "
        ++ ppBaseType tyTrue ++ "   and   " ++ ppBaseType tyFalse
  fmap (Just tyTrue,) $ insnOuterLambda $ \(StateVars st sp tid) k -> do
    return $ T.EApp (T.EId selectId)
                    [T.EId st, T.EId sp, T.EId tid, T.EId k,
                     scrutVal, trueVal, falseVal]
transInsn (LI.Call {LI.function,LI.arguments}) = do
  -- Roughly:
  -- \(st,sp,tid,k) @
  --    pushStackFrame(st,sp,tid,
  --      \(st',sp',tid',_) @
  --          f(<args>,st',sp',tid',k))
  --
  -- XXX should check for tail call and clear current stack frame if so
  -- XXX haven't considered parameter/return attributes at all
  fOp <- case function of
           Left _ -> fail "Unsupported: inline assembly function."
           Right o -> return o
  -- XXX. Not doing any type checking.  Probably should for good error messages.
  args <- mapM (fmap snd . transFCOperand . fst) arguments
  fmap (Nothing,) $ insnOuterLambda $ \(StateVars st sp tid) k -> do
    innerL <- insnInnerLambda noId $ \(StateVars st' sp' tid') ->
      transFunctionApplication fOp (args ++ map T.EId [st',sp',tid',k])
    return $ T.EApp (T.EId pushStackFrameId)
                    [T.EId st, T.EId sp, T.EId tid, innerL]
transInsn (LI.GetElementPtr {LI.address,LI.indices}) = do
  -- XXX need to think about "inBounds"

  -- See comment at "buildGEPHelpers" to understand what we're
  -- building here.
  intIndices <- mapM transGEPOperand indices
  (_,ptrVal) <- transFCOperand address
  assignedLType <- assignedOperandType address
  assignedBType <- transType assignedLType
  -- note we use the "assigned type" in the GEP calculations.  This is
  -- important: the type mentioned in an LLVM instruction is the basis for the
  -- calculations, not any type we may think we have inferred.  LLVM is
  -- permitted to lie here for purposes of pointer math.
  fmap (Nothing,) $ insnOuterLambda $
    \sv k -> buildGEPLookup ptrVal assignedBType sv k intIndices
transInsn (LI.BitCast {LI.operand0}) = do
  -- BitCast changes the type of a piece of data without changing the underlying
  -- bits.  When compiled for real, it's always a no-op.  For us, the situation
  -- is slightly more complicated, because of course our data representations
  -- depend on type.
  --
  -- In practice, the current strategy is this: we only support bitcast between
  -- types that have the same data representation in our model.  For example, if
  -- foo is a struct type with an int as its first element, then *foo and *int
  -- can be cast to each other.  We may do a little bit of sanity checking when
  -- we encounter a bitcast to see if the types are supported, but in general we
  -- are not guaranteeing good error messages right now (i.e., an unsupported
  -- bitcast may result in a type error in the generated CSP, rather than a nice
  -- error at cspgen runtime).
  (bty,e0) <- transFCOperand operand0
  fmap (Just bty,) $ insnOuterLambda $ \(StateVars st sp tid) k -> return $
    T.EApp (T.EId k) [T.EId st, T.EId sp, T.EId tid, e0]
transInsn i = fail $ "Unsupported instruction: " ++ show i

-- See comment at "buildGEPHelpers"
--
-- Arguments are:
--   - The current address
--   - Its BaseType
--   - the outer StateVars and continuation
--   - the list of indices
buildGEPLookup :: T.Exp -> BaseType -> StateVars -> T.Id -> [Either Int L.Name]
               -> CG T.Exp
buildGEPLookup e _ (StateVars {svStack,svStackPtr,svThreadID}) k [] =
  return $ T.EApp (T.EId k) [T.EId svStack, T.EId svStackPtr,
                             T.EId svThreadID, e]
buildGEPLookup _ _ _ _ (Left ix:_)| ix < 0 =
  fail "Unsupported: getElementPtr index is negative."
buildGEPLookup e (StructType flds) sv k (Left ix:ixs) | ix == 0 =
  case flds of
    [] -> fail "Unsupported: GEP index into empty struct type"
    (f1:_) -> buildGEPLookup e f1 sv k ixs
buildGEPLookup e bt@(StructType flds) sv k (Left ix:ixs) = do
  structTInfo <- lookupTypeInfo bt
  case (tiDataInfo structTInfo,flds) of
    (DIFirstClass _,_)  -> fail $ "Illegal: asked to index into first-class type "
                              ++ ppBaseType bt
    (DIArray _,_)      ->
       fail "Internal error: dataInfo for Struct is DIArray in buildGEPLookup"
    (_,[])      -> fail "Unsupported: GEP index into empty struct type"
    (DIStruct sinfo,_:fldsTail) ->
      case nth (zip (siGetFieldPtrs sinfo) fldsTail) (ix-1) of
        Nothing -> fail $ "Error: Attempt to index into field " ++ show ix
                       ++ " of type " ++ ppBaseType bt ++ ", but no such "
                       ++ "field found"
        Just (getFieldPtrId,fieldBT) -> do
          fieldTInfo <- lookupTypeInfo fieldBT
          locBndr <- freshTid $ Just "gepLocBndr"
          subFieldGEP <- buildGEPLookup (T.EId locBndr) fieldBT sv k ixs
          return $ T.EApp (T.EId $ tiLocMaybeElim fieldTInfo)
            [T.EApp (T.EId getFieldPtrId) [e],
             T.ELambda [T.PId locBndr] subFieldGEP,
             T.EPrefix (T.EId gepErrorName) [] (T.EConst T.CStop)]
buildGEPLookup _ (StructType _) _ _ (Right nm:_) =
  fail $ "Illegal: attempt to index into aggregate type with non-constant "
      ++ "index " ++ prettyLLVMName nm
buildGEPLookup e (NamedType nm) sv k ixs = do
  st <- lookupTypeDefFail nm "buildGEPLookup"
  bt' <- transType st
  buildGEPLookup e bt' sv k ixs
-- The next two cases use a "view pattern" to let us avoid duplication between
-- pointers and arrays.
buildGEPLookup e (isArrayLike -> Just (bt,_)) sv k (Left 0:ixs) =
  buildGEPLookup e bt sv k ixs
buildGEPLookup e (isArrayLike -> Just (bt,mlen)) sv k (ix:ixs) = do
  (intMin,intMax) <- getIntRange
  cspIndex <-
    case ix of
      Left i -> do
        when (i < 0) $ fail $ "Unsupported: negative array index " ++ show i
        case mlen of
          Nothing -> return ()
          Just len -> when (i >= len) $ fail $
               "Unsupported: index " ++ show i
            ++ "is out of bounds for array of length " ++ show len
        -- XXX we potentially lose lots of information here in translating this
        -- index - do something smarter.  Even if we stick with this, factor out
        -- the range checking.
        return $ if (i < intMin) || (i > intMax)
                   then unknownInt else knownInt (fromIntegral i)
      Right nm -> T.EId <$> lookupSSAName nm
  elementTInfo <- lookupTypeInfo bt
  locBndr <- freshTid $ Just "gepLocBndr"
  subFieldGEP <- buildGEPLookup (T.EId locBndr) bt sv k ixs
  return $ T.EApp (T.EId $ tiLocMaybeElim elementTInfo)
    [T.EApp (T.EId $ tiArrayIndexer elementTInfo) [e,cspIndex],
     T.ELambda [T.PId locBndr] subFieldGEP,
     T.EPrefix (T.EId gepErrorName) [] (T.EConst T.CStop)]
buildGEPLookup _ bt _ _ _ = fail $
  "GEP index into non-composite type " ++ ppBaseType bt

-- This checks if the input is a pointer or array type.  If so, it returns the
-- inner base type, and the length of the array if available.
isArrayLike :: BaseType -> Maybe (BaseType,Maybe Int)
isArrayLike (ArrayType bt len) = Just (bt, Just len)
isArrayLike (PointerType bt)   = Just (bt, Nothing)
isArrayLike _                  = Nothing


-- To avoid repeating a lot of code in the common case of an arithmetic operator
-- that has two operands which must have the same type.
transArithInsn :: L.Operand -> L.Operand -> T.Id -> String -> CG (Maybe BaseType,T.Exp)
transArithInsn operand0 operand1 runtimeImpl prettyName = do
  (ty1,val1) <- transFCOperand operand0
  (ty2,val2) <- transFCOperand operand1
  case (ty1,ty2) of
    (IntType,IntType) -> return ()
    _ -> fail $ "Arguments to \"" ++ prettyName ++ "\" instruction have "
             ++ "non-integer or non-matching types: " ++ ppBaseType ty1 
             ++ "  and  " ++ ppBaseType ty2
  let implExp = T.EApp (T.EId $ runtimeImpl) [val1,val2]
  fmap (Just ty1,) $ insnOuterLambda $ \(StateVars {svStack,svStackPtr,svThreadID}) k ->
    return $ T.EApp (T.EId k) $
      [T.EId svStack, T.EId svStackPtr, T.EId svThreadID, implExp]

transTerm :: AnalyzedBlock -> StateVars -> T.Id -> CG T.Exp
transTerm (AnalyzedBlock {abLabel,abTerminator,abLiveOut})
          (StateVars {svStack,svStackPtr,svThreadID})
          topLevelCont =
  let transDestArg :: Either L.Name L.Operand -> CG T.Exp
      transDestArg (Left n) = T.EId <$> lookupSSAName n
      transDestArg (Right o) = snd <$> transFCOperand o
      
      getDestArgs :: L.Name -> CG [T.Exp]
      getDestArgs block =
        case M.lookup block abLiveOut of
          Nothing -> fail $
               "Internal error: missing live-out data for block "
            ++ prettyLLVMName block ++ " from block "
            ++ prettyLLVMName abLabel
          Just args -> mapM transDestArg args
   in
  case abTerminator of
    _ LI.:= (LI.Ret {}) ->
      fail "Illegal: named 'return' terminator."
    LI.Do (LI.Ret {LI.returnOperand}) -> do
      retVal <-
        case returnOperand of
          Nothing -> return cspUnit
          Just rv -> snd <$> transFCOperand rv
      -- we build:
      --
      -- popStackFrame(st,sp,tid,
      --    \(st',sp',tid',_) @ topLevelCont (st',sp',tid',retVal))
      --
      -- This assumes retVal is constant.  Will be more complicated
      -- later.  XXX
      innerL <- insnInnerLambda noId $
        \StateVars {svStack=st',svStackPtr=sp',svThreadID=tid'} ->
          return $ T.EApp (T.EId topLevelCont)
                      [T.EId st', T.EId sp', T.EId tid', retVal]
      return $ T.EApp (T.EId popStackFrameId)
                 [T.EId svStack, T.EId svStackPtr, T.EId svThreadID, innerL]
    _ LI.:= (LI.CondBr {}) ->
      fail "Illegal: named 'conditional branch' terminator."
    LI.Do (LI.CondBr {LI.condition,LI.trueDest,LI.falseDest}) -> do
      (condType,condVal) <- transFCOperand condition
      (trueExp,falseExp) <-
        case condType of
          -- XXX losing information here by requiring intOne for true.
          IntType -> return (intOne,intZero)
          BoolType -> return (boolTrue,boolFalse)
          _ -> fail $
               "Type error in translation: argument ("
            ++ LP.showPretty condition ++ ") of conditional branch should "
            ++ "have type int but instead has type " ++ ppBaseType condType
      let standardArgs = map T.EId [svStack,svStackPtr,
                                    svThreadID,topLevelCont]
      thenLoc <- T.EId <$> lookupSSAName trueDest
      thenArgs <- getDestArgs trueDest
      let thenBranch = T.EApp thenLoc $ thenArgs ++ standardArgs
      elseLoc <- T.EId <$> lookupSSAName falseDest
      elseArgs <- getDestArgs falseDest
      let elseBranch = T.EApp elseLoc $ elseArgs ++ standardArgs
      return $
        T.EIfThenElse (T.EBinOp condVal T.BEq trueExp)
          thenBranch
          (T.EIfThenElse (T.EBinOp condVal T.BEq falseExp)
            elseBranch
            (T.EIntChoice thenBranch elseBranch))
    _ LI.:= (LI.Br {}) ->
      fail "Illegal: named 'branch' terminator."
    LI.Do (LI.Br {LI.dest}) -> do
      destLoc <- T.EId <$> lookupSSAName dest
      destArgs <- getDestArgs dest
      return $ T.EApp destLoc $
        destArgs ++ map T.EId [svStack,svStackPtr,svThreadID,topLevelCont]
    _ -> fail $ "Unsupported terminator: " ++ show abTerminator
  
-- This adds all the SSA variables in a function to the monad, since they may be
-- needed before they are declared.  This includes only the SSA variables
-- declared in the function body, not the function arguments (they are added
-- elsewhere).
addFunctionIDs :: String -> BasicData -> CG ()
addFunctionIDs fname (BasicData {blocks,varDefBlocks}) = do
  mapM_ (freshBlockSSA fname) $ M.keys blocks
  mapM_ freshSSAIfNotArg $ M.toList varDefBlocks
  where
    freshSSAIfNotArg :: (L.Name,DefSite) -> CG ()
    freshSSAIfNotArg (_,DSArg) = return ()
    freshSSAIfNotArg (n,_)     = void $ freshSSA n


transFunction :: L.Global -> CG [T.Definition]
transFunction (L.GlobalAlias _ _ _ _ _) =
  fail "Internal error: Alias encountered in transFunction"
transFunction (L.GlobalVariable _ _ _ _ _ _ _ _ _ _ _) =
  fail "Internal error: Variable encountered in transFunction"
transFunction (L.Function {L.name,L.parameters=(funArguments,funVarArgs),
                           L.basicBlocks}) = do
  setCurrentLoc $ "Function " ++ prettyFName
  case (basicBlocks,funVarArgs) of
    ([],_)   -> fail "Internal error: encountered declaration in transFunction"
    (_,True) -> -- varargs function
      fail $ "Varargs functions not supported: " ++ show name
    ((L.BasicBlock entrySid _ _):_,False) -> do
      -- begin by creating names for the top-level function and its arguments.
      argStack <- freshTid $ Just "funStack"
      argSP    <- freshTid $ Just "funSP"
      argTID   <- freshTid $ Just "funTID"
      argCont  <- freshTid $ Just "funCont"
      argOrig  <- mapM freshSSA argumentNames

      -- This is sanity checking: we should have added this function's
      -- declaration to the monad in transDefinition.  We could do more (for
      -- example, check whether the types this time match up with what we added
      -- to the monad), but I'm lazy and don't think that's necessary.
      ftid <- do
        mginfo <- lookupGlobal name
        case mginfo of
          Nothing -> fail $ "Internal error: function " ++ prettyLLVMName name
                         ++ "missing in transFunction."
          Just (GlobVar _) ->
            fail $ "Unsupported: function name " ++ prettyLLVMName name
                ++ "conflicts with global variable (in transFunction)"
          Just (GlobFunc gfi) -> do
            when (length (fargs gfi) /= length funArguments) $
              fail $ "Internal error: function definition has different "
                  ++ "number of arguments than declaration"
            return $ ftid gfi

      -- before translating the function body we add all SSA IDs used in it to
      -- the monad, since they may be used before declared.
      addFunctionIDs prettyFName basicData

      -- Now we translated the body of the function
      fblocks <- transBlocks aBlocks

      -- finally we construct the top-level function definition and clear the
      -- local variable state.
      entryTid <- lookupSSAName entrySid
      entryLive <-
        case M.lookup entrySid livenessData of
          Just (li,_) -> return $ M.keys li
          Nothing -> fail $
               "Internal Error: block " ++ prettyLLVMName entrySid
            ++ " missing liveness data."
      entryArgs <- mapM lookupSSAName entryLive
      clearSSAVars
      setFuncDefined name
      let
        body = T.EApp (T.EId entryTid) $ map T.EId
                    $ entryArgs ++ [argStack,argSP,argTID,argCont]
      {- return $ -}
      mapM squashDef $
          (T.DFun ftid
             [(map T.PId $ argOrig ++ [argStack,argSP,argTID,argCont],
               body)])
        : fblocks
  where
    argumentNames :: [L.Name]
    argumentNames = map (\(L.Parameter _ n _) -> n) funArguments

    basicData :: BasicData
    livenessData :: LivenessData
    aBlocks :: [AnalyzedBlock]
    (basicData,livenessData,aBlocks) =
      analyzeAndRepackage argumentNames basicBlocks

    prettyFName :: String
    prettyFName = prettyLLVMName name

-- This function looks at all the top-level definitions in a module.
-- Its only purpose is to add type definitions to the monad.  We do
-- this as a first pass because LLVM does not require names to be
-- declared before they are used.
addGlobalTypes :: [L.Definition] -> CG ()
addGlobalTypes = mapM_ addGlobalType
  where
    addGlobalType (L.TypeDefinition n Nothing) =
      fail $ "Unsupported: abstract type definition " ++ prettyLLVMName n
    addGlobalType (L.TypeDefinition n (Just llvmType)) = addTypeDef n llvmType
    addGlobalType _ = return ()

-- This function looks at all the top-level definitions in a module.
-- Its only function is to generate names for them (and add these
-- names to he monad).  This is necessary because LLVM does not
-- require names to be declared before they are used.
addGlobalNames :: [L.Definition] -> CG ()
addGlobalNames = mapM_ addGlobalName
  where
    addGlobalName :: L.Definition -> CG ()
    addGlobalName (L.GlobalDefinition (L.GlobalVariable {L.name}))
        | (   name == L.Name "llvm.global_ctors"
           || name == L.Name "llvm.global_dtors") =
      -- We handle the global initializers and destructors specially (as would any
      -- backend).  In particular, we don't add their names as normal globals.
      return ()
    addGlobalName (L.GlobalDefinition (L.GlobalVariable {L.name,L.type',
                                                         L.initializer})) = do
      setCurrentLoc $ "Global declaration " ++ prettyLLVMName name
      -- A special case to detect vtables - see DESIGN
      case isVTable type' initializer of
        Nothing -> do
          binfo <- transType type'
          freshGlobVar name binfo
        Just n -> freshGlobVar name (ArrayType FPtrType n)
    addGlobalName (L.GlobalDefinition 
         (L.Function {L.returnType,L.name,
                      L.parameters=(funArguments,funVarArgs)})) = do
      setCurrentLoc $ "Function " ++ prettyFName
      when funVarArgs $
        fail $ "Unsupported: Varargs function: " ++ show name
      
      returnBT <- transType returnType
      argBTs   <- mapM transType argumentTypes
      mtid <- lookupGlobal name
--    XXX add some check here for multiply declared things (but the check
--    out below is no good because it doesn't account for runtime stuff).
--      unless (isNothing mtid) $
--        fail $ "Unsupported: multiple declarations of top-level variable or "
--            ++ "function " ++ prettyFName
      when (isNothing mtid) $
        freshFunc name returnBT argBTs False
      where
        argumentTypes :: [L.Type]
        argumentTypes = map (\(L.Parameter t _ _) -> t) funArguments

        prettyFName :: String
        prettyFName = prettyLLVMName name
    addGlobalName (L.GlobalDefinition (L.GlobalAlias {L.name,L.aliasee})) = do
      case aliasee of
        LC.GlobalReference _ aliaseeName -> addAlias name aliaseeName
        _ -> fail $ "Unsupported: alias target is not a global identifier: "
                 ++ LP.showPretty aliasee
    addGlobalName _ = return ()

-- This function looks at the type and initializer for a top-level global and
-- attempts to determine if this global is a vtable.  We use a very simple
-- heuristic: If the global has type [n x i8*] for some n, and its initializer
-- consists of only "null" and bitcast function pointers (and there is at least
-- one fptr), then it's a vtable.  If the heuristic is met, we return n.
isVTable :: L.Type -> Maybe LC.Constant -> Maybe Int
isVTable (L.ArrayType {L.elementType,L.nArrayElements})
         (Just (LC.Array {LC.memberValues})) =
  case elementType of
    (L.PointerType {L.pointerReferent=L.IntegerType {L.typeBits}})->
      if typeBits == 8 && vtableMembers memberValues
         then Just (fromIntegral nArrayElements) else Nothing
    _ -> Nothing
  where
    vtableMembers :: [LC.Constant] -> Bool
    vtableMembers = vtableWalker False

    -- Bool indicates whether we've seen a bitcast function yet.
    vtableWalker :: Bool -> [LC.Constant] -> Bool
    vtableWalker seenF [] = seenF
    vtableWalker seenF (c:cs) =
      case c of
        LC.Null _ -> vtableWalker seenF cs
        LC.BitCast {LC.operand0=LC.GlobalReference t _} ->
          case t of
           L.PointerType {L.pointerReferent=L.FunctionType {}} -> 
             vtableWalker True cs
           _ -> False
        _ -> False
isVTable _ _ = Nothing

-- Like isVTable, this checks a type and initializer to determine if they
-- represent a vtable.  Unlike isVTable, it also translates the initializer.
-- This could not be done in isVTable because that function is called before
-- names for all functions have been generated.
transVTableInit :: L.Type -> LC.Constant -> CG (Maybe (Int,DataRep))
transVTableInit (L.ArrayType {L.elementType,L.nArrayElements})
                (LC.Array {LC.memberValues}) =
  case elementType of
    (L.PointerType {L.pointerReferent=L.IntegerType {L.typeBits}})->
      if typeBits == 8
         then vtableWalker False (fromIntegral nArrayElements)
                           memberValues []
         else return Nothing
    _ -> return Nothing
  where
    -- Bool indicates whether we've seen a bitcast function yet.
    vtableWalker :: Bool -> Int -> [LC.Constant] -> [DataRep]
                 -> CG (Maybe (Int,DataRep))
    vtableWalker seenF n [] agg = return $ 
      if seenF then Just (n,DRAgg (reverse agg)) else Nothing
    vtableWalker seenF n (c:cs) agg =
      case c of
        LC.Null _ -> vtableWalker seenF n cs ((DRValue $ T.EDot (T.EId fptrNullCon) []):agg)
        LC.BitCast {LC.operand0} -> do
          (ty,val) <- transConstant operand0
          case (ty,val) of
           (FPtrType, DRValue v)->
             vtableWalker True n cs (DRValue v : agg)
           _ -> return Nothing
        _ -> return Nothing
transVTableInit _ _ = return Nothing

-- This function looks at every top-level definition in a module.  It
-- translates the variable initializers, and filters out everything
-- but the function definitions, which are handled elsewhere.
--
-- There are two special cases: the global initializers and destructors, which
-- are identified by name and handled by helper functions
transDefinitions :: [L.Definition] -> CG [L.Global]
transDefinitions defs = reverse <$> foldM td [] defs
  where
    td :: [L.Global] -> L.Definition -> CG [L.Global]
    td gs (L.GlobalDefinition (L.GlobalVariable {L.name,L.initializer}))
        | name == (L.Name "llvm.global_ctors") = do
      setCurrentLoc "Global variable: llvm.global_ctors"
      transCtors initializer
      return gs
    td gs (L.GlobalDefinition (L.GlobalVariable {L.name,L.initializer}))
        | name == (L.Name "llvm.global_dtors") = do
      setCurrentLoc "Global variable: llvm.global_dtors"
      transDtors initializer
      return gs
    td gs (L.GlobalDefinition
             (L.GlobalVariable {L.name,L.type',L.initializer})) = do
      -- XXX Would like also to consider linkage,visibility,threadLocalmode, at least
      setCurrentLoc $ "Global declaration " ++ prettyLLVMName name
      (btype,val) <- do
        -- as in addGlobalNames, we have a special case here to check for a
        -- vtable.  See DESIGN.
        mVTI <- maybe (return Nothing) (transVTableInit type') initializer
        case mVTI of
          (Just (n,vti)) ->
            return (ArrayType FPtrType n,vti)
          _ -> do
            btype <- transType type'
            (btype',val) <- 
              case initializer of
                Nothing -> do
                  addWarning "UndefGlobal"
                     ("Global declaration without initializer " ++ show name)
                  v <- unknownValue btype
                  return (btype,v)
                Just i  -> transConstant i
            unless (btype == btype') $ fail $
                 "Type error in translation: global location type ("
              ++ ppBaseType btype
              ++ ") does not match type of its initializer ("
              ++ ppBaseType btype'
            return (btype,val)
      freshGlobMem name btype val
      return gs
    td gs (L.GlobalDefinition (L.GlobalAlias _ _ _ _ _)) = return gs
    td gs (L.GlobalDefinition 
             g@(L.Function {L.basicBlocks})) = do
      return $ if null basicBlocks then gs else (g:gs)
    td gs (L.TypeDefinition _ _)          = return gs
    td gs (L.MetadataNodeDefinition _ _)  = return gs
    td gs (L.NamedMetadataDefinition _ _) = return gs
    td _ (L.ModuleInlineAssembly _)       =
      fail "Unsupported: Assembly node encountered in transDefinitions"

    -- these functions handle the global initialization and teardown code.
    transCtors :: Maybe LC.Constant -> CG ()
    transCtors mc =
      case mc of
        Nothing -> fail "Illegal: llvm.global_ctors is missing definition"
        Just c  -> transCDtors addCtor c

    transDtors :: Maybe LC.Constant -> CG ()
    transDtors md = 
      case md of
        Nothing -> fail "Illegal: llvm.global_dtors is missing definition"
        Just d  -> transCDtors addDtor d

    transCDtors :: ((Int,L.Name) -> CG ()) -> LC.Constant -> CG ()
    transCDtors add (LC.Array {LC.memberValues}) = mapM_ addVal memberValues
      where
        addVal :: LC.Constant -> CG ()
        addVal (LC.Struct {LC.memberValues=[LC.Int {LC.integerValue},
                                            LC.GlobalReference _ nm]}) =
          add (fromIntegral integerValue,nm)
        addVal c = fail $ "Unsupported: ctors/dtors member does not have "
                       ++ " expected {int,var} shape.  " ++ LP.showPretty c
    transCDtors _ c =
      fail $ "Unsupported: ctors/dtors does not have expected Array shape: "
          ++ LP.showPretty c

-- Given a base type, this calculates the "unknown" value of that type in our
-- model.  This is really a helper for our implementation of Alloca, so the
-- output is in a weird form: a list of stack values.  In the case of a simple
-- type, like Int, there will just be one thing in the list.  In the case of a
-- composite type, like a struct, the list will contain many things - one for
-- each 'first-class' piece of data in the struct.
--
-- TODO: add "unknown" float/mutex/pid values to model?
unknownStackValues :: BaseType -> CG [T.Exp]
unknownStackValues IntType   =
  return [T.EDot (T.EId $ fciStackValTag intFCInfo) [unknownInt]]
unknownStackValues BoolType  =
  return [T.EDot (T.EId $ fciStackValTag boolFCInfo) [unknownBool]]
unknownStackValues FloatType =
  return [T.EDot (T.EId $ fciStackValTag floatFCInfo) [unknownFloat]]
unknownStackValues ptrBT@(PointerType innerBT) = do
  ptrTInfo <- lookupTypeInfo ptrBT
  innerTInfo <- lookupTypeInfo innerBT
  case tiDataInfo ptrTInfo of
    DIFirstClass (FirstClassInfo {fciStackValTag}) ->
      return [T.EDot (T.EId fciStackValTag) [T.EId $ tiUnknownLoc innerTInfo]]
    _ -> fail $ "Internal error: pointer type missing FirstClassInfo "
             ++ "in unknownStackValues (" ++ ppBaseType ptrBT ++ ")"
unknownStackValues (StructType bts) =
  concat <$> mapM unknownStackValues bts
unknownStackValues (NamedType n) = do
  sty <- lookupTypeDefFail n "unknownStackValues"
  bty <- transType sty
  unknownStackValues bty
unknownStackValues (ArrayType bt len) =
  concat . replicate len <$> unknownStackValues bt
unknownStackValues FPtrType =
  return [T.EDot (T.EId $ fciStackValTag fptrFCInfo) [T.EId fptrUnknownCon]]
unknownStackValues t = fail $ "Internal Error: unknownStackValue "
                     ++ "called on unsupported type " ++ ppBaseType t 
                     ++ "."

-- Compute an unknown value for a first-class type.
unknownFCValue :: BaseType -> CG T.Exp
unknownFCValue bt = do
  mv <- unknownValue bt
  case mv of
    DRValue e -> return e
    DRAgg _ -> fail $ "Internal error: unknownFCValue called on "
                   ++ "non-first class type " ++ ppBaseType bt

unknownValue :: BaseType -> CG DataRep
unknownValue IntType   = return $ DRValue unknownInt
unknownValue BoolType  = return $ DRValue unknownBool
unknownValue FloatType = return $ DRValue unknownFloat
unknownValue (PointerType innerBT) = do
  innerTInfo <- lookupTypeInfo innerBT
  return $ DRValue $ T.EId $ tiUnknownLoc innerTInfo
unknownValue (NamedType n) = do
  sty <- lookupTypeDefFail n "unknownFCValue"
  bty <- transType sty
  unknownValue bty
unknownValue VoidType  = return $ DRValue cspUnit
unknownValue FPtrType  = return $ DRValue $ T.EId fptrUnknownCon
unknownValue MutexType = return $ DRValue uninitializedMutex
unknownValue PIDType   = return $ DRValue $ T.EDot (T.EId tidUnknownCon) []
unknownValue (StructType bts) = DRAgg <$> mapM unknownValue bts
unknownValue (ArrayType bt len) = do
  cell <- unknownValue bt
  return $ DRAgg $ replicate len cell
unknownValue FunctionType =
  fail $ "Internal error: FunctionType encountered in unknownValue"

-- TODO: add "null" float/mutex/pid values to model?
zeroedValue :: BaseType -> CG DataRep
zeroedValue IntType    = return $ DRValue intZero
zeroedValue BoolType   = return $ DRValue boolFalse
zeroedValue FloatType  = return $ DRValue unknownFloat
zeroedValue (PointerType bt) = do
  tinfo <- lookupTypeInfo bt
  return $ DRValue $ T.EId $ tiNullLoc tinfo
zeroedValue MutexType  = return $ DRValue uninitializedMutex
zeroedValue PIDType    = return $ DRValue $ T.EDot (T.EId tidUnknownCon) []
zeroedValue (StructType bts) = DRAgg <$> mapM zeroedValue bts
zeroedValue (NamedType n) = do
  sty <- lookupTypeDefFail n "zeroedValue"
  bty <- transType sty
  zeroedValue bty
zeroedValue (ArrayType bt len) = do
  cell <- zeroedValue bt
  return $ DRAgg $ replicate len cell
zeroedValue t = fail $ "Internal Error: zeroedValue "
                     ++ "called on unsupported type " ++ ppBaseType t 
                     ++ "."


---------------
-- Memory model

-- A helper type for constructing the MInfo - maps instead of lists
data MIMaps = MIMaps {fcMap     :: M.Map BaseType [GlobVarInfo],
                      structMap :: M.Map BaseType [GlobVarInfo],
                      arrayMap  :: M.Map BaseType [GlobVarInfo]}
  deriving (Show)

-- Run through the accumulated state and build the MemInfo.  The main subtlety
-- here is to do with aggregate types.  Structs and arrays have a bunch of
-- subelements that need to be added to the MemInfo lists of the appropriate
-- types.
createMemInfo :: CG MemInfo
createMemInfo = do
  globals  <- map snd <$> allGlobals
  typinfs  <- allTypeInfos

  let
    -- This is the first pass at sorting the global variables into MIMaps.  It's
    -- missing only data for types where there are no globals.
    allVarsMap :: MIMaps
    allVarsMap =
      foldl' processGlobal (MIMaps M.empty M.empty M.empty) globals

    addTypeInfo :: (BaseType,b) -> CG (TypeInfo,b)
    addTypeInfo (bt,v) = (,v) <$> lookupTypeInfo bt

  let
    -- This stuff just adds types with no globals info the MIMaps.  They are
    -- needed because the runtime has stuff that relies on, for example, a
    -- definition of Int or Bool (even if there aren't any Int variables in the
    -- program).
    addEmptyBType :: BaseType -> M.Map BaseType [a] -> M.Map BaseType [a]
    addEmptyBType bt m = M.alter (Just . (maybe [] id)) bt m

    checkTInfo :: MIMaps -> TypeInfo -> MIMaps
    checkTInfo mi (TypeInfo {tiBase}) =
      case tiBase of
        StructType _ -> mi {structMap = addEmptyBType tiBase (structMap mi)}
        ArrayType bt _ -> mi {arrayMap = addEmptyBType bt (arrayMap mi)}
        _ -> mi {fcMap = addEmptyBType tiBase (fcMap mi)}

    mimaps :: MIMaps
    mimaps = foldl' checkTInfo allVarsMap typinfs

  uncoalescedFD <- mapM addTypeInfo $ M.toList $ fcMap mimaps
  let firstClassMInfo = coalesceTypeInfos uncoalescedFD
  structMInfo <- mapM addTypeInfo $ M.toList $ structMap mimaps
  arrayMInfo <- mapM addTypeInfo $ M.toList $ arrayMap mimaps

  return MInfo {firstClassMInfo,structMInfo,arrayMInfo}
  where
    processGlobal :: MIMaps -> GlobInfo -> MIMaps
    processGlobal m (GlobVar gvi) = addGVI m gvi
    processGlobal m (GlobFunc _) = m

    addToMap :: M.Map BaseType [a] -> BaseType -> a -> M.Map BaseType [a]
    addToMap m bt a = M.alter (\mas -> Just $ maybe [a] (a:) mas) bt m

    -- This assumes that it can ignore anything without a definition, as we
    -- don't need memory for it.
    addGVI :: MIMaps -> GlobVarInfo -> MIMaps
    addGVI m (GVInfo {gvlayout=Nothing}) = m
    addGVI m gvi@(GVInfo {gvtype,gvlayout=Just (GVCell _)}) =
      m {fcMap = addToMap (fcMap m) gvtype gvi}
    addGVI m gvi@(GVInfo {gvtype,gvlayout=Just (GVAgg gvis)}) =
      foldl' addGVI m' gvis
        where
          m' :: MIMaps
          m' = case gvtype of
                 (ArrayType bt _) ->
                   m {arrayMap = addToMap (arrayMap m) bt gvi}
                 (PointerType bt) ->
                   m {arrayMap = addToMap (arrayMap m) bt gvi}
                 -- Should I check for struct in this last case?  Would have
                 -- to thread in monad for error, and it's checked elsewhere..
                 _ -> m {structMap = addToMap (structMap m) gvtype gvi}

    -- Multiple BaseTypes have the same TypeInfos, or at least TypeInfos which
    -- share all location information.  For our firstClassMInfo, we want them to
    -- be identified.  We pick a representative TypeInfo, with a preference for
    -- one with FirstClassInfo.
    coalesceTypeInfos :: [(TypeInfo,[a])] -> [(TypeInfo,[a])]
    coalesceTypeInfos tis =
      map (\group -> let (gtis,gvars) = unzip group in
                     (pickTIRep gtis, concat gvars))
          groupedTIs
      where
        -- groupedTIs :: [[(TypeInfo,[a])]]
        fLocs f (ti1,_) (ti2,_) = f (tiLocType ti1) (tiLocType ti2)
        groupedTIs = groupBy (fLocs (==)) $ sortBy (fLocs compare) tis

        hasFCI :: TypeInfo -> Bool
        hasFCI ti = case tiDataInfo ti of
                      DIFirstClass _ -> True
                      _ -> False

        pickTIRep :: [TypeInfo] -> TypeInfo
        pickTIRep tiGroup =
          case filter hasFCI tiGroup of
            (t:_) -> t
            [] -> case tiGroup of
                   (t:_) -> t
                   [] -> error "Impossible: groupBy created empty sublist"
       

-- buildCspChannels builds the CSP channel declarations that list all
-- the channels we'll use to read and write to global variable cells.
-- Types for which there are no global variables do not get channels.
--
-- Only "first-class" types have variable cells.  Composite type, like
-- structs, are represented by multiple cells (just like in real
-- memory!).  Thus, there are no channels for structs.
--
-- As an example, for Ints, we have the channels:
--
-- channel int_read    : TIDTyp.Int_GLoc.Int_Typ
-- channel foo_write   : TIDTyp.Int_GLoc.Int_Typ
--
-- So a read communicates the thread ID, the location, and the value read.  A
-- write is the same, except with the value written.
buildCspChannels :: MemInfo -> [T.Definition]
buildCspChannels minfo = concatMap typChans $ firstClassMInfo minfo
  where
    -- type communicated over the channel (e.g., PIDTyp.Foo_GLoc.Foo_Typ)
    typChans :: (TypeInfo,[GlobVarInfo]) -> [T.Definition]
    typChans (_,[]) = []
    typChans (ti,_) =
      case tiDataInfo ti of
        DIFirstClass fci ->
          [T.DChan [fciReaderChan fci] chanArgs,
           T.DChan [fciWriterChan fci] chanArgs]
          where
           chanArgs = map T.TData [tidTypId,tiGlobalLocType ti,fciRepType fci]
        _ -> []

-- varCellBuilders constructs, for each first-class type, a CSPm function that
-- builds global variable cells of that type.  The function has type:
--
--     Typ_VAR :: (tiGlobalLocType fciInfo) -> (tyRepType tinfo) -> Proc
--
-- which builds a process representing a global variable of the appropriate
-- type.  Once again, we only do this for first-class types which have global
-- memory locations.
buildVarCellBuilders :: MemInfo -> CG [T.Definition]
buildVarCellBuilders (MInfo {firstClassMInfo}) =
  mapM buildChan
       [fci | (TypeInfo {tiDataInfo=DIFirstClass fci},tvGlobals) <- firstClassMInfo,
              not (null tvGlobals)]
  where
    buildChan :: FirstClassInfo -> CG T.Definition
    buildChan (FirstClassInfo {fciVarCellBuilder,
                               fciReaderChan,fciWriterChan}) = do
      topDataVar   <- freshTid $ Just "x"
      writeDataVar <- freshTid $ Just "x'"
      locVar       <- freshTid $ Just "vLoc"
      let locExp = T.EId locVar
          topDVExp = T.EId topDataVar
          writeDVExp = T.EId writeDataVar
          readCExp = T.EId fciReaderChan
          writeCExp = T.EId fciWriterChan
      return $
        -- VAR(loc,x) =
        --     reader_c?_!loc!x  -> VAR(loc,x)
        --  [] writer_c?_!loc?x' -> VAR(loc,x')
        T.DFun fciVarCellBuilder
          [([T.PId locVar, T.PId topDataVar],
            T.EExtChoice
              (T.EPrefix readCExp
                         [T.CFInput (T.PId noId), T.CFOutput locExp,
                          T.CFOutput topDVExp]
                         (T.EApp (T.EId fciVarCellBuilder)
                                 [locExp,topDVExp]))
              (T.EPrefix writeCExp
                         [T.CFInput (T.PId noId), T.CFOutput locExp,
                          T.CFInput $ T.PId writeDataVar]
                         (T.EApp (T.EId fciVarCellBuilder)
                                 [locExp,writeDVExp])))]

-- buildDataReps constructs the datatypes representing the actual LLVM types
--
-- This is much simpler than our original C version, because composite
-- types don't have representations in the LLVM model.  So all we have
-- here are base types.  Pointers also need a data rep, of course, but
-- they are defined elsewoere.
buildDataReps :: CG [T.Definition]
buildDataReps = do
  (cIntMin,cIntMax) <- getIntRange
  return $ (minIntDef cIntMin):(maxIntDef cIntMax):baseTypes
  where
    baseTypes = [intDataRep, cBoolDataRep, cFloatDataRep, unitDataRep, 
                 maxTidDef, tidDataRep, maxMidDef, midDataRep, mutDataRep]

-- buildLocationReaders builds a CSPm function that reads data from a memory
-- address.  This is a little complicated because the memory address might
-- come in any of four forms: Null, Unknown, a global address, or a local
-- address.
--
--   - In the case of Null or Unknown, we deadlock.
--                (XXX also send an alert signal?)
--
--   - In the case of a global address, we communicate with the appropriate
--     variable process.
--
--   - In the case of a local address, we read from the stack
--
-- We determine which case we are in by pattern matching on the provided
-- address.
--
-- The generated CSPm function is meant to look like:
--
--  readFoo :: (Stack, StackPtr, PIDTyp, FooLoc,
--              (Stack, StackPtr, PIDTyp, FooTyp) -> Proc) 
--          -> Proc
-- 
--  readFoo(_,_,tid,(FooGlobalTag.loc),k) = readFoo!tid!x?v -> k(st,sp,tid,v)
--  readFoo(st,sp,tid,(FooLocalTag.loc),k)  =
--     readFromStack (loc,fooStackValProj,st,sp,tid,k)
--  readFoo(_,_,_,FooNullLoc,_)           = STOP
--  readFoo(_,_,_,FooUnknownLoc,_)        = STOP
-- 
-- The first three arguments are the current stack, stack pointer, and thread
-- ID.  The next is the location we are meant to read from.  The last argument
-- is a continuation, which tells us what to do with the value stored in the
-- location once we find it.
-- 
-- It's necessary to use CPS here instead of just returning a FooTyp, because
-- a CSPm function with that return type would have no way to read from the
-- variable cells in the case of a global variable.
--
-- There is one small additional complication: For types with no global
-- variables, we do not generate the channels that would be used to read or
-- write those global variables.  So, in that case, we must also not generate
-- the clause of this definition that would access global variables.
buildLocationReaders :: MemInfo -> CG [T.Definition]
buildLocationReaders minfo =
  mapM buildLocationReader $ firstClassMInfo minfo
  where
    buildLocationReader :: (TypeInfo,[GlobVarInfo]) -> CG T.Definition
    buildLocationReader (TypeInfo {tiDataInfo=DIStruct _},_) =
      fail "Unsupported: struct in buildLocationReader"
    buildLocationReader (TypeInfo {tiDataInfo=DIArray _},_) =
      fail "Unsupported: array in buildLocationReader"
    buildLocationReader (TypeInfo {tiNullLoc,tiUnknownLoc,
                                   tiGlobalLocTag,tiLocalLocTag,
                                   tiDataInfo=DIFirstClass fci},
                         gvs) = do
      sBnd <- freshTid $ Just "st"
      spBnd <- freshTid $ Just "sp"
      tBnd <- freshTid $ Just "tid"
      lBnd <- freshTid $ Just "loc"
      kBnd <- freshTid $ Just "k"  
      vBnd <- freshTid $ Just "v"
      -- inner lambda for local reader, see below
      localInnerL <- insnInnerLambda vBnd $
        \StateVars {svStack=sBnd', svStackPtr=spBnd', svThreadID=tBnd'} ->
          return $ T.EApp (T.EId $ fciStackValProj fci) $
                     map T.EId [vBnd,sBnd',spBnd',tBnd',kBnd]
      return $ T.DFun (fciReader fci) $
          -- readFoo(st,sp,tid,FooNullLoc,k) = STOP
          ([T.PId sBnd,T.PId spBnd,T.PId tBnd,T.PId tiNullLoc,T.PId kBnd],
           T.EConst T.CStop)
          -- readFoo(st,sp,tid,FooUnknownLoc,k) = STOP
        : ([T.PId sBnd,T.PId spBnd,T.PId tBnd,T.PId tiUnknownLoc,T.PId kBnd],
           T.EConst T.CStop)
        : -- readFoo(st,sp,tid,(FooLocalTag.loc),k) =
          --     readValFromStack(loc,st,sp,tid,
          --         \(st',sp',tid',v) @ fooStackValProj(v,st',sp',tid',k))
          -- XXX can we take this out for types that can't go on the stack?
          ([T.PId sBnd,T.PId spBnd,T.PId tBnd,
            T.PDot (T.PId tiLocalLocTag) [T.PId lBnd], T.PId kBnd],
               T.EApp (T.EId readFromStackId) $
                 [T.EId lBnd, T.EId sBnd, T.EId spBnd,
                  T.EId tBnd, localInnerL])
          --  readFoo(_,_,tid,(FooGlobalTag.loc),k) =
          --       readFoo!tid!x?v -> k(st,sp,tid,v)
        : case gvs of
            [] -> []
            (_:_) ->
              [([T.PId sBnd, T.PId spBnd, T.PId tBnd,
                 T.PDot (T.PId tiGlobalLocTag) [T.PId lBnd], T.PId kBnd],
               gread (fciReaderChan fci) (T.EId tBnd) (T.EId lBnd) vBnd
                (T.EApp (T.EId kBnd) [T.EId sBnd,T.EId spBnd,T.EId tBnd,T.EId vBnd]))]

-- buildLocationWriters is an awful lot like buildLocationReaders (see above),
-- so I'll give the cliffs notes.  I'm sure these two definitions could be
-- combined in some elegant way, but they are already getting a little
-- unwieldly, so I skipped it.
--
-- The writers have this type:
--
--  writeFoo :: (Stack, StackPtr, TIDTyp, FooLoc, FooType,
--               (Stack, StackPtr, TIDTyp, FooType) -> Proc)
--           -> Proc
--
-- The primary difference is that the caller must supply the value to be
-- written.  We could have chosen to make the continuation here just
-- ((Stack,StackPtr,PIDTyp) -> Proc), since we're not reading any data that
-- needs to be passed on in this case.  But, for convenience and uniformity with
-- other statements, we pass along the value that was written (much like how "x
-- = e" is an expression that evaluates to e in C).
-- 
--  writeFoo(st,sp,tid,(FooGlobalTag.loc),v,k) = writeFoo!tid!x!v -> k(st,sp,tid,v)
--  writeFoo(st,sp,tid,(FooLocalTag.loc),v,k)  =
--    writeToStack(loc,FooTag.v,st,sp,tid,k)
--  writeFoo(_,_,_,FooNullLoc,_,_)             = STOP
--  writeFoo(_,__,,FooUnknownLoc,_,_)          = STOP
buildLocationWriters :: MemInfo -> CG [T.Definition]
buildLocationWriters minfo =
  mapM buildLocationWriter $ firstClassMInfo minfo
  where
    buildLocationWriter :: (TypeInfo,[GlobVarInfo]) -> CG T.Definition
    buildLocationWriter (TypeInfo {tiDataInfo=DIStruct _},_) =
      fail "Unsupported: struct in buildLocationWriter"
    buildLocationWriter (TypeInfo {tiDataInfo=DIArray _},_) =
      fail "Unsupported: array in buildLocationWriter"
    buildLocationWriter (TypeInfo {tiNullLoc,tiUnknownLoc,
                                   tiGlobalLocTag,tiLocalLocTag,
                                   tiDataInfo=DIFirstClass fci},
                         gvs) = do
      sBnd <- freshTid $ Just "st"
      spBnd <- freshTid $ Just "sp"
      tBnd <- freshTid $ Just "tid"
      lBnd <- freshTid $ Just "loc"
      kBnd <- freshTid $ Just "k"  
      vBnd <- freshTid $ Just "v"  
      -- inner lambda for local writer, see below
      localInnerL <- insnInnerLambda noId $
        \StateVars {svStack=sBnd', svStackPtr=spBnd', svThreadID=tBnd'} ->
          return $ T.EApp (T.EId kBnd) $
                     map T.EId [sBnd',spBnd',tBnd',vBnd]
      return $ T.DFun (fciWriter fci) $
          -- writeFoo(st,sp,tid,FooNullLoc,v,k) = STOP
          (map T.PId [sBnd,spBnd,tBnd,tiNullLoc,vBnd,kBnd],
           T.EConst T.CStop)
          -- writeFoo(st,sp,tid,FooUnknownLoc,v,k) = STOP
        : (map T.PId [sBnd,spBnd,tBnd,tiUnknownLoc,vBnd,kBnd],
           T.EConst T.CStop)
        : -- writeFoo(st,sp,tid,(FooLocalTag.loc),v,k) =
          --     writeToStack(loc,fooStackTag.v,st,sp,tid,
          --                    \st',sp',tid',_ @ k (st',sp',tid',v))
          -- XXX super ugly re-wrapping of k just to pass v instead of
          --     tagged v.  Maybe rethink interface here?  Rushing now.
          -- XXX can we take this out for types that can't go on the stack?
          ([T.PId sBnd,T.PId spBnd,T.PId tBnd,
            T.PDot (T.PId tiLocalLocTag) [T.PId lBnd],
            T.PId vBnd,T.PId kBnd],
                T.EApp (T.EId writeToStackId) $
                  [T.EId lBnd, T.EDot (T.EId $ fciStackValTag fci) [T.EId vBnd],
                   T.EId sBnd, T.EId spBnd, T.EId tBnd, localInnerL])
          --  writeFoo(st,sp,tid,(FooGlobalTag.loc),v,k) =
          --     writeFoo!tid!x!v -> k(st,sp,tid,v)
        : case gvs of
            [] -> []
            (_:_) ->
              [([T.PId sBnd, T.PId spBnd, T.PId tBnd,
                 T.PDot (T.PId tiGlobalLocTag) [T.PId lBnd],
                 T.PId vBnd, T.PId kBnd],
                gwrite (fciWriterChan fci) (T.EId tBnd) lBnd (T.EId vBnd)
                   (T.EApp (T.EId kBnd) (map T.EId [sBnd,spBnd,tBnd,vBnd])))]

-- buildTypedMemory builds a CSP process representing all the memory
-- associated with data of a particular type.  This process is just:
-- 
--   Foo_VAR(nm1,init1) ||| ... ||| Foo_VAR(nmk,initk)
-- 
-- for each global variable of type Foo.
--
-- XXX would it be more efficient to do this with renaming?
buildTypedMemory :: MemInfo -> CG [T.Definition]
buildTypedMemory minfo = 
  catMaybes <$> (mapM buildTypMem $ firstClassMInfo minfo)
  where
    buildTypMem :: (TypeInfo,[GlobVarInfo]) -> CG (Maybe T.Definition)
    buildTypMem (_,[])     = return Nothing
    buildTypMem (TypeInfo {tiDataInfo=DIStruct _},_) = return Nothing
    buildTypMem (TypeInfo {tiDataInfo=DIArray _},_) = return Nothing
    buildTypMem (TypeInfo {tiDataInfo=DIFirstClass fci},gvars) =
        (Just . T.DVar (T.PId $ fciVarCells fci)) <$> buildCells gvars
      where
        eVCB = T.EId $ fciVarCellBuilder fci

        initOrFail :: GlobVarInfo -> CG T.Exp
        initOrFail (GVInfo {gvtid,gvlayout}) =
          case gvlayout of
            Just (GVCell e) -> return e
            Just (GVAgg _) ->
              fail $ "Internal error: aggregate initializer encountered in "
                  ++ "buildTypedMemory at variable " ++ T.namePart gvtid
            Nothing -> 
              fail $ "Internal error: uninitialized memory encountered in "
                  ++ "buildTypedMemory at variable " ++ T.namePart gvtid
        
        buildCells :: [GlobVarInfo] -> CG T.Exp
        buildCells [] = fail "Internal Error: buildCells on empty list"
        buildCells [gvi] = do
          i <- initOrFail gvi
          return $ T.EApp eVCB [T.EDot (T.EId $ gvtid gvi) [],i]
        buildCells (gvi:gs) = do
          i <- initOrFail gvi
          T.EInterleave (T.EApp eVCB [T.EDot (T.EId $ gvtid gvi) [],i]) 
            <$> (buildCells gs)

-- buildLocations builds the datatypes representing the memory locations.
--
-- For each type, we build a datatypes of all global addresses of this type
--
--   data FooGlobals = Foo_z1 | Foo_z2 | ...
--
-- These list a unique address for every global of the appropriate type.
--
-- A location of a particular type is either null, unknown, a stack address, or
-- one of these globals.  So for each type we build a location data type, e.g.:
--
--   data FooLoc = FooLoc_Null | FooLoc_Unknown
-- .             | FooLocal StackLoc | FooGlobal FooGlobals
--
-- In the special case that there are no globals of this type, we do not define
-- FooGlobals, and omit the relevant constructor from FooLoc.
--
-- Only first-class types have locations.
--
-- XXX do the same for locals?
buildLocations :: MemInfo -> [T.Definition]
buildLocations minfo =
    concatMap (\p -> maybe [allLocations p] (:[allLocations p]) (buildLocList p))
            $ firstClassMInfo minfo
  where
    -- This builds the FooGlobals type
    buildLocList :: (TypeInfo,[GlobVarInfo]) -> Maybe T.Definition
    buildLocList (_,[]) = Nothing
    buildLocList (TypeInfo {tiGlobalLocType}, tvGlobals) =
      Just (T.DDataType tiGlobalLocType globalCons)
      where
        globalCons = map ( (,[]) . gvtid ) tvGlobals

    -- This builds the FooLoc type
    allLocations :: (TypeInfo,[GlobVarInfo]) -> T.Definition
    allLocations (tinfo,tvGlobals) =
      T.DDataType (tiLocType tinfo) $
          (tiNullLoc tinfo,[]) 
        : (tiUnknownLoc tinfo,[]) 
        : localCon
        : (if null tvGlobals then [] else [globalCon])
      where
        localCon = (tiLocalLocTag tinfo,[T.EId stackAddrType])
        globalCon = (tiGlobalLocTag tinfo,[T.EDot (T.EId $ tiGlobalLocType tinfo) []])


-- This builds the equality check for pointers.  For each first-class type Foo
-- we have a function:
--
--   fooLocEq :: (FooLoc,FooLoc) -> CInt
--   fooLocEq (FooLocUnknown,_) = CIntUnknown
--   fooLocEq (_,FooLocUnknown) = CIntUnknown
--   fooLocEq (l1,l2)           = if l1 == l2 then CIntKnown.1 else CIntKnown.0
locEquality :: MemInfo -> [T.Definition]
locEquality minfo = map (buildEqCheck . fst) $ firstClassMInfo minfo
  where
    b0,b1 :: T.Id
    b0 = T.Fixed "ptrEqBndr0"
    b1 = T.Fixed "ptrEqBndr1"
    
    buildEqCheck :: TypeInfo -> T.Definition
    buildEqCheck (TypeInfo {tiUnknownLoc, tiLocEqCheck}) =
      T.DFun tiLocEqCheck
        [([T.PId tiUnknownLoc,T.PId noId],unknownBool),
         ([T.PId noId,T.PId tiUnknownLoc],unknownBool),
         ([T.PId b0, T.PId b1],
          T.EIfThenElse (T.EBinOp (T.EId b0) T.BEq (T.EId b1))
                        boolTrue boolFalse)
        ]

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
memoryProcs (MInfo {firstClassMInfo}) =
 [ T.DVar (T.PId memoryName) $ buildMemory fcisWithVars,
   T.DFun runInMemoryName
          [([T.PId $ T.Fixed "procToRun"],runInMemory)],
   T.DFun hideMemoryName
          [([T.PId $ T.Fixed "procToRun"],hideMemory)]
 ]
 where
   fcisWithVars :: [FirstClassInfo]
   fcisWithVars = [fci | (ti,tvGlobals) <- firstClassMInfo,
                         not (null tvGlobals),
                         let (DIFirstClass fci) = tiDataInfo ti]

   buildMemory :: [FirstClassInfo] -> T.Exp
   buildMemory [] = T.EConst T.CStop
     -- In this case there are no globals

   buildMemory [FirstClassInfo {fciVarCells}] = T.EId fciVarCells

   buildMemory (FirstClassInfo {fciVarCells}:vs) = 
     T.EInterleave (T.EId fciVarCells)
                   (buildMemory vs)

   memTypeChans :: FirstClassInfo -> [T.Exp]
   memTypeChans (FirstClassInfo {fciReaderChan,fciWriterChan}) =
     [T.EId fciReaderChan,T.EId fciWriterChan]

     
   hideMemory =
     T.EHide (T.EId $ T.Fixed "procToRun")
             (T.EEnumSet $ concatMap memTypeChans fcisWithVars)
              
   runInMemory =
     T.EGenParallel (T.EId $ memoryName)
                    (T.EEnumSet $ concatMap memTypeChans fcisWithVars)
                    (T.EId (T.Fixed "procToRun"))


-- getElementPtr is the main LLVM instruction for indexing into datastructures.
-- Its semantics are considered complicated in LLVM, and it's doubly complicated
-- here.  Indexing into data structures is all about the way data is packed and
-- laid out in memory, which we have abstracted away as much as possible.
--
-- getElementPtr never involves dereferencing memory, but is not purely static.
-- Each index describes a location in an array or a struct.  LLVM requires
-- struct indices to be constant (so that we know what type we're getting out, I
-- think - convenient for us).  Array indices, on the other hand, do not need to
-- be constant (for example, when looping over an array, you might use an SSA
-- variable).  The initial address is also not necessarily constant, so even for
-- indexing into structs we will sometimes need a dynamic implementation.
--
-- So, in general, we must compute the result of getElementPtr dynamically in
-- the model.
--
-- - First, the case for structs.  Imagine:
--   
--   %mytype1 = [int; float; int]
--   %mytype2 = [int; mytype1; mytype1]
--   %mytype3 = [mytype2; int]
--   
--   %p = getElementPtr mytype3, mytype3* %foo, i32 0, i32 0, i32 1, i32 2
--   
--   Here, foo is a mytype3*.  The four indices in this GEP instruction say:
--   Look at the mytype3 at foo's location.  Look at the mytype2 at position 0
--   (e.g., the first element in the foo data structure).  Look at the first
--   mytype1 in that mytype2 (the thing at position 1 in the mytype2).  Return
--   the pointer to the last element of that mytype1 (the int in position 2).
--   
--   How is this interpreted in the model?  Roughly speaking we build accessor
--   functions for each struct that index 1-level into them.  Recall that we
--   don't have a distinct type of locations for struct - rather we use the type
--   of locations for the first element.  So getting the index of the first
--   element is just the identity function.  The accessors look like:
--   
--   getMytype1Pos1 :: (CIntLoc) -> MaybeFloatLoc
--   getMytype1Pos2 :: (CIntLoc) -> MaybeIntLoc
--   
--   The maybe is necessary in case the input location is an IntLoc global that is
--   really an int and not a struct, or for a stack underflow.  We also have
--   corresponding functions:
--   
--   maybeFloatLoc :: (MaybeFloatLoc,(FloatLoc) -> b,b) -> b
--   maybeIntLoc   :: (MaybeIntLoc,(IntLoc) -> b,b) -> b
--   
--   So, then, all together, our model for for the GEP instruction above looks something like:
--   
--     \(stack,sp,pid,k) @
--       maybeIntLoc(getMytype2Pos1(initialLoc),
--         \mt1loc @ 
--             maybeIntLoc(getMytype1Pos2(mt1loc),
--                         \intLoc @ k(stack,sp,pid,intLoc),
--                         GEPERROR -> STOP),
--         GEPERROR -> STOP)
--   
--   There are only two actual calls to the index functions because the initial
--   two "0" indices are "free" - the pointer doesn't change, only the type used
--   in calculating the next operation.  Currently, we only support GEP
--   instructions where the first index is 0.  For arrays we're going to have to
--   relax this?
--
-- - OK, now the case for arrays:
--
--   The case here is slightly simpler than the case for structs.  In
--   particular, indexing into an int[] always yields an int location, so we
--   don't need separate accessor functions for each element of the array.
--   Instead, we defined one function which takes an IntLoc x and an index n,
--   and returns the address of the nth int in the array x.  If x isn't actually
--   an array or n is past the end of it, we return Nothing as before.
buildGEPHelpers :: MemInfo -> CG [T.Definition]
buildGEPHelpers (MInfo {firstClassMInfo,structMInfo,arrayMInfo}) =
  ((gepErrorDef : maybeDefs) ++) <$> allFieldLookups
  -- this builds the getFooIndex functions and the maybe types.
  where
    valBndr,justBndr,nothingBndr :: T.Id
    valBndr = T.Fixed "locMaybeValBndr"
    justBndr = T.Fixed "locMaybeJustBndr"
    nothingBndr = T.Fixed "locMaybeNothingBndr"

    gepErrorDef :: T.Definition
    gepErrorDef = T.DChan [gepErrorName] []
    
    maybeDefs :: [T.Definition]
    maybeDefs = concatMap (maybeDef . fst) firstClassMInfo

    maybeDef :: TypeInfo -> [T.Definition]
    maybeDef (TypeInfo {tiLocType,tiLocMaybeType,
                        tiLocMaybeJust,tiLocMaybeNothing,tiLocMaybeElim}) =
      [T.DDataType tiLocMaybeType
         [(tiLocMaybeJust,[T.EId tiLocType]),
          (tiLocMaybeNothing,[])],
       T.DFun tiLocMaybeElim
         [([T.PDot (T.PId tiLocMaybeJust) [T.PId valBndr],
            T.PId justBndr, T.PId nothingBndr],
           T.EApp (T.EId justBndr) [T.EId valBndr]),
          ([T.PId tiLocMaybeNothing, T.PId justBndr, T.PId nothingBndr],
           T.EId nothingBndr)]]

    -- XXX this next bit is unfortunate and should be fixed.  Problem: we don't
    -- keep track of which arrayFieldLookup helper functions are used during the
    -- translation.  If there are only ever stack-allocated arrays for this
    -- type, then no globals will have shown up in the arrayMInfo.  So, we can't
    -- just build the array lookup helper for the stuff in the arrayMInfo.  The
    -- right thing to do is probably to pull the tiArrayIndexer thing out of the
    -- type info and keep track of when they are generated for a particular
    -- type.  But, I don't have time for that right this second.  Instead, I'm
    -- just going to build array indexers for all types.  Here we set up that
    -- list (preserving the global locality information from the arrayMInfo).
    arrayLookupsToBuild :: [(TypeInfo,[GlobVarInfo])]
    arrayLookupsToBuild =
      arrayMInfo ++ map (,[]) typesWithNoGlobalArrays
      where
        typesWithNoGlobalArrays :: [TypeInfo]
        typesWithNoGlobalArrays =
          (map fst firstClassMInfo ++ map fst structMInfo) \\ (map fst arrayMInfo)
    
    allFieldLookups :: CG [T.Definition]
    allFieldLookups = do
      structLookups <- concat <$> mapM structFieldLookups structMInfo
      arrayLookups <- mapM arrayFieldLookups arrayLookupsToBuild
      return $ arrayLookups ++ structLookups

    structFieldLookups :: (TypeInfo,[GlobVarInfo]) -> CG [T.Definition]
    structFieldLookups (tinfo@TypeInfo {
                          tiDataInfo=DIStruct (StructInfo {siGetFieldPtrs}),
                          tiBase=structBt@(StructType (fieldBT1:fieldBTs))},
                        gsInfos) = do
      when (length fieldBTs /= length siGetFieldPtrs) $
        fail $ "Internal error: length basetype has different number of "
            ++ "fields than structinfo in typeFieldLookups (" ++ ppBaseType structBt
            ++ ")"
      off <- offsets
      mapM (structFieldLookup tinfo gsInfos) $
           zip4 siGetFieldPtrs fieldBTs [1..] off
      where
        calcOffsets :: Int -> [BaseType] -> CG [Int]
        calcOffsets _ [] = return []
        calcOffsets n (bt:bts) = do
          szBt <- baseTypeSize bt
          (n:) <$> calcOffsets (n+szBt) bts

        offsets :: CG [Int]
        offsets = do
          initOffset <- baseTypeSize fieldBT1
          calcOffsets initOffset fieldBTs
    structFieldLookups (TypeInfo {tiDataInfo=DIArray _,tiBase},_) =
      fail $ "Internal error: array encountered in "
          ++ "structFieldLookups, base type " ++ ppBaseType tiBase
    structFieldLookups (TypeInfo {tiBase},_) =
      fail $ "Internal error: non-struct or empty struct encountered in "
          ++ "structFieldLookups, base type " ++ ppBaseType tiBase

    -- The next two functions are the meat of the thing, where we define the
    -- subelement address calculation.

    -- For structs:
    --
    -- For an example, suppose we are getting the nth field of struct Foo, and
    -- that field has type Bar.
    --
    -- We define, roughly:
    --
    -- getFooFieldN :: (FooAddr) -> MaybeBarAddr
    -- getFooFieldN (FooLocalTag.StackAddr.s) =
    --    if (s-distN) >= 0 then BarJust.BarLocalTag.StackAddr.(s-distN)
    --                    else BarNothing
    -- ..
    -- getFooFieldN (FooGlobalTag.fAddr) = BarJust.BarGlobalTag.bAddr
    -- ..
    -- getFooFieldN _ = BarNothing
    --
    -- The local case involves the magic number "distN".  This is the number of
    -- memory "cells" between the start of the struct and the nth field.  It's
    -- calculated by structFieldLookups and passed in here.
    --
    -- The global case looks a bit like magic.  The idea is that as we processed
    -- global variables we remembered (in the monad) which fields are close to
    -- each other: for each global location of type Foo, fAddr, we find in the
    -- monad the location of the corresponding bar, which is bAddr.
    structFieldLookup :: TypeInfo -> [GlobVarInfo] -> (T.Id,BaseType,Int,Int)
                      -> CG T.Definition
    structFieldLookup structTInfo gsInfos
                      (fName,fieldBaseType,n,distN) = do
      fieldTInfo <- lookupTypeInfo fieldBaseType
      globClauses <- mapM (globalClause fieldTInfo) gsInfos
      return $ T.DFun fName $
        localClause fieldTInfo : globClauses ++ [catchAllClause fieldTInfo]
      where
        addrBndr :: T.Id
        addrBndr = T.Fixed "fieldLookupBndr"
        
        globalClause :: TypeInfo -> GlobVarInfo -> CG ([T.Pat],T.Exp)
        globalClause fieldTInfo (GVInfo {gvtid=topTId,
                                         gvlayout=Just (GVAgg flds)}) =
          case nth flds n of
            Nothing ->
              fail $ "Internal error: GlobVarLayout has too few fields "
                  ++ "in globalClause (field " ++ show n ++ ", loc "
                  ++ show topTId ++ ")"
            Just fieldGVI -> 
              return ([T.PDot (T.PId $ tiGlobalLocTag structTInfo)
                              [T.PId topTId]],
                      T.EDot (T.EId $ tiLocMaybeJust fieldTInfo)
                             [T.EId (tiGlobalLocTag fieldTInfo),
                              T.EId (gvtid fieldGVI)])
        globalClause _ (GVInfo {gvtid}) =
          fail $ "Internal error: GlobVarInfo has no initializer or "
              ++ "non-struct initialiser in globalClause (loc "
              ++ show gvtid ++ ")"

        localClause :: TypeInfo -> ([T.Pat],T.Exp)
        localClause fieldTInfo =
          ([T.PDot (T.PId $ tiLocalLocTag structTInfo)
                   [T.PDot (T.PId stackAddrCon) [T.PId addrBndr]]],
            T.EIfThenElse
              (T.EBinOp offsetAddr T.BGeq (T.EConst $ T.CInt 0))
              (T.EDot (T.EId $ tiLocMaybeJust fieldTInfo)
                      [T.EId (tiLocalLocTag fieldTInfo),T.EId stackAddrCon,
                       offsetAddr])
              (T.EId $ tiLocMaybeNothing fieldTInfo))
          where
            offsetAddr = T.EBinOp (T.EId addrBndr)
                                  T.BMinus
                                  (T.EConst (T.CInt $ fromIntegral distN))

        catchAllClause :: TypeInfo -> ([T.Pat],T.Exp)
        catchAllClause fieldTInfo =
          ([T.PId noId],T.EId $ tiLocMaybeNothing fieldTInfo)

    -- For arrays:
    --
    -- If we've got two arrays for a type, say foo:
    --
    -- foo x[10], y[3];
    --
    -- Then, in memory, we have 13 cells:
    --     fooLoc_x, fooLoc_x_1, fooLoc_x_2, ... fooLoc_x_9,
    --     fooLoc_y, fooLoc_y_1, fooLoc_y_2
    --
    -- Now, not all of these may be reachable by GEP due to the limited
    -- representation of ints, which are used to index.  For our example, say
    -- the range of int is 0..4.  Then fooArrayIndexer will look like:
    --
    -- fooArrayIndexer :: (FooLoc,CInt) -> FooLocMaybe
    -- fooArrayIndexer (FooLocalTag.StackAddr.s,CIntKnown.x) =
    --   let addr = s-(distFoo*x) within
    --   if addr >= 0 then FooJust.FooLocalTag.StackAddr.addr
    --                else FooNothing
    -- fooArrayIndexer (FooGlobalTag.fooLoc_x,CIntKnown.0) = FooJust.FooGlobalTag.fooLoc_x
    -- fooArrayIndexer (FooGlobalTag.fooLoc_x,CIntKnown.1) = FooJust.FooGlobalTag.fooLoc_x_1
    -- fooArrayIndexer (FooGlobalTag.fooLoc_x,CIntKnown.2) = FooJust.FooGlobalTag.fooLoc_x_2
    -- fooArrayIndexer (FooGlobalTag.fooLoc_x,CIntKnown.3) = FooJust.FooGlobalTag.fooLoc_x_3
    -- fooArrayIndexer (FooGlobalTag.fooLoc_x,CIntKnown.4) = FooJust.FooGlobalTag.fooLoc_x_4
    -- fooArrayIndexer (FooGlobalTag.fooLoc_y,CIntKnown.0) = FooJust.FooGlobalTag.fooLoc_y
    -- fooArrayIndexer (FooGlobalTag.fooLoc_y,CIntKnown.1) = FooJust.FooGlobalTag.fooLoc_y_1
    -- fooArrayIndexer (FooGlobalTag.fooLoc_y,CIntKnown.2) = FooJust.FooGlobalTag.fooLoc_y_2
    -- fooArrayIndexer (_,_) = FooNothing
    --
    -- The only tricky bit here is the local case.  It's just like the local
    -- case for structs.  "distFoo" is the number of memory cells that a "foo"
    -- takes up (i.e., the number of stack cells that increasing the index by 1
    -- walks past).
    --
    -- Note that we are only supporting array GEP where the index is actually
    -- the first element of a declared array.  There are other legal uses of GEP
    -- with an array type that we don't support.  First, your initial location
    -- could be halfway through the array.  Second, you could just be using the
    -- array type to do pointer math on some other type of data.  The first one
    -- of these would be fairly easy to support by just adding a whole bunch
    -- more clauses (though this might introduce efficiency problems).  The
    -- second one seems trickier.
    arrayFieldLookups :: (TypeInfo,[GlobVarInfo]) -> CG T.Definition
    arrayFieldLookups (TypeInfo {
                          tiArrayIndexer,tiLocalLocTag,tiGlobalLocTag,
                          tiLocMaybeJust,tiLocMaybeNothing,tiBase},
                       arrLocInfos) = do
        (_,cIntMax) <- getIntRange
        elementSize <- baseTypeSize tiBase
        let distN = T.EConst $ T.CInt $ fromIntegral elementSize
        return $ T.DFun tiArrayIndexer $
          localClause distN
              : concatMap (knownGlobalClauses cIntMax) arrLocInfos
             ++ [catchAllClause]
      where
        inputAddrBndr,outputAddrBndr,indexBndr :: T.Id
        inputAddrBndr = T.Fixed "arrayInLocBndr"
        outputAddrBndr = T.Fixed "arrayOutLocBndr"
        indexBndr = T.Fixed "arrayIndexBndr"

        localClause :: T.Exp -> ([T.Pat],T.Exp)
        localClause distN =
          ([T.PDot (T.PId tiLocalLocTag)
                   [T.PDot (T.PId stackAddrCon) [T.PId inputAddrBndr]],
            T.PDot (T.PId knownIntCon) [T.PId indexBndr]],
           T.ELet [T.DVar (T.PId outputAddrBndr)
                     (T.EBinOp (T.EId inputAddrBndr) T.BMinus
                        (T.EBinOp distN T.BTimes (T.EId indexBndr)))]
             (T.EIfThenElse
               (T.EBinOp (T.EId outputAddrBndr) T.BGeq (T.EConst $ T.CInt 0))
               (T.EDot (T.EId tiLocMaybeJust) $
                  map T.EId [tiLocalLocTag, stackAddrCon, outputAddrBndr])
               (T.EId tiLocMaybeNothing)))

        -- All the clauses for one array.  The int arg is the max representable
        -- int.
        knownGlobalClauses :: Int -> GlobVarInfo -> [([T.Pat],T.Exp)]
        knownGlobalClauses maxCInt (GVInfo {gvtid=topTID,
                                            gvlayout=Just (GVAgg cells)}) =
          map (knownGlobalClause $ T.PId topTID) $
            zip [0..highestClause] $ map (T.EId . gvtid) cells
          where
            highestClause = min maxCInt (length cells)
        knownGlobalClauses _ _ = []
            
        -- array loc, Index, cell loc
        knownGlobalClause :: T.Pat -> (Int,T.Exp) -> ([T.Pat],T.Exp)
        knownGlobalClause source (i,dest) =
          ([T.PDot (T.PId tiGlobalLocTag) [source],
            T.PDot (T.PId knownIntCon) [T.PConst $ T.CInt $ fromIntegral i]],
           T.EDot (T.EId tiLocMaybeJust) [T.EId tiGlobalLocTag, dest])

        catchAllClause :: ([T.Pat],T.Exp)
        catchAllClause = ([T.PId noId,T.PId noId],T.EId tiLocMaybeNothing)


-- baseTypeSize is a helper that calculates the number of 32-bit "cells" in
-- memory that will be occupied by a data value of a particular base type.
-- Currently this is only used by buildGEPHElpers, but I expect it will be more
-- broadly useful.
--
-- It returns a result in CG because it might have to lookup a type name.
baseTypeSize :: BaseType -> CG Int
baseTypeSize IntType   = return 1
baseTypeSize BoolType  = return 1
baseTypeSize FloatType = return 1
baseTypeSize MutexType = return 1
baseTypeSize PIDType   = return 1
baseTypeSize VoidType  = return 1
baseTypeSize (StructType bts) =
  sum <$> mapM baseTypeSize bts
baseTypeSize (NamedType n) = do
  st <- lookupTypeDefFail n "baseTypeSize"
  bt <- transType st
  baseTypeSize bt
baseTypeSize (PointerType _) = return 1
baseTypeSize (ArrayType bt len) = (len*) <$> baseTypeSize bt
baseTypeSize FPtrType = return 1
baseTypeSize FunctionType =
  fail "InternalError: FunctionType encountered in baseTypeSize"

-- buildFunctionPointers constructs two definitions related to function
-- pointers.  First, the definition of the type FPtr, which contains a tag for
-- each function declared in the program.  E.g., if the program had three
-- top-level functions called "main", "f" and "g", we might have:
--
--     data FPtr = FP_main | FP_f | FP_g
--
-- Second, the definition of the error channel for function pointers
buildFunctionPointers :: CG [T.Definition]
buildFunctionPointers = do
  functions <- allFunctions
  return [buildFPtr functions,fptrErrorChan]
  where
    buildFPtr :: [(L.Name,GlobFuncInfo)] -> T.Definition
    buildFPtr fs = T.DDataType fptrRepId $ (fptrNullCon,[])
                                         : (fptrUnknownCon,[])
                                         : map ((,[]) . ftag . snd) fs

    fptrErrorChan :: T.Definition
    fptrErrorChan = T.DChan [fptrErrorName] []


-- buildFunctionPointerDerefs constructs the helpers that are used when the use
-- of a function poitner as a function occurs in the llvm program.  At a high
-- level, these functions check if the function pointer used corresponds to a
-- function of the type required, and build the application if so.
--
-- Unlike most things that we think of as the "memory model".  The definitions
-- constructed here must go in the same file as the translation of the program
-- itself.  This is because the names of the functions that function pointers
-- refer to must be in scope.
buildFunctionPointerDerefs :: CG [T.Definition]
buildFunctionPointerDerefs = do
  fpDerefNames <- allFPtrDerefs
  functions <- map snd <$> allFunctions
  let
    addType :: GlobFuncInfo -> CG ([T.Id],T.Id,GlobFuncInfo)
    addType gfi = do
      args <- mapM lookupRepType (fargs gfi)
      ret <- lookupRepType (fret gfi)
      return (args,ret,gfi)
  functionsWithTypes <- mapM addType functions
  let
    -- This finds all the functions of a given type.  It's called once for each
    -- function type that actually appears in a function pointer dereference.
    -- If there are many such types this is inefficient and we should do
    -- something smarter (precompute a map from function types to all functions
    -- of that type, either here or as functions are added to the monad).  But,
    -- my current examples don't exercise this much so I'm not going to bother
    functionsOfType :: [T.Id] -> T.Id -> [GlobFuncInfo]
    functionsOfType args ret =
      [gfi | (fargs,fret,gfi) <- functionsWithTypes, fargs == args, fret == ret]

    -- Int is number of args, for convenience
    derefSets :: [(T.Id,Int,[GlobFuncInfo])]
    derefSets = map (\((args,ret),nm) -> (nm,length args,functionsOfType args ret))
                    fpDerefNames
  return $ map buildFPtrDeref derefSets
  where
    -- For each type of function where an fptr deref actually occured in the
    -- code, we here build the helper that looks up the corresponding function
    -- and applies it.  For an example, imagine the function type in question is:
    --
    --   (A,B) -> C
    --
    -- Then we here build a helper of type:
    --
    --     (FPtrTag,ARep,BRep,Stack,StackPtr,PID,(Stack,StackPtr,PID,C) -> Proc)
    --  -> Proc
    --
    -- Suppose there are two functions of this type, f and g.  Our helper looks like:
    --
    -- fptrHelper (FPTag_f,a,b,st,sp,pid,k) = f(a,b,st,sp,pid,k)
    -- fptrHelper (FPTag_g,a,b,st,sp,pid,k) = g(a,b,st,sp,pid,k)
    -- fptrHelper _ = fptr_deref_ERROR -> STOP
    buildFPtrDeref :: (T.Id,Int,[GlobFuncInfo]) -> T.Definition
    buildFPtrDeref (helperName,numArgs,funcs) =
      T.DFun helperName $ (map helperClause funcs)
        ++ [(replicate (numArgs + 5) (T.PId noId),
             T.EPrefix (T.EId fptrErrorName) [] (T.EConst T.CStop))]

      where
        realArgs,structuralArgs,args :: [T.Id]
        realArgs = map T.Fixed (["fptrRealArg_" ++ (show n) | n <- [0..(numArgs-1)]])
        structuralArgs = map T.Fixed ["st","sp","pid","k"]
        args = realArgs ++ structuralArgs

        helperClause :: GlobFuncInfo -> ([T.Pat],T.Exp)
        helperClause (GFInfo {ftid,ftag}) =
          (map T.PId (ftag:args),T.EApp (T.EId ftid) $ map T.EId args)



buildMemoryModel :: CG T.FDRMod
buildMemoryModel = T.FDRMod <$> do
  minfo <- createMemInfo
  let cspChannels = buildCspChannels minfo
  varCellBuilders <- buildVarCellBuilders minfo
  dataReps        <- buildDataReps
  locationReaders <- buildLocationReaders minfo
  locationWriters <- buildLocationWriters minfo
  gepHelpers      <- buildGEPHelpers minfo
  typedMemory     <- buildTypedMemory minfo
  fptrs           <- buildFunctionPointers
  let stackModel = buildStack minfo
-- XXX replace with full system once in place

  return $ concat [dataReps,
                   buildLocations minfo,
                   locEquality minfo,
                   cspChannels,
                   varCellBuilders,
                   typedMemory,
                   memoryProcs minfo,
                   gepHelpers,
                   stackModel,
                   locationReaders,
                   locationWriters,
                   fptrs
                  ]

-----------------------------------------------------------------------------
----------- Stubs
-----------------------------------------------------------------------------

-- It is convenient to define "stubs" for functions that are declared but not
-- defined.  These are CSPm functions that accept the right number of
-- arguments and always return the "unknown" value of the appropriate type.
-- Note that these are unsound models, since they fail to account for any of
-- the effects of the actual functions.
--
-- In our model of the stack, the calling function pushes a new stack frame
-- boundary before the stub runs, and it's the stub's job to return it.  So,
-- supposing we're stubbing out a function that takes two arguments and returns
-- a Foo, we have:
--
--  stub(_,_,st,sp,pid,k) =
--     popStackFrame(st,sp,pid,\st',sp',pid',_ @ k(st',sp',pid',UnknownFooVal))
--
stubOut :: GlobFuncInfo -> CG T.Definition
stubOut (GFInfo {ftid,fargs,fret,fdef}) = do
  undefinedRet <- unknownFCValue fret
  when fdef $ fail $
    "Internal Error: stubOut called on defined function " ++ T.namePart ftid
  st <- freshTid $ Just "stubSt"
  sp <- freshTid $ Just "stubSp"
  pid <- freshTid $ Just "stubPID"
  k <- freshTid $ Just "stubCont"
  innerLam <- insnInnerLambda noId $ \(StateVars st' sp' pid') -> return $
    T.EApp (T.EId k) ([T.EId st', T.EId sp', T.EId pid', undefinedRet])
  return $
    T.DFun ftid
           [(map T.PId $
               (replicate (length fargs) (T.Fixed "_")) ++ [st,sp,pid,k],
             T.EApp (T.EId popStackFrameId) [T.EId st,T.EId sp,T.EId pid,innerLam])]


-------------------------------------------
--- Top-level helper functions

-- runAsMain builds the useful "run" and "runAsMain" helper function.  "run"
-- just runs a process in memory, filling in an empty stack:
--
-- run(f) = runInMemory(<StackFrameBoundary>,StackAddr.1,PID.0,\(_,_,_,_) @ SKIP)
--
-- runAsMain also sets up the llvm.global_ctors and llvm.global_dtors definitions to run
-- before/after the function (if they are present).
--
-- Because it needs to pull the accumulated ctors/dtors from the monad, this
-- must be run after the main translation.
--
-- Suppose we have ctors f1 and f2, and dtors g1 and g2, to be run in that
-- order.  Then this looks like:
--
-- runAsMain (m) =
--   runInMemory(
--     f1(<StackFrameBoundary>,StackAddr.1,PID.0,\(_,_,_,_) @
--       f2(<StackFrameBoundary>,StackAddr.1,PID.0,\(_,_,_,_) @
--          m(<StackFrameBoundary>,StackAddr.1,PID.0,\(_,_,_,_) @
--           g1(<StackFrameBoundary>,StackAddr.1,PID.0,\(_,_,_,_) @
--             g2(<StackFrameBoundary>,StackAddr.1,PID.0,\(_,_,_,_) @ SKIP)))))
--   )
--
-- A couple things to note:
--
--   - We're throwing away the return value of main.  Probably we should keep it
--     around and display it with a final event.
--
--   - We're ignoring the possibility that any of these functions somehow screw
--     up the stack or does any multithreading fanciness.  I don't really know
--     what the right model here is, but for now I'm imagining that each runs on
--     "bare metal".
runAsMain :: CG [T.Definition]
runAsMain = do
  ctors <- map snd <$> sortBy sortPair <$> getCtors
  dtors <- map snd <$> reverse <$> sortBy sortPair <$> getDtors
  ctorTNames <- mapM lookupFunctionName ctors
  dtorTNames <- mapM lookupFunctionName dtors
  let functionsToRun = ctorTNames ++ tlFId : dtorTNames
  return $ [
    T.DFun runName
      [([T.PId tlFId],
        T.EApp (T.EId runInMemoryName) [foldApps [tlFId]])],
    T.DFun runAsMainName
      [([T.PId tlFId],
        T.EApp (T.EId runInMemoryName) [foldApps functionsToRun])]
    ]
  where
    sortPair :: (Int,b) -> (Int,b) -> Ordering
    sortPair (i1,_) (i2,_) = compare i1 i2

    tlFId :: T.Id
    tlFId = T.Fixed "fAsMain"

    lookupFunctionName :: L.Name -> CG T.Id
    lookupFunctionName nm = do
      mginfo <- lookupGlobal nm
      case mginfo of
        Nothing -> fail $
             "Error: Unknown global " ++ prettyLLVMName nm
          ++ " in ctors or dtors"
        Just (GlobVar _) -> fail $
             "Error: Non-function global " ++ prettyLLVMName nm
          ++ " in ctors or dtors"
        Just (GlobFunc (GFInfo {ftid})) -> return ftid

    foldApps :: [T.Id] -> T.Exp
    foldApps = foldr addF (T.EConst T.CSkip)
      where
        addF :: T.Id -> T.Exp -> T.Exp
        addF f k =
          T.EApp (T.EId f) [T.EList [T.EId stackFrameCon],
                            T.EDot (T.EId stackAddrCon)
                                   [T.EConst $ T.CInt 1],
                            tidZero,
                            T.ELambda (replicate 4 (T.PId noId)) k]

----------------------------------------
--- LLVM analysis helper functions

-- These function calculate the "assigned" type of an llvm operand or constant.
-- By assigned, we mean that they calculate the type that the LLVM IR is
-- claiming this thing has.  This may be very different than the type calculated
-- by our transConstant/transOperand functions, which instead provide the
-- internal representation type we are using for this thing.

assignedOperandType :: L.Operand -> CG L.Type
assignedOperandType (L.LocalReference ty _) = return ty
assignedOperandType (L.ConstantOperand c)   = assignedConstantType c
assignedOperandType i@(L.MetadataStringOperand _) =
  fail $ "Unsupported: metadata operand encountered in assignedOperandType "
      ++ LP.showPretty i
assignedOperandType i@(L.MetadataNodeOperand _)   =
  fail $ "Unsupported: metadata operand encountered in assignedOperandType "
      ++ LP.showPretty i

-- Find the type of a constant.
assignedConstantType :: LC.Constant -> CG L.Type
assignedConstantType (LC.Int {LC.integerBits}) = return $ L.IntegerType integerBits
assignedConstantType (LC.Float {LC.floatValue}) = return $ 
  uncurry L.FloatingPointType $
    case floatValue of
      L.Half _        -> (16,L.IEEE)
      L.Single _      -> (32,L.IEEE)
      L.Double _      -> (64,L.IEEE)
      L.Quadruple _ _ -> (128,L.IEEE)
      L.X86_FP80 _ _  -> (80,L.DoubleExtended)
      L.PPC_FP128 _ _ -> (128,L.PairOfFloats)
assignedConstantType (LC.Null {LC.constantType=ct}) = return ct
assignedConstantType (LC.Struct {LC.isPacked,LC.memberValues}) =
  L.StructureType isPacked <$> mapM assignedConstantType memberValues
assignedConstantType (LC.Array {LC.memberType,LC.memberValues}) =
  return $ L.ArrayType (fromIntegral $ length memberValues) memberType
assignedConstantType (LC.Vector {LC.memberValues}) =
  case memberValues of
    [] -> fail "Unsupported: empty vector encountered in assignedConstantType"
    v:_ -> 
      L.VectorType (fromIntegral $ length memberValues)
               <$> assignedConstantType v
assignedConstantType (LC.Undef {LC.constantType=ct}) = return ct
assignedConstantType (LC.BlockAddress {})        = return $
  L.PointerType (L.IntegerType 8) (L.AddrSpace 0)
  -- According to llvm docs, blockaddess always has type i8*
assignedConstantType (LC.GlobalReference ty _)   = return ty
-- For the binary operations, we assume the instruction is well-formed, which
-- means both operands have the same type and that's the result type.
assignedConstantType (LC.Add {LC.operand0})       = assignedConstantType operand0
assignedConstantType (LC.FAdd {LC.operand0})      = assignedConstantType operand0
assignedConstantType (LC.Sub {LC.operand0})       = assignedConstantType operand0
assignedConstantType (LC.FSub {LC.operand0})      = assignedConstantType operand0
assignedConstantType (LC.Mul {LC.operand0})       = assignedConstantType operand0
assignedConstantType (LC.FMul {LC.operand0})      = assignedConstantType operand0
assignedConstantType (LC.UDiv {LC.operand0})      = assignedConstantType operand0
assignedConstantType (LC.SDiv {LC.operand0})      = assignedConstantType operand0
assignedConstantType (LC.FDiv {LC.operand0})      = assignedConstantType operand0
assignedConstantType (LC.URem {LC.operand0})      = assignedConstantType operand0
assignedConstantType (LC.SRem {LC.operand0})      = assignedConstantType operand0
assignedConstantType (LC.FRem {LC.operand0})      = assignedConstantType operand0
assignedConstantType (LC.Shl {LC.operand0})       = assignedConstantType operand0
assignedConstantType (LC.LShr {LC.operand0})      = assignedConstantType operand0
assignedConstantType (LC.AShr {LC.operand0})      = assignedConstantType operand0
assignedConstantType (LC.And {LC.operand0})       = assignedConstantType operand0
assignedConstantType (LC.Or {LC.operand0})        = assignedConstantType operand0
assignedConstantType (LC.Xor {LC.operand0})       = assignedConstantType operand0
assignedConstantType (LC.GetElementPtr {})        =
  fail "Unimplemented: getElementPtr in assignedConstantType"
assignedConstantType (LC.Trunc {LC.type'})        = return type'
assignedConstantType c                            =
  fail $ "Unsupported constant in assignedConstantType: " ++ LP.showPretty c


----------------------
-- Top-level interface

data CspModules =
  CspModules {cmGlobalState :: T.FDRMod,
              cmStubs       :: Maybe T.FDRMod,
              cmCode        :: T.FDRMod}

-- This is the top-level function that turns an LLVM module into CSP code.
--
-- It does a bunch of stuff.  There are, first, three passes over the
-- set of all top-level definitions in the LLVM files:
--
--    1) Add typedefs to monad
--    2) Generate names for all top-level variables and functions.
--    3) Process variable initializers and filter out everything but
--       function definitions (which will be translated subsequently)
--
--  After these three initial passes, we translate the function bodies
--  to CSP and build the memory model based on data computed during
--  the previous steps.

transModule :: L.Module -> CG CspModules
transModule (L.Module {L.moduleDefinitions}) = do
  -- Three passes over all top-levels
  addGlobalTypes moduleDefinitions
  addGlobalNames moduleDefinitions
  globals <- transDefinitions moduleDefinitions

  -- Translate functions, build mem model, put together output
  functionDefs <- concat <$> mapM transFunction globals
  cmGlobalState <- buildMemoryModel
  functionPointerHelpers <- buildFunctionPointerDerefs
  -- set up stubs
  functions <- allFunctions
  let undefinedFunctions = [gfi | (_,gfi) <- functions, not (fdef gfi)]
  cmStubs <- if null undefinedFunctions then return Nothing
                else Just . T.FDRMod <$> mapM stubOut undefinedFunctions
  -- toplevels
  topLevelHelpers <- runAsMain
  let topLevels = concat [functionPointerHelpers,functionDefs,topLevelHelpers]
      cmCode = T.FDRMod {T.topLevels}
  return $ CspModules {cmGlobalState,cmStubs,cmCode}
