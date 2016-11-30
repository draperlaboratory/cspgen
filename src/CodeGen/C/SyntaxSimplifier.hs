{- |
Module      :  CodeGen.C.SyntaxSimplifier
Description :  C Grammar Simplifier
Copyright   :  Draper Laboratories

Author      :  Chris Casinghino

This module translates the C AST from Language.C into our internal AST, which
is substantially simpler.  Some unhandled constructs are rejected, but mostly
what is done here is just additional parsing and typechecking.

-}

{-# OPTIONS_GHC -fno-warn-warnings-deprecations #-}

module CodeGen.C.SyntaxSimplifier (simplifyTranslUnit,SimplResult(..)) where

import Prelude hiding (mapM,sequence)
import Data.Maybe (isJust)
import Data.List (isPrefixOf)
import Data.Traversable (mapM)
import qualified Data.Map as M
import Text.PrettyPrint (render)

import Control.Monad.State hiding (mapM)
import Control.Monad.Except hiding (mapM)

import qualified Language.C.Syntax.AST as S
import qualified Language.C.Syntax.Constants as S
import qualified Language.C.Data.Node as S
import qualified Language.C.Data.Position as S
import qualified Language.C.Data.Ident as S
import qualified Language.C.Pretty as S

import qualified CodeGen.C.Syntax as T

------------------------------
---  Interface

starterState :: SimpState
starterState = SimpState {
                 localObject = M.empty,
                 globalObject = M.fromList [(S.builtinIdent "__builtin_va_list",
                                             T.Fixed "gcc_builtin_va_list")],
                 scopeObject = [],

                 localSUE = M.empty,
                 globalSUE = M.empty,
                 scopeSUE = [],

                 labels = M.empty,

                 warnings = [],

                 uniq = 0
               }

data SimplResult =
  SR {srWarnings :: [String],

      srResult   :: T.TransUnit,

      -- The simplification also computes identifiers for each library function
      srLibIds   :: [T.Id]}
  
-- This takes as an argument a list of library functions
simplifyTranslUnit :: S.CTranslUnit -> [S.Ident] -> Either String SimplResult
simplifyTranslUnit tu fnames = do
  ((srLibIds,srResult), st) <-
    runStateT ((,) <$> initState fnames <*> trCTranslUnit tu) starterState
  return $ SR {srWarnings=warnings st,
               srResult,srLibIds}
  where
    initState :: [S.Ident] -> Simp [T.Id]
    initState  = mapM (freshObject T.VSGlobal)

-----------------------------

-- As part of this simplification, we disambiguate any shadowed identifiers
-- (i.e., make identifiers globally unique).  For that, we need some
-- infrastructure to keep track of State:
data Scope = SDeclared S.Ident (Maybe T.Id)
           | SBoundary

-- There are three main namespaces in C:
-- 
--   - struct/union/enum tags (not the fields)
-- 
--   - labels 
--
--   - regular variables, parameter, typedef names, and everything else
--
-- Additionally, struct/union/enum has a local namespace for its fields.
--
-- Labels are special in that they always have "function scope".  So, we don't
-- need to consider global labels.
--
-- For the other two categories, we must support both global and local
-- declarations.  So, for each namespace we track as state three things:
--
-- The global declarations, the local declarations, and the scope of each
-- local declaration (to support shadowing).
data SimpState = SimpState {localSUE  :: M.Map S.Ident T.Id,
                            globalSUE :: M.Map S.Ident T.Id,
                            scopeSUE  :: [Scope],

                            localObject  :: M.Map S.Ident T.Id,
                            globalObject :: M.Map S.Ident T.Id,
                            scopeObject  :: [Scope],

                            labels :: M.Map S.Ident T.Id,

                            warnings :: [String],
                            
                            uniq   :: Int}

type Simp a = StateT SimpState (Either String) a

beginScope :: Simp ()
beginScope = do
  s <- get
  put $ s {scopeSUE    = SBoundary : scopeSUE s,
           scopeObject = SBoundary : scopeObject s}

endScope :: Simp ()
endScope = do
  s <- get
  let (sO',lO')     = popScope (scopeObject s) (localObject s)
      (sSUE',lSUE') = popScope (scopeSUE s) (localSUE s)
  put $ s {scopeObject = sO',
           localObject = lO',
           scopeSUE    = sSUE',
           localSUE    = lSUE'}
  where
    popScope :: [Scope] -> M.Map S.Ident T.Id -> ([Scope],M.Map S.Ident T.Id)
    popScope []                            lm = ([],lm)
    popScope (SBoundary : scs)             lm = (scs,lm)
    popScope (SDeclared sid mshadow : scs) lm =
      case mshadow of
        Nothing    -> popScope scs (M.delete sid lm)
        Just linfo -> popScope scs (M.insert sid linfo lm)

addWarning :: String -> Simp ()
addWarning w = do
  s <- get
  put $ s {warnings = w:(warnings s)}

---------------------------
--- Working with identifiers
freshTid :: String -> T.VarScope -> Simp T.Id
freshTid nm vs = do
  s <- get
  put $ s {uniq = 1 + uniq s}
  return $ T.Id nm vs $ uniq s

freshObject :: T.VarScope -> S.Ident -> Simp T.Id
freshObject sc sid@(S.Ident nm _ _) = do
  tid <- freshTid nm sc
  case sc of
    T.VSGlobal -> modify $ \s -> 
        s {globalObject = M.insert sid tid (globalObject s)}
    T.VSLocal  -> do
      mOldTid <- M.lookup sid <$> gets localObject
      modify $ \s -> s {localObject = M.insert sid tid (localObject s),
                        scopeObject = SDeclared sid mOldTid : scopeObject s}
  return tid

lookupObject :: S.Ident -> Simp (Maybe T.Id)
lookupObject sid = do
  s <- get
  case M.lookup sid (localObject s) of
    Nothing      -> return $ M.lookup sid (globalObject s)
    tid@(Just _) -> return tid

lookupOrMakeSUE :: T.VarScope -> S.Ident -> Simp T.Id
lookupOrMakeSUE sc sid@(S.Ident nm _ _) = do
  s <- get
  case M.lookup sid $ localSUE s of
    Nothing -> 
      case M.lookup sid $ globalSUE s of
        Just tid -> return tid
        Nothing  -> do
          tid <- freshTid nm sc
          case sc of
            T.VSGlobal -> modify $ \s' -> 
              s' {globalSUE = M.insert sid tid (globalSUE s')}
            T.VSLocal -> do
              mOldTid <- M.lookup sid <$> gets globalSUE
              modify $ \s' ->
                s' {localSUE = M.insert sid tid (localSUE s),
                    scopeSUE = SDeclared sid mOldTid : scopeSUE s}
          return tid
    Just tid -> return tid

lookupOrMakeLabel :: S.Ident -> Simp T.Id
lookupOrMakeLabel sid@(S.Ident nm _ _) = do
  oldLabels <- gets labels
  case M.lookup sid oldLabels of
    Just tlab -> return tlab
    Nothing   -> do
      tid <- freshTid nm T.VSLocal
      modify $ \s' -> s' {labels = M.insert sid tid (labels s')}
      return tid
  
resetLocalState :: Simp ()
resetLocalState = do
  s <- get
  put $ s {localObject = M.empty,
           scopeObject = [],
           localSUE = M.empty,
           scopeSUE = [],
           labels = M.empty}

--------------------------------
-- Working with source positions

niToP :: S.NodeInfo -> T.SPos
niToP ni = T.SPos {T.sourceName,T.sourceLine,T.sourceColumn}
  where
    p =  S.posOfNode ni
         
    sourceName = S.posFile p
    sourceLine = S.posRow p
    sourceColumn = S.posColumn p

-----------------------------
--- Failure and warnings
failNI :: S.NodeInfo -> String -> Simp a
failNI ni s = throwError $ s ++ ", at " ++ show (niToP ni)

warnNI :: S.NodeInfo -> String -> Simp ()
warnNI ni s = addWarning $ s ++ ", at " ++ show (niToP ni)

------------------------------
-- The translation
trCTranslUnit :: S.CTranslUnit -> Simp T.TransUnit
trCTranslUnit (S.CTranslUnit sexts _) = do
  exts <- concat <$> mapM (\s -> trCExtDecl s <* resetLocalState) sexts
  return $ T.TransUnit {T.exts}

trCExtDecl :: S.CExtDecl -> Simp [T.ExternalDecln]
trCExtDecl (S.CDeclExt d)  = map T.ExtDecln <$> trCDeclExt d T.VSGlobal
trCExtDecl (S.CFDefExt d)  = do def <- trCFDefExt d
                                return [T.ExtFunDef def]
trCExtDecl (S.CAsmExt _ ni) = failNI ni "Unsupported: assembly code"
 

trCDeclExt :: S.CDecl -> T.VarScope -> Simp [T.Decln]
trCDeclExt d outerScope = do
  tdecls <- trCDecl d outerScope
  mapM topLevelDecl tdecls
  where
    ni = S.annotation d
    sp = niToP ni

    topLevelDecl :: (Maybe T.Id,T.Type,Maybe (Maybe T.StorageClass),
                     Maybe T.Initializer, Maybe Integer)
                 -> Simp T.Decln
    topLevelDecl (_,_,_,_,Just _) = failNI ni
      "Illegal: top-level declaration with bit-field size annotation"
    topLevelDecl (_,_,Nothing,Just _,_) = failNI ni
      "Illegal: typedef with initializer"
    topLevelDecl (Nothing,_,Nothing,_,_) = failNI ni
      "Illegal: typdef with no identifier"
    topLevelDecl (Just nm,ty,Nothing,_,_) = return $ T.TyDef ty nm sp
    topLevelDecl (Nothing,ty,Just _,minit,_) =
      case (minit,ty) of
        (Just _,_) -> failNI ni $ 
          "Illegal: abstract declaration with initializer"
        (_,T.Struct _ _ _) -> return $ T.StructDecln ty sp
        (_,T.Union _ _ _)  -> return $ T.UnionDecln ty sp
        (_,T.Enum  _ _ _)  -> return $ T.EnumDecln ty sp
        _ -> failNI ni $ 
            "Unsupported: abstract declaration that isn't "
         ++ "a struct, union or enum type (" ++ show ty ++ ")"
    topLevelDecl (Just nm,ty,Just msc,minit,_) =
      case ty of
        T.Func fsp args varargs retty -> do
          when (isJust minit) $ failNI ni
            "Illegal: function declaration with initializer"
          return $ T.FunDecln 
             (T.FDecln {T.funStorage = msc,
                        T.funName = nm,
                        T.funArgs = args,
                        T.funVariadic = varargs,
                        T.funReturnTy = retty,
                        T.funPos = fsp})
             sp
        _ -> return $ T.VarDecln
               (T.VDecln {T.vdIdent = nm,
                          T.vdStorage = msc,
                          T.vdType = ty,
                          T.vdInit = minit})
               sp

-- Each "CDecl" potentially corresponds to several identifiers.  For example, in the
-- declaration:
-- 
--    int x=3, *y;
--
-- For each declared identifier (or abstract declaration) we return:
--
--   - The id (which is T.NoId for abstract declarations)
--
--   - The type of the identifier (in the example above, Int for x, and
--     Pointer Int for y)
--
--   - Information about the storage class, if any.  This is messy because the
--     "typedef" keyword is parsed as a storage class, but we don't treat it
--     that way in our internal syntax tree.  So, "Nothing" means typedef,
--     otherwise there is an optional storage class.
--
--   - An optional initializer (above, "Just 3" for x and "Nothing" for y)
--
--   - An optional bit-field size.  Necessary becausse "S.CDecl" is also used
--     for struct/union declarations, where explicit sizes may appear.
--
-- There are a variety of things that can occur in declarations that we just
-- throw away.  In particular, we drop type qualifiers (const and volatile)
-- and __attribute__ specifications because we do not model them.
--
-- Since this function can be called from global or local scope, it takes as an
-- argument the appropriate method for allocating new variables.
--
-- XXX Known problems: Declarations of the form
--
--    struct foo {...} x, y;
--
-- are handled really poorly.  Right now this gets parsed into what is
-- essentially two separate declarations:
--
--   struct foo {...} x;
--   struct foo {...} y;
--
-- which doesn't make sense, becuase foo should be added to the struct
-- namespace once.  A cleaner translation that preserves my intent that each
-- ExternalDecln contains at most one new identifier would be:
--
--   struct foo {...};
--   struct foo x;
--   struct foo y;
--
-- But I'm not doing this yet (and I have to think harder about whether it is
-- actually a general solution to the problem).  It's quite tricky in the case
-- of anonymous structs, because I'd have to generate a fresh name or soemthing.
trCDecl :: S.CDecl -> T.VarScope
        -> Simp [(Maybe T.Id,T.Type,Maybe (Maybe T.StorageClass),
                  Maybe T.Initializer, Maybe Integer)]
trCDecl (S.CDecl specifiers initDeclList outerNI) outerLife = do
  (typ,mmsc) <- processDeclSpecs specifiers outerLife
  case initDeclList of
    [] -> return [(Nothing,typ,mmsc,Nothing,Nothing)]
    _ -> do
      ds <- mapM (processInitDeclarator typ outerNI outerLife) initDeclList
      return $ map (\(nm,t,i,e) -> (nm,t,mmsc,i,e)) ds
  where
    -- The Specifiers list can contain storage classes, type qualifiers, and
    -- type names.  We throw away type qualifiers, because we don't handle
    -- them at all in the translation.
    --
    -- If the list contains more than one storage class, we declare defeat.
    -- If the list contains more than one type specifier, we declare defeat.
    --
    -- Otherwise, we return a type, and a (Maybe (Maybe StorageClass)), which
    -- is Nothing in the case of a typedef, and otherwise indicates a
    -- non-typedef declaration with an optional storage class.
    --
    -- processDeclSpec is to be folded over the list of declaration
    -- specifiers according to these rules.  The "bool" indicates whether
    -- "typedef" has been seen, and the "maybe storageclass" indicates whether
    -- any other storage class has been seen.
    processDeclSpec :: (Bool, Maybe T.StorageClass, [S.CTypeSpec])
                     -> S.CDeclSpec
                     -> Simp (Bool, Maybe T.StorageClass, [S.CTypeSpec])
    processDeclSpec (td,msc,tss) ds =
      case ds of
        S.CStorageSpec (S.CTypedef ni) ->
          if td then 
              failNI ni "Typedef keyword encountered twice in one declaration"
            else if isJust msc then 
                failNI ni "Unsupported: typedef with other storage class"
              else return (True,Nothing,tss)
        S.CStorageSpec sc -> do
          tsc <- transSS sc
          let ni = S.annotation sc
          case msc of
            Just _ -> failNI ni
               "Unsupported: multiple storage classes in one declaration"
            Nothing -> 
              if td then
                failNI ni "Unsupported: typedef with other storage class"
              else return (False,Just tsc,tss)
        S.CTypeQual _ -> return (td,msc,tss)
        S.CTypeSpec ts -> return (td,msc,ts:tss)

    processDeclSpecs :: [S.CDeclSpec] -> T.VarScope -> Simp (T.Type, Maybe (Maybe T.StorageClass))
    processDeclSpecs dss l = do
      (tdef,mmsc,tss) <- foldM processDeclSpec (False,Nothing,[]) dss
      typ <- trCTypeSpec outerNI tss l
      case (tdef,mmsc) of
        (True,Just _) ->
            failNI outerNI "Unsupported: typedef with other storage class"
        (True,Nothing) -> return (typ,Nothing)
        (False,msc) -> return (typ,Just msc)
                        

    transSS :: S.CStorageSpec -> Simp T.StorageClass
    transSS (S.CTypedef  ni) = failNI ni "Internal Error: typedef encountered in transSS"
    transSS (S.CThread   ni) = failNI ni "Unsupported: thread local storage"
    transSS (S.CRegister ni) = failNI ni "Unsupported: register storage class"
    transSS (S.CAuto     _)  = return T.SCAuto
    transSS (S.CStatic   _)  = return T.SCStatic
    transSS (S.CExtern   _)  = return T.SCExtern
                          

    processInitDeclarator :: T.Type -> S.NodeInfo -> T.VarScope
                          -> (Maybe S.CDeclr, Maybe S.CInit, Maybe S.CExpr)
                          -> Simp (Maybe T.Id,T.Type,Maybe T.Initializer,Maybe Integer)
    processInitDeclarator t ni l (mdecl,sinit,ssz) = do
      (nm,typ) <- 
        case mdecl of
          Nothing   -> return (Nothing,t)
          Just decl -> processDeclarator t decl l
      tinit <- mapM trCInit sinit
      tsz <-  -- XXX C permits a bit more here
        case ssz of
          Nothing -> return Nothing
          Just (S.CConst (S.CIntConst (S.CInteger i _ _) _)) -> return $ Just i
          _ -> failNI ni "Unsupported: bit-field size that isn't a int literal"
      return (nm,typ,tinit,tsz)
    

    -- XXX ignoring ASM name.  probably fine
    processDeclarator :: T.Type -> S.CDeclr -> T.VarScope -> Simp (Maybe T.Id,T.Type)
    processDeclarator ty (S.CDeclr mnm dds _ _ _) l = do
      mtnm <- 
        case (mnm,l) of
          (Nothing,_) -> return Nothing
          (Just nm,T.VSGlobal) -> do
          -- in global scope, multiple declarations are allowed
            mtnm' <- lookupObject nm
            case mtnm' of
              Just tnm' -> return $ Just tnm'
              Nothing -> Just <$> freshObject l nm
          (Just nm,T.VSLocal) -> Just <$> freshObject l nm
      (mtnm,) <$> processDirectDeclarators ty dds


    -- modifiers that appear in the name part of a declaration
    processDirectDeclarators :: T.Type -> [S.CDerivedDeclr] -> Simp T.Type
    processDirectDeclarators outert dds = foldM processDD outert (reverse dds)
      where
        processDD t (S.CPtrDeclr _ ni) = return $ T.PointerType (niToP ni) t
        processDD t (S.CArrDeclr _ (S.CNoArrSize complete) ni) =
          if not complete then return (T.ArrayType (niToP ni) t Nothing)
          else failNI ni $ "Unsupported: complete array missing size"
        processDD t (S.CArrDeclr _ (S.CArrSize _ e) ni) = -- XXX what is bool here?
          case e of
            S.CConst (S.CIntConst i _) ->
              return $ T.ArrayType (niToP ni) t (Just $ S.getCInteger i)
            _ -> do
              warnNI ni $ "Ignored unsupported non-constant array size "
                       ++ render (S.pretty e)
              return $ T.ArrayType (niToP ni) t Nothing
        processDD _ (S.CFunDeclr (Left _) _ ni) =
          failNI ni "Unsupported: \"old style\" function parameters."
        processDD t (S.CFunDeclr (Right (params,varargs)) _ ni) = do
          args <- mapM trFunArg params
          -- If the function has a single unnamed argument of type void,
          -- replace this with no argumsnts
          let args' = case args of
                        [(Nothing,T.VoidType _)] -> []
                        _ -> args
          return $ T.Func (niToP ni) args' varargs t
          where
            trFunArg :: S.CDecl -> Simp (Maybe T.Id,T.Type)
            trFunArg (S.CDecl declspecs innerdds innerni) = do
              (typ,msc) <- processDeclSpecs declspecs T.VSLocal
              case msc of
                Nothing -> failNI innerni "Illegal: function parameter typedef"
                Just Nothing -> return ()
                Just (Just _) -> failNI innerni 
                  "Unsupported: function parameter with storage class"
              case innerdds of
                [] -> return (Nothing,typ)
                [(Just d,Nothing,Nothing)] -> processDeclarator typ d T.VSLocal
                _ -> failNI innerni "Unsupported function parameter"


data TSModifiers =  TSModifiers {tsShort :: Bool,
                                 tsLong  :: Int,
                                 tsSigned :: Bool,
                                 tsUnsigned :: Bool}


noModifiers :: TSModifiers -> Bool
noModifiers (TSModifiers {tsShort,tsLong,tsSigned,tsUnsigned}) =
    not $ or [tsShort,tsLong>0,tsSigned,tsUnsigned]

data TSModifiable = TSInt | TSDouble | TSChar

trCTypeSpec :: S.NodeInfo -> [S.CTypeSpec] -> T.VarScope -> Simp T.Type
trCTypeSpec outerni specs lf = processTypeSpec specs Nothing initMods
  where
    initMods = TSModifiers False 0 False False

    processTypeSpec :: [S.CTypeSpec] -> Maybe TSModifiable -> TSModifiers -> Simp T.Type
    processTypeSpec [] mm mds = handleModifiables mm outerni mds

    processTypeSpec (S.CVoidType ni:[]) Nothing mods | noModifiers mods =
      return $ T.VoidType $ niToP ni
    processTypeSpec (S.CVoidType ni:_) _ _ =
      failNI ni "Illegal: void type with additional specifiers"

    processTypeSpec (S.CCharType _:tss) Nothing mds =
      processTypeSpec tss (Just TSChar) mds
    processTypeSpec (S.CCharType ni:_) _ _ =
      failNI ni $ "Illegal: \"char\" specifier appears twice or with "
               ++ "another base type in declaration"

    processTypeSpec (S.CShortType ni:_) _ mds | tsShort mds =
      failNI ni "Illegal: specifier \"short\" appears twice"
    processTypeSpec (S.CShortType ni:_) _ mds | tsLong mds > 0 =
      failNI ni $ "Illegal: specifiers \"short\" and \"long\" both appear "
               ++ "in the same declaration"
    processTypeSpec (S.CShortType _:tss) mm mds  =
      processTypeSpec tss mm (mds {tsShort = True})
      
    processTypeSpec (S.CIntType _:tss) Nothing mds =
      processTypeSpec tss (Just TSInt) mds
    processTypeSpec (S.CIntType ni:_) (Just _) _ =
      failNI ni $ "Illegal: \"int\" specifier appears twice or with "
               ++ "annother base type in declaration"

    processTypeSpec (S.CLongType ni:_) _ mds | tsLong mds > 1 =
      failNI ni "Illegal: specifier \"long\" appears more than twice"
    processTypeSpec (S.CLongType ni:_) _ mds | tsShort mds =
      failNI ni $ "Illegal: specifiers \"short\" and \"long\" both appear "
                 ++ "in the same declaration"
    processTypeSpec (S.CLongType _:tss) mm mds  =
      processTypeSpec tss mm (mds {tsLong = (tsLong mds) + 1})
      
    processTypeSpec (S.CFloatType ni:[]) Nothing mds | noModifiers mds =
      return $ T.Floating (niToP ni) T.Float
    processTypeSpec (S.CFloatType ni:_) _ _ =
      failNI ni "Illegal: \"float\" type with additional specifiers"

    processTypeSpec (S.CDoubleType _:tss) Nothing mds =
      processTypeSpec tss (Just TSDouble) mds
    processTypeSpec (S.CDoubleType ni:_) (Just _) _ =
      failNI ni $ "Illegal: \"double\" specifier appears twice or with "
               ++ "another base type in declaration"

    processTypeSpec (S.CInt128Type ni:_) _ _ =
      failNI ni "Unsupported: int128 type."

    processTypeSpec (S.CSignedType ni:_) _ mds | tsSigned mds =
      failNI ni "Illegal: specifier \"signed\" appears twice"
    processTypeSpec (S.CSignedType ni:_) _ mds | tsUnsigned mds =
      failNI ni $ "Illegal: specifiers \"signed\" and \"unsigned\" both appear "
               ++ "in the same declaration"
    processTypeSpec (S.CSignedType _:tss) mm mds =
      processTypeSpec tss mm (mds {tsSigned = True})
    
    processTypeSpec (S.CUnsigType ni:_) _ mds | tsUnsigned mds =
      failNI ni "Illegal: specifier \"unsigned\" appears twice"
    processTypeSpec (S.CUnsigType ni:_) _ mds | tsSigned mds =
      failNI ni $ "Illegal: specifiers \"signed\" and \"unsigned\" both appear "
               ++ "in the same declaration"
    processTypeSpec (S.CUnsigType _:tss) mm mds =
      processTypeSpec tss mm (mds {tsUnsigned=True})

    processTypeSpec (S.CBoolType ni:[]) Nothing mods | noModifiers mods =
      return $ T.BoolType $ niToP ni
    processTypeSpec (S.CBoolType ni:_) _ _ =
      failNI ni "Illegal: bool type with additional specifiers"


    processTypeSpec (S.CComplexType ni:_) _ _ =
      failNI ni $ "Unsupported: \"complex\" type"

    processTypeSpec (S.CSUType csu _:[]) Nothing mds | noModifiers mds =
      trCStructUnion csu lf
    processTypeSpec (S.CSUType _ ni:_) _ _ =
      failNI ni $ "Illegal: structure or union type with "
               ++ "additional specifiers"

    processTypeSpec (S.CEnumType enum _:[]) Nothing mds | noModifiers mds =
      trCEnum lf enum
    processTypeSpec (S.CEnumType _ ni:_) _ _ =
      failNI ni "Illegal: enum type with additional specifiers"

    processTypeSpec (S.CTypeDef nm ni:[]) Nothing mds | noModifiers mds = do
      mtnm <- lookupObject nm
      case mtnm of
        Nothing -> failNI ni $ "Undeclared type identifier " ++ show nm
        Just tnm -> return $ T.TypeDef (niToP ni) tnm
    processTypeSpec (S.CTypeDef _ ni:_) _ _ =
      failNI ni "Illegal: type identifier with additional specifiers"

    processTypeSpec (S.CTypeOfExpr _ ni:_) _ _ =
      failNI ni "Unsupported: \"typeof\" in declaration"

    processTypeSpec (S.CTypeOfType _ ni:_) _ _ =
      failNI ni "Unsupported: \"typeof\" in declaration"

    handleModifiables :: Maybe TSModifiable -> S.NodeInfo -> TSModifiers -> Simp T.Type
    handleModifiables mts ni mods =
      case mts of
        Nothing     -> intcase T.Signed -- "int" is implied, according to C spec
        Just TSInt  -> intcase T.Signed
        Just TSChar -> intcase T.Unsigned
        Just TSDouble ->
          if tsSigned mods then
            failNI ni $ "Illegal: \"signed\" and \"double\" specifiers "
                     ++ "appear together"
          else if tsUnsigned mods then
            failNI ni $ "Illegal: \"unsigned\" and \"double\" specifiers "
                     ++ "appear together"
          else if tsShort mods then
            failNI ni $ "Illegal: \"unsigned\" and \"short\" specifiers "
                     ++ "appear together"
          else if tsLong mods > 0 then
            return $ T.Floating (niToP ni) T.LongDouble
          else 
            return $ T.Floating (niToP ni) T.Double
      where
        signedness :: Maybe (T.BaseIntType -> T.IntegralType)
        signedness | tsSigned mods   = Just T.Signed
                   | tsUnsigned mods = Just T.Unsigned
                   | otherwise       = Nothing

        intcase :: (T.BaseIntType -> T.IntegralType) -> Simp T.Type
        intcase dfltSgn =
          let sgn = case signedness of
                      Just s  -> s
                      Nothing -> dfltSgn in
          return $ T.Integral (niToP ni) $
            if tsShort mods then sgn T.ShortInt
            else if tsLong mods > 0 then sgn T.LongInt
            else sgn T.Int
      

trCStructUnion :: S.CStructUnion -> T.VarScope -> Simp T.Type
trCStructUnion (S.CStruct _ Nothing Nothing _ ni) _ =
  failNI ni $ "Illegal: struct or union missing both name and fields"
trCStructUnion (S.CStruct tag mnm mflds _ ni) lf = do
  mtnm <- mapM (lookupOrMakeSUE lf) mnm

  sOrU sp mtnm <$> mapM trSUContents mflds
  where
    sp = niToP ni

    sOrU = case tag of 
             S.CStructTag -> T.Struct
             S.CUnionTag -> T.Union
             
    trSUContents :: [S.CDecl] -> Simp [(Maybe String,T.Type,Maybe Integer)]
    trSUContents flds = do
      beginScope 
      cntns <- concat <$> mapM trSUDecl flds
      endScope
      return cntns

    trSUDecl :: S.CDecl -> Simp [(Maybe String,T.Type,Maybe Integer)]
    trSUDecl d = do
      ds <- trCDecl d T.VSLocal
      mapM trSUField ds
      where
        fni = S.annotation d

        trSUField :: (Maybe T.Id,T.Type,Maybe (Maybe T.StorageClass),
                      Maybe T.Initializer, Maybe Integer)
                   -> Simp (Maybe String,T.Type,Maybe Integer)
        trSUField (_,_,Nothing,_,_) =
          failNI fni "Illegal: typedef encountered in structure field"
        trSUField (_,_,Just (Just _),_,_) =
          failNI fni "Illegal: storage class encountered in structure field"
        trSUField (_,_,_,Just _,_) =
          failNI fni "Illegal: initializer encountered in structure field"
        trSUField (Nothing,_,_,_,Nothing) =
          failNI fni "Illegal: structure field lacks both name and size"
        trSUField (Nothing,typ,_,_,Just sz) = return (Nothing,typ,Just sz)
        trSUField (Just tid,typ,_,_,msz) = return (Just (T.stringPart tid),typ,msz)
      

trCEnum :: T.VarScope -> S.CEnum -> Simp T.Type
trCEnum _ (S.CEnum Nothing Nothing _ ni) =
  failNI ni "Illegal: enumeration declaration without name or enumerators"
trCEnum _ (S.CEnum _ (Just []) _ ni) =
  failNI ni $ "Illegal: enumeration declaration with empty but present "
           ++ "list of enumerators"
trCEnum life (S.CEnum mnm menums _ ni) = do
    mtnm <- mapM (lookupOrMakeSUE life) mnm
    T.Enum (niToP ni) mtnm <$> mapM trEnumerators menums
  where
    trEnumerators :: [(S.Ident,Maybe S.CExpr)] -> Simp [(T.Id,Maybe T.Exp)]
    trEnumerators = mapM trEnumerator

    trEnumerator :: (S.Ident,Maybe S.CExpr) 
                 -> Simp (T.Id, Maybe T.Exp)
    trEnumerator (enm,meval) = (,) <$> freshObject life enm <*> mapM trCExpr meval


trCFDefExt :: S.CFunDef -> Simp T.FunDef
trCFDefExt (S.CFunDef _ _ (_:_) _ ni) = failNI ni
   "Unsupported: old-style function arguments"
trCFDefExt (S.CFunDef declspecs declr [] stmt ni) = do
  beginScope
  decl <- trCDeclExt (S.CDecl declspecs [(Just declr,Nothing,Nothing)] ni) T.VSGlobal
  case decl of
    [T.FunDecln fdcl sp] -> do
      bdy <- trCStat stmt
      (return $ T.FunDef {T.decl = fdcl, T.funBody = bdy, T.fdPos = sp})
           <* endScope
    [] -> failNI ni
     "Illegal: function definition with abstract declaration"
    (_:_:_) -> failNI ni
     "Illegal: function definition declares multiple identifiers"
    _ -> failNI ni 
     "Illegal: function definition with non-function declaration"

trCStat :: S.CStat -> Simp T.Statement
trCStat (S.CLabel lab s _ ni) = do
  tlab <- lookupOrMakeLabel lab
  T.Labelled tlab <$> trCStat s <*> pure (niToP ni)
trCStat (S.CCase e s ni) =
  T.Case <$> trCExpr e <*> trCStat s <*> pure (niToP ni)
trCStat (S.CCases _ _ _ ni) = failNI ni "Unsupported: case statement over range"
trCStat (S.CDefault s ni) = T.Default <$> trCStat s <*> pure (niToP ni)
trCStat (S.CExpr me ni)   = T.ExpStm <$> mapM trCExpr me <*> pure (niToP ni)
trCStat (S.CCompound (_:_) _ ni) = failNI ni "Unsupported: local labels"
trCStat (S.CCompound [] dss ni) = do
  beginScope
  tc <- T.Compound <$> (concat <$> mapM trCBlockItem dss) <*> pure (niToP ni)
  endScope
  return tc
  where
    trCBlockItem :: S.CBlockItem -> Simp [Either T.Decln T.Statement]
    trCBlockItem (S.CBlockStmt s) = do ts <- trCStat s
                                       return $ [Right ts]
    trCBlockItem (S.CBlockDecl d) = do tds <- trCDeclExt d T.VSLocal
                                       return $ map Left tds
    trCBlockItem (S.CNestedFunDef fd) = failNI (S.annotation fd) 
      "Unsupported: nested function definitions"
trCStat (S.CIf e s1 ms2 ni) = 
  T.IfStm <$> trCExpr e <*> trCStat s1 <*> mapM trCStat ms2 
          <*> pure (niToP ni)
trCStat (S.CSwitch e s ni) =
  T.Switch <$> trCExpr e <*> trCStat s <*> pure (niToP ni)
trCStat (S.CWhile e s isDoWhile ni) =
  if isDoWhile then
    T.DoWhile <$> trCStat s <*> trCExpr e <*> pure (niToP ni)
  else
    T.While <$> trCExpr e <*> trCStat s <*> pure (niToP ni)
trCStat (S.CFor initl me1 me2 s ni) = 
  T.For <$> tde <*> mapM trCExpr me1 <*> mapM trCExpr me2
        <*> trCStat s <*> pure (niToP ni)
  where
    tde = case initl of 
            Left Nothing  -> return $ Right Nothing
            Left (Just e) -> Right . Just <$> trCExpr e
            Right d       -> Left <$> trCDeclExt d T.VSLocal
trCStat (S.CGoto lab ni)  = T.Goto <$> lookupOrMakeLabel lab <*> pure (niToP ni)
trCStat (S.CGotoPtr _ ni) = failNI ni "Unsupported: computed goto"
trCStat (S.CCont ni)      = return $ T.Continue (niToP ni)
trCStat (S.CBreak ni)     = return $ T.Break (niToP ni)
trCStat (S.CReturn me ni) = T.Return <$> mapM trCExpr me <*> pure (niToP ni)
trCStat (S.CAsm _ ni)     = return $ T.Asm (niToP ni)

trCExpr :: S.CExpr -> Simp T.Exp
trCExpr (S.CComma es ni) = T.CommaExp <$> mapM trCExpr es <*> pure (niToP ni)
trCExpr (S.CAssign aop e1 e2 ni) = 
    T.AssignExp taop <$> trCExpr e1 <*> trCExpr e2 <*> pure (niToP ni)
  where
    taop = case aop of
             S.CAssignOp -> T.Assign
             S.CMulAssOp -> T.MulAssign
             S.CDivAssOp -> T.DivAssign
             S.CRmdAssOp -> T.ModAssign
             S.CAddAssOp -> T.AddAssign
             S.CSubAssOp -> T.SubAssign
             S.CShlAssOp -> T.LeftAssign
             S.CShrAssOp -> T.RightAssign
             S.CAndAssOp -> T.BitwiseAndAssign
             S.CXorAssOp -> T.BitwiseXorAssign
             S.COrAssOp  -> T.BitwiseOrAssign
trCExpr (S.CCond test mte fe ni) =
  T.Cond <$> trCExpr test <*> mapM trCExpr mte <*> trCExpr fe 
         <*> pure (niToP ni)
trCExpr (S.CBinary bop ce1 ce2 ni) =
  T.Bin tbop <$> trCExpr ce1 <*> trCExpr ce2 <*> pure (niToP ni)
  where
    tbop = case bop of
             S.CMulOp -> T.Multiply
             S.CDivOp -> T.Divide
             S.CRmdOp -> T.Modulus
             S.CAddOp -> T.Add
             S.CSubOp -> T.Subtract
             S.CShlOp -> T.LeftShift
             S.CShrOp -> T.RightShift
             S.CLeOp  -> T.LessThan
             S.CGrOp  -> T.GreaterThan
             S.CLeqOp -> T.LessThanOrEqual
             S.CGeqOp -> T.GreaterThanOrEqual
             S.CEqOp  -> T.Equal
             S.CNeqOp -> T.NotEqual
             S.CAndOp -> T.BitwiseAnd
             S.CXorOp -> T.BitwiseXor
             S.COrOp  -> T.BitwiseOr
             S.CLndOp -> T.LogicalAnd
             S.CLorOp -> T.LogicalOr
trCExpr (S.CCast d e ni) =
  T.Cast <$> typ <*> trCExpr e <*> pure (niToP ni)
  where
    typ = do 
      ds <- trCDecl d T.VSLocal -- Scope doesn't matter here, since we fail if there are names
      case ds of
        [] -> failNI ni "Illegal: missing type in type cast"
        (_:_:_) -> failNI ni "Illegal: multiple types in type cast"
        [(_,_,Nothing,_,_)] -> failNI ni "Illegal: typedef in type cast"
        [(_,_,Just (Just _),_,_)] -> failNI ni "Illegal: storage class in type cast"
        [(_,_,_,Just _,_)] -> failNI ni "Illegal: initializer in type cast"
        [(_,_,_,_,Just _)] -> failNI ni "Illegal: bit field size in type cast"
        [(Just _,_,_,_,_)] -> 
            failNI ni "Illegal: non-abstract declaration used as type cast"
        [(Nothing,t,Just Nothing,Nothing,Nothing)] -> return t
trCExpr (S.CUnary uop e ni) =
  T.Unary tuop <$> trCExpr e <*> pure (niToP ni)
  where
    tuop = case uop of 
             S.CPreIncOp  -> T.PreInc
             S.CPreDecOp  -> T.PreDec
             S.CPostIncOp -> T.PostInc
             S.CPostDecOp -> T.PostDec
             S.CAdrOp     -> T.Address
             S.CIndOp     -> T.Indirection
             S.CPlusOp    -> T.UnaryPlus
             S.CMinOp     -> T.UnaryMinus
             S.CCompOp    -> T.BitwiseNot
             S.CNegOp     -> T.LogicalNot
trCExpr (S.CSizeofExpr e ni) = T.SizeOfExp <$> trCExpr e <*> pure (niToP ni)
trCExpr (S.CSizeofType d ni) = T.SizeOfTy <$> typ <*> pure (niToP ni)
  where
    typ = do 
      ds <- trCDecl d T.VSLocal -- Size doesn't matter here, since names cause failure
      case ds of  -- XXX factor out as type name decl
        [] -> failNI ni "Illegal: missing type in sizeof expression"
        (_:_:_) -> failNI ni "Illegal: multiple types in sizeof expression"
        [(_,_,Nothing,_,_)] -> failNI ni "Illegal: typedef in sizeof expression"
        [(_,_,Just (Just _),_,_)] -> failNI ni "Illegal: storage class in sizeof expression"
        [(_,_,_,Just _,_)] -> failNI ni "Illegal: initializer in sizeof expression"
        [(_,_,_,_,Just _)] -> failNI ni "Illegal: bit field size in sizeof expression"
        [(Just _,_,_,_,_)] -> 
            failNI ni "Illegal: non-abstract declaration used as sizeof expression"
        [(Nothing,t,Just Nothing,Nothing,Nothing)] -> return t
trCExpr (S.CAlignofExpr _ ni) = failNI ni "Unsupported: alignof(e) expression"
trCExpr (S.CAlignofType _ ni) = failNI ni "Unsupported: alignof(t) expression"
trCExpr (S.CComplexReal _ ni) = failNI ni "Unsupported: complex numbers"
trCExpr (S.CComplexImag _ ni) = failNI ni "Unsupported: complex numbers"
trCExpr (S.CIndex e1 e2 ni) =
  T.Subscript <$> trCExpr e1 <*> trCExpr e2 <*> pure (niToP ni)
trCExpr (S.CCall f args ni) =
  T.FunCall <$> trCExpr f <*> mapM trCExpr args <*> pure (niToP ni)
trCExpr (S.CMember e (S.Ident lab _ _) deref ni) = do
  te <- trCExpr e
  return $ T.CompSel te selop lab (niToP ni)
  where
    selop = if deref then T.IndirSel else T.DirSel
trCExpr (S.CVar sid@(S.Ident nm _ _) ni) = do
  mtid <- lookupObject sid
  case mtid of
    Nothing  -> 
      if isPrefixOf "__builtin" nm
      then return $ T.IdExp (T.Fixed nm) (niToP ni)
      else failNI ni $ "Variable " ++ nm ++ " out of scope"
    Just tid -> return $ T.IdExp tid (niToP ni)
trCExpr (S.CConst c) = return $ T.ConstExp (trCConst c)
                                           (niToP (S.annotation c))
trCExpr (S.CCompoundLit _ _ ni) = failNI ni "Unsupported: compound literals"
trCExpr (S.CStatExpr _ ni) = failNI ni
   "Unsupported: compound statement as expression"
trCExpr (S.CLabAddrExpr _ ni) = failNI ni
   "Unsupported: taking the address of a label"
trCExpr (S.CBuiltinExpr a) = failNI (S.annotation a) "Unsupported: GNU C builtins"

trCConst :: S.CConst -> T.Const
trCConst (S.CIntConst   (S.CInteger i _ _) _) = T.IntConst i
trCConst (S.CCharConst  (S.CChar c _) _)      = T.CharConst [c]
trCConst (S.CCharConst  (S.CChars cs _) _)    = T.CharConst cs
trCConst (S.CFloatConst (S.CFloat s) _)       = T.FloatConst s
trCConst (S.CStrConst   (S.CString s _) _)    = T.StringConst s

trCInit :: S.CInit -> Simp T.Initializer
trCInit (S.CInitExpr e _)     = T.SimpleInitializer <$> trCExpr e
trCInit (S.CInitList parts _) = T.ListInitializer <$> mapM trCInitListEl parts
  where
    trCInitListEl :: ([S.CDesignator],S.CInit) -> Simp ([T.InitDesignator],T.Initializer)
    trCInitListEl (desgs,i) = (,) <$> mapM trCDesig desgs <*> trCInit i

    trCDesig :: S.CDesignator -> Simp T.InitDesignator
    trCDesig (S.CArrDesig e ni)     =
      T.ArrDesig <$> trCExpr e <*> pure (niToP ni)
    trCDesig (S.CMemberDesig (S.Ident s _ _) ni) =
      return $ T.MemberDesig s (niToP ni)
    trCDesig (S.CRangeDesig _ _ ni) = failNI ni "Unsupported: Range initializers"
