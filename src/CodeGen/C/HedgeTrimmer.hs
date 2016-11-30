{- |
Module      :  CodeGen.C.HedgeTrimmer
Description :  Code simplification via elimination of unused definitions.
Copyright   :  Draper Laboratories

Authors     :  Chris Casinghino

Running CPP has the effect of including loads and loads of definitions from
headers.  Most aren't used, but get in the way of CSP generation.  Hedge
trimmer takes in a translation unit and gets rid of any declarations that
aren't from the specified files or used by stuff in the specified files.


-}


module CodeGen.C.HedgeTrimmer (trim) where

import qualified Data.Set as S
import Data.List (foldl')

import System.FilePath (takeFileName)

import CodeGen.C.Syntax

-- The goal of hedge trimmer is to eliminate all the "unused" definitions and
-- declarations that are included in a file after running CPP.
--
-- Defining unused is surprisingly tricky.  A natural guess is that we want to
-- keep only the stuff that was in the file before CPP pasted in the
-- #includes, along with anything that stuff relies on.  But, in general an
-- #include statement is just a textual include and it could be that the
-- programmer actually intends the included stuff to be an important part of
-- this particular compilation unit.
--
-- For now, we're being as agnostic as possible.  The relevant hedge trimmer
-- functions take in a list of files and keep around all the stuff that
-- originally came from those files and anything that stuff relies on.  As a
-- minor twist, declarations mentioned in the "externals" file, which we know
-- will be hand-coded in the CSP runtime, do not count as used.  This is because
-- we don't want to keep their definitions - we've got that stuff already.
--
-- We need two basic pieces of analysis for this purpose:
--
-- - The "used" functions find every identifier that's refered to in a
--   particular piece of C syntax.
--
-- - the "declared" functions find every identifier that's declared in a
--   particular piece of syntax.
--
-- The overall hedgetrimmer pass then uses these tools like this: we take the
-- result of CPP and consider each external declaration in reverse order,
-- maintaining a collection of every identifier used by the definitions we've
-- decided to keep so far.  For each new declaration, we keep it if (a) it's
-- from one of the files from which we are keeping everything, or (b) it
-- declares an identifier that's used by code we've already kept.  If we keep
-- this declaration, we add all identifiers it uses to the collection.  Then
-- we move on to the next declaration.



-- The C namespaces.  There are two additional namespaces that we do not need
-- to keep track of for hedgetrimmer: Each struct and union has a unique
-- namespace associated with its member names, and there is a namespace of
-- labels.
data Names = Names {objectNames :: S.Set Id, -- objects, functions, typedefs and
                                             -- enum constants

                    tagNames    :: S.Set Id  -- names of structs, unions and enums
                   } deriving (Show)

nUnion :: Names -> Names -> Names
nUnion (Names {objectNames=o1, tagNames=t1})
       (Names {objectNames=o2, tagNames=t2}) =
  Names {objectNames = o1 `S.union` o2,
         tagNames    = t1 `S.union` t2}

nUnions :: [Names] -> Names
nUnions = foldl' nUnion nEmpty

nEmpty :: Names
nEmpty = Names {objectNames=S.empty,
                tagNames   =S.empty}

nDifference :: Names -> Names -> Names
nDifference (Names {objectNames=o1, tagNames=t1})
            (Names {objectNames=o2, tagNames=t2}) =
  Names {objectNames = S.difference o1 o2,
         tagNames = S.difference t1 t2}

nSubtractObjects :: Names -> S.Set Id -> Names
nSubtractObjects n os = n {objectNames = S.difference (objectNames n) os}
           
nNull :: Names -> Bool
nNull (Names {objectNames,tagNames}) = 
  S.null objectNames && S.null tagNames

nIntersection  :: Names -> Names -> Names
nIntersection (Names {objectNames=o1, tagNames=t1})
              (Names {objectNames=o2, tagNames=t2}) =
  Names {objectNames = S.intersection o1 o2,
         tagNames    = S.intersection t1 t2}

nInsertObject :: Id -> Names -> Names
nInsertObject o n = n {objectNames = S.insert o (objectNames n)}

nInsertTag :: Id -> Names -> Names
nInsertTag t n = n {tagNames = S.insert t (tagNames n)}

--------------------
--- used*
--------------------

usedExternalDecln :: ExternalDecln -> Names
usedExternalDecln (ExtDecln d)   = usedDecln d
usedExternalDecln (ExtFunDef fd) = usedFunDef fd

usedDecln :: Decln -> Names
usedDecln (FunDecln fd _)    = usedFDecln fd
usedDecln (VarDecln vd _)    = usedVDecln vd
usedDecln (TyDef ty _ _)     = usedType ty
usedDecln (StructDecln ty _) = usedType ty
usedDecln (UnionDecln ty _)  = usedType ty
usedDecln (EnumDecln ty _)   = usedType ty

-- The union of the stuff used in the declaration and (the stuff used in the
-- body, minus the function arguments)
usedFunDef :: FunDef -> Names
usedFunDef (FunDef {decl,funBody}) = 
  nUnion (usedFDecln decl)
         (nSubtractObjects (usedStatement funBody) args)
  where
    args :: S.Set Id
    args = foldl (\s (mnm,_) -> case mnm of
                                  Just nm -> S.insert nm s
                                  Nothing -> s)
                 S.empty (funArgs decl)

usedFDecln :: FDecln -> Names
usedFDecln (FDecln {funArgs,funReturnTy}) =
  nUnions $ usedType funReturnTy : map (usedType . snd) funArgs

usedVDecln :: VDecln -> Names
usedVDecln (VDecln {vdType,vdInit}) =
  nUnion (usedType vdType) (maybe nEmpty usedInitializer vdInit)

usedType :: Type -> Names
usedType (VoidType _)       = nEmpty
usedType (Integral _ _)     = nEmpty
usedType (BoolType _)       = nEmpty
usedType (Floating _ _)     = nEmpty
usedType (PointerType _ t)  = usedType t
usedType (ArrayType _ t _)  = usedType t
usedType (Struct _ mn flds) = usedStructUnion mn flds
usedType (Union _ mn flds)  = usedStructUnion mn flds
usedType (Enum _ mn Nothing)    = (maybe id nInsertTag mn) nEmpty
usedType (Enum _ _ (Just flds)) = nUnions $ map usedEnum flds
  where
    usedEnum :: (Id, Maybe Exp) -> Names
    usedEnum (_, me) = maybe nEmpty usedExp me
usedType (Func _ args _ t) = 
  nUnions $ (usedType t) : map (usedType . snd) args
usedType (TypeDef _ nm)      = nInsertObject nm nEmpty

-- When a struct appears _with_ its fields, it is a declaration of the tag
-- (not a use), and the types of the fields may also use various identifiers.
-- When a struct appears _without_ its fields, it is a use of the tag.
-- 
usedStructUnion :: Maybe Id -> Maybe [(Maybe String, Type, Maybe Integer)] -> Names
usedStructUnion mn Nothing    = (maybe id nInsertTag mn) nEmpty
usedStructUnion _ (Just flds) = nUnions $ map usedField flds
  where
    usedField :: (Maybe String, Type, Maybe Integer) -> Names
    usedField (_, t, _) = usedType t

usedStatement :: Statement -> Names
usedStatement (Compound dss _) =
 -- This is a little tricky, because we must deal with the possibility that
 -- declarations shadow outer declarations.  This makes order important: if a
 -- variable is used and then a new thing of the same name is declarted in a
 -- later statement, it's used.  If it's declared and then used, it's not
 -- used.
  foldr compoundPart nEmpty dss
  where
    compoundPart :: Either Decln Statement -> Names -> Names
    compoundPart (Left d) n    = nUnion (usedDecln d)
                                        (nDifference n (declaredDecln d))
    compoundPart (Right s) n   = nUnion (usedStatement s) n
usedStatement (ExpStm me _)    = maybe nEmpty usedExp me
usedStatement (IfStm e s1 ms2 _) =
  nUnions [usedExp e, usedStatement s1, maybe nEmpty usedStatement ms2]
usedStatement (Switch e s _)   = nUnion (usedExp e) (usedStatement s)
usedStatement (Case e s _)     = nUnion (usedExp e) (usedStatement s)
usedStatement (Default s _)    = usedStatement s 
usedStatement (While e s _)    = nUnion (usedExp e) (usedStatement s)
usedStatement (DoWhile s e _)  = nUnion (usedExp e) (usedStatement s)
usedStatement (For dme me2 me3 s _) =
   case dme of
     Left ds  -> nDifference (nUnions $ simpleUsed : map usedDecln ds)
                             (nUnions $ map declaredDecln ds)
     Right me -> nUnion simpleUsed $ maybe nEmpty usedExp me
 where
   -- everything except the stuff before the first semicolon
   simpleUsed = nUnions [maybe nEmpty usedExp me2,
                         maybe nEmpty usedExp me3,
                         usedStatement s]
usedStatement (Labelled _ s _) = usedStatement s
usedStatement (Return me _)    = maybe nEmpty usedExp me
usedStatement (Break _)        = nEmpty
usedStatement (Continue _)     = nEmpty
usedStatement (Goto _ _)       = nEmpty
usedStatement (Asm _)          = nEmpty -- XXX ?

usedInitializer :: Initializer -> Names
usedInitializer (SimpleInitializer e) = usedExp e
usedInitializer (ListInitializer is)  =
  nUnions $ map (\(ds,i) -> nUnions $ (usedInitializer i) : map usedDesig ds)
                is
  where
    usedDesig (ArrDesig e _)    = usedExp e
    usedDesig (MemberDesig _ _) = nEmpty

usedExp :: Exp -> Names
usedExp (CommaExp es _)       = nUnions $ map usedExp es
usedExp (IdExp nm _)          = nInsertObject nm nEmpty
usedExp (ConstExp _ _)        = nEmpty
usedExp (AssignExp _ e1 e2 _) = nUnion (usedExp e1) (usedExp e2)
usedExp (Subscript e1 e2 _)   = nUnion (usedExp e1) (usedExp e2)
usedExp (FunCall e1 es _)     = nUnions $ map usedExp (e1:es)
usedExp (CompSel e _ _ _)     = usedExp e
usedExp (Unary _ e _)         = usedExp e
usedExp (Bin _ e1 e2 _)       = nUnion (usedExp e1) (usedExp e2)
usedExp (SizeOfExp e _)       = usedExp e
usedExp (SizeOfTy t _)        = usedType t
usedExp (Cast t e _)          = nUnion (usedType t) (usedExp e)
usedExp (Cond e1 me e3 _)     = nUnions $ (maybe nEmpty usedExp me)
                                        : map usedExp [e1,e3]

--------------------
--- declared*
--------------------

-- Note that for all of the declared* functions, we are interested only in
-- _externally visible_ declarations.  So, for example:
--
--  if (e) {var x = 3; return x} else {return 4}
--
-- declares x, but the outside world doesn't see it, so we don't record it.

declaredExternalDecln :: ExternalDecln -> Names
declaredExternalDecln (ExtFunDef (FunDef {decl})) =
  nInsertObject (funName decl) nEmpty
declaredExternalDecln (ExtDecln d) = declaredDecln d

declaredDecln :: Decln -> Names
declaredDecln (FunDecln fd _)   = nInsertObject (funName fd) nEmpty
declaredDecln (VarDecln vd _)   = nInsertObject (vdIdent vd) nEmpty
declaredDecln (TyDef ty nm _)   = nInsertObject nm $ declaredType ty
declaredDecln (StructDecln t _) = declaredType t
declaredDecln (UnionDecln t _)  = declaredType t
declaredDecln (EnumDecln t _)   = declaredType t

declaredType :: Type -> Names
declaredType (VoidType _)       = nEmpty
declaredType (Integral _ _)     = nEmpty
declaredType (BoolType _)       = nEmpty
declaredType (Floating _ _)     = nEmpty

-- these come up, for example, in    "struct foo {int x;} *bar;"
declaredType (PointerType _ t)  = declaredType t
declaredType (ArrayType _ t _)  = declaredType t
declaredType (Struct _ mn mfs)  = declaredStructUnion mn mfs
declaredType (Union _ mn mfs)   = declaredStructUnion mn mfs
declaredType (Enum _ mn _)      = (maybe id nInsertTag mn) nEmpty
declaredType (Func _ arg _ ret) =
  nUnions $ (declaredType ret) : map (declaredType . snd) arg
declaredType (TypeDef _ _)      = nEmpty

declaredStructUnion :: Maybe Id -> Maybe [(Maybe String,Type,Maybe Integer)] -> Names
declaredStructUnion _  Nothing = nEmpty
declaredStructUnion mn (Just flds) =
  (maybe id nInsertTag mn) $ nUnions $ map (\(_,t,_) -> declaredType t) flds



--------------------
-- HedgeTrimmer
--------------------

-- Tell me the filenames of stuff we're keeping and the C translation unit to trim.
trim :: [FilePath] -> TransUnit -> TransUnit
trim keeperFiles (TransUnit {exts}) =
  TransUnit . snd $ foldl' trimmer (nEmpty,[]) $ reverse exts
  where
    keeperFileNames :: [String]
    keeperFileNames = map takeFileName keeperFiles

    fromKeeper :: ExternalDecln -> Bool
    fromKeeper e =
      (takeFileName sourceName) `elem` keeperFileNames
      where
        SPos {sourceName} = locExternal e

    keepDecl :: Names -> ExternalDecln -> Bool
    keepDecl used d = (fromKeeper d)
                   || (not $ nNull $ nIntersection used (declaredExternalDecln d))
          
    trimmer :: (Names,[ExternalDecln]) -> ExternalDecln -> (Names,[ExternalDecln])
    trimmer (used,eds) ed = if keepDecl used ed then 
                                (nUnion used (usedExternalDecln ed),
                                 ed:eds)
                            else 
                                (used,eds)
{-
-----------------
--- Testing stuff

loc1,loc2 :: SPos
loc1 = SPos {sourceName = "file1", sourceLine = 0, sourceColumn = 0}
loc2 = SPos {sourceName = "file2", sourceLine = 0, sourceColumn = 0}

----  File1

dec11 = ExtDecln (
  TyDef (BoolType loc1)
        (Id "foo")
        loc1
  )

file1 = TransUnit { exts = [dec11] }

----  File2

dec21 = ExtDecln (VarDecln 
  (VDecln {vdIdent = Id "x",
           vdStorage = Nothing,
           vdInit = Nothing,
           vdType = TypeDef loc2 (Id "foo")})
  loc2)


file2 = TransUnit { exts = [dec21] }

files = TransUnit { exts = [dec11,dec21] }
-}
                            
