module CodeGen.C.SimplifyReferences (sRefTransUnit) where

{- |
   Module      :  CodeGen.C.SimplifyReferences
   Description :  C Simplifier - translate away most loops
   Copyright   :  Draper Laboratories
   
   Author      :  Chinedu Okongwu
   
   This module implements a transformation over the C AST.  In some generated C
   code, we are seeing the following idiom: a local variable is declared, then a a
   second variable is defined to be the address of the first variable, and then the
   first variable is never used again.  This eliminates the second variable.
-}


import CodeGen.C.Syntax
--import Data.Maybe

-- The idiom we are simplifying looks like this:
--
--    ...
--    int x = 0;
--    int* x_ref = &x;
--    ...
--    int y = 3;
--    int* y_ref = &y;
--    ...
--
-- x_ref is never modified, we delete its declaration and replace it
-- by &x everywhere.

sRefTransUnit :: TransUnit -> TransUnit
sRefTransUnit x =  TransUnit (map sRefExtDec (exts x))

sRefExtDec :: ExternalDecln -> ExternalDecln
sRefExtDec (ExtFunDef x)  = ExtFunDef (sRefFunDef x)
sRefExtDec e@(ExtDecln _) = e

--checks a function for instances of the idiom
sRefFunDef :: FunDef -> FunDef
sRefFunDef fd@(FunDef {funBody}) = fd {funBody = sRefStm funBody}

--checks a statement for instance of the idiom and simplifies it
sRefStm :: Statement -> Statement
sRefStm (Compound eds sp)       = Compound (sRefCompound eds) sp
sRefStm (ExpStm e sp)           = ExpStm e sp
sRefStm (While e s sp)          = While e (sRefStm s) sp
sRefStm (IfStm e s (Just ms) sp)= IfStm e (sRefStm s) (Just $ sRefStm ms) sp
sRefStm (IfStm e s Nothing sp)  = IfStm e (sRefStm s) Nothing sp
sRefStm (Switch e s sp)         = Switch e (sRefStm s) sp
sRefStm (Case e s sp)           = Case e (sRefStm s) sp
sRefStm (Default s sp)          = Default (sRefStm s) sp
sRefStm (DoWhile s e sp)        = DoWhile (sRefStm s) e sp
sRefStm (For ede e ce s sp)     = For ede e ce (sRefStm s) sp
sRefStm (Labelled i s sp)       = Labelled i (sRefStm s) sp
sRefStm (Return e sp)           = Return e sp
sRefStm (Break sp)              = Break sp
sRefStm (Continue sp)           = Continue sp
sRefStm (Goto i sp)             = Goto i sp
sRefStm (Asm sp)                = Asm sp

--implementation of replacement algorithm with not modified check
sRefCompound :: [Either Decln Statement] -> [Either Decln Statement]
sRefCompound (x1@(Left (VarDecln x _)):x2@(Left (VarDecln y spy)):ys) = 
  if typeCheck && referenceCheck && notModifiedCheck
    then x1:sRefCompound (findRef (vdIdent x) (vdIdent y) ys)
    else x1:sRefCompound (x2:ys)
  where
    typeCheck, referenceCheck, notModifiedCheck :: Bool
    typeCheck = (vdType y) == (PointerType spy (vdType x))

    referenceCheck =
      case vdInit y of
        Just (SimpleInitializer (Unary Address (IdExp x' _) _)) ->
          (vdIdent x) == x'
        _ -> False

    notModifiedCheck =  all (nmcCompound (vdIdent y)) ys

sRefCompound (Left d:xs)  = Left d:sRefCompound xs
sRefCompound (Right s:xs) = Right (sRefStm s):sRefCompound xs
sRefCompound []     = []

--Performs the not modified check to ensure that the reference variable being
--replaced is not modified at a later point in the code execution.
nmcCompound :: Id -> Either Decln Statement -> Bool 
nmcCompound _ (Left _)                         = True
nmcCompound i (Right (Compound eds _))         = all (nmcCompound i) eds 
nmcCompound i (Right (ExpStm me _))            = 
  case me of
    Just e  -> nmcExp i e
    Nothing -> True
nmcCompound i (Right (IfStm e st (Just mst) _))= 
  (nmcExp i e) && (nmcCompound i $ Right st) && (nmcCompound i $ Right mst)
nmcCompound i (Right (IfStm e st Nothing _))   = 
  (nmcExp i e) && (nmcCompound i $ Right st)
nmcCompound i (Right (Switch e st _))          =
  (nmcExp i e) && (nmcCompound i $ Right st)
nmcCompound i (Right (Case e st _))            =
  (nmcExp i e) && (nmcCompound i $ Right st)
nmcCompound i (Right (Default st _))           = nmcCompound i $ Right st
nmcCompound i (Right (While e st _))           =
  (nmcExp i e) && (nmcCompound i $ Right st)
nmcCompound i (Right (DoWhile st e _))         =
  (nmcExp i e) && (nmcCompound i $ Right st)
nmcCompound i (Right (For ede me1 me2 st _))   = 
  (nmcExp' i me1) && (nmcExp' i me2) && (nmcEde i ede) && 
  (nmcCompound i $ Right st)
  where
    nmcExp' _ me = 
      case me of 
        Just e -> nmcExp i e
        Nothing -> True

    nmcEde _ edme =
      case edme of 
        Right (Just e) -> nmcExp i e
        Right Nothing  -> True
        Left   _       -> True 
nmcCompound i (Right (Labelled _ st _))        = (nmcCompound i $ Right st)
nmcCompound i (Right (Return me _))            = 
  case me of 
    Just e -> nmcExp i e
    Nothing -> True
nmcCompound _ (Right (Break _))                = True
nmcCompound _ (Right (Continue _))             = True
nmcCompound _ (Right (Goto _ _))               = True
nmcCompound _ (Right (Asm _))                  = True

--Performs the Not Modified Check on experessions
nmcExp :: Id -> Exp -> Bool
nmcExp i (CommaExp es _)       = all (nmcExp i) es 
nmcExp _ (IdExp _ _)           = True
nmcExp _ (ConstExp _ _)        = True
nmcExp i (AssignExp _ e1 e2 _) = 
  case e1 of 
    (IdExp x _) -> (x /= i) && nmcExp i e2
    _           -> (nmcExp i e1) && (nmcExp i e2)
nmcExp i (Subscript e1 e2 _)   = (nmcExp i e1) && (nmcExp i e2)
nmcExp i (FunCall e es _)      = (nmcExp i e) && (all (nmcExp i) es)
nmcExp i (CompSel e _ _ _)     = nmcExp i e
nmcExp i (Unary Address (IdExp i' _) _) = not (i == i')
nmcExp i (Unary _ e _)         = nmcExp i e
nmcExp i (Bin _ e1 e2 _)       = (nmcExp i e1) && (nmcExp i e2)
nmcExp i (SizeOfExp e _)       = nmcExp i e
nmcExp _ (SizeOfTy _ _)        = True
nmcExp _ (Cast _ _ _)          = True
nmcExp i (Cond e1 me e2 _)     = 
  case me of
    Just e  -> (nmcExp i e1) && (nmcExp i e) && (nmcExp i e2)
    Nothing -> (nmcExp i e1) && (nmcExp i e2)

--finds and replaces instances of the reference variable 
findRef :: Id -> Id -> [Either Decln Statement] 
        -> [Either Decln Statement]
findRef varx vary zs = map findRef' zs
  where
    findRef' :: Either Decln Statement -> Either Decln Statement
    findRef' (Left z)  = Left (fRefDec varx vary z)
    findRef' (Right z) = Right (fRefStm varx vary z)

--fixes declarations with instance of pointer to var 
--replacing them with address of actual var
fRefDec :: Id -> Id -> Decln -> Decln
fRefDec  _    _   (FunDecln z spz)    = FunDecln z spz
fRefDec varx vary (VarDecln vd spz)   = 
  VarDecln (vd {vdInit = fmap fRefInitializer (vdInit vd)}) spz
  where 
    fRefInitializer :: Initializer -> Initializer
    fRefInitializer (SimpleInitializer e) = 
      SimpleInitializer $ fRefExp varx vary e
    fRefInitializer (ListInitializer linits) =
      ListInitializer $
         map (\(dg,izr) -> (dg,fRefInitializer izr)) linits

fRefDec varx vary (TyDef t z spz)     = TyDef (fRefType varx vary t) z spz
fRefDec varx vary (StructDecln t spz) = StructDecln (fRefType varx vary t) spz
fRefDec varx vary (UnionDecln t spz)  = UnionDecln (fRefType varx vary t) spz
fRefDec varx vary (EnumDecln t spz)   = EnumDecln (fRefType varx vary t) spz

--fixes instances in statements
fRefStm :: Id -> Id -> Statement -> Statement
fRefStm varx vary (Compound zs spz)                       = 
  Compound (foldr f' [] zs) spz
  where 
    f' :: Either Decln Statement -> [Either Decln Statement]
       -> [Either Decln Statement]
    f' (Left z) acc  = Left (fRefDec varx vary z)  : acc
    f' (Right z) acc = Right (fRefStm varx vary z) : acc
fRefStm varx vary (ExpStm (Just e) spz)                   = 
  ExpStm (Just $ fRefExp varx vary e) spz
fRefStm   _   _ s@(ExpStm Nothing _)                      = s
fRefStm varx vary (IfStm e st mst spz)                    =
  IfStm (fRefExp varx vary e) (fRefStm varx vary st)
        (fmap (fRefStm varx vary) mst) spz
fRefStm varx vary (Switch e st spz)                       =
  Switch (fRefExp varx vary e) (fRefStm varx vary st) spz
fRefStm varx vary (Case e st spz)                         =
  Case (fRefExp varx vary e) (fRefStm varx vary st) spz
fRefStm varx vary (Default st spz)                        =
  Default (fRefStm varx vary st) spz
fRefStm varx vary (While e st spz)                        =
  While (fRefExp varx vary e) (fRefStm varx vary st) spz
fRefStm varx vary (DoWhile st e spz)                      =
  DoWhile (fRefStm varx vary st) (fRefExp varx vary e) spz
fRefStm varx vary (For eds me1 me2 st spz)                =
  For eds' me1' me2' (fRefStm varx vary st) spz
  where
    eds' :: Either [Decln] (Maybe Exp)
    eds' = case eds of
             Left ds  -> Left $ map (fRefDec varx vary) ds
             Right me -> Right $ fmap (fRefExp varx vary) me

    me1', me2' :: Maybe Exp
    me1' = fmap (fRefExp varx vary) me1
    me2' = fmap (fRefExp varx vary) me2
fRefStm varx vary (Labelled i st spz)                     =
  Labelled i (fRefStm varx vary st) spz
fRefStm varx vary (Return (Just e) spz)                   =
  Return (Just $ fRefExp varx vary e) spz
fRefStm _ _    s@(Return Nothing _)                       = s
fRefStm _ _    s@(Break _)                                = s
fRefStm _ _    s@(Continue _)                             = s
fRefStm _ _    s@(Goto _ _)                               = s
fRefStm _ _    s@(Asm _)                                  = s

--fixes instances in expressions
fRefExp :: Id -> Id -> Exp -> Exp
fRefExp varx vary (CommaExp z spz)        = 
  CommaExp (map (fRefExp varx vary) z) spz
fRefExp varx vary (IdExp z spz)           = 
  if (z == vary) then Unary Address (IdExp varx spz) spz else IdExp z spz
fRefExp  _  _     (ConstExp c spz)        = ConstExp c spz
fRefExp varx vary (AssignExp aop a b spz) =
  AssignExp aop (fRefExp varx vary a) (fRefExp varx vary b) spz
fRefExp varx vary (Subscript a b spz)     = 
  Subscript (fRefExp varx vary a) (fRefExp varx vary b) spz
fRefExp varx vary (FunCall a b spz)       = 
  FunCall (fRefExp varx vary a) (map (fRefExp varx vary) b) spz
fRefExp varx vary (CompSel a sop z spz)   =
  CompSel (fRefExp varx vary a) sop z spz 
fRefExp varx vary (Unary uop a spz)       = 
  Unary uop (fRefExp varx vary a) spz
fRefExp varx vary (Bin bop a b spz)       = 
  Bin bop (fRefExp varx vary a) (fRefExp varx vary b) spz
fRefExp varx vary (SizeOfExp a spz)       = 
  SizeOfExp (fRefExp varx vary a) spz
fRefExp varx vary (SizeOfTy ty spz)       = 
  SizeOfTy (fRefType varx vary ty) spz
fRefExp varx vary (Cast ty a spz)         =
  Cast (fRefType varx vary ty) (fRefExp varx vary a) spz
fRefExp varx vary (Cond a (Just b) c spz) =
  Cond (fRefExp varx vary a) (Just $ fRefExp varx vary b) (fRefExp varx vary c) spz
fRefExp varx vary (Cond a Nothing b spz)  =
  Cond (fRefExp varx vary a) Nothing (fRefExp varx vary b) spz

fRefType :: Id -> Id -> Type -> Type
fRefType   _   _  s@(VoidType _)               = s
fRefType   _   _  s@(Integral _ _)             = s
fRefType   _   _  s@(BoolType _)               = s
fRefType   _   _  s@(Floating _ _)             = s
fRefType varx vary (PointerType spz t)         = 
  PointerType spz (fRefType varx vary t)
fRefType varx vary (ArrayType spz t msz)       = 
  ArrayType spz (fRefType varx vary t) msz
fRefType varx vary (Struct spz nm (Just xs))   = 
  Struct spz nm (Just $ map f' xs)
  where 
    f' :: (Maybe String, Type, Maybe Integer) -> (Maybe String, Type, Maybe Integer)
    f' (x, y, z) = (x, fRefType varx vary y, z)
fRefType   _   _ s@(Struct _ _ Nothing)        = s
fRefType varx vary (Union spz a (Just xs))     = 
  Union spz a (Just $ map f' xs)
  where
    f' :: (Maybe String, Type, Maybe Integer) -> (Maybe String, Type, Maybe Integer)
    f' (x, y, z) = (x, (fRefType varx vary y), z)
fRefType  _   _  s@(Union _ _ Nothing)         = s
fRefType varx vary (Enum spz a (Just xs))      =
  Enum spz a (Just $ map f' xs)
  where 
    f' :: (Id, Maybe Exp) -> (Id, Maybe Exp)
    f' (x, Just y) = (x, Just (fRefExp varx vary y))
    f' (x, Nothing)= (x, Nothing)
fRefType  _  _ s@(Enum _ _ Nothing )           = s
fRefType varx vary (Func spz xs b bt)          =
  Func spz (map f' xs) b (fRefType varx vary bt)
  where 
    f' :: (Maybe Id,Type) -> (Maybe Id,Type)
    f' (x, t) = (x, (fRefType varx vary t))
fRefType   _   _   (TypeDef spz a)             = 
  TypeDef spz a
