module CodeGen.C.SimplifyLValues (sLValTransUnit) where

{- |
   Module      :  CodeGen.C.LValues
   Description :  C Simplifier - clean up lvalues
   Copyright   :  Draper Laboratories
   
   Author      :  Chris Casinghino
   
   This module implements a simple translation on our C AST.  
   1) Expression of the form    e -> l   are translated to (*e).l
   2) Expressions of the form    *&e     are translated to e

-}

import CodeGen.C.Syntax

sLValExp :: Exp -> Exp
sLValExp (CommaExp es sp) = CommaExp (map sLValExp es) sp
sLValExp e@(IdExp _ _)    = e
sLValExp e@(ConstExp _ _) = e
sLValExp (AssignExp aop e1 e2 sp) = AssignExp aop (sLValExp e1)
                                              (sLValExp e2) sp
sLValExp (Subscript e1 e2 sp)  = Subscript (sLValExp e1) (sLValExp e2) sp
sLValExp (FunCall e es sp)     = FunCall (sLValExp e) (map sLValExp es) sp
sLValExp (CompSel e sop nm sp) = 
  case sop of
    IndirSel -> CompSel (sLValExp $ Unary Indirection e sp) DirSel nm sp
    DirSel -> CompSel (sLValExp e) sop nm sp

sLValExp (Unary uop e sp)      =
  case uop of
    Indirection ->
      case e of
        Unary Address e' _ -> sLValExp e'
        _ -> normalCase
    _ -> normalCase
  where
    normalCase = Unary uop (sLValExp e) sp
sLValExp (Bin bop e1 e2 sp)    = Bin bop (sLValExp e1) (sLValExp e2) sp
sLValExp (SizeOfExp e1 sp)     = SizeOfExp (sLValExp e1) sp
sLValExp e@(SizeOfTy _ _)      = e
sLValExp (Cast t e sp)         = Cast t (sLValExp e) sp
sLValExp (Cond e1 me2 e3 sp)   = Cond (sLValExp e1) (fmap sLValExp me2)
                                      (sLValExp e3) sp

sLValInit :: Initializer -> Initializer
sLValInit (SimpleInitializer e) = SimpleInitializer (sLValExp e)
sLValInit (ListInitializer is) = 
  ListInitializer $ map (\(ds,i) -> (map sLValDesig ds, sLValInit i)) is
  where
    sLValDesig :: InitDesignator -> InitDesignator
    sLValDesig (ArrDesig e sp)     = ArrDesig (sLValExp e) sp
    sLValDesig d@(MemberDesig _ _) = d

sLValStmt :: Statement -> Statement
sLValStmt (Compound eds sp) = Compound (map sLValDeclStmt eds) sp
  where
    sLValDeclStmt :: Either Decln Statement -> Either Decln Statement
    sLValDeclStmt (Left d)  = Left $ sLValDecln d
    sLValDeclStmt (Right s) = Right $ sLValStmt s
sLValStmt (IfStm e s1 s2 sp)     = IfStm (sLValExp e) (sLValStmt s1)
                                         (fmap sLValStmt s2) sp
sLValStmt (Switch e s sp)        = Switch (sLValExp e) (sLValStmt s) sp
sLValStmt (ExpStm e sp)          = ExpStm (fmap sLValExp e) sp
sLValStmt (Case e s sp)          = Case (sLValExp e) (sLValStmt s) sp
sLValStmt (Default s sp)         = Default (sLValStmt s) sp
sLValStmt st@(Continue _)        = st
sLValStmt st@(Goto _ _)          = st
sLValStmt st@(Asm _)             = st
sLValStmt (While e s sp)         = While (sLValExp e) (sLValStmt s) sp
sLValStmt (DoWhile s e sp)       = DoWhile (sLValStmt s) (sLValExp e) sp
sLValStmt (For de1 me2 me3 s sp) = For de1' me2' me3' s' sp
  where
    de1' = case de1 of
             Left ds  -> Left $ map sLValDecln ds
             Right me -> Right $ fmap sLValExp me
                         
    me2' = fmap sLValExp me2
    me3' = fmap sLValExp me3
    s'   = sLValStmt s
sLValStmt (Labelled nm s sp) = Labelled nm (sLValStmt s) sp
sLValStmt (Return e sp)      = Return (fmap sLValExp e) sp
sLValStmt st@(Break _)       = st

sLValDecln :: Decln -> Decln
sLValDecln (VarDecln vd sp) = VarDecln (vd {vdInit = fmap sLValInit $ vdInit vd})
                                       sp
sLValDecln d@(FunDecln _ _)    = d
sLValDecln d@(TyDef _ _ _)     = d
sLValDecln d@(StructDecln _ _) = d
sLValDecln d@(UnionDecln _ _)  = d
sLValDecln d@(EnumDecln _ _)   = d

sLValFunDef :: FunDef -> FunDef
sLValFunDef fd = fd {funBody = sLValStmt (funBody fd)}

sLValExternalDecln :: ExternalDecln -> ExternalDecln
sLValExternalDecln (ExtFunDef fdef) = ExtFunDef (sLValFunDef fdef)
sLValExternalDecln (ExtDecln dcl)   = ExtDecln (sLValDecln dcl)

sLValTransUnit :: TransUnit -> TransUnit
sLValTransUnit (TransUnit {exts}) = 
    TransUnit {exts=map sLValExternalDecln exts}
