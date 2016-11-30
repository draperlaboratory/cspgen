module CodeGen.C.SimplifyLoop (sLoopTransUnit) where

{- |
   Module      :  CodeGen.C.SimplifyLoop
   Description :  C Simplifier - translate away most loops
   Copyright   :  Draper Laboratories
   
   Author      :  Chris Casinghino
   

   This module implements a simple translation on our C AST.  All loops are
   translated into loops of the form "for (;;) {...}".

-}

import CodeGen.C.Syntax

-- These functions translate all loops into loops of the form "for (;;) {...}".
--
-- The translation goes as follows:
--
-- "While" loops are easiest:
--
--     while(e) {s};  
--  ~> for (;;) {if (e) {s} else {break}}
--
-- "Do while" loops are a little trickier.  Note that the statement "s" here
-- goes into its own block, to make sure any declarations in it aren't in
-- scope in e.
--
--     do {s} while (e);
--  ~> for (;;) { {s}; if (e) { <no statement> } else {break}}
--
-- "For" loops are:
--    
--     for (s1;e;s2) { s }
--  ~> s1; for(;;) {if (e) {break;} else {{s};s2}}
--
-- Again we make sure "s" is its own block, since definition in it aren't in
-- scope in s2.

likeTrue :: Exp -> Bool
likeTrue (ConstExp (IntConst i) _) = i /= 0
likeTrue _ = False

-- Makes a "for (;;) { }}
simpleFor :: SPos -> Statement -> Statement
simpleFor sp s = For (Right Nothing) Nothing Nothing s sp

sLoopStmt :: Statement -> Statement
sLoopStmt (Compound eds sp) = Compound (map sLoopDeclStmt eds) sp
  where
    sLoopDeclStmt :: Either Decln Statement -> Either Decln Statement
    sLoopDeclStmt (Left d)  = Left d
    sLoopDeclStmt (Right s) = Right $ sLoopStmt s
sLoopStmt (IfStm e s1 s2 sp)  = IfStm e (sLoopStmt s1) (fmap sLoopStmt s2) sp
sLoopStmt (Switch e s sp)     = Switch e (sLoopStmt s) sp
sLoopStmt st@(ExpStm _ _)     = st
sLoopStmt (Case e s sp)       = Case e (sLoopStmt s) sp
sLoopStmt (Default s sp)      = Default (sLoopStmt s) sp
sLoopStmt st@(Continue _)     = st
sLoopStmt st@(Goto _ _)       = st
sLoopStmt st@(Asm _)          = st
-- While loops, with a special case for while(1)
sLoopStmt (While e s sp) | likeTrue e  = simpleFor sp $ sLoopStmt s
sLoopStmt (While e s sp)               = simpleFor sp (IfStm e s' (Just $ Break sp) sp)
  where
    s' = sLoopStmt s

-- Do-while loops, with a special case for while(1)
sLoopStmt (DoWhile s e sp) | likeTrue e = simpleFor sp $ sLoopStmt s
sLoopStmt (DoWhile s e sp)              =
  simpleFor sp $
      Compound [Right $ Compound [Right s'] sp,
                Right $ IfStm e (ExpStm Nothing sp) (Just $ Break sp) sp] sp
  where
    s' = sLoopStmt s

-- For loops, with some special cases to more cleanly handle the possibility that any of
-- s1, e and s2 are missing.
sLoopStmt (For de1 me2 me3 s sp) =
  case de1 of
    Right Nothing   -> loop
    Right (Just e1) -> Compound [Right (ExpStm (Just e1) sp), Right loop] sp
    Left  d         -> Compound ((map Left d) ++ [Right loop]) sp
  where
    s'  = sLoopStmt s
          

    loop = simpleFor sp (case me2 of
                           Nothing -> body
                           Just e2 -> IfStm e2 body (Just $ Break sp) sp)

    body = case me3 of
             Nothing -> s'
             Just e3 ->
                 Compound [Right $ Compound [Right s'] sp,
                           Right $ ExpStm (Just e3) sp] sp

sLoopStmt (Labelled nm s sp) = Labelled nm (sLoopStmt s) sp
sLoopStmt st@(Return _ _)    = st
sLoopStmt st@(Break _)       = st


sLoopFunDef :: FunDef -> FunDef
sLoopFunDef fd = fd {funBody = sLoopStmt (funBody fd)}

sLoopExternalDecln :: ExternalDecln -> ExternalDecln
sLoopExternalDecln (ExtFunDef fdef) = ExtFunDef (sLoopFunDef fdef)
sLoopExternalDecln ed@(ExtDecln _)  = ed

sLoopTransUnit :: TransUnit -> TransUnit
sLoopTransUnit (TransUnit {exts}) = 
    TransUnit {exts=map sLoopExternalDecln exts}
