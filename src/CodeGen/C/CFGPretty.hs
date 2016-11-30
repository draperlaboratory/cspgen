{-# LANGUAGE RankNTypes #-}
{- |
   Module      :  CFGPretty
   Description :  Pretty Printing for the CFGs generated using ASTtoCFG
   Copyright   :  Draper Laboratories
   
   Author      :  Chinedu Okongwu
   
   This generates a string which should be suitable as input for the cspgen code generator
-}
module CodeGen.C.CFGPretty (ppCFG) where

import Compiler.Hoopl

import CodeGen.C.CFG
import CodeGen.C.Pretty
import CodeGen.C.CGMonad
import CodeGen.C.CFGPointsTo

import qualified Language.CSPM.Syntax as T

import Data.List (intersperse)


ppCFG :: [Proc PTFacts] -> String
ppCFG x = concat $ map printProc x

printProc :: Proc PTFacts -> String
printProc (Proc {procDecln=FInfo {ftid,fret},procArgs,procBody}) = 
       ppBaseType fret ++ " " ++ pprintId ftid ++ "("
    ++ (concat $ intersperse ", " $ 
          map (\(argnm,ty) -> ppBaseType ty ++ " " ++ emitId argnm) procArgs)
    ++ ")\n" ++ ppProcBody procBody ++ "\n\n" 


pprintId :: T.Id -> String 
pprintId (T.Id (x,_)) = show x 
pprintId (T.Fixed x)  = show x

-- GNil and GUnit constructors make graphs that are open at entry and exit.
-- No need to worry about pattern matching those because the type of procbody
-- is closed at both entry and exit
ppProcBody :: Graph (AInsn PTFacts) C C -> String
ppProcBody pbody = g pbody
  where g :: Graph (AInsn PTFacts) e x -> String
        g GNil = ""
        g (GUnit block) = b block
        g (GMany g_entry g_blocks g_exit) =
            open b g_entry ++ body g_blocks ++ open b g_exit

        body :: Body (AInsn PTFacts) -> String
        body blocks = concatMap b (mapElems blocks)

        b :: forall e x . Block (AInsn PTFacts) e x -> String
        b (BlockCO l b1)   = ppAInsn l ++ "\n" ++ b b1
        b (BlockCC l b1 n) = ppAInsn l ++ "\n" ++ b b1 ++ ppAInsn n ++ "\n"
        b (BlockOC   b1 n) =           b b1 ++ ppAInsn n ++ "\n"
        b (BNil)          = ""
        b (BMiddle n)     = ppAInsn n ++ "\n"
        b (BCat b1 b2)    = b b1   ++ b b2
        b (BSnoc b1 n)    = b b1   ++ ppAInsn n ++ "\n"
        b (BCons n b1)    = ppAInsn n ++ "\n" ++ b b1

ppAInsn :: AInsn PTFacts e x -> String
ppAInsn (AInsn i ptf) = ppInsn i ++ "    <" ++ ppPTFacts ptf ++ ">"

ppInsn :: Insn e x -> String
ppInsn (ILabel _ l) = "Label: " ++ show l ++ ";"
ppInsn (IExp e)     = emitExp e ++ ";"
ppInsn (IDecl d)    = emitDecln d
ppInsn (ICleanup i) = "<cleanup " ++ emitId i ++ ">"

ppInsn (IGoto _ ids l)  = "goto " ++ showIdsNice ids ++ " " ++ show l ++ ";"
ppInsn (ICond _ ids1 ids2 e l1 l2) = 
          "cond " ++ showIdsNice ids1 ++ " " ++ showIdsNice ids2 ++ " (" ++ emitExp e ++ ") "
       ++ show l1 ++ " " ++ show l2 ++ ";"
ppInsn (IReturn _ ids me) = "return " ++ showIdsNice ids 
                         ++ maybe "" (\e -> " " ++ emitExp e) me ++ ";"
ppInsn (ITailCall _ ids args) = "recursiveTailCall " ++ showIdsNice ids ++ " (" 
                             ++ concat (intersperse "," (map show args)) ++ ")"

open :: (a -> String) -> MaybeO z a -> String
open _ NothingO  = ""
open p (JustO n) = p n
