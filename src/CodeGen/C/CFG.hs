{-# LANGUAGE GADTs #-}

module CodeGen.C.CFG where


{- |

  Module      :  CodeGen.C.CFG
  Description :  Control-flow graph for a C-like IR
  Copyright   :  Draper Laboratories
  
  Author      :  Chris Casinghino
-}

import Compiler.Hoopl

import CodeGen.C.Syntax
import CodeGen.C.Pretty (emitId,emitExp,emitDecln)
import CodeGen.C.CGMonad

import qualified Language.CSPM.Syntax as T

import Data.List (intersperse,intercalate)
import qualified Data.Map as M

-- We're cheating a bit here in the case of IExp and function calls.
--
-- In C, function calls are a type of expressions, which we've said
-- are "open on exit" here.  But function calls are a non-local
-- control transfer, and thus are really "closed on exit".
--
-- I think that since I'm only interested intraprocedural analysis for
-- now I can basically get away with this.  We're basically modelling
-- a function call as a black box that does some stuff and then comes
-- back to the call site.  That's not strictly true, but only in the
-- case where a function never returns, which shouldn't mess up any of
-- our analyses.
data Insn e x where
  ILabel    :: SPos -> Label                 -> Insn C O

  IExp      :: Exp                           -> Insn O O
  IDecl     :: Decln                         -> Insn O O
  ICleanup  :: Id                            -> Insn O O
                 
  -- The exit nodes all take an extra [Id] parameter, which indicates a bunch of
  -- IDs that need to be cleaned up just before this control-flow transfer (but,
  -- crucially, after evaluating any expressions embedded in the exit
  -- instruction, which is why we don't just add ICleanup nodes).  ICond takes
  -- two lists of IDs because the ids that need to be cleaned up may be
  -- different by branch.
  --
  -- XXX It's quite possible we could get rid of ICleanup all-together and just
  -- do cleanup before control-flow transfers without any hit to performance.
  -- This would simplify the CFG structure a bit, but I think it would make it
  -- harder to implement the liveness analysis with Hoopl.
  IGoto     :: SPos -> [Id] -> Label                 -> Insn O C
  ICond     :: SPos -> [Id] -> [Id] -> Exp -> Label -> Label -> Insn O C
  IReturn   :: SPos -> [Id] -> Maybe Exp             -> Insn O C
               
  -- Though we don't model most function calls as actual control-flow transfer,
  -- it's convenient to have recursive tail calls as a special case because of
  -- the way loop detection works in FDR.
  ITailCall :: SPos -> [Id] -> [Exp]                 -> Insn O C

instance NonLocal Insn where
    entryLabel (ILabel _ l) = l

    successors (IGoto _ _ l)         = [l]
    successors (ICond _ _ _ _ l1 l2) = [l1,l2]
    successors (IReturn _ _ _)       = []
    successors (ITailCall _ _ _)     = []

instance Show (Insn e x) where
  show (ILabel _ l) = "Label: " ++ show l ++ ";"

  show (IExp e)     = emitExp e ++ ";"
  show (IDecl d)    = emitDecln d
  show (ICleanup i) = "<cleanup " ++ emitId i ++ ">"

  show (IGoto _ ids l)  = "goto " ++ showIdsNice ids ++ " " ++ show l ++ ";"
  show (ICond _ ids1 ids2 e l1 l2) = 
          "cond " ++ showIdsNice ids1 ++ " " ++ showIdsNice ids2 ++ " (" ++ show e ++ ") "
       ++ show l1 ++ " " ++ show l2 ++ ";"
  show (IReturn _ ids me) = "return " ++ showIdsNice ids 
                         ++ maybe "" (\e -> " " ++ show e) me ++ ";"
  show (ITailCall _ ids args) = "recursiveTailCall " ++ showIdsNice ids ++ " (" 
                             ++ concat (intersperse "," (map show args)) ++ ")"

-- We allow instructions in the graph to be annotated.  Typically, we will chose
-- annotations that result from dataflow analysis to improve the code generation.
data AInsn a e x = AInsn (Insn e x) a

instance NonLocal (AInsn a) where
    entryLabel (AInsn i _) = entryLabel i

    successors (AInsn i _) = successors i

instance Show a => Show (AInsn a e x) where
  show (AInsn i a) =
    show i ++ "    <" ++ show a ++ ">"

getInsn :: AInsn a e x -> Insn e x
getInsn (AInsn i _) = i

getAnnot :: AInsn a e x -> a
getAnnot (AInsn _ a) = a



data Proc a = 
    Proc {procDecln :: FInfo,
          procArgs  :: [(Id,BaseType)],
          procPos   :: SPos,
          
          procEntry :: Label,
          procBody  :: Graph (AInsn a) C C,

          procLocations :: M.Map Label T.Id
         }

failProc :: Proc a -> String -> CG b
failProc p msg = 
  fail $ "Error in translation: " ++ msg ++ ", in function "
      ++ (T.namePart $ ftid $ procDecln p) ++ " at " ++ show (procPos p)

instance Show a => Show (Proc a) where
  show (Proc {procDecln=FInfo {ftid,fret},procArgs,procBody}) = 
       show fret ++ " " ++ show ftid ++ "("
    ++ (concat $ intersperse ", " $ 
          map (\(argnm,ty) -> show ty ++ " " ++ show argnm) procArgs)
    ++ ")\n" ++ showGraph show procBody ++ "\n\n"

-- XXX This is probably reallllly inefficient, but I couldn't find a better way to
-- do it with what's available in the Hoopl library.
mapProc :: (Block (AInsn a) C C -> Block (AInsn b) C C)
        -> Proc a -> Proc b
mapProc f p@(Proc {procBody,procEntry}) = p {procBody = body'}
  where
    blocks = case procBody of
               GMany NothingO body NothingO ->
                   postorder_dfs_from body procEntry
    
    body' = bodyGraph $ mapFromList $ map (\b -> (entryLabel b,f b)) blocks

showIdsNice :: [Id] -> String
showIdsNice ids = "[" ++ (intercalate "," $ map emitId ids) ++ "]"
