{-# LANGUAGE RankNTypes #-}
{- |

  Module      :  CodeGen.C.ReduceLabels
  Description :  Remove redudant labels from the CFG
  Copyright   :  Draper Laboratories
  
  Author      :  Chinedu Okongwu

  This module eliminates certain unnecessary blocks from the control flow graph.
  In particular, because of the way the graph is generated, it includes many
  blocks of the form:

  Label1:
    goto Label2

  This block can be eliminated if we change any jump to Label1 with a jump to
  Label2, which is what this module does.
-}

module CodeGen.C.CFGEmptyBlocks (eliminateEmptyBlocks) where

-- We use Hoopl's graph representation
import Compiler.Hoopl

-- source and target
import qualified CodeGen.C.CFG    as T

import CodeGen.C.CFGPointsTo

import qualified Data.Map as M
import Data.Maybe (fromMaybe)


-- This function removes any potentially redundant label blocks and label 
-- from the list of Proc PTFacts objects.
--
-- The general way this works is by checking each instruction in each block to
-- see if it contains a conditional jump to instruction or a GoTo
-- instruction. If so, the forward referenced label is checked to see if it
-- refers to a block with an empty body and GoTo instruction as its exit. If
-- this is also the case, the original forward referencing label is replaced
-- with the destination label of this GoTo instruction. In order to maintain the
-- integrity of the Proc PTFact, the entry label is also checked and potentially
-- modified to ensure that it does not also refer to a redundant block.
eliminateEmptyBlocks :: T.Proc PTFacts -> T.Proc PTFacts
eliminateEmptyBlocks p@(T.Proc {T.procBody=body,T.procEntry=entry}) = 
    p {T.procBody=newBody, T.procEntry=newEntry}
  where
    newEntry :: Label
    newBody :: Graph (T.AInsn PTFacts) C C
    (newEntry, newBody) = cleanProc entry body

-- Pulls apart the Proc into a list of labelled blocks, cleans that up, and
-- packages the result back up into a Proc.
cleanProc :: Label -> Graph (T.AInsn PTFacts) C C
          -> (Label,Graph (T.AInsn PTFacts) C C)
cleanProc l (GMany NothingO body NothingO) = 
  (getLabel l realLabels, GMany NothingO cleanedBody NothingO)
  where 
    realLabels :: M.Map Label Label
    realLabels = buildLabelMap body
    
    relabelledBody :: Body (T.AInsn PTFacts)
    relabelledBody = cleanBody realLabels body

    cleanedBody :: Body (T.AInsn PTFacts)
    cleanedBody = shrinkBody realLabels relabelledBody


-- Replaces jump target labels in each block in the body according to the
-- supplied map.
cleanBody :: M.Map Label Label
          -> Body (T.AInsn PTFacts)
          -> Body (T.AInsn PTFacts)
cleanBody labels body = mapMap (cleanBlock labels) body

-- Replaces jump target labels in each instruction in the block according to the
-- supplied map.  We only need to change the exit node, since it's the only one
-- that can jump.
cleanBlock :: M.Map Label Label
           -> Block (T.AInsn PTFacts) C C
           -> Block (T.AInsn PTFacts) C C 
cleanBlock labels block = blockJoin bEntry bBody (cleanAInsn labels bExit)
  where
    bEntry :: T.AInsn PTFacts C O
    bBody :: Block (T.AInsn PTFacts) O O
    bExit :: T.AInsn PTFacts O C
    (bEntry,bBody,bExit) = blockSplit block

-- Replaces any jump target in the instruction according to the supplied map.
cleanAInsn :: M.Map Label Label 
           -> T.AInsn PTFacts O C
           -> T.AInsn PTFacts O C
cleanAInsn labels (T.AInsn i ptf) = T.AInsn (cleanInsn i) ptf
  where
    cleanInsn :: T.Insn O C -> T.Insn O C
    cleanInsn (T.IGoto s ids l) = T.IGoto s ids (getLabel l labels)
    cleanInsn (T.ICond s ids1 ids2 e l1 l2) = 
       T.ICond s ids1 ids2 e (getLabel l1 labels) (getLabel l2 labels)
    cleanInsn p@(T.IReturn _ _ _) = p
    cleanInsn p@(T.ITailCall _ _ _) = p

-- Creates a map from each label to the label we'd like to replace it with,
-- possibly itself.  For example, for the blocks:
--
--   L1:
--     Goto L2;
--   L2:
--     Goto L3;
--   L3:
--     <do something interesting>
--     return;
--
-- We create the map <(L1,L3),(L2,L3),(L3,L3)>, since we're going to remove the
-- L1 and L2 blocks from the program and anybody who used to jump to those
-- labels should now jump to L3.
buildLabelMap :: LabelMap (Block (T.AInsn PTFacts) C C) -> M.Map Label Label
buildLabelMap block = M.fromList $ map (\l -> (l, chaseLabel l block)) 
                                       (mapKeys block)

-- Takes a label l and find the "real" corresponding label (i.e., the label of
-- the first block that (a) will be jumped to after jumping to l and (b)
-- actually does something).
chaseLabel :: Label -> LabelMap (Block (T.AInsn PTFacts) C C) -> Label 
chaseLabel l lbs = chase l
  where 
    -- This does the main work of chaseLabel.  The only sublety is that we must
    -- check if "isEmptyGoto" returns the original label l, so that we don't
    -- enter an infinite loop in the case of divergent C code.  In this corner
    -- case, we leave the whole loop alone - it would be cleaner (but more
    -- complicated) to reduce it to a single label.
    chase :: Label -> Label
    chase l' =
      case mapLookup l' lbs >>= isEmptyGoto of
        Nothing              -> l'
        Just l'' | l'' == l  -> l
        Just l'' | otherwise -> chase l''

-- Checks to see if the input block has an empty body and a goto instruction as
-- an exit. If so, the jump to label is returned.
isEmptyGoto :: Block (T.AInsn PTFacts) C C -> Maybe Label
isEmptyGoto block = if isEmptyBlock blockBody then gotoLabel else Nothing
  where 
    blockBody :: Block (T.AInsn PTFacts) O O
    blockExit :: T.AInsn PTFacts O C
    (_, blockBody, blockExit) = blockSplit block

    gotoLabel :: Maybe Label
    gotoLabel =
      case blockExit of
        T.AInsn (T.IGoto _ _ l) _  -> Just l
        _                          -> Nothing

-- Checks the given map for a label that has the input label as its key. 
-- It then returns either the input label or the found label value.
getLabel :: Label -> M.Map Label Label ->  Label
getLabel l m = fromMaybe l (M.lookup l m)


-- Eliminates empty blocks from the body.  Note that not _every_ empty block can
-- be removed because we leave in empty blocks that are part of an infinite loop
-- to avoid changing the semantics.  So, instead, we remove any blocks whose
-- label is no longer used (according to the label map).
shrinkBody :: M.Map Label Label
           -> Body (T.AInsn PTFacts)
           -> Body (T.AInsn PTFacts)
shrinkBody labels body = mapFilter shrinkCheck body
  where
    shrinkCheck :: Block (T.AInsn PTFacts) C C -> Bool
    shrinkCheck b = let label = entryLabel b in 
                    label == getLabel label labels

