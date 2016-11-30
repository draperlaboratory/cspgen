{- |

   Module      :  CodeGen.LLVM.Analysis
   Description :  Analysis of LLVM IR
   
   Author      :  Chris Casinghino
   
   This module performs various analyses on LLVM IR to supply information needed
   by the translation passes.  In particular, it computes data about the structure
   of the basic block graph and does liveness analysis for the SSA variables.

-}
module CodeGen.LLVM.Analysis
  (BasicData(..),
   LiveInInfo(..),
   LivenessData,
   AnalyzedBlock(..),
   DefSite(..),
   displayBasicData,
   displayLivenessData,
   analyzeFunction,
   analyzeAndRepackage)
where

import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.List (foldl',(\\),nub,find)
import Data.Maybe (maybeToList,fromMaybe)

import Text.PrettyPrint.HughesPJ

import qualified LLVM.General.AST as L (Name(..))
import qualified LLVM.General.AST.Global as L
import qualified LLVM.General.AST.Instruction as L
import qualified LLVM.General.AST.Operand as L
import qualified LLVM.General.PrettyPrint as LP

-- A type to represent the location where variables are defined.  Since we are
-- in SSA form, there should be exactly one definition site for each variable.
-- However, we treat Phi nodes differently, as if they are defined in each
-- predecessor block rather than the block where the phi node occurs.
type PhiDef = [(L.Operand,L.Name)]

data DefSite = DSArg           -- Is an argument to the function
             | DSNormal L.Name -- Defined by a non-phi instruction/terminator
             | DSPhi PhiDef    -- Defined by a phi instruction

-- helper function for dealing with phi nodes
isPhiNode :: L.Named L.Instruction -> Bool
isPhiNode (L.Do (L.Phi {}))   = True
isPhiNode (_ L.:= (L.Phi {})) = True
isPhiNode _                   = False

-- This datatype includes the useful data that we can compute from a single pass
-- over the basic blocks of a function.  In particular, we calculate the graph
-- structure and where variables are defined/used.
data BasicData =
  BasicData {
    -- Map from names to the basic blocks
    blocks :: M.Map L.Name L.BasicBlock,

    -- Maps from basic blocks to immediate successor/predecessor blocks
    blockSuccs :: M.Map L.Name [L.Name],
    blockPreds :: M.Map L.Name [L.Name],

    -- Map from basic block labels to a list of Phi variables whose definitions
    -- start the block (and their definitions).
    blockPhis :: M.Map L.Name [(L.Name,PhiDef)],
    
    -- Map from blocks to the SSA variables used in them.  This includes
    -- variables defined and subsequently used within this block.
    blockVarUses :: M.Map L.Name [L.Name],

    -- Map from blocks to the SSA variables defined in them.  Note that this
    -- includes phi nodes defined in successor blocks.
    blockVarDefs :: M.Map L.Name [L.Name],

    -- Map from SSA variables to the name of the basic block where they are
    -- defined, or the name of several blocks in the case of a phi node.
    varDefBlocks :: M.Map L.Name DefSite,

    -- Map from SSA variables to the names of the basic blocks where they are
    -- used.
    varUseBlocks :: M.Map L.Name [L.Name]

  }

-- Liveness data for a function.  A map from block names to the SSA variables
-- which are live-in and live-out for that block.
--
-- For the purposes of this data, uses of variables in a Phi instruction count
-- as uses in the corresponding predecessor block.  Likewise, the variable
-- defined by the Phi node is counted as defined in the predecessor block.  This
-- matches our plan to compile-away Phi nodes as assignments in the predecessor
-- blocks.
data LiveInInfo = LiveInNatural | LiveInPhi PhiDef

type LivenessData = M.Map L.Name (M.Map L.Name LiveInInfo, S.Set L.Name)

-------------------------------------------------------------------------
-- This is for debugging
displayBasicData :: BasicData -> String
displayBasicData (BasicData {blocks,blockSuccs,blockPreds,
                             blockVarUses,blockVarDefs,
                             varDefBlocks,varUseBlocks}) =
    render (text "Basic Block information:"
        $+$ nest 2 bbDocs
        $+$ text "\n"
        $+$ text "Variable information:"
        $+$ nest 2 varDocs)
  where
    showName :: L.Name -> Doc
    showName (L.Name s) = text $ "%" ++ s
    showName (L.UnName w) = text $ "%" ++ show w
    
    getList :: L.Name -> M.Map L.Name [L.Name] -> Doc
    getList b m = case M.lookup b m of
                    Nothing -> text "NONE"
                    Just ns -> listOfNames ns
    
    listOfNames :: [L.Name] -> Doc
    listOfNames ps = hsep $ punctuate comma $ map showName ps
    
    bbDocs :: Doc
    bbDocs = vcat $ map bbDoc $ M.keys blocks

    bbDoc :: L.Name -> Doc
    bbDoc b =
          showName b
      $+$ nest 2 
           (    ((text "Predecessors: ") <> preds)
            $+$ ((text "Successors:   ") <> succs)
            $+$ ((text "Var Defs:     ") <> varDefs)
            $+$ ((text "Var Uses:     ") <> varUses))
      where
        preds,succs,varDefs,varUses :: Doc
        preds = getList b blockPreds
        succs = getList b blockSuccs
        varDefs = getList b blockVarDefs
        varUses = getList b blockVarUses
                 
    varDocs :: Doc
    varDocs = vcat $ map varDoc $ M.keys varDefBlocks

    varDoc :: L.Name -> Doc
    varDoc b =
          showName b
      $+$ nest 2
           (    ((text "Defined: ") <> def)
            $+$ ((text "Used:    ") <> used))
      where
        def,used :: Doc
        def = case M.lookup b varDefBlocks of
                Nothing -> text "UNDEFINED"
                Just DSArg         -> text "<function argument>"
                Just (DSNormal b') -> showName b'
                Just (DSPhi bs)    -> listOfNames $ map snd bs

        used = getList b varUseBlocks


displayLivenessData :: LivenessData -> String
displayLivenessData ld =
  render (text "Liveness Information:"
      $+$ nest 2 lvDocs)
  where
    showName :: L.Name -> Doc
    showName (L.Name s) = text $ "%" ++ s
    showName (L.UnName w) = text $ "%" ++ show w

    showPhi :: (L.Operand,L.Name) -> Doc
    showPhi (o,n) = parens $ (text $ LP.showPretty o)
                          <> comma
                         <+> showName n

    showLiveIn :: (L.Name,LiveInInfo) -> Doc
    showLiveIn (n,LiveInNatural) = showName n
    showLiveIn (n,LiveInPhi def) =
      showName n <+> (brackets $ hsep $ punctuate comma $ map showPhi def)

    displayList :: (a -> Doc) -> [a] -> Doc
    displayList sh ps = hsep $ punctuate comma $ map sh ps

    lvDocs :: Doc
    lvDocs = vcat $ map lvDoc $ M.toList ld

    lvDoc :: (L.Name,(M.Map L.Name LiveInInfo,S.Set L.Name)) -> Doc
    lvDoc (b,(i,o)) =
             showName b
         $+$ nest 2
              (    (text "Live in:  ") <> displayList showLiveIn (M.toList i)
               $+$ (text "Live out: ") <> displayList showName (S.toList o))

---------------------------------------------------------------
---------------------------------------------------------------
-- Computing the BasicData, and helper functions

-- convenient for use with M.alter
addIfAbsent :: Eq a => a -> Maybe [a] -> Maybe [a]
addIfAbsent a Nothing = Just [a]
addIfAbsent a (Just as) = Just $ if a `elem` as then as else a:as

-- Return any locals used by an operand.
--
-- XXX Here I am ignoring ConstantOperand, and failing on
-- MetadataStringOperand and MetaDataNodeOperand.  I think the constants
-- genuinely can't refer to locals, but I don't understand what the metadata
-- stuff is at all.  For "production" code I'd need to, at the very least,
-- fail more gracefully here.
operandVars :: L.Operand -> [L.Name]
operandVars (L.LocalReference _ vnm) = [vnm]
operandVars (L.ConstantOperand _)        = []
operandVars i@(L.MetadataStringOperand _) =
  error $ "Unsupported MetadataStringOperand: " ++ show i
operandVars i@(L.MetadataNodeOperand _)   =
  error $ "Unsupported MetadataNodeOperand: " ++ show i

-- Calculates the successor blocks and variables used by a Terminator.
-- Returned in that order.
terminatorInfo :: L.Terminator -> ([L.Name],[L.Name])
terminatorInfo (L.Ret {L.returnOperand}) =
    ([],maybe [] operandVars returnOperand)
terminatorInfo (L.CondBr {L.condition,L.trueDest,L.falseDest}) =
    ([trueDest,falseDest],operandVars condition)
terminatorInfo (L.Br {L.dest}) = ([dest],[])
terminatorInfo (L.Switch {L.operand0',L.defaultDest,L.dests}) =
  (defaultDest : map snd dests, operandVars operand0')
terminatorInfo (L.IndirectBr {L.operand0',L.possibleDests}) =
  (possibleDests, operandVars operand0')
terminatorInfo (L.Invoke {L.function',L.arguments',
                          L.returnDest,L.exceptionDest}) =
  ([returnDest,exceptionDest],
   nub $ concatMap operandVars $
     case function' of
       Left _  -> map fst arguments'
       Right o -> o : map fst arguments')
terminatorInfo (L.Resume {L.operand0'}) = ([],operandVars operand0')
terminatorInfo (L.Unreachable _) = ([],[])

-- Calculates the used variables of an instruction and the type of the data
-- compute by the instruction, if any.
--
-- Notes:
--
--   - We treat Phi instruction like any other instructions, returning the
--     operands.  In practice, we often consider phi nodes to be uses in the
--     previous block rather than the current block, since they are compiled
--     away as assignments in the previous block.  Thus, it is incumbent on
--     users of this function to first handle phi nodes separately if desired.
--
--   - We are ignoring any metadata.  I don't think it can contain anything we'd
--     want to count as the use of a variable.
instructionInfo :: L.Instruction -> [L.Name]
instructionInfo i = nub $ concatMap operandVars $ iops i
  where
    iops :: L.Instruction -> [L.Operand]
    iops (L.Add {L.operand0,L.operand1})  = [operand0,operand1]
    iops (L.FAdd {L.operand0,L.operand1}) = [operand0,operand1]
    iops (L.Sub {L.operand0,L.operand1})  = [operand0,operand1]
    iops (L.FSub {L.operand0,L.operand1}) = [operand0,operand1]
    iops (L.Mul {L.operand0,L.operand1})  = [operand0,operand1]
    iops (L.FMul {L.operand0,L.operand1}) = [operand0,operand1]
    iops (L.UDiv {L.operand0,L.operand1}) = [operand0,operand1]
    iops (L.SDiv {L.operand0,L.operand1}) = [operand0,operand1]
    iops (L.FDiv {L.operand0,L.operand1}) = [operand0,operand1]
    iops (L.URem {L.operand0,L.operand1}) = [operand0,operand1]
    iops (L.SRem {L.operand0,L.operand1}) = [operand0,operand1]
    iops (L.FRem {L.operand0,L.operand1}) = [operand0,operand1]
    iops (L.Shl {L.operand0,L.operand1})  = [operand0,operand1]
    iops (L.LShr {L.operand0,L.operand1}) = [operand0,operand1]
    iops (L.AShr {L.operand0,L.operand1}) = [operand0,operand1]
    iops (L.And {L.operand0,L.operand1})  = [operand0,operand1]
    iops (L.Or {L.operand0,L.operand1})   = [operand0,operand1]
    iops (L.Xor {L.operand0,L.operand1})  = [operand0,operand1]
    iops (L.Alloca {L.numElements})       = maybeToList numElements
    iops (L.Load {L.address})             = [address]
    iops (L.Store {L.address,L.value})    = [address,value]
    iops (L.GetElementPtr {L.address,L.indices}) =
      address : indices
    iops (L.Fence {}) = []
    iops (L.CmpXchg {L.address, L.expected, L.replacement}) =
      [address, expected, replacement]
    iops (L.AtomicRMW {L.address, L.value}) = [address, value]
    iops (L.Trunc {L.operand0})           = [operand0]
    iops (L.ZExt {L.operand0})            = [operand0]
    iops (L.SExt {L.operand0})            = [operand0]
    iops (L.FPToUI {L.operand0})          = [operand0]
    iops (L.FPToSI {L.operand0})          = [operand0]
    iops (L.UIToFP {L.operand0})          = [operand0]
    iops (L.SIToFP {L.operand0})          = [operand0]
    iops (L.FPTrunc {L.operand0})         = [operand0]
    iops (L.FPExt {L.operand0})           = [operand0]
    iops (L.PtrToInt {L.operand0})        = [operand0]
    iops (L.IntToPtr {L.operand0})        = [operand0]
    iops (L.BitCast {L.operand0})         = [operand0]
    iops (L.AddrSpaceCast {L.operand0})   = [operand0]
    iops (L.ICmp {L.operand0,L.operand1}) = [operand0,operand1]
    iops (L.FCmp {L.operand0,L.operand1}) = [operand0,operand1]
    iops (L.Phi {L.incomingValues})       = map fst incomingValues
    iops (L.Call {L.function,L.arguments}) =
      case function of
        Left _ -> map fst arguments
        Right o -> o : map fst arguments
    iops (L.Select {L.condition', L.trueValue, L.falseValue}) =
      [condition',trueValue,falseValue]
    iops (L.VAArg {L.argList})            = [argList]
    iops (L.ExtractElement {L.vector, L.index}) =
      [vector,index]
    iops (L.InsertElement {L.vector,L.element,L.index}) =
      [vector, element, index]
    iops (L.ShuffleVector {L.operand0, L.operand1}) =
      [operand0,operand1]
    iops (L.ExtractValue {L.aggregate}) = [aggregate]
    iops (L.InsertValue {L.aggregate,L.element}) = [aggregate,element]
    iops (L.LandingPad {L.personalityFunction}) = [personalityFunction]

-- The main function for computing a BasicData.  Its args are the function's
-- arguments and its basic blocks.
computeFunctionBasics :: [L.Name] -> [L.BasicBlock] -> BasicData
computeFunctionBasics args = foldl' computeBlock initialBD
  where
    initialBD :: BasicData
    initialBD = BasicData {blocks = M.empty,
                           blockSuccs = M.empty,
                           blockPreds = M.empty,
                           blockPhis  = M.empty,
                           blockVarUses = M.empty,
                           blockVarDefs = M.empty,
                           varDefBlocks = M.fromList $ map (,DSArg) args,
                           varUseBlocks = M.empty}

    -- Strip off the name from an instruction, returning the instruction and
    -- updating the BasicData to indicate the definition site.  First arg is the
    -- block's name.
    --
    -- Note that this function does not handle phi nodes correctly, and should
    -- never be called on one.
    unName :: L.Name -> BasicData -> L.Named a -> (BasicData,a)
    unName _ bd (L.Do a) = (bd,a)
    unName bnm bd@(BasicData {blockVarDefs,varDefBlocks}) (vnm L.:= x) =
      (bd {blockVarDefs = M.alter (addIfAbsent vnm) bnm blockVarDefs,
           varDefBlocks = M.insert vnm (DSNormal bnm) varDefBlocks},
       x)


    -- This checks if the first instruction is a phi.  If so, the bd is
    -- updated and we check the next instruction.  Eventually, the updated
    -- bd and the remainder of the list is returned.
    computePhis :: L.Name -> [L.Named L.Instruction] -> BasicData
                -> ([L.Named L.Instruction],BasicData)
    computePhis block instructions initial_bd =
      let (other_ins,bd,phis) = cp instructions initial_bd []
       in (other_ins,bd {blockPhis = M.insert block (reverse phis)
                                            $ blockPhis bd})
      where
        -- As phis are processed, they are also accumulated into a list.  At the
        -- end, that list is added as blockPhis
        cp :: [L.Named L.Instruction] -> BasicData
           -> [(L.Name,PhiDef)]
           -> ([L.Named L.Instruction],BasicData,[(L.Name,PhiDef)])
        cp [] bd acc = ([],bd,acc)
        cp (phivar L.:= L.Phi {L.incomingValues} : other_ins) bd acc =
          cp other_ins (foldl' addPhiUses bd_with_defs incomingValues)
             ((phivar,incomingValues) : acc)
            where
              bd_with_defs =
                bd {varDefBlocks =
                       M.insert phivar (DSPhi $ incomingValues)
                              $ varDefBlocks bd,
                    blockVarDefs =
                       foldl' (flip $ M.alter (addIfAbsent phivar))
                              (blockVarDefs bd)
                              (map snd incomingValues),
                    varUseBlocks =
                       M.alter (addIfAbsent block) phivar $ varUseBlocks bd,
                    blockVarUses =
                       M.alter (addIfAbsent phivar) block $ blockVarUses bd}

              addPhiUses :: BasicData -> (L.Operand,L.Name) -> BasicData
              addPhiUses bd1 (op,pred_block) =
                addVarUses pred_block bd1 (operandVars op)
        cp (i@(L.Do (L.Phi {})) : _) _ _ =
          error $ "Error: unnamed Phi encountered: " ++ show i
        cp other_ins bd acc = (other_ins,bd,acc)


    -- Add all the data about a basic block to the BasicData.
    --
    -- We handle phi nodes specially.  We intend to compile away phi nodes as
    -- assignments in each predecessor block.  So:
    --
    -- - Uses of variables in a phi node count as uses in the appropriate
    --   predecessor block, not the current one.
    --
    -- - The variables defined by a phi node are counted as defined in each
    --   predecessor block.
    computeBlock :: BasicData -> L.BasicBlock -> BasicData
    computeBlock bd bb@(L.BasicBlock bnm allIns trm) =
      foldl' (computeIns bnm) (computeTrm bnm bd2 trm) nonPhiIns
      where
        bd1 = bd {blocks = M.insert bnm bb $ blocks bd}

        (nonPhiIns,bd2) = computePhis bnm allIns bd1

    -- Add all the data about an instruction to the BasicData.  First arg is
    -- block name.
    computeIns :: L.Name -> BasicData -> L.Named L.Instruction -> BasicData
    computeIns bnm bd nins =
      -- Two things of interest can happen in an instruction: it can define an
      -- ssa variable, and it can use some ssa variables.  The first is handled
      -- by our "unName" helper function, and our helper function
      -- "instructionInfo" computes the uses, which we here add to the basic
      -- block.
      addVarUses bnm bd' vars
      where
        -- The basic data with definition info added, and the terminator.
        bd' :: BasicData
        ins :: L.Instruction
        (bd',ins) = unName bnm bd nins

        -- The SSA variables used by the instruction
        vars :: [L.Name]
        vars = instructionInfo ins
      

    -- Add all the data about a terminator to the BasicData.  First arg is block
    -- name.
    computeTrm :: L.Name -> BasicData -> L.Named L.Terminator -> BasicData
    computeTrm bnm bd ntrm =
      -- Three things of interest can happen in a terminator: it can define an
      -- ssa variable (e.g., in the case of a function call), it can use some
      -- ssa variables, and it can transfer control to some number of successor
      -- blocks.  Here, the the call to "unName" deals with the first, and our
      -- helper function "terminatorInfo" computes the latter two, which we then
      -- add to the BasicData.
      addVarUses bnm
             (bd' {blockSuccs = M.insert bnm succBlocks $ blockSuccs bd'}
                  {blockPreds = foldl' (flip $ M.alter (addIfAbsent bnm))
                                       (blockPreds bd') succBlocks})
             usedVars
      where
        -- The basic data with definition info added, and the terminator.
        bd' :: BasicData
        term :: L.Terminator
        (bd',term) = unName bnm bd ntrm
        
        -- The successor blocks and operands used by this terminator
        succBlocks :: [L.Name]
        usedVars :: [L.Name]
        (succBlocks,usedVars) = terminatorInfo term
                  
    -- Add any variable uses to the BasicData.  First arg is block name.
    addVarUses :: L.Name -> BasicData -> [L.Name] -> BasicData
    addVarUses block basicdata vars = foldl' addVar basicdata vars
      where
        addVar :: BasicData -> L.Name -> BasicData
        addVar bd@(BasicData {blockVarUses,varUseBlocks}) v =
          bd {blockVarUses = M.alter (addIfAbsent v) block blockVarUses,
              varUseBlocks = M.alter (addIfAbsent block) v varUseBlocks}

---------------------------------------------------------------
---------------------------------------------------------------
-- Computing the LivenessData, and helper functions

-- The main function for computing a LivenessData from a function's blocks.
--
-- Requires precomputation of BasicData
--
-- This is based on the approach in Section 19.6 of Appel's "Modern compiler
-- implementation in ML".  Roughly: for each variable, we walk backwards from
-- each use site until we reach its definition.  When this walk takes us from a
-- block to its predecessor, we mark the variable live-in to the original block
-- and live-out from its predecessor.  The algorithm will terminate because we
-- record the blocks we've seen and don't walk through them a second time.
--
-- There are a couple major differences from his algorithm.  First, we don't
-- calculate the interference graph, as we aren't doing register allocation or
-- anything similar.  Second, while he calculates the live-in and live-out sets
-- for each statement, we need them only for basic blocks.
--
-- Phi nodes are the major complication.  Recall that phi nodes will be compiled
-- away by a definition in each predecessor block.  Thus, we treat variables
-- defined in a phi node as if they were defined in each predecessor block, and
-- uses of variables in phi nodes count as uses in the corresponding block.  To
-- make code generation easier, the "Live In" set records whether the variable
-- is "really" live in or is defined in an initial Phi node (and the
-- corresponding definition).  This is the only bit that requires special logic
-- (which appears in "liveInAtBlock), because computeFunctionBasics already
-- produces a BasicData that follows the "phi nodes appear in predecessor
-- blocks" convention.
computeFunctionLiveness :: BasicData -> LivenessData
computeFunctionLiveness (BasicData {varUseBlocks,varDefBlocks,
                                    blockPreds,blocks,blockPhis}) =
    -- This just adds empty sets for any blocks that didn't come up in the
    -- search.
    foldl' (\ld b -> M.insert b (M.empty,S.empty) ld)
           livenessData
           (M.keys blocks \\ M.keys livenessData)
  where
    livenessData = foldl' computeVarLiveness M.empty $ M.keys varDefBlocks

    
    -- This calculates the blocks where a particular variable is live-in or
    -- live-out.  They are added to the input LivenessData
    computeVarLiveness :: LivenessData -> L.Name -> LivenessData
    computeVarLiveness initLiveness v =
      fst $ foldl' computeVarUse (initLiveness,S.empty) varUseSites
      where
        lookupEmpty :: Ord k => k -> M.Map k [a] -> [a]
        lookupEmpty k m = fromMaybe [] $ M.lookup k m
        
        varUseSites, varDefSites :: [L.Name]
        varUseSites = lookupEmpty v varUseBlocks

        varDefSites = case M.lookup v varDefBlocks of
                        Nothing           -> []
                        Just DSArg        -> []
                        Just (DSNormal b) -> [b]
                        Just (DSPhi bs)   -> map snd bs

        -- helpers for updating the livenessdata
        makeLiveIn :: LivenessData -> L.Name -> LivenessData
        makeLiveIn ld block =
          M.alter (\ml -> case ml of
                            Nothing -> Just (M.singleton v liveInInfo, S.empty)
                            Just (lin,lout) -> Just (M.insert v liveInInfo lin, lout))
                  block ld
          where
            liveInInfo :: LiveInInfo
            liveInInfo = fromMaybe LiveInNatural $ do
              bps <- M.lookup block blockPhis
              phiDef <- lookup v bps
              return $ LiveInPhi phiDef

        makeLiveOut :: LivenessData -> L.Name -> LivenessData
        makeLiveOut ld block =
          M.alter (\ml -> case ml of
                            Nothing -> Just (M.empty, S.singleton v)
                            Just (lin,lout) -> Just (lin, S.insert v lout))
                  block ld

        -- Check if the definition of a variable occurs before any use in a
        -- basic block.  This can fail to happen with the definition occurs
        -- because of Phi nodes.
        --
        -- This function assumes it is only called if a variable is both used
        -- and defined in the relevant block.
        definedBeforeUsedIn :: L.Name -> L.Name -> Bool
        definedBeforeUsedIn var b =
          case M.lookup b blocks of
            Nothing -> False
            Just (L.BasicBlock _ nins ntrm) ->
              dbui (dropWhile isPhiNode nins) ntrm
              -- drop Phi nodes here becuase they aren't really here.
          where
            dbui :: [L.Named L.Instruction] -> L.Named L.Terminator -> Bool
            -- If we reach the end of the block and have seen neither a
            -- definition nor a use, then both must occur because of Phi nodes.
            -- This can only happen when some successor block has one phi node
            -- that defines the variable and a subsequent phi node that uses it.
            -- Thus, the definition does occur before the use.
            dbui [] (L.Do trm)   = not $ var `elem` snd (terminatorInfo trm)
            dbui [] (_ L.:= trm) = not $ var `elem` snd (terminatorInfo trm)
            dbui (L.Do ins : xs) trm = (not $ var `elem` instructionInfo ins)
                                    && dbui xs trm
            dbui (v' L.:= ins : xs) trm =
                 not (v `elem` instructionInfo ins)
              && (v == v' || dbui xs trm) 

        -- The next few functions are the main liveness algorithm.  They take in:
        --    - The current liveness data and the set of blocks we've already
        --      traversed.
        --    - The name of a block where the variable is used.
        --
        -- And update the initial pair appropriately.  A block is marked as
        -- traversed when it is encountered in liveOutAtBlock, and that function
        -- also checks if its argument has been traversed, providing the
        -- termination metric.
        --
        -- There is a slight inefficiency in that when we traverse over a block
        -- it gets updated twice rather than just once (in both liveInAtBlock
        -- and liveOutAtBlock).  Could fix this, but it doesn't seem like a big
        -- problem.
        computeVarUse :: (LivenessData,S.Set L.Name) -> L.Name
                      -> (LivenessData,S.Set L.Name)
        computeVarUse (live,checked) block =
          -- This condition is a bit subtle.  If the variable is defined and
          -- then used in this block, we don't need to go any farther.  However,
          -- it's not enough to just check whether the variable is defined in
          -- this block, because it's actually possible for the variable to be
          -- used _before_ it is defined in this block, in the case of a loop.
          if definedBeforeUsedIn v block
             then (live,checked)
             else liveInAtBlock (live,checked) block

        liveInAtBlock :: (LivenessData,S.Set L.Name) -> L.Name
                      -> (LivenessData,S.Set L.Name)
        liveInAtBlock (live,checked) block =
          foldl' liveOutAtBlock (makeLiveIn live block,checked)
              $ lookupEmpty block blockPreds

        liveOutAtBlock :: (LivenessData,S.Set L.Name) -> L.Name
                       -> (LivenessData,S.Set L.Name)
        liveOutAtBlock p@(live,checked) block =
          if S.member block checked
            then p
            else
              if block `elem` varDefSites
                then p'
                else liveInAtBlock p' block
          where
            p' = (makeLiveOut live block,S.insert block checked)

--------------------------------------------------------------------
-- Reorganization

-- This "repackages" each of the basic blocks for a function, based on the
-- analysis above.  In particular, the repackaged basic blocks record their
-- live-in sets, they have no phi nodes, and for each successor block we've
-- recorded its live-in variables in terms of the operands we must pass (taking
-- care of the relevant phivariable instantiations).

data AnalyzedBlock =
  AnalyzedBlock {abLabel  :: L.Name,
                 abInstructions :: [L.Named L.Instruction],
                 abTerminator :: L.Named L.Terminator,
                 abLiveIn :: [L.Name],
                 abLiveOut :: M.Map L.Name [Either L.Name L.Operand]}

repackageBlock :: LivenessData -> L.BasicBlock -> AnalyzedBlock
repackageBlock ld (L.BasicBlock abLabel allIns abTerminator) =
  AnalyzedBlock {abLabel, abInstructions, abTerminator,
                 abLiveIn, abLiveOut}
  where
    abInstructions :: [L.Named L.Instruction]
    abInstructions = dropWhile isPhiNode allIns

    -- XXX fail more gracefully
    liveIntoBlock :: L.Name -> [(L.Name,LiveInInfo)]
    liveIntoBlock b =
      case M.lookup b ld of
        Just (li,_) -> M.toList li
        Nothing -> error $ "Internal error: no data for block " ++ show b
                        ++ " in 'liveIntoBlock'"

    abLiveIn :: [L.Name]
    abLiveIn = map fst $ liveIntoBlock abLabel

    abLiveOut :: M.Map L.Name [Either L.Name L.Operand]
    abLiveOut = M.fromList $
      map (\(b,li) -> (b,map liveInInfoToOperand li)) successorLiveIn
      where
        successorBlocks :: [L.Name]
        (successorBlocks,_) = terminatorInfo $
          case abTerminator of
           (L.Do t) -> t
           (_ L.:= t) -> t

        successorLiveIn :: [(L.Name,[(L.Name,LiveInInfo)])]
        successorLiveIn = map (\b -> (b,liveIntoBlock b)) successorBlocks

        liveInInfoToOperand :: (L.Name,LiveInInfo) -> Either L.Name L.Operand
        liveInInfoToOperand (v,LiveInNatural) = Left v
        liveInInfoToOperand (v,LiveInPhi pd) =
          case find ((abLabel ==) . snd) pd of
            Just (o,_) -> Right o
            Nothing -> error $
                 "Internal error: no predecessor operand for block "
              ++ show abLabel ++ " in LiveInInfo for variable " ++ show v
        
----------------------------------------------------------------------------
-- Top-level

-- To analyze a function f, provide:
--    (1) the names of f's arguments and
--    (2) f's basic blocks
analyzeFunction :: [L.Name] -> [L.BasicBlock] -> (BasicData,LivenessData)
analyzeFunction args bbs = (bd,ld)
  where
    bd = computeFunctionBasics args bbs
    ld = computeFunctionLiveness bd

analyzeAndRepackage :: [L.Name] -> [L.BasicBlock]
                    -> (BasicData,LivenessData,[AnalyzedBlock])
analyzeAndRepackage args bbs = (bd,ld,map (repackageBlock ld) bbs)
  where
    (bd,ld) = analyzeFunction args bbs
    

