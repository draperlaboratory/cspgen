module CodeGen.C.CFGLiveness where

{- |

  Module      :  CodeGen.C.CFGLiveness
  Description :  Liveness analysis and optimization for the CFG
  Copyright   :  Draper Laboratories
  
  Author      :  Chris Casinghino
-}

import CodeGen.C.CFG
import CodeGen.C.Syntax
import CodeGen.C.CFGPointsTo

import qualified Data.Set as S
import qualified Data.Map as M
import Data.Maybe (fromMaybe)

import Control.Monad.Identity

import Compiler.Hoopl

data Mode = MOutput | MInput | MUnknown
  deriving (Show,Eq)

type Modes = M.Map Id [Mode]

-----------------------------------
-- Analyzing particular expressions

-- "expUsedVars fmap l e" adds the variables used by e to the set l.  Here, by
-- "use", we mean that e actually uses the value in the variable.  So, assigning
-- to a variable does not count as a use.  fmap is some mode information about
-- functions (i.e., whether those functions take in "output" variables that get
-- squashed, as far as we know).
expUsedVars :: Modes -> Live -> Exp -> Live
expUsedVars modeMap lv eu = expUses lv eu
  where
    expUses :: Live -> Exp -> Live
    expUses l (CommaExp es _)        = foldl expUses l es
    expUses l (IdExp v _)            = if isLocal v then S.insert v l else l
    expUses l (ConstExp _ _)         = l
    expUses l (AssignExp _ e1 e2 _)  = S.union used $ expUses ((S.\\) l squashed) e2
      where
        (squashed,used) = expDefLocs e1
    expUses l (Subscript e1 e2 _)    = expUses (expUses l e1) e2
    expUses l (FunCall ef es _)      =
      case ef of
        IdExp fname _ ->
          case M.lookup fname modeMap of
            Nothing -> noModesAnswer
            Just modes -> 
              if length modes == length es 
                then 
                  let (squashed,used) = foldl expUsesArg (S.empty,S.empty) (zip modes es)
                  in
                     (S.\\) (S.union l' used) ((S.\\) squashed used)
                else noModesAnswer
        _             -> noModesAnswer
      where
        -- pairs are(squashedVars,usedVars). if a squashed var is also in used,
        -- then we should be careful not to actually squash it.
        -- 
        -- XXX would like to generalize this
        expUsesArg :: (Live,Live) -> (Mode,Exp) -> (Live,Live)
        expUsesArg (squashed,used) (MOutput,Unary Address (IdExp v _) _) = 
            (S.insert v squashed,used)
        expUsesArg (squashed,used) (_,ea) = (squashed,expUses used ea)

        noModesAnswer = foldl expUses l' es

        l' = case ef of
               (IdExp _ _) -> l
               _           -> expUses l ef -- XXX
    expUses l (CompSel e _ _ _)      = expUses l e
    expUses l (Unary _ e _)          = expUses l e   -- XXX deref?
    expUses l (Bin _ e1 e2 _)        = expUses (expUses l e1) e2
    expUses l (SizeOfExp _ _)        = l
    expUses l (SizeOfTy _ _)         = l
    expUses l (Cast _ e _)           = expUses l e
    expUses l (Cond e1 me2 e3 _)     = expUses (expUses (maybe l (expUses l) me2) e1) e3

    -- Assume the input exp is an lvalue.  Returns vars that are squashed, and vars that are used.
    expDefLocs :: Exp -> (Live,Live)
    expDefLocs (CommaExp es _) = 
      case reverse es of
        []       -> (S.empty,S.empty)
        (e1:es') -> let (squashed,used) = expDefLocs e1 in
                      (squashed,foldl expUses used es')
    expDefLocs (IdExp v _)           = (if isLocal v then S.singleton v else S.empty, S.empty)
    expDefLocs (ConstExp _ _)        = (S.empty,S.empty)
    expDefLocs (AssignExp _ e1 e2 _) = (S.empty,expUses (expUses S.empty e2) e1)
    expDefLocs (Subscript e1 e2 _)   = (S.empty,expUses (expUses S.empty e2) e1)
    expDefLocs (FunCall _ef es _)     = (S.empty,foldl expUses S.empty es)
        -- XXX what about non-function ids in ef?  need "usedfuncname" or something
    expDefLocs (CompSel e1 DirSel _ _)   =
        -- Crucially, we can't say the vars in e1 are squashed here, since we
        -- represent the whole struct as one value and not all of it is overwritten.
      (S.empty, expUses S.empty e1)
    expDefLocs (CompSel e1 IndirSel _ _) = -- XXX need points to
      (S.empty, expUses S.empty e1)
    expDefLocs (Unary Indirection e1 _)  = -- XXX really need points to analysis here
      (S.empty, expUses S.empty e1)
    expDefLocs (Unary _ e1 _)            = expDefLocs e1 -- XXX?
    expDefLocs (Bin _ e1 e2 _)           = (S.empty, expUses (expUses S.empty e1) e2)
    expDefLocs (SizeOfExp e _)           = (S.empty, expUses S.empty e)
    expDefLocs (SizeOfTy _ _)            = (S.empty, S.empty)
    expDefLocs (Cast _ e _)              = expDefLocs e
    expDefLocs (Cond e1 me2 e3 _)        = (S.intersection sq1 sq2,
                                            expUses (S.union used1 used2) e1)
      where
        (sq1,used1) = case me2 of
                        Nothing -> (S.empty, S.empty)
                        Just e2 -> expDefLocs e2
        (sq2,used2) = expDefLocs e3

-- like expUses, but for decls
declUses :: Modes -> Live -> Decln -> Live
declUses _ f (FunDecln _ _)    = f
declUses m f (VarDecln vd _)   = 
    S.delete (vdIdent vd) 
             (maybe f (initUses f) (vdInit vd))
 where
   initUses :: Live -> Initializer -> Live
   initUses l (SimpleInitializer e) = expUsedVars m l e
   initUses l (ListInitializer is)  = foldl initUses l $ map snd is
declUses _ f (TyDef _ _ _)     = f
declUses _ f (StructDecln _ _) = f
declUses _ f (UnionDecln _ _)  = f
declUses _ f (EnumDecln _ _)   = f

-------------------------------

type Live = S.Set Id

liveLattice :: DataflowLattice Live
liveLattice = DataflowLattice
  { fact_name = "Live variables",
    fact_bot  = S.empty,
    fact_join = add
  }
  where
    add _ (OldFact old) (NewFact new) = (ch,j)
      where
        j = new `S.union` old
        ch = changeIf (S.size j > S.size old)

-- transfer function bits.  Top-level because we use them in both liveness and deadVarCleanup
firstLive :: PTInsn C O -> Live -> Live
firstLive (AInsn (ILabel _ _) _) f = f

middleLive :: Modes -> PTInsn O O -> Live -> Live
middleLive m (AInsn i _)  f = middleLiveI i
  where
    middleLiveI :: Insn O O -> Live
    middleLiveI (IExp e)     = expUsedVars m f e
    middleLiveI (IDecl d)    = declUses m f d
    middleLiveI (ICleanup v) = S.insert v f

liveFact :: FactBase Live -> Label -> Live
liveFact f l = fromMaybe S.empty $ lookupFact l f

lastLive :: Modes -> PTInsn O C -> FactBase Live -> Live
lastLive m (AInsn i _) f = lastLiveI i
  where
    lastLiveI :: Insn O C -> Live
    lastLiveI (IGoto _ vs l)            = foldr S.insert (liveFact f l) vs
    lastLiveI (ICond _ vs1 vs2 e l1 l2) = 
        foldr S.insert 
              (expUsedVars m (S.union (liveFact f l1) (liveFact f l2)) e)
              (vs1 ++ vs2)
    lastLiveI (IReturn _ vs me)         = 
        foldr S.insert 
        (case me of
           Nothing -> fact_bot liveLattice
           Just e  -> expUsedVars m (fact_bot liveLattice) e)
        vs
    lastLiveI (ITailCall _ vs es)       =
      foldl (expUsedVars m) (foldr S.insert (fact_bot liveLattice) vs) es
                                   

liveness :: Modes -> BwdTransfer PTInsn Live
liveness m = mkBTransfer3 firstLive (middleLive m) (lastLive m)

-- Computes the locals reachable from a set of variables.  Same as reachablePT,
-- except any globals are filtered out.
reachableLocals :: PTFacts -> S.Set Id -> PointsTo
reachableLocals ptf vars = fmap (S.filter isLocal) $ reachablePT ptf vars

deadVarCleanup :: FuelMonad m => Modes -> BwdRewrite m PTInsn Live 
deadVarCleanup m = mkBRewrite3 firstRewrite middleRewrite lastRewrite
  where
    firstRewrite :: FuelMonad m => PTInsn C O -> Live -> m (Maybe (Graph PTInsn C O))
    firstRewrite _ _ = return Nothing

    -- We use this to compute which variables "go dead" based on the difference
    -- between two sets of reachable variables.
    --
    -- XXX In the two "Top" cases here, our analysis was insufficiently precise to
    -- come up with a good answer, so we throw our hands up and say "I don't know".
    -- In practice, this means no dead variables are cleaned up, even though some
    -- variables may in fact be going dead.
    -- 
    -- In principle, this should only be a performance problem and not a soundness
    -- problem.  In practice, this could mean some variables remain in the local
    -- state map after they should be gone, which could mean we fail to catch a
    -- variable used after it's out of scope.  We're not focused on that kind of
    -- error, so I'm not too worried.  Ideally, the right thing to do is to pair
    -- this liveness analysis with a scope analysis that also removes whatever we
    -- missed at the appropriate scope boundaries.
    reachDiff :: PointsTo -> PointsTo -> S.Set Id
    reachDiff before after = 
      case (before, after) of
        (Top,_) -> S.empty
        (_,Top) -> S.empty
        (PElem b, PElem a) -> (S.\\) b a

    middleRewrite :: FuelMonad m => PTInsn O O -> Live -> m (Maybe (Graph PTInsn O O))
    middleRewrite n lv_after = 
        case S.toList dead of
          []       -> return $ Nothing
          deadVars -> return $ Just $ blockGraph $ 
            foldl (\b v -> BSnoc b (AInsn (ICleanup v) pt_after)) (BMiddle n) deadVars
      where
        lv_before = middleLive m n lv_after
           
        -- We use the before and after points-to sets to calculate all variables
        -- reachable from the before and after live sets.
        pt_before, pt_after :: PTFacts
        pt_before = getAnnot n
        pt_after  = middlePt n pt_before

        rch_before, rch_after :: PointsTo
        rch_before = reachableLocals pt_before lv_before
        rch_after  = reachableLocals pt_after  lv_after
                        
        dead :: S.Set Id
        dead = reachDiff rch_before rch_after

    -- This factors out some repeated computation from lastRewrite.  In
    -- particular, given the instruction in question, one of its potential
    -- target labels, and the live set corresponding to that target label, we
    -- compute the reachable set after the instruction.
    reachAfterLast :: PTInsn O C -> Label -> Live -> PointsTo
    reachAfterLast n@(AInsn _ pt_before) lab lv_after = 
      reachableLocals pt_after lv_after
      where
        -- XXX this "fromMaybe" hides an error instance (the label should
        -- never be missing here).  report it instead?
        pt_after = fromMaybe M.empty $ lookupFact lab $ lastPt n pt_before

    lastRewrite :: FuelMonad m => PTInsn O C -> FactBase Live -> m (Maybe (Graph PTInsn O C))
    lastRewrite n@(AInsn i pt_before) fb = lastRewriteI i
      where
        lastRewriteI :: FuelMonad m => Insn O C -> m (Maybe (Graph PTInsn O C))
        lastRewriteI (ICond sp ids1 ids2 e lab1 lab2) =

        -- Conditional nodes are the trickiest bit of this optimization.  In
        -- particular, the case where some variables are live-out only on one
        -- branch or the other requires special attention.
        --
        -- If a variable is live-out only on one branch, we can assume that
        -- branch deals with cleaning it up at the appropriate time.  But the
        -- other branch will never consider this variable again, and thus does
        -- not clean it up.  So, for performance, we tell the code generator to
        -- remove this variable from the state map for that branch.
        --
        -- We also must be careful here to accurately track when we make changes
        -- to this node, so that the dataflow analysis/rewriting pass doesn't
        -- loop.
          let
            lv_after1, lv_after2, lv_before :: Live
            lv_after1 = liveFact fb lab1
            lv_after2 = liveFact fb lab2
    
            lv_before = lastLive m n fb
            
            rch_before, rch_after1, rch_after2 :: PointsTo
            rch_before = reachableLocals pt_before lv_before
            rch_after1 = reachAfterLast n lab1 lv_after1
            rch_after2 = reachAfterLast n lab2 lv_after2
    
            removeBranch1 = reachDiff rch_before rch_after1
            removeBranch2 = reachDiff rch_before rch_after2
    
            changeBranch1 = removeBranch1 == (S.fromList ids1)
            changeBranch2 = removeBranch2 == (S.fromList ids2)
          in
            if not (changeBranch1 || changeBranch2)
              then return Nothing
              else return $ Just $ gUnitOC $ BlockOC BNil $
                AInsn
                  (ICond sp (S.toList removeBranch1) (S.toList removeBranch2)
                         e lab1 lab2)
                  pt_before
        lastRewriteI (IGoto sp ids lab) = 
          let
            lv_after, lv_before :: Live
            lv_after  = liveFact fb lab
            lv_before = lastLive m n fb

            rch_before, rch_after :: PointsTo
            rch_before = reachableLocals pt_before lv_before
            rch_after  = reachAfterLast n lab lv_after
    
            removeVars = reachDiff rch_before rch_after
          in
            if removeVars == S.fromList ids 
              then return Nothing
              else return $ Just $ gUnitOC $ BlockOC BNil $
                AInsn (IGoto sp (S.toList removeVars) lab) pt_before
        lastRewriteI (IReturn sp ids me) = 
          let
            lv_before = lastLive m n fb

            rch_before, rch_after :: PointsTo
            rch_before = reachableLocals pt_before lv_before
            rch_after  = PElem S.empty
    
            removeVars = reachDiff rch_before rch_after
          in
            if removeVars == S.fromList ids 
              then return Nothing
              else return $ Just $ gUnitOC $ BlockOC BNil $
                AInsn (IReturn sp (S.toList removeVars) me) pt_before
        lastRewriteI (ITailCall sp ids args) = 
          let
            lv_before = lastLive m n fb
    
            rch_before,rch_after :: PointsTo
            rch_before = reachableLocals pt_before lv_before
            rch_after  = PElem S.empty
                         
            removeVars = reachDiff rch_before rch_after
          in
            if removeVars == S.fromList ids 
              then return Nothing
              else return $ Just $ gUnitOC $ BlockOC BNil $
                AInsn (ITailCall sp (S.toList removeVars) args) pt_before
                      
livenessOptimization :: FuelMonad m => Modes -> BwdPass m PTInsn Live
livenessOptimization m = 
    BwdPass {bp_lattice  = liveLattice,
             bp_transfer = liveness m,
             bp_rewrite  = deadVarCleanup m}

procLiveness :: Modes -> Proc PTFacts -> Proc PTFacts
procLiveness m p@(Proc {procBody,procEntry}) = rwf infiniteFuel mproc'
  where
    rwf :: Fuel -> InfiniteFuelMonad Identity a -> a
    rwf f ma = runIdentity $ runWithFuel f ma

    mproc' :: (FuelMonad m,CheckpointMonad m) => m (Proc PTFacts)
    mproc' = do
      (body',_,_) <- analyzeAndRewriteBwd (livenessOptimization m)
                                          (JustC [procEntry])
                                          procBody noFacts
      return $ p {procBody = body'}
