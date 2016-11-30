{-# OPTIONS -fno-warn-orphans #-}

module CodeGen.C.CFGPointsTo 
  (procPT,reachablePT,
   PointsTo,PTFacts,PTInsn,
   middlePt,lastPt, ppPTFacts)
where

{- |

  Module      :  CodeGen.C.CFGPointsTo
  Description :  May-point-to analysis for the CFG
  Copyright   :  Draper Laboratories
  
  Author      :  Chris Casinghino
-}

import CodeGen.C.CFG
import CodeGen.C.Syntax

import qualified Data.Set as S
import qualified Data.Map as M
import Data.Maybe (fromMaybe,maybeToList)
import Data.List (intersperse,nub)

import Compiler.Hoopl hiding ((<*>))

import Control.Monad.Identity

-- import System.IO.Unsafe (unsafePerformIO)

instance CheckpointMonad Identity where
  type Checkpoint Identity = ()

  checkpoint = return ()

  restart () = return ()


-----------------------------------
-- Reachability:
--
-- This analysis computes the collection of identifiers that are "reachable"
-- from any given pointer at each program point.  For example, consider:
-- 
-- int x = 3;
-- int* ref = &x;
--
-- Just after these lines we expect the analysis to have observed that the set
-- of reachable variables from ref is {x}.  On the other hand, consider:
--
-- int x,y,z;
-- scanf("%d",&z);
-- int* ref = z ? &x : &y;
--
-- Here, the reachable set for ref is {x,y}, since we can't tell statically
-- which value ref is given.  In some situations, like a pointer initialized to
-- null, the set will be empty.  In other situations, like an uninitialized
-- pointer, the set should morally contain everything.  These sets form a
-- lattice with empty as the bottom and "everything" as the top.  We use Hoopl's
-- supplied "WithTop" to add this top element explicitly.
--
-- So far we've been talking just about what things a pointer can directly point
-- to, but we actually care about "reachability" instead.  Any memory that can
-- be modified by a series of indirections from a pointer counts.  For example,
-- consider:
--
-- int x;
-- int* y = &x;
-- int** z = &y;
--
-- After this code, the reachable set for y is {x} and the reachable set for z
-- is {y,x}.  Similarly, consider:
--
-- struct {int* a;
--         int* b} z;
-- int x,y;
-- z.a = &x;
-- z.b = &y;
--
-- After this code executes the reachable set for z is {x,y}.  When structs
-- contain other structs (or pointers to other structs), we must consider every
-- location accessible all the way down.

--------------------------------
-- Points to:
--
-- We can think of the "reachability" relation as being the transitive closure
-- of a shallower relation, the "may point to" relation.
--
-- Consider our earlier example:
--
-- int x;
-- int* y = &x;
-- int** z = &y;
--
-- Here, a "may point to" analysis should yield the set {y} for z and the set
-- {x} for y.
--
-- We care about reachability, but it is easier to start by doing a "may point
-- to" analysis and then take the transitive closure after.

---------------------------------
-- Imprecision and "collective" variables
--
-- Summary: When processing assignments like "x = e", we take the _union_ of x's
-- previous possible valuewith the values that come from e, rather than the more
-- precise thing of saying x can now only point to what e points to.  So, rather
-- than "points to", our analysis is more like "has ever pointed to".  We'd like
-- to fix this going forward.
--
-- In the points to analysis, we're being quite imprecise when it comes to
-- structs.  We don't keep track of what is pointed to by the individual fields
-- of a struct.  Instead, if any part of a struct might point to some location,
-- we say the struct might point to that location.  This simplifies the
-- implementation of the analysis quite a bit, since doing the right thing would
-- probably involve keeping track of the type of each variable and a bunch of
-- struct information which is non-local to a particular function.
--
-- So, in the case of an assignment like "x.l = e", we're just adding the
-- addresses indicated by "e" to the set of things "x" might point to.  And in
-- general it's quite hard to say if an assignment is really assigning into part
-- of a struct, so we just treat everything this way.
--
-- XXX fix this by threading in the CG monad, which _should_ have the necessary
-- type info.
type PointsTo = WithTop (S.Set Id)
type PTFacts  = M.Map Id PointsTo

type PTInsn   = AInsn PTFacts

-- I'd like to thread failure through a monad for cleaner errors, but hoopl
-- doesn't support this for the analysis.
failExp :: Exp -> String -> a
failExp e err = error msg
  where
    msg = "Error during points-to analysis: " ++ err 
       ++ ", in expression at " ++ show (locExp e) ++ "."

ptBot,ptTop :: PointsTo
ptBot = PElem S.empty
ptTop = Top

ptInsert :: Id -> PointsTo -> PointsTo
ptInsert v = fmap (S.insert v)

ptSize :: PointsTo -> Maybe Int
ptSize Top = Nothing
ptSize (PElem xs) = Just $ S.size xs

ptUnion  :: PointsTo -> PointsTo -> PointsTo
ptUnion Top        _          = Top
ptUnion _          Top        = Top
ptUnion (PElem xs) (PElem ys) = PElem $ S.union xs ys

--missing IDs are assumed to be bottom
ptfLookup :: Id -> PTFacts -> PointsTo
ptfLookup var ptf = fromMaybe ptBot (M.lookup var ptf)

ptfJoin :: PTFacts -> Id -> PointsTo -> PTFacts
ptfJoin ptf x pt = M.insert x pt' ptf
  where
    pt' = case M.lookup x ptf of
            Nothing -> pt
            Just ptOld -> ptUnion pt ptOld
-----------------------------------
-- Analyzing particular expressions

-- Process any changes to PTFacts caused by an Exp.  This is for a top-level
-- Exp, though we have to consider the subcomponents of most forms since
-- assignments can, in principle, occur anywhere.  The case for assignment calls
-- out to helper functions to process lvalues, etc.
expPTUpdate :: PTFacts -> Exp -> PTFacts
expPTUpdate ptf (CommaExp es _)     = foldl expPTUpdate ptf es
expPTUpdate ptf (IdExp _ _)         = ptf
expPTUpdate ptf (ConstExp _ _)      = ptf
expPTUpdate ptf e@(AssignExp Assign elv erv _) =
  case extractLValueID ptf elv of
    Top -> -- XXX If this is Top, the lvalue could point to anything.  Modelling
           -- that is hard (I need to update all in-scope variables or something?)
           -- For now let's just throw an error and see if it comes up.
      failExp e "Can't estimate possible range of lvalue in assignment."
    PElem lv_ids ->
      S.foldr (\lv_id ptf' -> ptfJoin ptf' lv_id rv_pt) ptf lv_ids
  -- XXX here is the source of the imprecision documented above.
  where
    rv_pt = pointsToExp ptf erv

expPTUpdate ptf (AssignExp _ _ _ _)   = ptf
  -- XXX ignoring pointer arithmetic here and assuming that the modifying assign
  -- operations can't change pointer values.

expPTUpdate ptf (Subscript e1 e2 _) = foldl expPTUpdate ptf [e1,e2]
expPTUpdate ptf (FunCall ef es _)   = foldl expPTUpdate ptf (ef:es)
  -- XXX This is a bit wrong.  Consider:
  -- 
  --   int x = 3; int* y = &x; int** z = &y; f(z)
  --
  -- The call to f could change what is pointed to by y (and, also, what's
  -- pointed to by things reachable from y).  The possible things f can change y
  -- to are kind of limited since it doesn't have access to any locals that
  -- aren't explicitly passed to it, but the possibility still exists.
  --
  -- The easiest way to be sound would be to change the points-to set for
  -- anything passed to a function to Top.  Somewhat harder but more
  -- fined-grained approaches:
  -- some kind of interprocedural analysis.
  --
  -- But for now, we just do the completely unsound thing of assuming f doesn't
  -- make any changes like this.

expPTUpdate ptf (CompSel e _ _ _)   = expPTUpdate ptf e
expPTUpdate ptf (Unary _ e _)       = expPTUpdate ptf e
expPTUpdate ptf (Bin _ e1 e2 _)     = foldl expPTUpdate ptf [e1,e2]
expPTUpdate ptf (SizeOfExp e _)     = expPTUpdate ptf e
expPTUpdate ptf (SizeOfTy _ _)      = ptf
expPTUpdate ptf (Cast _ e _)        = expPTUpdate ptf e
expPTUpdate ptf (Cond e1 me2 e3 _)  = 
  let es = e1 : e3 : maybeToList me2 in
  foldl expPTUpdate ptf es

-- like expPTUpdate, but for decls
declPTUpdate :: PTFacts -> Decln -> PTFacts
declPTUpdate pt (FunDecln _ _)    = pt
declPTUpdate pt (VarDecln vd _)   = M.insert (vdIdent vd) targets pt
  where
    targets :: PointsTo
    targets = case vdInit vd of
                Nothing -> ptBot
                   -- XXX this is technically unsound, in that local variables
                   -- have undefined initial contents and thus could point to
                   -- anything.  But that introduces way too much uncertainty in
                   -- practice.  Would be nice to issue a warning or something,
                   -- or check if the uninitialized value is ever used.
                Just i  -> pointsToInit i

    pointsToInit :: Initializer -> PointsTo
    pointsToInit (SimpleInitializer e) = pointsToExp pt e
    pointsToInit (ListInitializer _)   = ptTop -- XXX very pessimistic
declPTUpdate pt (TyDef _ _ _)     = pt
declPTUpdate pt (StructDecln _ _) = pt
declPTUpdate pt (UnionDecln _ _)  = pt
declPTUpdate pt (EnumDecln _ _)   = pt

-- Find the set of things that an expression might point to.  I.e., if we see an
-- assignment
-- 
--   x = e;
-- 
-- Compute from e the fact we will record for x?
pointsToExp :: PTFacts -> Exp -> PointsTo
pointsToExp ptf (CommaExp es _)      = 
  case es of 
    [] -> ptBot
    _  -> pointsToExp ptf $ last es
pointsToExp ptf (IdExp v _)          = fromMaybe ptBot (M.lookup v ptf)
pointsToExp _   (ConstExp _ _)       = ptBot
pointsToExp ptf (AssignExp _ _ e2 _) = pointsToExp ptf e2
pointsToExp ptf (Subscript e1 _ _)   = pointsToExp ptf e1
pointsToExp _   (FunCall _ _ _)      = ptBot
  -- XXX here again we're a little stuck - it's hard to model what local
  -- variables this function might return.  Come back if unsoundness is a
  -- problem.
pointsToExp ptf (CompSel e _ _ _)    = pointsToExp ptf e
  -- XXX here we are very conservative, saying anything all that the struct points to
  -- is reachable.
pointsToExp ptf (Unary Address e _)  =
  -- Per ISO/IEC 9899:2011, 6.5.3.2.3:
  -- 
  --   "If the operand [of &] is the result of the unary * operator, neither
  --    that operator nor the & operatore is evaluated and the result is as if
  --    both were omitted, except that the constraints on the operators still
  --    apply and the result is not an lvalue, except..."
  --
  -- We're ignoring the except bit, which goes on to say that the result is not
  -- an lvalue, among other things.  GCC seems to ignore that bit too, for what
  -- it's worth.
  case e of
    Unary Indirection e' _ -> pointsToExp ptf e'
    _ -> extractLValueID ptf e
pointsToExp ptf (Unary Indirection e _) =
  case pointsToExp ptf e of
    Top         -> Top
    PElem e_ids -> S.fold addIndirections ptBot e_ids
      where
        addIndirections :: Id -> PointsTo -> PointsTo
        addIndirections x pt = 
          case M.lookup x ptf of
            Nothing  -> pt
            Just xpt -> ptUnion xpt pt
pointsToExp ptf (Unary _ e _)     = pointsToExp ptf e
pointsToExp _   (Bin _ _ _ _)     = ptBot
  -- Note that this assume that expressions like x + y can't be lvalues, which
  -- isn't quite true (for example, in pointer arithmetic).  But we should throw
  -- an error in that case during sanity checking or code generation.

pointsToExp _   (SizeOfExp _ _)   = ptBot
pointsToExp _   (SizeOfTy _ _)    = ptBot
pointsToExp ptf (Cast _ e _)      = pointsToExp ptf e
pointsToExp ptf (Cond _ me2 e3 _) =
  -- since the conditional operator could return either, we take the union of
  -- the places they point to.
  ptUnion (maybe ptBot (pointsToExp ptf) me2)
          (pointsToExp ptf e3)

-- This takes in an lvalue and pulls out the id that will be modified upon
-- assigning to the lvalue.  Note that this may not be the id mentioned in the
-- lvalue.  For example, in the assignment:
--
--  (*x) = 3;
-- 
-- It's actually whatever x points to that gets modified.  And, in fact, we may
-- not know exactly what x points to, so this returns a PointsTo, which is a set
-- of variables enhanced with a "top" element representing "could be anything,
-- man".
extractLValueID :: PTFacts -> Exp -> PointsTo
extractLValueID _ (IdExp x _) = ptInsert x ptBot
extractLValueID pt (Unary Indirection e _) =
  -- (*e) = ...
  -- we want the union of everything e might point to.
  case extractLValueID pt e of
    Top -> Top
    PElem e_ids -> foldl ptUnion ptBot $
      map (\e_id -> fromMaybe ptBot (M.lookup e_id pt)) (S.toList e_ids)
      -- XXX is ptBot right here?
extractLValueID ptf (CompSel e DirSel  _ _) =
  -- (e.l) = ...  For now we just find the lvalue in e.  See discussion above.
  extractLValueID ptf e
extractLValueID ptf (Subscript e _ _) =
  -- e[foo] = ... Same reasoning as previous case.
  extractLValueID ptf e
extractLValueID ptf (Cast _ e _) =
  -- (t)e     Ignore the cast
  extractLValueID ptf e
extractLValueID _ e = failExp e $ "Unsupported lvalue"

---------------------------------
-- HOOPL analysis

ptLattice :: DataflowLattice PTFacts
ptLattice = DataflowLattice
  { fact_name = "May-have-pointed-to lattice",
    fact_bot  = M.empty,
    fact_join = add
  }
  where
    -- we fold over the bindings in the new fact.  For each var, if it doesn't
    -- appear in the old map, we add it.  If it does, we union its PointsTo set.
    -- We keep track along the way of whether anything has changed.
    add _ (OldFact old) (NewFact new) =
      let (bchange,joined) = M.foldWithKey update (False,old) new
       in (changeIf bchange,joined)
      where
        update :: Id -> PointsTo -> (Bool,PTFacts) -> (Bool,PTFacts)
        update var pt (changed,acc) =
           (changed || ptSize ptOld /= ptSize ptNew,
            M.insert var ptNew acc)
           where
             ptOld = ptfLookup var acc
             ptNew = ptUnion pt ptOld

-- -- transfer function bits.
firstPt :: AInsn a C O -> PTFacts -> PTFacts
firstPt (AInsn i _) f = firstPtI i
  where
    firstPtI :: Insn C O -> PTFacts
    firstPtI (ILabel _ _) = f

middlePt :: AInsn a O O -> PTFacts -> PTFacts
middlePt (AInsn i _) f = middlePtI i
  where
    middlePtI :: Insn O O -> PTFacts
    middlePtI (IExp e)     = expPTUpdate f e
    middlePtI (IDecl d)    = declPTUpdate f d
    middlePtI (ICleanup _) = f

lastPt :: AInsn a O C -> PTFacts -> FactBase PTFacts
lastPt (AInsn i _) f = lastPtI i
  where
    lastPtI :: Insn O C -> FactBase PTFacts
    lastPtI (IGoto _ _ l)         = mapSingleton l f
    lastPtI (ICond _ _ _ e l1 l2) =
      mkFactBase ptLattice [(l1,f'),(l2,f')]
      where
        f' = expPTUpdate f e
    lastPtI (IReturn _ _ _)   = mapEmpty
    lastPtI (ITailCall _ _ _) = mapEmpty

pointsTo :: FwdTransfer (AInsn a) PTFacts
pointsTo = mkFTransfer3 firstPt middlePt lastPt

-- We don't actually do any rewriting as part of the points to analysis.
-- It's just for the analysis bits.
ptRewrite :: FuelMonad m => FwdRewrite m (AInsn a) PTFacts
ptRewrite = mkFRewrite3 firstRewrite middleRewrite lastRewrite
  where
    firstRewrite :: FuelMonad m => AInsn a C O -> PTFacts -> m (Maybe (Graph (AInsn a) C O))
    firstRewrite _ _ = return Nothing

    middleRewrite :: FuelMonad m => AInsn a O O -> PTFacts -> m (Maybe (Graph (AInsn a) O O))
    middleRewrite _ _ = return Nothing

    lastRewrite :: FuelMonad m => AInsn a O C -> PTFacts -> m (Maybe (Graph (AInsn a) O C))
    lastRewrite _ _ = return Nothing

ptOptimization :: FuelMonad m => FwdPass m (AInsn a) PTFacts
ptOptimization =
  FwdPass {fp_lattice  = ptLattice,
           fp_transfer = pointsTo,
           fp_rewrite  = ptRewrite}

-- XXX Memory considerations: keeping a PTFacts for every instruction seems
-- horrific, memory-wise.  For large processes this is a potential source of
-- memory issues.
--
-- ptAnnotateProc uses the results of the dataflow analysis to reconstruct and
-- record the dataflow fact for each individual instruction.  This is pretty
-- ugly/inefficient - it would be nice if the dataflow analysis just preserved
-- this information for us.  But, hoopl doesn't do that, and reimplementing
-- dataflow analysis is a lot of work.  So, we just recreate it after the fact
-- from the Hoopl-produced FactBase.
--
-- This is necessary because the results of the points-to analysis are needed AT
-- EACH NODE during the liveness analysis.  Individual instructions don't carry
-- enough information to uniquely identify them, so we pair them up with the
-- relevant dataflow facts.  It might be nicer to record this stuff in a map,
-- or, better, to recompute it as needed during liveness analysis and not keep
-- it around at all.  But, the Hoopl interface doesn't make that possible.
--
-- Each instruction is annotated with the PTFact that holds _before_ that
-- instruction.
ptAnnotateProc :: Proc () -> FactBase PTFacts -> Proc PTFacts
ptAnnotateProc p fb = mapProc annotateBlock p
  where
    annotateBlock :: Block (AInsn ()) C C -> Block PTInsn C C
    annotateBlock b = blockJoin aEntry aBodyBlock aExit
      where
        (entry,bodyBlock,exit) = blockSplit b

        aEntry :: PTInsn C O
        initFact :: PTFacts
        (aEntry,initFact) = 
          case entry of
            AInsn i@(ILabel _ lab) _ -> 
              case mapLookup lab fb of
                Nothing -> error $ "Internal error during points-to analysis at label "
                                ++ show lab ++ ": missing entry label in map"
                Just f  -> (AInsn i f,f)

        aBodyBlock :: Block PTInsn O O
        pretailFact :: PTFacts
        (pretailFact,aBodyBlock) = fmap (blockFromList . reverse) $ 
            foldl annotateOpen (initFact,[]) (blockToList bodyBlock)
        
        annotateOpen :: (PTFacts,[PTInsn O O]) -> AInsn () O O 
                     -> (PTFacts,[PTInsn O O])
        annotateOpen (ptf,acc) a@(AInsn i _) = 
            (middlePt a ptf,AInsn i ptf : acc)

        aExit :: PTInsn O C
        aExit = case exit of
                  AInsn i _ -> AInsn i pretailFact

-- XXX this type could be generalized.  Perhaps just use type classes for
-- the annotations.
procPT :: Proc () -> Proc PTFacts
procPT p@(Proc {procBody,procEntry}) = ptAnnotateProc p results
  where
    results = rwf infiniteFuel mresults

    rwf :: Fuel -> InfiniteFuelMonad Identity a -> a
    rwf f ma = runIdentity $ runWithFuel f ma
 
    mresults :: (FuelMonad m,CheckpointMonad m) => m (FactBase PTFacts)
    mresults = do
      (_,fb,_) <- analyzeAndRewriteFwd ptOptimization
                                       (JustC [procEntry])
                                       procBody noFacts
      return fb

-- Computes which variables are reachable from a given set.  Note that in
-- addition to the variables in the input set, any global variables at all in
-- the PTFacts will be considered reachable (since they are global).
reachablePT :: PTFacts -> S.Set Id -> PointsTo
reachablePT ptf s = reach liveSet s
  where
    -- The liveset is the variables we were passed, plus any globals in the
    -- domain of the PTFacts map.
    liveSet :: [Id]
    liveSet = nub $ (filter isGlobal $ M.keys ptf) ++ S.toList s
    
    -- Worklist, answer accumulation
    reach :: [Id] -> S.Set Id -> PointsTo
    reach [] acc = PElem acc
    reach (x:xs) acc =
      case M.lookup x ptf of
        Nothing  -> reach xs acc
        Just Top -> Top
        Just (PElem x_pt) ->
          reach (newWork ++ xs) (S.union x_pt acc)
          where
            newWork = S.toList (S.difference x_pt acc)
            
ppPTFacts :: PTFacts -> String
ppPTFacts theFacts = concat $ intersperse ", " $ map showFact stringList
  where 
    showFact :: (Id, String) -> String
    showFact (x, string) = "(" ++ showId x ++ ", " ++ string ++ ")"    
    stringList :: [(Id, String)]
    stringList = M.toList ptstrings
    ptstrings :: M.Map Id String
    ptstrings = M.map ppPointsTo theFacts

ppPointsTo :: Pointed C O (S.Set Id) -> String
ppPointsTo (PElem idSet) = showSet 
  where
    showSet :: String
    showSet = concat $ intersperse ", " setStrings 
    setStrings :: [String]
    setStrings = S.toList $ S.map showId idSet
ppPointsTo Top           = ""

showId :: Id -> String
showId (Id x _ _) = show x
showId (Fixed x)  = show x
