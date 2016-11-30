{-# OPTIONS_GHC -fno-warn-orphans #-}

module CodeGen.C.ASTtoCFG (cfgTransUnit) where

{- |

  Module      :  CodeGen.C.ASTtoCFG
  Description :  Translation of the C AST to a control-flow graph + typing info
  Copyright   :  Draper Laboratories
  
  Author      :  Chris Casinghino
-}

-- In addition to translating the dynamic parts of the AST into the
-- corresponding hooplese, this also adds the static parts into the CG
-- monad's knowledge of the types.

-- XXX Right now, we're forgetting all scope information in this translation and
-- relying on the liveness analysis to remove variables after they are last
-- used.  This isn't strictly accurate - for example, we don't reject ill-formed
-- C programs where variables are mentioned after they leave scope.  In general,
-- a slight rethinking of the difference between automatic and dynamically
-- allocated variables would help clean up these infelicities.

import Control.Monad (when)

-- We use Hoopl's graph representation
import Compiler.Hoopl

-- source and target
import qualified CodeGen.C.Syntax as S
import qualified CodeGen.C.CFG    as T
import qualified Language.CSPM.Syntax as T

import CodeGen.C.CGMonad

import CodeGen.C.CodeGen
import CodeGen.C.CFGLiveness
import CodeGen.C.CFGPointsTo
import CodeGen.C.CFGEmptyBlocks

import qualified Data.Map as M

-- This handles function declarations.  We record the function in the monad and
-- create a CSP name for it, don't produce a Proc yet (since this is only the
-- declaration, not the body).
addFunctionDeclaration :: S.FDecln -> CG FInfo
addFunctionDeclaration (S.FDecln {S.funName,S.funArgs,S.funReturnTy}) = do
  mf <- lookupFunction funName
  case mf of
    Just finfo -> return finfo
      -- This function has already been declared.  XXX should we check that the
      -- old declaration matches the new one?
    Nothing -> do
      -- This is the first time we are seeing this function.  Come up with
      -- a target name for it and add it to the monad.
      fret <- transType funReturnTy
      fargs <- mapM (transType . snd) funArgs
      freshFunction funName fargs fret

-- External function declarations are translated into Procs (their
-- bodies are the things that become CFGs).  Everything else is just
-- added to the monad as part of the memory model or type.
--
-- Would be nice to be less specific about the annotations in the proc here,
-- but I don't see an easy way.
cfgTransUnit :: Modes -> S.TransUnit -> CG [T.Proc PTFacts]
cfgTransUnit modes (S.TransUnit {S.exts=declns}) = do 
    unopt <- cfgExts declns []
    return $ map runOptimizers unopt
  where
    runOptimizers :: T.Proc () -> T.Proc PTFacts
    runOptimizers = eliminateEmptyBlocks . (procLiveness modes) . procPT

    cfgExts :: [S.ExternalDecln] -> [T.Proc ()] -> CG [T.Proc ()]

    cfgExts [] acc = return $ reverse acc

    cfgExts (S.ExtFunDef fd : exts) acc = do
      tf <- cfgFunction fd
      cfgExts exts (tf : acc)

    cfgExts (S.ExtDecln dcl@(S.VarDecln 
                 (S.VDecln {S.vdIdent, S.vdInit, S.vdType}) sp) : exts) 
            acc = do
      binfo <- transType vdType
      ival <- case vdInit of
            Just i -> Just <$> transInitializer binfo i uninitializedGlobal sp
            Nothing -> return Nothing
      alreadyDeclared <- globalExists vdIdent
      -- In C, multiple declarations of the same global are allowed and refer to
      -- the same entity.  That entity may only be defined (i.e., declared with
      -- an initializer) once.
      case (alreadyDeclared,ival) of
        (False,_) -> freshGlobal vdIdent binfo ival (S.locDecln dcl) >> return ()
        (True,Just ti) -> addGlobalInitializer vdIdent ti
        (True,Nothing) -> return ()
      cfgExts exts acc
    
    -- VERY SPECIAL CASE FOR CHANNELS XXXXXX
    cfgExts (S.ExtDecln (S.TyDef (S.Struct _ _ _) (S.Id "chan" S.VSGlobal u) sp) : exts)
            acc = do
      addTypeDef (S.Id "chan" S.VSGlobal u) (ChannelType sp)
      cfgExts exts acc

    -- VERY SPECIAL CASE FOR MUTEXES XXXXXX
    cfgExts (S.ExtDecln (S.TyDef (S.Union _ _ _) (S.Id "pthread_mutex_t" S.VSGlobal u) sp) : exts)
            acc = do
      addTypeDef (S.Id "pthread_mutex_t" S.VSGlobal u) (MutexType sp)
      cfgExts exts acc

    -- VERY SPECIAL CASE FOR THREADS XXXXXX
    cfgExts (S.ExtDecln (S.TyDef _ (S.Id "pthread_t" S.VSGlobal u) sp) : exts)
            acc = do
      addTypeDef (S.Id "pthread_t" S.VSGlobal u) (PIDType sp)
      cfgExts exts acc

    --- VERY SPECIAL CASE FOR THREAD CONFIGURATION STRUCT XXXXX
    ---
    --- This one is particularly bad because our representation doesn't match
    --- the type at all.  If someone used something other than NULL we'd be
    --- hosed.
    ---
    --- Here the union is defined before the typedef, so we have two cases.  We
    --- ignore the first declaration and special-case the second.
    cfgExts (S.ExtDecln (S.UnionDecln  (S.Union _ (Just (S.Id "pthread_attr_t" _ _)) _) _) : exts)
            acc = cfgExts exts acc
    cfgExts (S.ExtDecln (S.TyDef (S.Union _ _ _) (S.Id "pthread_attr_t" S.VSGlobal u) sp) : exts)
            acc = do
      addTypeDef (S.Id "pthread_attr_t" S.VSGlobal u) (UnitType sp)
      cfgExts exts acc


    cfgExts (S.ExtDecln (S.TyDef typ tydefid _) : exts) acc = do
      -- A small hack here for more readable output.  A common C pattern is:
      -- 

      -- typedef struct {
      --   ...
      -- } MyName;
      -- 
      -- Declarations like this don't add a name to the struct namespace, so
      -- the name in the StructType will be S.NoId, which results in a
      -- translation with a terrible made up name.  A better name would be
      -- something to do with MyName, but that's not visible while translating
      -- the struct type itself.  So before we lookup btyp (which will add it
      -- to the monad if it's previously unseen), we replace S.NoId with some
      -- variant of MyName.
      --
      -- XXX this is potentially error prone in the case where whatever name we
      -- pick is actually added to the struct namespace later.  But the system
      -- as it stands uses just these struct names to identify structs, so
      -- this problem can't be fixed without a larger rewrite.
      let typRenamed =
            case (typ,tydefid) of
              (S.Struct sp Nothing flds,S.Id tdnm _ _) ->
                S.Struct sp (Just $ S.Fixed (tdnm ++ "_istr")) flds
              (_,_) -> typ
      
      btyp <- transType typRenamed
      addTypeDef tydefid btyp

      cfgExts exts acc

    cfgExts (e@(S.ExtDecln (S.StructDecln (S.Struct _ Nothing _) _)):_) _ =
      failExternal e $ "Unsupported: top-level struct declaration with no struct name tag"
    cfgExts (S.ExtDecln (S.StructDecln st@(S.Struct _ _ _) _):es) acc = do
      btype <- transType st
      _ <- lookupTypeInfo btype  -- this will compute accessors for the struct
                                 -- and add them to the state monad for future
                                 -- use
      cfgExts es acc

    cfgExts (e@(S.ExtDecln (S.StructDecln _ _)):_) _ =
      failExternal e $ "Internal Error: top-level StructDecln with non-struct type "

    cfgExts (S.ExtDecln (S.FunDecln fdecl _) : exts) acc = do
      _ <- addFunctionDeclaration fdecl
      cfgExts exts acc

    cfgExts (e : _) _ =
      failExternal e $ "Unsupported top-level :" ++ show e

cfgFunction :: S.FunDef -> CG (T.Proc ())
cfgFunction (S.FunDef {S.decl, S.funBody, S.fdPos}) = do
  let S.FDecln {S.funName,S.funArgs} = decl
      
      transArg :: (Maybe S.Id,S.Type) -> CG (S.Id,BaseType)
      transArg (Nothing,_) = failPos fdPos $
         "Unsupported: function with unnamed argument."
      transArg (Just asid,atyp) = (asid,) <$> transType atyp
  targs <- mapM transArg funArgs
  finfo <- addFunctionDeclaration decl
  setFunctionDefined funName fdPos
  (procEntry,procBody,procLocations) <- cfgFunctionBody funName funBody
  return $ T.Proc {T.procDecln = finfo, 
                   T.procArgs = targs,
                   T.procEntry, T.procBody, 
                   T.procLocations, T.procPos = fdPos}

-- The translation of statements is broken down into several bits, to help
-- handle the GADT structure of out CFG representation.
--
-- In particular, having a single "cfgStatement :: S.Statement -> CG (CFG e x)"
-- doesn't quite make sense, because what are e and x?  So, we need to break
-- down function bodies into basic blocks that can start with an entry label and
-- end with a control flow transfer.
--
-- So, we build a type to represent these things:
data StmtBlock = StmtBlock {sbPos   :: S.SPos,
                            sbLabel :: Label,
                            sbBody  :: [T.AInsn () O O],
                            sbExit  :: T.AInsn () O C}
  deriving (Show)

flattenOnce :: S.Statement -> [Either S.Decln S.Statement]
flattenOnce (S.Compound dss _) = dss
flattenOnce s                  = [Right s]

cfgFunctionBody :: S.Id -> S.Statement -> CG (Label,Graph (T.AInsn ()) C C, M.Map Label T.Id)
cfgFunctionBody funName s = do
  (blocks,m) <- blockify funName s
  case blocks of
    [] -> failStmt s "Internal error: blockify returned empty list"
    (StmtBlock {sbLabel=eLabel}:_) ->
      return (eLabel, 
              bodyGraph $ mapFromList $
                 map (\b -> (sbLabel b, sbToB b)) blocks,
              m)
  where
    sbToB :: StmtBlock -> Block (T.AInsn ()) C C
    sbToB (StmtBlock {sbPos, sbLabel, sbBody, sbExit}) = 
      blockJoin (T.AInsn (T.ILabel sbPos sbLabel) ())
                (foldr BCons BNil sbBody)
                sbExit

-- We need to translate lists of statements into blocks.  The toughest part of
-- this is keeping track of control flow.  We translate all C control transfers
-- into IGoto, ICond, and IReturn.  To do this, we need to keep track of some
-- contextual information while we translate a function body.  In particular, we
-- need to know:
--
-- - The current "default" continuation.  That is, if we reach the end of this
--   block without an explicit control transfer, what's next?  At the beginning
--   of a function body, this is just to do a return.  But at other times it is
--   different.  While translating a loop body, we need to know the label
--   corresponding to the beginning of the loop so we can jump back there.
--   While translating a branch of a conditional, we need to know the label
--   corresponding to the block that starts just after the conditional.  Etc.
--
-- - The current "break" continuation, if any.  If we encounter a "break"
--   statement, we should break out of the current control structure to the
--   "next" block.  So, we need to keep track of that next block.
--
-- - Whether the start of this block is also the start of a new local scope in
--   the C source.  The scopes field indicates how many nested lexical scopes we
--   are currently in.
data ControlContext = ControlContext {ccLabel    :: Label,
                                      ccPos      :: S.SPos,
                                      ccDefault  :: T.AInsn () O C,
                                      ccBreak    :: Maybe (T.AInsn () O C)
                                     }
  deriving Show

-- To keep track of parts of the function body, we use a:
type BodyPart = (ControlContext, [Either S.Decln S.Statement])

-- The function body starts off as a one-element [BodyPart], and as we go we
-- break the list down into smaller pieces based on the encountered
-- control-flow.
blockify :: S.Id -> S.Statement -> CG ([StmtBlock],M.Map Label T.Id)
blockify funName funbody = do
  (entry,entryTid) <- freshLocation locName
  peelBlocks [(starterCC entry (S.locStmt funbody),
              flattenOnce funbody)]
             ([],M.singleton entry entryTid)
  where
    S.Id locName _ _ = funName

    starterCC :: Label -> S.SPos -> ControlContext
    starterCC ccLabel ccPos = 
      ControlContext {ccLabel,ccPos,
                      ccDefault = T.AInsn (T.IReturn internal [] Nothing) (),
                      ccBreak = Nothing}

    locEds :: Either S.Decln S.Statement -> S.SPos
    locEds = either S.locDecln S.locStmt

    peelBlocks :: [BodyPart] -> ([StmtBlock], M.Map Label T.Id) 
               -> CG ([StmtBlock], M.Map Label T.Id)
    peelBlocks []       (ss,m) = return $ (reverse ss,m)
    peelBlocks (bp:bps) (ss,m) = do
      (b1,m',remainder) <- amputate bp m []
      peelBlocks (remainder ++ bps) (b1:ss,m')

    amputateExit :: ControlContext -> [T.AInsn () O O] -> T.AInsn () O C 
                 -> M.Map Label T.Id -> [BodyPart]
                 -> CG (StmtBlock, M.Map Label T.Id, [BodyPart])
    amputateExit (ControlContext {ccPos,ccLabel}) acc exit mp bps =
      return $
        (StmtBlock {sbPos = ccPos,
                    sbLabel = ccLabel,
                    sbBody = reverse acc,
                    sbExit = exit},
         mp,bps)

    amputate :: BodyPart -> M.Map Label T.Id -> [T.AInsn () O O] 
             -> CG (StmtBlock, M.Map Label T.Id, [BodyPart])
    amputate (cc,[]) m acc = amputateExit cc acc (ccDefault cc) m []

    -- detect tail calls as a special case:
    amputate (cc,[Right (S.ExpStm (Just (S.FunCall (S.IdExp funName' _) args pos)) _)]) 
            m acc | funName == funName' =
      amputateExit cc acc (T.AInsn (T.ITailCall pos [] args) ()) m []
                             
    amputate (cc,Left d : dss) m acc = amputate (cc,dss) m (T.AInsn (T.IDecl d) () : acc)
    amputate (cc,Right s : dss) m acc =
      case s of
        S.Compound dss' cpos -> do
          -- this could be optimized for the (very common) cases where dss is empty or
          -- acc is empty, to avoid generating extra blocks.
          (blockLabel,blockLoc) <- freshLocation locName
          (afterLabel,afterLoc) <- freshLocation locName
          let 
            bodyCC = ControlContext {
                       ccLabel    = blockLabel,
                       ccPos      = cpos,
                       ccDefault  = T.AInsn (T.IGoto internal [] afterLabel) (),
                       ccBreak    = ccBreak cc
                     }

            afterCC = ControlContext {
                        ccLabel   = afterLabel,
                        ccPos     = internal,   -- XXX check if list is empty and update pos
                        ccDefault = ccDefault cc,
                        ccBreak   = ccBreak cc
                      }
          amputateExit cc acc (T.AInsn (T.IGoto cpos [] blockLabel) ())
                       (M.insert afterLabel afterLoc $
                          M.insert blockLabel blockLoc m)
                       [(bodyCC,dss'),(afterCC,dss)]
        S.ExpStm Nothing _  -> amputate (cc,dss) m acc
        S.ExpStm (Just e) _ -> amputate (cc,dss) m (T.AInsn (T.IExp e) () : acc)
        S.IfStm e sthen mselse spos -> do
          -- "branchExit" is the default exit continuation for the two branches
          -- we're going to create here.  If there are more statements in the
          -- current list, we make a new entry point for them (and a new
          -- corresponding BodyPart).  If not, this is the current default
          -- continuation (except we add a nested scope level).
          (branchExit,afterBlocks,m') <-
            case dss of
              [] -> return (ccDefault cc, [], m)
              (eds:_) -> do
                (afterLabel,afterLoc) <- freshLocation locName
                let pos = locEds eds
                return (T.AInsn (T.IGoto pos [] afterLabel) (),
                        [(ControlContext {
                            ccLabel    = afterLabel,
                            ccPos      = pos,
                            ccDefault  = ccDefault cc,
                            ccBreak    = ccBreak cc
                          },
                          dss)],
                        M.insert afterLabel afterLoc m)
          -- We make labels for the two branches and construct BodyParts for
          -- them.  In the case of a missing "else" branch, the bodypart is
          -- somewhat anemic - all we need is a label to put the current default
          -- continuation at.  But I don't see a much cleaner way to do it immediately.
          (thenLabel,thenLoc) <- freshLocation locName
          (elseLabel,elseLoc) <- freshLocation locName
          let thenBP, elseBP :: BodyPart
              thenBP = (ControlContext {
                          ccLabel    = thenLabel,
                          ccPos      = S.locStmt sthen,
                          ccDefault  = branchExit,
                          ccBreak    = ccBreak cc
                        },
                        flattenOnce sthen)

              elseBP = (ControlContext {
                          ccLabel    = elseLabel,
                          ccPos      = elsePos,
                          ccDefault  = branchExit,
                          ccBreak    = ccBreak cc
                        },
                        elseCode)
          
              (elsePos,elseCode) = 
                case mselse of
                  Nothing    -> (spos,[])
                  Just selse -> (S.locStmt selse, flattenOnce selse)
          amputateExit cc acc (T.AInsn (T.ICond spos [] [] e thenLabel elseLabel) ())
                     (M.insert thenLabel thenLoc (M.insert elseLabel elseLoc m'))
                     ([thenBP, elseBP] ++ afterBlocks)
        S.Switch _ _ _  -> failStmt s "Switch statements unsupported"
        S.Case _ _ _    -> failStmt s "Case statements are not supported"
        S.Default _ _   -> failStmt s "Default statements are not supported"
        S.While _ _ _   -> failStmt s "Internal error: while loop encountered in amputate"
        S.DoWhile _ _ _ -> failStmt s "Internal error: do while loop encountered in amputate"
        S.For (Right Nothing) Nothing Nothing lbody spos -> do
          (loopExit,afterBlocks,m') <-
            case dss of
              [] -> return (ccDefault cc, [], m)
              (eds:_) -> do
                (afterLabel,afterLoc) <- freshLocation locName
                let pos = locEds eds
                return (T.AInsn (T.IGoto pos [] afterLabel) (),
                        [(ControlContext {
                            ccLabel   = afterLabel,
                            ccPos     = pos,
                            ccDefault = ccDefault cc,
                            ccBreak   = ccBreak cc
                          },
                         dss)],
                        M.insert afterLabel afterLoc m)
          -- As a small optimization of the generated code, if we haven't
          -- produced any statements yet in this block we don't start a new
          -- block for the body of the loop.  We can just use the current label.
          (loopLabel,m'') <- 
            case acc of
              []  -> return (ccLabel cc, m')
              _:_ -> do (l,lloc) <- freshLocation locName
                        return (l,M.insert l lloc m')
          let loopBP = (ControlContext {
                          ccLabel   = loopLabel,
                          ccPos     = spos,
                          ccDefault = T.AInsn (T.IGoto spos [] loopLabel) (),
                          ccBreak   = Just loopExit
                        },
                        flattenOnce lbody)

          case acc of
            []  -> do (asb, am, abp) <- amputate loopBP m'' []
                      return (asb, am, abp ++ afterBlocks)
            _:_ -> 
              amputateExit cc acc (T.AInsn (T.IGoto spos [] loopLabel) ()) m''
                         $ [loopBP] ++ afterBlocks
        S.For _ _ _ _ _ -> 
          failStmt s "Internal error: non-trivial for loop encountered in amputate"
        S.Labelled _ _ _ -> failStmt s "Labelled statments are not supported"
        S.Return me sp -> do
          -- XXX here we are throwing an error if dss is non-empty, but when we
          -- add support for goto and labels, it will be necessary to check for
          -- labelled bits after a return.
          when (not $ null dss) (failStmt s "Unsupported: statements after a return")
          amputateExit cc acc (T.AInsn (T.IReturn sp [] me) ()) m []
        S.Break _ -> do
          -- XXX same problem as in return case
          when (not $ null dss) (failStmt s "Unsupported: statements after a break")
          case ccBreak cc of
            Nothing -> failStmt s "Unsupported: break statement outside of a loop"
            Just bexit -> amputateExit cc acc bexit m []
        S.Continue _   -> failStmt s "Continue statements are not supported"
          -- continue is actually a little tricky - it goes to the END of a
          -- loop, and so it interacts with the loop conditions we've already
          -- factored out.
        S.Goto _ _ -> failStmt s "Goto statements are not supported"
        S.Asm _ -> failStmt s "Assembly statements are not supported"
