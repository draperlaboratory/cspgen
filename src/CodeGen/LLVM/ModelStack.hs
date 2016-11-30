{- |

   Module      :  CodeGen.LLVM.ModelStack
   Description :  This module builds the stack model
   
   Author      :  Chris Casinghino
   
-}

module CodeGen.LLVM.ModelStack (buildStack) where

import qualified Language.CSPM.Syntax as T

import CodeGen.LLVM.CGMonad
import CodeGen.LLVM.ModelIdentifiers
import CodeGen.LLVM.ModelBasics

import Data.Maybe (mapMaybe)

{-

XXX

This file contains all the definitions for our stack model.  Many of these
definitions don't actually depend on the particular file we are translating (for
example, the definitions for pushing and popping from the stack).  It would be
_much_ nicer write them directly into CSP files, rather then writing them as
datatypes here.  However, this is a bit tricky - they can't go into our current
"runtime" file because they are _used_ by other definitions that are generated
(like readers and writers for arbitrary locations).  And they can't go before
the generated code because they rely on generated types, like stack addresses.

How to do better?  Two possibilities:

 - Come up with a better story for interleaving hand-written and generated parts
   of our models.
 
 - Build a quasiquoter for CSP.  This would (unfortunately) mean these
   definitions are still generated at cspgen runtime, but at least we wouldn't
   have to write them in this horrible style.

-}


-- buildStack is the top-level call that creates the stack model.  This model is
-- specific to the particular LLVM development in question - for example, to
-- reduce the state space, which values can be stored on the stack depends on
-- which values are actually used by the program.  Thus, it takes a "MemInfo",
-- which summarizes the variable space of the program, as input.
buildStack :: MemInfo -> [T.Definition]
buildStack minfo =
     [maxStackAddrDef,stackTypeDef,
      stackAddrTypeDef, stackValueTypeDef stackTypes,
      pushStackFrameDef, popStackFrameDef,
      pushOnStackDef,stackErrorChans]
  ++ readFromStackDefs
  ++ writeToStackDefs
  ++ stackValueProjectionDefs stackTypes
  where
    -- XXX expect to do something smarter here when I try to reduce the local
    -- state space.  There aren't locals of every type.
    stackTypes :: [TypeInfo]
    stackTypes = map fst $ firstClassMInfo minfo

-- This is just a type synonym
stackTypeDef :: T.Definition
stackTypeDef = T.DVar (T.PId stackType)
                  (T.EApp (T.EId $ T.Fixed "Seq") [T.EId stackValType])

-- XXX make configurable
maxStackAddrDef :: T.Definition
maxStackAddrDef = T.DVar (T.PId maxStackAddr) (T.EConst (T.CInt 50))

----------------------------------------
----- Stack frame manipulation

-- These two have the same type as a translated statement:
--
-- (Stack, StackID, ThreadID,
--    (Stack, StackID, ThreadID, Unit) -> Proc)
-- -> Proc
--
-- They are meant to be invoked at every function call or return.

-- pushStackFrameDef just adds a stack frame boundary and increments the stack
-- pointer.
pushStackFrameDef :: T.Definition
pushStackFrameDef = T.DFun pushStackFrameId
  -- pushStackFrame (st,SAddr.sp,tid,k) =
  --    if sp >= maxStackAddr
  --      then stackOverflowError -> STOP
  --      else k (<StackFrameBoundary>^st, SAddr.(1+sp), tid, Unit)

  [([T.PId st,T.PDot (T.PId stackAddrCon) [T.PId sp], T.PId tid, T.PId k],
    ifNotOverflow sp $
      T.EApp (T.EId k) 
        [T.EListConcat (T.EList [T.EId stackFrameCon]) (T.EId st),
         T.EDot (T.EId stackAddrCon) [T.EBinOp (T.EConst (T.CInt 1))
                                        T.BPlus (T.EId sp)],
         T.EId tid, cspUnit])]
  where
    st,sp,tid,k :: T.Id 
    st  = T.Fixed "st"
    sp  = T.Fixed "sp"
    tid = T.Fixed "tid"
    k   = T.Fixed "k"

-- popStackFrameDef pops everything up to and including the next stack frame
-- boundary, decrementing the pointer appropriately.
popStackFrameDef :: T.Definition
popStackFrameDef = T.DFun popStackFrameId
  -- popStackFrameDef (<>,_,_,_) =
  --   stackUnderflowError                 -> STOP
  -- popStackFrameDef (<stackFrameCon>^st,SAddr.sp,tid,k) =
  --   if sp <= 0 then stackUnderflowError -> STOP
  --              else k (st,SAddr.(sp-1),tid,Unit)
  -- popStackFrameDef (<st1>^st,SAddr.sp,tid,k) =
  --   if sp <= 0 then stackUnderflowError -> STOP
  --              else popStackFrameDef (st,SAddr.(sp-1),tid,k)
  [([T.PList [],T.PId noId,T.PId noId,T.PId noId], underflowAndStop),

   ([T.PConcat (T.PList [T.PId stackFrameCon]) (T.PId st),
     T.PDot (T.PId stackAddrCon) [T.PId sp], T.PId tid, T.PId k],
    ifNotUnderflow sp $
      T.EApp (T.EId k)
        [T.EId st,
         T.EDot (T.EId stackAddrCon)
            [T.EBinOp (T.EId sp) T.BMinus (T.EConst $ T.CInt 1)],
         T.EId tid, cspUnit]),

   ([T.PConcat (T.PList [T.PId st1]) (T.PId st),
     T.PDot (T.PId stackAddrCon) [T.PId sp], T.PId tid, T.PId k],
    ifNotUnderflow sp $
      T.EApp (T.EId popStackFrameId)
        [T.EId st,
         T.EDot (T.EId stackAddrCon)
            [T.EBinOp (T.EId sp) T.BMinus (T.EConst $ T.CInt 1)],
         T.EId tid, T.EId k])
  ]
  where
    st,st1,sp,tid,k :: T.Id
    st  = T.Fixed "st"
    st1 = T.Fixed "st1"
    sp  = T.Fixed "sp"
    tid = T.Fixed "tid"
    k   = T.Fixed "k"

----------------------------------------
----- Stack value manipulation

-- Here we have three functions: pushing new values to the stack, writing to an
-- existing stack address and reading from an existing stack address.


-- pushOnStack is, roughly, the implemenation of alloca.  It pushes the supplied
-- list of values to the stack and provides the address of the last thing pushed
-- to the continuation.
--
-- In CSP:
-- pushOnStack             :: (<StackVal>,Stack,StackPtr,ThreadID,
--                 (Stack,StackPtr,ThreadID,StackPtr) -> Proc)
--                                                    -> Proc
-- pushOnStack (<>,st,SAddr.sp,tid,k) =
--   if sp <= 0
--     then stackUnderFlow                            -> STOP
--     else k (st,SAddr.sp,tid,SAddr.sp-1)
-- pushOnStack (v1^<>,st,SAddr.sp,tid,k) =
--   if sp >= maxStack
--      then stackOverFlow                            -> STOP
--      else k (<v1>^st,SAddr.(1+sp),tid,SAddr.sp)
-- pushOnStack (v1^<vs>,st,SAddr.sp,tid,k) =
--   if sp >= maxStack
--      then stackOverFlow                            -> STOP
--      else pushOnStack (vs,<v1>^st,SAddr.(1+sp),tid,k)
pushOnStackDef             :: T.Definition
pushOnStackDef = T.DFun pushOnStackId
  [([T.PList [], T.PId st, T.PDot (T.PId stackAddrCon) [T.PId sp],
     T.PId tid, T.PId k],
    ifNotUnderflow sp $
      T.EApp (T.EId k)
        [T.EId st, T.EDot (T.EId stackAddrCon) [T.EId sp],T.EId tid,
         T.EDot (T.EId stackAddrCon)
           [T.EBinOp (T.EId sp) T.BMinus (T.EConst $ T.CInt 1)]]),
   ([T.PList [T.PId v1], T.PId st, T.PDot (T.PId stackAddrCon) [T.PId sp],
     T.PId tid, T.PId k],
    ifNotOverflow sp $
      T.EApp (T.EId k)
        [T.EListConcat (T.EList [T.EId v1]) (T.EId st),
         T.EDot (T.EId stackAddrCon) [T.EBinOp (T.EConst $ T.CInt 1) T.BPlus (T.EId sp)],
         T.EId tid, T.EDot (T.EId stackAddrCon) [T.EId sp]]),
   ([T.PConcat (T.PList [T.PId v1]) (T.PId vs),
     T.PId st, T.PDot (T.PId stackAddrCon) [T.PId sp],
     T.PId tid, T.PId k],
    ifNotOverflow sp $
      T.EApp (T.EId pushOnStackId)
        [T.EId vs,
         T.EListConcat (T.EList [T.EId v1]) (T.EId st),
         T.EDot (T.EId stackAddrCon)
                 [T.EBinOp (T.EConst $ T.CInt 1) T.BPlus (T.EId sp)],
         T.EId tid, T.EId k])
  ]
  where
    v1, vs, st, sp, tid, k :: T.Id
    v1         = T.Fixed "v1"
    vs         = T.Fixed "vs"
    st         = T.Fixed "st"
    sp         = T.Fixed "sp"
    tid        = T.Fixed "tid"
    k          = T.Fixed "k"


-- Reads from a stack location, passing the value to the continuation.  The
-- produced value is still in the tagged union type, and must be projected out
-- by the caller.  To recurse down the stack without forgetting everything that
-- comes before, we use a helper (basically, nth).
--
-- data MaybeStackVal             = JustSV StackVal | NothingSV
--
-- maybeStackVal                               :: (a,StackVal                         -> a,MaybeStackVal) -> a
-- maybeStackVal (n,_,NothingSV)  = n
-- maybeStackVal (_,j,JustSV.v)   = j v
--
-- readFromStackHelper                         :: (Int,Stack)                   -> Maybe StackVal
-- readFromStackHelper (_,<>)     = NothingSV
-- readFromStackHelper (0,<v>^_)  = JustSV.v
-- readFromStackHelper (n,<_>^st) = readFromStackHelper(n-1,st)
--
-- The current stack pointer is how many things are in the list right now.  The
-- address of the variable to be read is how many things are after that variable
-- in the list.  Thus, (sp-(addr+1)) is how many elements we must move past on the
-- stack to get what we're looking for.
--
-- readFromStack                               :: (StackAddr,Stack,StackAddr,ThreadId,
--                   (Stack,StackAddr,TheadId,StackVal) -> Proc)
--                                                      -> Proc
-- readFromStack (SAddr.loc, st, SAddr.sp, tid, k) =
--    maybeStackVal(stackUnderflowerror                 -> STOP,
--                  \v @ k (st,SAddr.sp,tid,v),
--                  readFromStackHelper(sp-(loc+1),st))
readFromStackDefs                              :: [T.Definition]
readFromStackDefs =
  [maybeStackValTypeDef,maybeStackValDef,
   readFromStackHelperDef,readFromStackDef]
  where
    maybeStackValTypeId,justSVCon,nothingSVCon :: T.Id
    maybeStackValTypeId           = T.Fixed "MaybeStackVal"
    justSVCon                     = T.Fixed "JustSV"
    nothingSVCon                  = T.Fixed "NothingSV"

    maybeStackValTypeDef :: T.Definition
    maybeStackValTypeDef =
      T.DDataType maybeStackValTypeId
        [(nothingSVCon,[]), (justSVCon,[T.EId stackValType])]

    maybeStackValId :: T.Id
    maybeStackValId = T.Fixed "maybeStackVal"

    maybeStackValDef :: T.Definition
    maybeStackValDef = T.DFun maybeStackValId
      [(map T.PId [n,noId,nothingSVCon],T.EId n),
       ([T.PId noId, T.PId j, T.PDot (T.PId justSVCon) [T.PId v]],
        T.EApp (T.EId j) [T.EId v])]
      where
        n,j,v :: T.Id
        n = T.Fixed "n"
        j = T.Fixed "j"
        v = T.Fixed "v"

    readFromStackHelperId :: T.Id
    readFromStackHelperId = T.Fixed "readFromStackHelper"
    
    readFromStackHelperDef :: T.Definition
    readFromStackHelperDef = T.DFun readFromStackHelperId
      [([T.PId noId, T.PList []],T.EId nothingSVCon),
       ([T.PConst (T.CInt 0), T.PConcat (T.PList [T.PId v]) (T.PId noId)],
        T.EDot (T.EId justSVCon) [T.EId v]),
       ([T.PId n, T.PConcat (T.PList [T.PId noId]) (T.PId st)],
        T.EApp (T.EId readFromStackHelperId)
          [T.EBinOp (T.EId n) T.BMinus (T.EConst $ T.CInt 1), T.EId st])]
      where
        n,v,st :: T.Id
        n = T.Fixed "n"
        v = T.Fixed "v"
        st = T.Fixed "st"

    readFromStackDef :: T.Definition
    readFromStackDef = T.DFun readFromStackId
      [([T.PDot (T.PId stackAddrCon) [T.PId loc], T.PId st,
         T.PDot (T.PId stackAddrCon) [T.PId sp], T.PId tid, T.PId k],
        T.EApp (T.EId maybeStackValId)
          [underflowAndStop,
           T.ELambda [T.PId v] (T.EApp (T.EId k) $
              [T.EId st, T.EDot (T.EId stackAddrCon) [T.EId sp], T.EId tid, T.EId v]),
           T.EApp (T.EId readFromStackHelperId)
               [T.EBinOp (T.EId sp) T.BMinus
                   (T.EBinOp (T.EId loc) T.BPlus (T.EConst $ T.CInt 1)),
                T.EId st]])]
      where
        loc,st,sp,tid,k,v :: T.Id
        loc = T.Fixed "loc"
        st = T.Fixed "st"
        sp = T.Fixed "sp"
        tid = T.Fixed "tid"
        k = T.Fixed "k"
        v = T.Fixed "v"


-- Writes to a stack location, passing the written value to the continuation.
-- The value to write must be provided in the tagged union type, so that's the
-- responsibility of the caller.  Writing is a lot like reading, and has a
-- similar collection of helpers.
--
-- sequenceReverseHelper :: (<a>,<a>) -> <a>
-- sequenceReverseHelper (<>,acc)     = acc
-- sequenceReverseHelper (<x>^xs,acc) = sequenceReverseHelper(xs,<x>^acc)
--
-- sequenceReverse :: (<a>) -> <a>
-- sequenceReverse (xs) = sequenceReverseHelper (xs,<>)
--
-- data MaybeStack = JustS Stack | NothingS
--
-- maybeStack :: (a,Stack -> a,MaybeStack) -> a
-- maybeStack (n,_,NothingS) = n
-- maybeStack (_,j,JustS.v)  = j v
--
-- writeToStackHelper :: (Int,StackVal,Stack,Stack) -> Maybe Stack
-- writeToStackHelper (_,_,_,<>)         = NothingS
-- writeToStackHelper (0,v',st1,<v>^st2) = JustSV.((sequenceReverse(st1))^<v'>^st2)
-- writeToStackHelper (n,v',st1,<v>^st2) =
--   writeToStackHelper (n-1,v',<v>^st1,st2)
--
-- writeToStack :: (StackAddr,StackVal,Stack,StackAddr,ThreadId,
--                   (Stack,StackAddr,TheadId,StackVal) -> Proc)
--               -> Proc
-- writeToStack (SAddr.loc, v, st, SAddr.sp, tid, k) =
--    maybeStackVal(stackUnderflowError -> STOP,
--                  \v @ k (st,SAddr.sp,tid,v),
--                  writeToStackHelper(sp-(loc+1),v,<>,st)) 
writeToStackDefs :: [T.Definition]
writeToStackDefs =
  [sequenceReverseHelperDef,sequenceReverseDef,
   maybeStackTypeDef,maybeStackDef,
   writeToStackHelperDef,writeToStackDef]
  where
    sequenceReverseHelperId, sequenceReverseId :: T.Id
    sequenceReverseHelperId = T.Fixed "sequenceReverseHelper"
    sequenceReverseId = T.Fixed "sequenceReverse"

    sequenceReverseHelperDef :: T.Definition
    sequenceReverseHelperDef = T.DFun sequenceReverseHelperId
      [([T.PList [],T.PId acc], T.EId acc),
       ([T.PConcat (T.PList [T.PId x]) (T.PId xs), T.PId acc],
        T.EApp (T.EId sequenceReverseHelperId)
           [T.EId xs,T.EListConcat (T.EList [T.EId x]) (T.EId acc)])
      ]
      where
        acc,x,xs :: T.Id
        acc = T.Fixed "acc"
        x = T.Fixed "x"
        xs = T.Fixed "xs"

    sequenceReverseDef :: T.Definition
    sequenceReverseDef = T.DFun sequenceReverseId
      [([T.PId xs],
        T.EApp (T.EId sequenceReverseHelperId) [T.EId xs,T.EList []])
      ]
      where
        xs :: T.Id
        xs = T.Fixed "xs"
    
    maybeStackTypeId,justSCon,nothingSCon :: T.Id
    maybeStackTypeId = T.Fixed "MaybeStack"
    justSCon         = T.Fixed "JustS"
    nothingSCon      = T.Fixed "NothingS"

    maybeStackTypeDef :: T.Definition
    maybeStackTypeDef =
      T.DDataType maybeStackTypeId
        [(nothingSCon,[]), (justSCon,[T.EId stackType])]

    maybeStackId :: T.Id
    maybeStackId = T.Fixed "maybeStack"

    maybeStackDef :: T.Definition
    maybeStackDef = T.DFun maybeStackId
      [(map T.PId [n,noId,nothingSCon],T.EId n),
       ([T.PId noId, T.PId j, T.PDot (T.PId justSCon) [T.PId v]],
        T.EApp (T.EId j) [T.EId v])]
      where
        n,j,v :: T.Id
        n = T.Fixed "n"
        j = T.Fixed "j"
        v = T.Fixed "v"

    writeToStackHelperId :: T.Id
    writeToStackHelperId = T.Fixed "writeToStackHelper"

    writeToStackHelperDef :: T.Definition
    writeToStackHelperDef = T.DFun writeToStackHelperId
      [([T.PId noId, T.PId noId, T.PId noId, T.PList []],
        T.EId nothingSCon),
       ([T.PConst (T.CInt 0), T.PId v', T.PId st1,
         T.PConcat (T.PList [T.PId v]) (T.PId st2)],
        T.EDot (T.EId justSCon)
          [T.EListConcat (T.EApp (T.EId sequenceReverseId) [T.EId st1])
             (T.EListConcat (T.EList [T.EId v']) (T.EId st2))]),
       ([T.PId n, T.PId v', T.PId st1,
         T.PConcat (T.PList [T.PId v]) (T.PId st2)],
        T.EApp (T.EId writeToStackHelperId)
          [T.EBinOp (T.EId n) T.BMinus (T.EConst $ T.CInt 1),
           T.EId v', T.EListConcat (T.EList [T.EId v]) (T.EId st1),
           T.EId st2])]
      where
        n,v,v',st1,st2 :: T.Id
        n = T.Fixed "n"
        v = T.Fixed "v"
        v' = T.Fixed "v'"
        st1 = T.Fixed "st1"
        st2 = T.Fixed "st2"
        
    writeToStackDef :: T.Definition
    writeToStackDef = T.DFun writeToStackId
      [([T.PDot (T.PId stackAddrCon) [T.PId loc], T.PId v, T.PId st,
         T.PDot (T.PId stackAddrCon) [T.PId sp], T.PId tid, T.PId k],
        T.EApp (T.EId maybeStackId)
          [underflowAndStop,
           T.ELambda [T.PId st']
              (T.EApp (T.EId k) $
                 [T.EId st', T.EDot (T.EId stackAddrCon) [T.EId sp],
                  T.EId tid, T.EId v]),
           T.EApp (T.EId writeToStackHelperId)
             [T.EBinOp (T.EId sp) T.BMinus
                (T.EBinOp (T.EId loc) T.BPlus (T.EConst $ T.CInt 1)),
              T.EId v,
              T.EList [],
              T.EId st]])]
      where
        loc,v,st,st',sp,tid,k :: T.Id
        loc = T.Fixed "loc"
        v = T.Fixed "v"
        st = T.Fixed "st"
        st' = T.Fixed "st'"
        sp = T.Fixed "sp"
        tid = T.Fixed "tid"
        k = T.Fixed "k"

----------------------------------------
----- Data type representations

-- The type of values that go on the stack.  A tagged union of all the
-- first-class value types.
stackValueTypeDef :: [TypeInfo] -> T.Definition
stackValueTypeDef types =
  T.DDataType stackValType $
      (stackFrameCon,[])
    : mapMaybe svCon types
  where
    svCon :: TypeInfo -> Maybe (T.Id,[T.Exp])
    svCon (TypeInfo {tiDataInfo}) =
      case tiDataInfo of
        DIFirstClass fci -> Just (fciStackValTag fci,[T.EId $ fciRepType fci])
        _ -> Nothing

-- "Stack address" representation
stackAddrTypeDef :: T.Definition
stackAddrTypeDef =
  T.DDataType stackAddrType
              [(stackAddrCon,[T.ESetFromTo (T.EConst (T.CInt 0))
                                           (T.EId maxStackAddr)])]

-- Projections from the stackValue type.  We build one of these for
-- each first-class type.  It might error, so it must be a proc.
--
-- For a particular type Foo, we have:
--
-- fooStackProj :: (StackValue,Stack,StackAddr,ThreadId,
--                  (Stack,StackAddr,ThreadId,FooTyp) -> Proc)
--              -> Proc
-- fooStackProj (FooTag.v,st,sp,tid,k) = k (st,sp,tid,v)
-- fooStackProj (_,_,_,_,_) = stackMisprojectionERROR -> STOP
stackValueProjectionDefs :: [TypeInfo] -> [T.Definition]
stackValueProjectionDefs tis = mapMaybe svProj tis
  where
    svProj :: TypeInfo -> Maybe T.Definition
    svProj (TypeInfo {tiDataInfo=DIFirstClass fci}) = Just $
      T.DFun (fciStackValProj fci)
        [([T.PDot (T.PId $ fciStackValTag fci) [T.PId v],
           T.PId st, T.PId sp, T.PId tid, T.PId k],
          T.EApp (T.EId k) $ map T.EId [st, sp, tid, v]),
         (map T.PId (replicate 5 noId),
          T.EPrefix (T.EId stackMisprojErrorId) [] (T.EConst T.CStop))]
    svProj (TypeInfo {tiDataInfo=_}) = Nothing

    v,st,sp,tid,k :: T.Id
    v = T.Fixed "v"
    st = T.Fixed "st"
    sp = T.Fixed "sp"
    tid = T.Fixed "tid"
    k = T.Fixed "k"

----------------------------------------
----- Stack manipulation errors

stackErrorChans :: T.Definition
stackErrorChans = T.DChan [stackUnderflowErrorId,
                           stackOverflowErrorId,
                           stackMisprojErrorId]
                          []

-----------------------------------------
----- Helpers

-- A couple common idioms - checking for stack underflow or overflow.  Both take
-- the name of the stack pointer and an expression indicating what to do if no
-- problem is detected.  They check whether an underflow/overflow would occur in
-- when the stack pointer is decremented/incremented.
underflowAndStop :: T.Exp
underflowAndStop = T.EPrefix (T.EId stackUnderflowErrorId) [] (T.EConst T.CStop)

ifNotUnderflow :: T.Id -> T.Exp -> T.Exp
ifNotUnderflow sp e =
  T.EIfThenElse (T.EBinOp (T.EId sp) T.BLeq (T.EConst $ T.CInt 0))
    underflowAndStop e

overflowAndStop :: T.Exp
overflowAndStop = T.EPrefix (T.EId stackOverflowErrorId) [] (T.EConst T.CStop)

ifNotOverflow :: T.Id -> T.Exp -> T.Exp
ifNotOverflow sp e = 
  T.EIfThenElse (T.EBinOp (T.EId sp) T.BGeq (T.EId maxStackAddr))
    overflowAndStop e
