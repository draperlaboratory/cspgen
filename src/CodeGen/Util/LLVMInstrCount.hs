module LLVMInstrCount where 
{-
  This module provides a simple llvm function counter. The number of instructions in the target llvm source file is returned along with a list of the named instructions used.
-}
import qualified LLVM.General as L
import qualified LLVM.General.Context as L
import qualified LLVM.General.AST as LA
import qualified LLVM.General.Diagnostic as Diag


import System.Console.GetOpt
import System.Environment
import Control.Monad.Except
import Data.List(nub, intersperse, sort, group, unzip4,sortBy)
import Data.Function(on)

data Options = Options { optNoisy  :: Bool }
data StatInfo = StatInfo  { llName     :: String,
                            instrCount :: Int,
                            llInstrs   :: [String],
                            llTerms    :: [String]
                          }

defaultOpts :: Options 
defaultOpts = Options { optNoisy = False }


-- A list of options consisting of:
-- * a short name
-- * a long name
-- * an options transformer
-- * a short description of the option
optionList :: [(Char, String, ArgDescr (Options -> Options), String)]
optionList = [('n', "noisy-output", NoArg (\o -> o {optNoisy=True}), 
                "Writes output to standard out instead of output file")
             ]

options :: [OptDescr (Options -> Options)]
options = map (\(a,b,c,d) -> Option [a] [b] c d) optionList

main :: IO ()
main = do 
  argv <- getArgs
  case getOpt Permute options argv of 
    (opts, ifiles, []) -> do
      let Options {optNoisy} = foldl (\o f -> f o) defaultOpts opts
      multiFileCounter optNoisy ifiles
    (_, _, errs) -> error $ usage errs
  where
    header = "Usage: LLVMInstrCount [OPTIONS] FILE(s)"
    usage errs = concat errs ++ "\n" ++ usageInfo header options

multiFileCounter :: Bool -> [String] -> IO ()
multiFileCounter noisy fileList = do
  infoList <- mapM fileInstrCounter fileList
  let summary = summarize infoList
      detailed = map fileInfoString infoList
      output = concat $ intersperse "-------------------\n" (summary : detailed)
  case noisy of 
    True -> putStrLn output 
    False -> writeFile "instrCounter.analysis" output

fileInfoString :: StatInfo -> String
fileInfoString (StatInfo {llName=name,instrCount=num,llInstrs=is,llTerms=ts}) = 
  (concat $ intersperse "\n" stringList) ++ "\n"
  where 
    modName = "Module Name: " ++ name
    modCount = "Number of instructions " ++ (show num)
    modInstrs = "List of instructions used (with frequency): " : (showStats is)
    modTerm = "Terminator used: " : (showStats ts)
    stringList = (modName : modCount : modInstrs) ++ modTerm

summarize :: [StatInfo] -> String
summarize [] = ""
summarize list = (concat $ intersperse "\n" outStrings) ++ "\n"
  where 
    total = sum $ map (\si -> instrCount si) list
    totalString = "Number of instructions " ++ (show total)
    instrStats = showStats $ concat $ map (\si -> llInstrs si) list
    termStats = showStats $ concat $ map (\si -> llTerms si) list
    iHeadString = "List of instructions used (with frequency): "
    iTermString = "List of terminators used (with frequency): "
    outStrings = 
      (totalString : iHeadString : instrStats) ++ (iTermString : termStats) 

fileInstrCounter :: String -> IO StatInfo
fileInstrCounter filename = do
  result <-
    liftIO $ L.withContext $ \c ->
      runExceptT $ L.withModuleFromLLVMAssembly c file processModule
  output <-
    case result of 
      Left (Left s)  -> return StatInfo { llName=filename, instrCount=0,
                                          llInstrs=[s], llTerms=[] 
                                        }
      Left (Right d) -> return StatInfo { llName=filename, instrCount=0,
                                          llInstrs=[Diag.diagnosticDisplay d], 
                                          llTerms=[]
                                        }
      Right o        -> return o
  return output
  where
    file = L.File filename

processModule :: L.Module -> IO StatInfo
processModule lm = do
  lam <- L.moduleAST lm
  let laDefs = LA.moduleDefinitions lam
      sInfo = combineInfo $ map getDefCount laDefs
      modName :: String
      modName = LA.moduleName lam
  return StatInfo { llName=modName, instrCount=instrCount sInfo, 
                    llInstrs=llInstrs sInfo, llTerms=llTerms sInfo
                  }

  
-- Converts a list of StatInfos into a single StatInfo
combineInfo :: [StatInfo] -> StatInfo
combineInfo [] = StatInfo {llName="",instrCount=0,llInstrs=[],llTerms=[]}
combineInfo xs = 
  StatInfo { llName="", instrCount=sum getNum, 
             llInstrs=concat getInstrs, llTerms=concat getTerms 
           }
  where 
    getNum = map (\si -> instrCount si) xs
    getInstrs = map (\si -> llInstrs si) xs
    getTerms = map (\si -> llTerms si) xs

-- Accepts a list of strings and returns another list of strings representing
-- the each unique string and its frequency
showStats :: [String] -> [String]
showStats names = 
  map (\(string,int) -> string ++ " (" ++ (show int) ++ ")") $ list
  where 
    list = reverse $ sortBy (compare `on` snd) $ getStats names 

-- Accepts a list of strings and returns a list of pairs representing each
-- unique string and its frequency
getStats :: [String] -> [(String,Int)]
getStats [] = []
getStats xs = map (\list@(x:xs) -> (x,length list)) $ group $ sort xs

getDefCount :: LA.Definition -> StatInfo
getDefCount (LA.GlobalDefinition globDef) = getGlobCount globDef
getDefCount _ = StatInfo {llName="", instrCount=0, llInstrs=[], llTerms=[]}

getGlobCount :: LA.Global -> StatInfo
getGlobCount (LA.Function _ _ _ _ _ _ _ _ _ _ _ bblocks) = 
  combineInfo $ map getBlockCount bblocks
getGlobCount _ = StatInfo{llName="", instrCount=0, llInstrs=[], llTerms=[]}

getBlockCount :: LA.BasicBlock -> StatInfo
getBlockCount (LA.BasicBlock _ nis term) = 
  StatInfo{ llName="", instrCount=length nis, 
            llInstrs=getInstrNames nis,llTerms=[getTermName term] 
          }

getInstrNames :: [LA.Named LA.Instruction]  -> [String]
getInstrNames [] = []
getInstrNames (((LA.Name name) LA.:= _):nis) = name:(getInstrNames nis)
getInstrNames (((LA.UnName _ ) LA.:= instr):nis) = 
  (getInstrString instr):(getInstrNames nis)
getInstrNames ((LA.Do instr):nis) = (getInstrString instr):(getInstrNames nis)

getTermName :: LA.Named LA.Terminator -> String
getTermName ((LA.Name name) LA.:= _) = name
getTermName ((LA.UnName _ ) LA.:= term) = getTermString term
getTermName (LA.Do term) = getTermString term

getInstrString :: LA.Instruction -> String
getInstrString (LA.Add _ _ _ _ _) = "add"
getInstrString (LA.FAdd _ _ _ _) = "fadd"
getInstrString (LA.Sub _ _ _ _ _)= "sub"
getInstrString (LA.FSub _ _ _ _) = "fsub"
getInstrString (LA.Mul _ _ _ _ _) = "mul"
getInstrString (LA.FMul _ _ _ _) = "fmul"
getInstrString (LA.UDiv _ _ _ _) = "udiv"
getInstrString (LA.SDiv _ _ _ _) = "sdiv"
getInstrString (LA.FDiv _ _ _ _) = "fdiv"
getInstrString (LA.URem _ _ _) = "urem"
getInstrString (LA.SRem _ _ _) = "srem"
getInstrString (LA.FRem _ _ _ _) = "frem"
getInstrString (LA.Shl _ _ _ _ _) = "shl"
getInstrString (LA.LShr _ _ _ _) = "lshr"
getInstrString (LA.AShr _ _ _ _) = "ashr"
getInstrString (LA.And _ _ _) = "and"
getInstrString (LA.Or _ _ _) = "or"
getInstrString (LA.Xor _ _ _) = "xor"
getInstrString (LA.Alloca _ _ _ _) = "alloca"
getInstrString (LA.Load _ _ _ _ _) = "load"
getInstrString (LA.Store _ _ _ _ _ _) = "store"
getInstrString (LA.GetElementPtr _ _ _ _) = "getElementPtr"
getInstrString (LA.Fence _ _) = "fence"
getInstrString (LA.CmpXchg _ _ _ _ _ _) = "cmpXchg"
getInstrString (LA.AtomicRMW _ _ _ _ _ _) = "atomicRMW"
getInstrString (LA.Trunc _ _ _) = "trunc"
getInstrString (LA.ZExt _ _ _) = "zext"
getInstrString (LA.SExt _ _ _) = "sext"
getInstrString (LA.FPToUI _ _ _) = "fptoui"
getInstrString (LA.FPToSI _ _ _) = "fptosi"
getInstrString (LA.UIToFP _ _ _) = "uitofp"
getInstrString (LA.SIToFP _ _ _) = "sitofp"
getInstrString (LA.FPTrunc _ _ _) = "fptrunc"
getInstrString (LA.FPExt _ _ _) = "fprext"
getInstrString (LA.PtrToInt _ _ _) = "ptrToInt"
getInstrString (LA.IntToPtr _ _ _) = "intToPtr"
getInstrString (LA.BitCast _ _ _) = "bitcast"
getInstrString (LA.AddrSpaceCast _ _ _) = "autoSpaceCast"
getInstrString (LA.ICmp _ _ _ _) = "icmp"
getInstrString (LA.FCmp _ _ _ _) = "fcmp"
getInstrString (LA.Phi _ _ _) = "phi"
getInstrString (LA.Call _ _ _ _ _ _ _) = "call"
getInstrString (LA.Select _ _ _ _) = "select"
getInstrString (LA.VAArg _ _ _) = "vaarg"
getInstrString (LA.ExtractElement _ _ _) = "extractElement"
getInstrString (LA.InsertElement _ _ _ _) = "insertElement"
getInstrString (LA.ShuffleVector _ _ _ _) = "shuffleVector"
getInstrString (LA.ExtractValue _ _ _) = "extractValue"
getInstrString (LA.InsertValue _ _ _ _) = "insertValue"
getInstrString (LA.LandingPad _ _ _ _ _) = "landingPad"

getTermString :: LA.Terminator -> String
getTermString (LA.Ret _ _) = "ret"
getTermString (LA.CondBr _ _ _ _) = "condBr"
getTermString (LA.Br _ _ ) = "br"
getTermString (LA.Switch _ _ _ _) = "switch"
getTermString (LA.IndirectBr _ _ _) = "indirectBr"
getTermString (LA.Invoke _ _ _ _ _ _ _ _) = "invoke"
getTermString (LA.Resume _ _) = "resume"
getTermString (LA.Unreachable _) = "unreachable"
