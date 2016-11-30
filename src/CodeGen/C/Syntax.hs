{- |
Module      :  CodeGen.C.Syntax
Description :  ADT for CCN
Copyright   :  Draper Laboratories

Authors     :  Chris Casinghino and Cody Roux

Abstract Data Type for C

-}

module CodeGen.C.Syntax
where

data SPos = SPos {sourceName :: String,
                  sourceLine :: !Int,
                  sourceColumn :: !Int}

initialPos :: String -> SPos
initialPos sourceName = SPos {sourceName,
                              sourceLine = 0,
                              sourceColumn = 0}

-- cribbed from parsec
instance Show SPos where
  show (SPos {sourceName,sourceLine,sourceColumn}) =
    (if null sourceName then "" else "\"" ++ sourceName ++ "\"") ++ showLineColumn
    where
      showLineColumn = "(line " ++ show sourceLine ++ ", column "
                    ++ show sourceColumn ++ ")"

instance Eq SPos where
    _ == _ = True

instance Ord SPos where
    compare _ _ = EQ

-- | Identifiers.
data VarScope = VSLocal | VSGlobal
  deriving Show

data Id = Id String VarScope Int
        | Fixed String
  deriving (Show)

instance Eq Id where
  Id _ _ i1  == Id _ _ i2  = i1 == i2
  Fixed s1 == Fixed s2 = s1 == s2
  _ == _               = False

instance Ord Id where
  compare (Id _ _ i1) (Id _ _ i2)  = compare i1 i2
  compare (Fixed s1) (Fixed s2) = compare s1 s2
  compare (Id _ _ _) (Fixed _) = LT
  compare (Fixed _) (Id _ _ _) = GT

stringPart :: Id -> String
stringPart (Id s _ _)  = s
stringPart (Fixed s) = s

isLocal :: Id -> Bool
isLocal (Id _ VSLocal _)  = True
isLocal (Id _ VSGlobal _) = False
isLocal (Fixed _)         = False

isGlobal :: Id -> Bool
isGlobal (Id _ VSLocal _)  = False
isGlobal (Id _ VSGlobal _) = True
isGlobal (Fixed _)         = True


-- | Integral types
data BaseIntType = Char | ShortInt | Int | LongInt
                   deriving (Show, Eq)

data IntegralType = Signed BaseIntType | Unsigned BaseIntType
                    deriving (Show, Eq)

-- | Floating-point types
data FloatingType = Float | Double | LongDouble
                    deriving (Show, Eq)

type StructFields = [(Maybe String, Type, Maybe Integer)]

data Type = VoidType SPos
          | Integral SPos IntegralType
          | BoolType SPos
          | Floating SPos FloatingType
          | PointerType SPos Type
          | ArrayType SPos Type (Maybe Integer)
          | Struct SPos (Maybe Id) (Maybe StructFields)
          | Union SPos (Maybe Id) (Maybe StructFields)
          | Enum SPos (Maybe Id) (Maybe [(Id, Maybe Exp)])
          | Func SPos [(Maybe Id,Type)] Bool Type
          | TypeDef SPos Id
            deriving (Show, Eq)

data TypeQual = TQConst | TQVolatile | TQInline

-- | The type of C-flat constants. These are restricted to integers, floats, characters and strings.
data Const = CharConst [Prelude.Char] | IntConst Integer | FloatConst String
           | StringConst String
             deriving (Show, Eq)

-- | Selection operators; DirSel corresponds to the dot notation, IndirSel to arrow.
data SelOp = DirSel | IndirSel
           deriving (Show, Eq)

-- | Unary operators.
data UnaryOp = Address | Indirection | UnaryPlus | UnaryMinus | BitwiseNot | LogicalNot
             | PreInc | PreDec | PostInc | PostDec
               deriving (Show, Eq)

-- | Binary operators.
data BinOp = Multiply | Divide | Modulus
           | Add | Subtract
           | LeftShift | RightShift
           | LessThan | GreaterThan | LessThanOrEqual | GreaterThanOrEqual | Equal | NotEqual
           | BitwiseAnd | BitwiseXor | BitwiseOr
           | LogicalAnd | LogicalOr
             deriving (Show, Eq)

data Exp = CommaExp [Exp] SPos
         | IdExp Id SPos
         | ConstExp Const SPos
         | AssignExp AssignOp Exp Exp SPos
         | Subscript Exp Exp SPos
         | FunCall Exp [Exp] SPos
         | CompSel Exp SelOp String SPos
         | Unary UnaryOp Exp SPos
         | Bin BinOp Exp Exp SPos
         | SizeOfExp Exp SPos
         | SizeOfTy Type SPos
         | Cast Type Exp SPos
         | Cond Exp (Maybe Exp) Exp SPos
           deriving (Show, Eq)


-- | Optional initializers for variable declarations.
data Initializer = SimpleInitializer Exp 
                 | ListInitializer [([InitDesignator],Initializer)]
                   deriving (Show, Eq)

data InitDesignator = ArrDesig Exp SPos
                    | MemberDesig String SPos
                    deriving (Show,Eq)


-- | Assignement operators.
data AssignOp = Assign
              | AddAssign | SubAssign
              | MulAssign | DivAssign | ModAssign
              | LeftAssign | RightAssign
              | BitwiseAndAssign | BitwiseXorAssign | BitwiseOrAssign
                deriving (Show, Eq)

-- | Statements
-- 
-- Assembly statements are thrown away, but we record where they occur with
-- the "Asm" statement.  This lets us parse files that involve assembly and
-- throw an error later, during code generation, if the assembly is
-- encountered.  In practice, these statements usually occur in definition
-- from headers that are never used, and are therefore thrown away during
-- hedge trimming.
data Statement = Compound [Either Decln Statement] SPos
               | ExpStm (Maybe Exp) SPos
               | IfStm Exp Statement (Maybe Statement) SPos 
               | Switch Exp Statement SPos
               | Case Exp Statement SPos
               | Default Statement SPos
               | While Exp Statement SPos 
               | DoWhile Statement Exp SPos
               | For (Either [Decln] (Maybe Exp)) (Maybe Exp) (Maybe Exp)
                     Statement SPos
               | Labelled Id Statement SPos
               | Return (Maybe Exp) SPos
               | Break SPos
               | Continue SPos
               | Goto Id SPos
               | Asm SPos
                 deriving (Show, Eq)

-- | Variable declarations.
data VDecln = VDecln { vdIdent :: Id,
                       vdStorage :: Maybe StorageClass,
                       vdType :: Type,
                       vdInit :: Maybe Initializer
                     }
             deriving (Show, Eq)

-- | Function declarations.
data FDecln = FDecln { funStorage  :: Maybe StorageClass,
                       funName     :: Id,
                       funArgs     :: [(Maybe Id, Type)],
                       funVariadic :: Bool,
                       funReturnTy :: Type,
                       funPos      :: SPos
                     }
              deriving (Show, Eq)

-- | Function definitions.
data FunDef = FunDef { decl :: FDecln,
                       funBody :: Statement,
                       fdPos :: SPos
                     }
              deriving (Show, Eq)

-- | Top-level function definitions. May or may not contain a function body, depending
-- on whether the declaration is a forward declaration
data Decln = FunDecln FDecln SPos
           | VarDecln VDecln SPos
           | TyDef Type Id SPos
           -- Invariant : the type must be a struct declaration
           | StructDecln Type SPos
           -- Invariant : the type must be a union declaration
           | UnionDecln Type SPos
           -- Invariant : the type must be an enumeration
           | EnumDecln Type SPos
           deriving (Show, Eq)

data ExternalDecln = ExtFunDef FunDef
                   | ExtDecln Decln
                   deriving (Show, Eq)

data StorageClass = SCAuto | SCRegister | SCStatic | SCExtern
     deriving (Show,Eq)

-- | A C-flat file is made of a translation unit, which is just
-- a list of external declarations
data TransUnit = TransUnit { exts :: [ExternalDecln] }
               deriving (Show, Eq)

-- | Get location information

locDecln :: Decln -> SPos
locDecln (FunDecln _ sp)    = sp
locDecln (VarDecln _ sp)    = sp
locDecln (TyDef _ _ sp)     = sp
locDecln (StructDecln _ sp) = sp
locDecln (UnionDecln _ sp)  = sp
locDecln (EnumDecln _ sp)   = sp

locStmt :: Statement -> SPos
locStmt (Compound _ sp)   = sp
locStmt (IfStm _ _ _ sp)  = sp
locStmt (Switch _ _ sp)   = sp
locStmt (While _ _ sp)    = sp
locStmt (DoWhile _ _ sp)  = sp
locStmt (For _ _ _ _ sp)  = sp
locStmt (Labelled _ _ sp) = sp
locStmt (Return _ sp)     = sp
locStmt (Break sp)        = sp
locStmt (Continue sp)     = sp
locStmt (Goto _ sp)       = sp
locStmt (ExpStm _ sp)     = sp
locStmt (Case _ _ sp)     = sp
locStmt (Default _ sp)    = sp
locStmt (Asm sp)          = sp

locExp :: Exp -> SPos
locExp (CommaExp _ sp)      = sp
locExp (IdExp _ sp)         = sp
locExp (ConstExp _ sp)      = sp
locExp (Subscript _ _ sp)   = sp
locExp (FunCall _ _ sp)     = sp
locExp (CompSel _ _ _ sp)   = sp
locExp (Unary _ _ sp)       = sp
locExp (Bin _ _ _ sp)       = sp
locExp (SizeOfExp _ sp)     = sp
locExp (SizeOfTy _ sp)      = sp
locExp (Cast _ _ sp)        = sp
locExp (Cond _ _ _ sp)      = sp
locExp (AssignExp _ _ _ sp) = sp

locExternal :: ExternalDecln -> SPos
locExternal (ExtFunDef (FunDef {fdPos})) = fdPos
locExternal (ExtDecln d) = locDecln d

locType :: Type -> SPos
locType (BoolType sp) = sp
locType (VoidType sp) = sp
locType (Integral sp _) = sp
locType (Floating sp _) = sp
locType (PointerType sp _) = sp
locType (ArrayType sp _ _) = sp
locType (Struct sp _ _) = sp
locType (Union sp _ _) = sp
locType (Enum sp _ _) = sp
locType (Func sp _ _ _) = sp
locType (TypeDef sp _) = sp
