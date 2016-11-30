{- |
   Module      :  Pretty
   Description :  Pretty Printing for the C-Flat ADT
   Copyright   :  Draper Laboratories
   
   Authors      :  Cody Roux and Chris Casinghino
   
   This generates a string which should be suitable as input for a C compiler
-}


module CodeGen.C.Pretty 
 (emitExp,emitDecln,emitStatement,emitTransUnit,emitExternalDecln,emitId)
where

import CodeGen.C.Syntax
import Text.PrettyPrint hiding (render)
import Data.List (intersperse)
import Data.Char (showLitChar)
import Prelude hiding (id)


ppMaybe :: (a -> Doc) -> Maybe a -> Doc
ppMaybe _ Nothing = empty
ppMaybe f (Just a) = f a

ppId :: Id -> Doc
ppId (Id s _ _)  = text s
ppId (Fixed s) = text s

commas :: [Doc] -> Doc
commas es = cat $ intersperse (comma <> char ' ') es

semis :: [Doc] -> Doc
semis es = cat $ map (\e -> e <> semi <> char ' ') es


ppArgs :: [Doc] -> Doc
ppArgs funArgs = parens $ commas funArgs


ppBaseIntType :: BaseIntType -> Doc
ppBaseIntType Char     = text "char"
ppBaseIntType ShortInt = text "short"
ppBaseIntType Int      = text "int"
ppBaseIntType LongInt  = text "long"

ppIntegralType :: IntegralType -> Doc
ppIntegralType (Signed t)   = text "signed" <+> ppBaseIntType t
ppIntegralType (Unsigned t) = text "unsigned" <+> ppBaseIntType t

ppFloatingType :: FloatingType -> Doc
ppFloatingType Float  = text "float"
ppFloatingType Double = text "double"
ppFloatingType LongDouble = text "long double"


ppField :: (Maybe String, Type, Maybe Integer) -> Doc
ppField (x, ty, msz) = 
  let dec = ppTypeDec ty (ppMaybe text x) in
  case msz of
    Nothing -> dec
    Just i -> dec <+> colon <+> (text $ show i)

ppFields :: Maybe [(Maybe String, Type, Maybe Integer)] -> Doc
ppFields = ppMaybe $ \l -> braces $ semis $ map ppField l

ppEnumField :: (Id, Maybe Exp) -> Doc
ppEnumField (id, Nothing) = ppId id
ppEnumField (id, Just e) = ppId id <+> text "=" <+> ppExp e

ppEnumFields :: Maybe [(Id, Maybe Exp)] -> Doc
ppEnumFields = ppMaybe (\l -> braces $ commas $ map ppEnumField l)


ppTypeDec :: Type -> Doc -> Doc
ppTypeDec (BoolType _)           x = text "_Bool" <+> x
ppTypeDec (VoidType _)           x = text "void" <+> x
ppTypeDec (Integral _ it)        x = ppIntegralType it <+> x
ppTypeDec (Floating _ ft)        x = ppFloatingType ft <+> x
ppTypeDec (PointerType _ t)      x = ppTypeDec t $ text "*" <+> x
ppTypeDec (ArrayType _ t size)   x = ppTypeDec t $ 
                                         x <> (brackets $ ppMaybe (text.show) size)
ppTypeDec (Struct _ name fields) x = text "struct" <+> ppMaybe ppId name <+> ppFields fields <+> x
ppTypeDec (Union _ name fields)  x = text "union" <+> ppMaybe ppId name <+> ppFields fields <+> x
ppTypeDec (Enum _ name fields)   x = text "enum" <+> ppMaybe ppId name <+> ppEnumFields fields <+> x
ppTypeDec (Func _ args _ rty)    x = ppTypeDec rty ( (parens x) <> 
                                     (ppArgs $ map (\(v, tv) -> ppTypeDec tv (ppMaybe ppId v)) args))
ppTypeDec (TypeDef _ id)         x = ppId id <+> x

ppType :: Type -> Doc
ppType t = ppTypeDec t empty


-- ppTypeQual :: TypeQual -> Doc
-- ppTypeQual TQConst = text "const"
-- ppTypeQual TQVolatile = text "volatile"
-- ppTypeQual TQInline = text "inline"

ppConst :: Const -> Doc
ppConst (CharConst c)   = text $ "\'" ++ foldr showLitChar "" c ++ "\'"
ppConst (IntConst i)    = text $ show i
ppConst (FloatConst f)  = text $ f
ppConst (StringConst s) = text $ show s -- XXX is this right?

ppSelOp :: SelOp -> Doc
ppSelOp DirSel   = text "."
ppSelOp IndirSel = text "->"

ppUnaryOp :: UnaryOp -> Doc
ppUnaryOp Address     = text "&"
ppUnaryOp Indirection = text "*"
ppUnaryOp UnaryPlus   = text "+"
ppUnaryOp UnaryMinus  = text "-"
ppUnaryOp BitwiseNot  = text "~"
ppUnaryOp LogicalNot  = text "!"
ppUnaryOp _ = error "Internal error: ppUnaryOp called on inc or dec"

ppBinOp :: BinOp -> Doc
ppBinOp Multiply = text "*"
ppBinOp Divide = text "/"
ppBinOp Modulus = text "%"
ppBinOp Add = text "+"
ppBinOp Subtract = text "-"
ppBinOp LeftShift = text "<<"
ppBinOp RightShift = text ">>"
ppBinOp LessThan = text "<"
ppBinOp GreaterThan = text ">"
ppBinOp LessThanOrEqual = text "<="
ppBinOp GreaterThanOrEqual = text ">="
ppBinOp Equal = text "=="
ppBinOp NotEqual = text "!="
ppBinOp BitwiseAnd = text "&"
ppBinOp BitwiseXor = text "^"
ppBinOp BitwiseOr = text "|"
ppBinOp LogicalAnd = text "&&"
ppBinOp LogicalOr = text "||"

ppExp :: Exp -> Doc
ppExp (CommaExp es _) = commas $ map ppExp es
ppExp (IdExp x _) = ppId x
ppExp (ConstExp c _) = ppConst c
ppExp (Subscript e1 e2 _) = ppExp e1 <> brackets (ppExp e2)
ppExp (FunCall e es _) = ppExp e <> (ppArgs $ map ppExp es)
ppExp (CompSel e op x _) = parens (ppExp e) <> ppSelOp op <> text x
ppExp (Unary PreInc e _) = text "++" <> parens (ppExp e)
ppExp (Unary PreDec e _) = text "--" <> parens (ppExp e)
ppExp (Unary PostInc e _) = parens (ppExp e) <> text "++"
ppExp (Unary PostDec e _) = parens (ppExp e) <> text "--"
ppExp (Unary uop e _) = ppUnaryOp uop <> parens (ppExp e)
ppExp (Bin bop e1 e2 _) = parens (ppExp e1) <> ppBinOp bop <> parens (ppExp e2)
ppExp (SizeOfExp e _) = text "sizeof" <> parens (ppExp e)
ppExp (SizeOfTy t _) = text "sizeof" <> parens (ppType t)
ppExp (Cast t e _) = parens (ppType t) <> parens (ppExp e)
ppExp (Cond e1 e2 e3 _) = parens (ppExp e1) <+> text "?" <+> parens (ppMaybe ppExp e2)
                          <+> text ":" <+> parens (ppExp e3)
ppExp (AssignExp aop e1 e2 _) = ppExp e1 <+> ppAssignOp aop <+> ppExp e2


ppInitializer :: Initializer -> Doc
ppInitializer (SimpleInitializer e) = ppExp e
ppInitializer (ListInitializer ds) = braces $ commas $ map ppDI ds
  where
    ppDI ([],i) = ppInitializer i
    ppDI (desigs,i) = cat (map ppDesig desigs) <+> text "=" <+> ppInitializer i

    ppDesig (ArrDesig e _) = brackets $ ppExp e
    ppDesig (MemberDesig nm _) = text "." <> text nm
 
ppVDecln :: VDecln -> Doc
ppVDecln (VDecln {vdIdent, vdStorage, vdType, vdInit}) =
    ppMaybe ppStorageClass vdStorage <+> ppTypeDec vdType (ppId vdIdent) 
                <+> ppMaybe (\i -> text "=" <+> ppInitializer i) vdInit
      

ppAssignOp :: AssignOp -> Doc
ppAssignOp Assign = text "="
ppAssignOp AddAssign = text "+="
ppAssignOp SubAssign = text "-="
ppAssignOp MulAssign = text "*="
ppAssignOp DivAssign = text "/="
ppAssignOp ModAssign = text "%="
ppAssignOp LeftAssign = text "<<="
ppAssignOp RightAssign = text ">>="
ppAssignOp BitwiseAndAssign = text "&="
ppAssignOp BitwiseXorAssign = text "^="
ppAssignOp BitwiseOrAssign = text "|="


ppDeclnOrStmt :: Either Decln Statement -> Doc
ppDeclnOrStmt (Left d)  = ppDecln d
ppDeclnOrStmt (Right s) = ppStatement s

ppStatement :: Statement -> Doc
ppStatement (Compound sts _) = 
    braces $ vcat $ map ppDeclnOrStmt sts
ppStatement (IfStm e s1 ms2 _) = 
    text "if" <> parens (ppExp e) 
             $$ ppStatement s1 
             $$ ppMaybe (\s2 -> text "else" $$ ppStatement s2) ms2
ppStatement (Switch e s _) =
    text "switch" <+> parens (ppExp e) <+> ppStatement s
ppStatement (While e s _) = text "while" <> parens (ppExp e) $$ ppStatement s
ppStatement (For ds1 e s2 body sp) = 
    text "for" <> parens 
             ((case ds1 of
                Right e1 -> ppMaybe ppExp e1 <> semi
                Left [] -> semi
                Left [d1] -> ppDecln d1
                Left _ -> error $ "Unsupported during pretty printing: for loops with "
                               ++ "multi-variable initializers (at " ++ show sp ++ ").")
              <+> ppMaybe ppExp e <> semi <+> ppMaybe ppExp s2) 
             $$ ppStatement body

ppStatement (Labelled l s _) = ppId l <> text ":" <+> ppStatement s
ppStatement (Return e _) = text "return" <+> ppMaybe ppExp e <> semi
ppStatement (Break _) = text "break" <> semi
ppStatement (DoWhile s e _) = 
    text "do" <+> ppStatement s <+> text "while" <+> parens (ppExp e) <> semi
ppStatement (ExpStm e _) = ppMaybe ppExp e <> semi
ppStatement (Case e s _) = text "case" <+> parens (ppExp e) 
                                       <+> colon
                                       <+> ppStatement s
ppStatement (Default s _) = text "default" <+> colon <+> ppStatement s
ppStatement (Continue _)  = text "continue" <> semi
ppStatement (Goto l _)    = text "goto" <+> ppId l <> semi
ppStatement (Asm _)       = text "<asm>"

ppFDecln :: FDecln -> Doc
ppFDecln (FDecln {funStorage, funName, funArgs, funReturnTy}) =
    ppMaybe ppStorageClass funStorage <+> ppTypeDec funReturnTy (ppId funName) 
                <> (ppArgs $ map (\(x, ty) -> ppTypeDec ty (ppMaybe ppId x)) funArgs)
                                                                                       
ppFunDef :: FunDef -> Doc
ppFunDef (FunDef {decl, funBody}) = ppFDecln decl $$ ppStatement funBody


ppDecln :: Decln -> Doc
ppDecln (FunDecln dec _) = ppFDecln dec <> semi
ppDecln (VarDecln vdec _) = ppVDecln vdec <> semi
ppDecln (TyDef ty id _) = text "typedef" <+> ppTypeDec ty (ppId id) <> semi
ppDecln (StructDecln ty _) = ppType ty <> semi
ppDecln (UnionDecln ty _) = ppType ty <> semi
ppDecln (EnumDecln ty _) = ppType ty <> semi

ppExternalDecln :: ExternalDecln -> Doc
ppExternalDecln (ExtFunDef fdef) = ppFunDef fdef
ppExternalDecln (ExtDecln dec) = ppDecln dec

ppStorageClass :: StorageClass -> Doc
ppStorageClass SCAuto = text "auto"
ppStorageClass SCRegister = text "register"
ppStorageClass SCStatic = text "static"
ppStorageClass SCExtern = text "extern"

ppTransUnit :: TransUnit -> Doc
ppTransUnit (TransUnit exts) = vcat $ map ppExternalDecln exts

genStyle :: Style
genStyle = Style {mode = LeftMode, lineLength = 0, ribbonsPerLine = 0}

render :: Doc -> String
render = renderStyle genStyle

-- Pretty printers for various pieces of the grammar
emitTransUnit :: TransUnit -> String
emitTransUnit = render . ppTransUnit

emitExp :: Exp -> String
emitExp = render . ppExp

emitDecln :: Decln -> String
emitDecln = render . ppDecln

emitStatement :: Statement -> String
emitStatement = render . ppStatement

emitExternalDecln :: ExternalDecln -> String
emitExternalDecln = render . ppExternalDecln

emitId :: Id -> String
emitId = render . ppId
