-- | print out data structures
-- for better understanding what is going on
module CodeGen.IL.Dump
  ( printEnv, printBinds )
where

import Prelude.Compat
import Data.Text (Text)
import qualified Data.Text as T
import Data.Monoid ((<>))
import qualified Data.Map as M

import Language.PureScript.Environment
import Language.PureScript.CoreFn
import Language.PureScript.Types 
import Language.PureScript.PSString (PSString, mkString, prettyPrintString)
import Language.PureScript.Names

printType :: SourceType -> Text
printType (TUnknown _ i) = "TUnknown " 
printType (TypeVar _ t) = "TypeVar " <> t
printType (TypeLevelString _ t) = "TypeLevelString" <> prettyPrintString t
printType (TypeWildcard _ (Just t)) = "TypeWildcard (" <> t <> ")"
printType (TypeWildcard _ Nothing) = "TypeWildcard Nothing"
printType (TypeConstructor _ c) = "TypeConstructor (" <> showQualified runProperName c <>")"  
printType (TypeOp _ _) = "TypeOp"
printType (TypeApp _ t1 t2 ) = "TypeApp (" <> printType t1 <> "," <> printType t2 <> ")"
printType (ForAll _ _ _ _) = "Forall"
printType (ConstrainedType _ _ _) = "ConstrainedType"
printType (Skolem _ _ _ _) ="Skolem"
printType (REmpty _) = "REmpty"
printType (RCons _ _ _ _) = "RCons"
printType (KindedType _ _ _) = "KindedType"
printType (BinaryNoParensType _ _ _ _) = "BinaryNoParensType"
printType (ParensInType _ _) = "ParensInType"

printEnv :: Environment -> Text
printEnv (Environment names _ _ _ _ _ _) =
  M.foldrWithKey (\k (st,_,_) t -> t <> (showQualified runIdent k) <> ":" <> printType st <> "\n") "" names  

printBinder :: (Binder a) -> Text
printBinder (NullBinder _) = "NullBinder"
printBinder (LiteralBinder _ l) = "LiteralBinder(" <> printLiteralBinder l <> ")"
printBinder (VarBinder _ id) = "VarBinder(" <> showIdent id <> ")"
printBinder (ConstructorBinder _ tn cn bs) =
  "ConstructorBinder("
  <> showQualified runProperName tn
  <> showQualified runProperName cn
  <> T.intercalate "," ( map printBinder bs)
  <> ")"
printBinder (NamedBinder _ id b) = "NamedBinder(" <> showIdent id <> "," <> printBinder b <> ")"

printLiteralBinder :: Literal (Binder a) -> Text
printLiteralBinder (StringLiteral str) = prettyPrintString str
printLiteralBinder (CharLiteral c) = T.pack (show c)
printLiteralBinder (NumericLiteral num) = either (T.pack . show) (T.pack . show) num
printLiteralBinder (BooleanLiteral True) = "true"
printLiteralBinder (BooleanLiteral False) = "false"
printLiteralBinder (ObjectLiteral bs) =
  "{ "
  <> T.intercalate ", " (map printObjectPropertyBinder bs)
  <> " }"
  where
  printObjectPropertyBinder :: (PSString, Binder a) -> Text
  printObjectPropertyBinder (key, binder) = prettyPrintString key <> ": " <> printBinder binder
printLiteralBinder (ArrayLiteral bs) =
  "[ "
  <> T.intercalate ", " (map printBinder bs)
  <> " ]"


printExpr :: Expr a -> Text
printExpr (Literal _ l) = printLiteralExpr l
printExpr (Constructor _ tn cn ids) =
  "Constructor("
  <> runProperName tn
  <> runProperName cn
  <> T.intercalate "," ( map showIdent ids)
  <> ")"
printExpr (Accessor _ ps e) = "Accessor(" <> prettyPrintString ps <> "," <> printExpr e <> ")"
printExpr (ObjectUpdate _ e xs)
  = "ObjectUpdate(" <> printExpr e <> ",["
    <> T.intercalate "," ( map (\(s,e)->"(" <> prettyPrintString s <> "," <> printExpr e <> ")") xs)
    <> "])"
printExpr (Abs _ id e) = "Abs(" <> showIdent id <> "," <> printExpr e <> ")"
printExpr (App _ e1 e2) = "App(" <> printExpr e1 <> "," <> printExpr e2 <> ")"
printExpr (Var _ id) = "Var(" <> showQualified showIdent id <> ")"
printExpr (Case _ es as) = "Case([" <> T.intercalate "," (map printExpr es)
                           <> "],[" <> T.intercalate "," (map printCaseAlternative as)
                           <> "])"
printExpr (Let _ bs e) = "Let([" <> T.intercalate "," (map printBind bs)
                         <> "]," <> printExpr e <> ")"

printLiteralExpr :: Literal (Expr a) -> Text
printLiteralExpr (StringLiteral str) = prettyPrintString str
printLiteralExpr (CharLiteral c) = T.pack (show c)
printLiteralExpr (NumericLiteral num) = either (T.pack . show) (T.pack . show) num
printLiteralExpr (BooleanLiteral True) = "true"
printLiteralExpr (BooleanLiteral False) = "false"
printLiteralExpr (ObjectLiteral bs) =
  "{ "
  <> T.intercalate ", " (map printObjectPropertyExpr bs)
  <> " }"
  where
  printObjectPropertyExpr :: (PSString, Expr a) -> Text
  printObjectPropertyExpr (key, binder) = prettyPrintString key <> ": " <> printExpr binder
printLiteralExpr (ArrayLiteral bs) =
  "[ "
  <> T.intercalate ", " (map printExpr bs)
  <> " ]"

printBind :: Bind a -> Text
printBind (NonRec _ id e) = "NonRec(" <> showIdent id <> "," <> printExpr e <> ")"
printBind (Rec xs) = "Rec([" <> T.intercalate ","
                     (map (\((_,id),e)->"(" <> showIdent id <> "," <> printExpr e <> ")") xs)
                     <> "])"

printCaseAlternative :: CaseAlternative a -> Text
printCaseAlternative (CaseAlternative bs (Left gs)) =
  "CaseAlternative([" <> T.intercalate "," (map printBinder bs) <> "],["
  <> T.intercalate "," ( map (\(g,e)->"("<>printExpr g <> "," <> printExpr e <> ")") gs )
  <> "])"
printCaseAlternative (CaseAlternative bs (Right e)) =
  "CaseAlternative([" <> T.intercalate "," (map printBinder bs) <> "],"
  <> printExpr e <> ")"

printBinds :: [Bind a] -> Text
printBinds bs = "--- Binds ---\n" <>
                T.intercalate "\n" (map printBind bs)
                <> "\n"

