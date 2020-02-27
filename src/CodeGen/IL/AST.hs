-- | Data types for the imperative core AST
-- | Modified for c++
module CodeGen.IL.AST where

import Prelude.Compat

import Control.Monad ((>=>))
import Control.Monad.Identity (Identity(..), runIdentity)
import Data.Text (Text)

import Language.PureScript.Comments
import Language.PureScript.PSString (PSString)
import Language.PureScript.Traversals

-- | Built-in unary operators
data UnaryOperator
  = Negate
  | Not
  | BitwiseNot
  | Positive
  | New
  deriving (Show, Eq)

-- | Built-in binary operators
data BinaryOperator
  = Add
  | Subtract
  | Multiply
  | Divide
  | Modulus
  | EqualTo
  | NotEqualTo
  | LessThan
  | LessThanOrEqualTo
  | GreaterThan
  | GreaterThanOrEqualTo
  | And
  | Or
  | BitwiseAnd
  | BitwiseOr
  | BitwiseXor
  | ShiftLeft
  | ShiftRight
  | ZeroFillShiftRight
  deriving (Show, Eq)

newtype NameSpace = NameSpace Text
  deriving (Show, Eq, Ord)

-- |
-- A qualified name, i.e. a name with an optional namespace
--
data Quali a = Quali (Maybe NameSpace) a
  deriving (Show, Eq, Ord, Functor)

data TypeSpec
  = Ident (Quali Text)
  | Void
  | Auto
  | TemplateArg Text
  -- ^ Template Argument
  | Template (Quali Text) [TypeSpecSeq]
  -- ^ function or class Template with id and arguments
  | Funct TypeSpecSeq [TypeSpecSeq]
  -- ^ Function return type and arguments
  deriving (Show, Eq)

data ConstSpec
  = Const
  deriving (Show, Eq)

-- | Reference Specifier
data RefSpec
  = Pointer
  | LvalueRef (Maybe ConstSpec) 
  deriving (Show, Eq)


data TypeSpecSeq
  = TypeSpecSeq TypeSpec (Maybe RefSpec)  
  deriving (Show, Eq)

-- | Data type for simplified JavaScript expressions
data AST
  = NumericLiteral  (Either Integer Double)
  -- ^ A numeric literal
  | StringLiteral  PSString
  -- ^ A string literal
  | BooleanLiteral  Bool
  -- ^ A boolean literal
  | Unary  UnaryOperator AST
  -- ^ A unary operator application
  | Binary  BinaryOperator AST AST
  -- ^ A binary operator application
  | ArrayLiteral  [AST]
  -- ^ An array literal
  | Indexer AST AST
  -- ^ An array indexer expression
  | ObjectLiteral [(PSString, AST)]
  -- ^ An object literal
  | Function TypeSpecSeq (Maybe Text) [(TypeSpecSeq,Text)] AST
  -- ^ A function introduction (return type, optional name, typed arguments (type,identifier) , body)
  | App  AST [AST]
  -- ^ Function application
  | Var  Text
  -- ^ Variable
  | Block [AST]
  -- ^ A block of expressions in braces
  | VariableIntroduction Text TypeSpecSeq (Maybe AST)
  -- ^ A variable introduction and optional initialization
  | Assignment AST AST
  -- ^ A variable assignment
  | While AST AST
  -- ^ While loop
  | For Text AST AST AST
  -- ^ For loop
  | ForIn Text AST AST
  -- ^ ForIn loop
  | IfElse AST AST (Maybe AST)
  -- ^ If-then-else statement
  | Return AST
  -- ^ Return statement
  | ReturnNoResult 
  -- ^ Return statement with no return value
  | Throw AST
  -- ^ Throw statement
  | InstanceOf AST AST
  -- ^ instanceof check
  | Comment [Comment] AST
  -- ^ Commented JavaScript
  deriving (Show, Eq)

everywhere :: (AST -> AST) -> AST -> AST
everywhere f = go where
  go :: AST -> AST
  go (Unary  op j) = f (Unary  op (go j))
  go (Binary  op j1 j2) = f (Binary  op (go j1) (go j2))
  go (ArrayLiteral  js) = f (ArrayLiteral  (map go js))
  go (Indexer  j1 j2) = f (Indexer  (go j1) (go j2))
  go (ObjectLiteral  js) = f (ObjectLiteral  (map (fmap go) js))
  go (Function  ret name args j) = f (Function  ret name args (go j))
  go (App  j js) = f (App  (go j) (map go js))
  go (Block  js) = f (Block  (map go js))
  go (VariableIntroduction name type' j) = f (VariableIntroduction name type' (fmap go j))
  go (Assignment  j1 j2) = f (Assignment  (go j1) (go j2))
  go (While  j1 j2) = f (While  (go j1) (go j2))
  go (For  name j1 j2 j3) = f (For  name (go j1) (go j2) (go j3))
  go (ForIn  name j1 j2) = f (ForIn  name (go j1) (go j2))
  go (IfElse  j1 j2 j3) = f (IfElse  (go j1) (go j2) (fmap go j3))
  go (Return  js) = f (Return  (go js))
  go (Throw  js) = f (Throw  (go js))
  go (InstanceOf  j1 j2) = f (InstanceOf  (go j1) (go j2))
  go (Comment  com j) = f (Comment  com (go j))
  go other = f other

everywhereTopDown :: (AST -> AST) -> AST -> AST
everywhereTopDown f = runIdentity . everywhereTopDownM (Identity . f)

everywhereTopDownM :: (Monad m) => (AST -> m AST) -> AST -> m AST
everywhereTopDownM f = f >=> go where
  f' = f >=> go
  go (Unary  op j) = Unary  op <$> f' j
  go (Binary  op j1 j2) = Binary  op <$> f' j1 <*> f' j2
  go (ArrayLiteral  js) = ArrayLiteral  <$> traverse f' js
  go (Indexer  j1 j2) = Indexer  <$> f' j1 <*> f' j2
  go (ObjectLiteral  js) = ObjectLiteral  <$> traverse (sndM f') js
  go (Function  ret name args j) = Function  ret name args <$> f' j
  go (App  j js) = App  <$> f' j <*> traverse f' js
  go (Block  js) = Block  <$> traverse f' js
  go (VariableIntroduction name type' j) = VariableIntroduction name type' <$> traverse f' j
  go (Assignment  j1 j2) = Assignment  <$> f' j1 <*> f' j2
  go (While  j1 j2) = While  <$> f' j1 <*> f' j2
  go (For  name j1 j2 j3) = For  name <$> f' j1 <*> f' j2 <*> f' j3
  go (ForIn  name j1 j2) = ForIn  name <$> f' j1 <*> f' j2
  go (IfElse  j1 j2 j3) = IfElse  <$> f' j1 <*> f' j2 <*> traverse f' j3
  go (Return  j) = Return  <$> f' j
  go (Throw  j) = Throw  <$> f' j
  go (InstanceOf  j1 j2) = InstanceOf  <$> f' j1 <*> f' j2
  go (Comment  com j) = Comment  com <$> f' j
  go other = f other

everything :: (r -> r -> r) -> (AST -> r) -> AST -> r
everything (<>.) f = go where
  go j@(Unary _ j1) = f j <>. go j1
  go j@(Binary _ j1 j2) = f j <>. go j1 <>. go j2
  go j@(ArrayLiteral js) = foldl (<>.) (f j) (map go js)
  go j@(Indexer j1 j2) = f j <>. go j1 <>. go j2
  go j@(ObjectLiteral js) = foldl (<>.) (f j) (map (go . snd) js)
  go j@(Function _ _ _ j1) = f j <>. go j1
  go j@(App j1 js) = foldl (<>.) (f j <>. go j1) (map go js)
  go j@(Block js) = foldl (<>.) (f j) (map go js)
  go j@(VariableIntroduction _ _ (Just j1)) = f j <>. go j1
  go j@(Assignment j1 j2) = f j <>. go j1 <>. go j2
  go j@(While j1 j2) = f j <>. go j1 <>. go j2
  go j@(For _ j1 j2 j3) = f j <>. go j1 <>. go j2 <>. go j3
  go j@(ForIn _ j1 j2) = f j <>. go j1 <>. go j2
  go j@(IfElse j1 j2 Nothing) = f j <>. go j1 <>. go j2
  go j@(IfElse j1 j2 (Just j3)) = f j <>. go j1 <>. go j2 <>. go j3
  go j@(Return j1) = f j <>. go j1
  go j@(Throw j1) = f j <>. go j1
  go j@(InstanceOf j1 j2) = f j <>. go j1 <>. go j2
  go j@(Comment _ j1) = f j <>. go j1
  go other = f other
