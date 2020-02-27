-- | This module optimizes code in the intermediate representation.
module CodeGen.IL.Optimizer (optimize) where

import Prelude.Compat

import Control.Monad.Supply.Class (MonadSupply)
import Data.Text (Text)
import Language.PureScript.CoreImp.Optimizer.Common (applyAll)
import CodeGen.IL.AST
import CodeGen.IL.Common (unusedName)
import CodeGen.IL.Optimizer.Blocks 
import CodeGen.IL.Optimizer.Unused
import CodeGen.IL.Optimizer.Common (removeFromBlock,isUsed)
import CodeGen.IL.Optimizer.Inliner 
import CodeGen.IL.Optimizer.MagicDo
import CodeGen.IL.Optimizer.TCO

import qualified Language.PureScript.Constants as C

-- | Apply a series of optimizer passes to simplified IL code
optimize :: MonadSupply m => AST -> AST -> m AST
optimize mn il = do
  return il
-- optimize mn il = do
--     il' <- untilFixedPoint (inlineFnComposition . inlineUnsafeCoerce . inlineUnsafePartial . tidyUp) il
--     untilFixedPoint (return . ignoreUnusedResults . inlineCommonValues
--                      . inlineCommonOperators . tidyUp) . tco mn . inlineST
--       =<< untilFixedPoint (return . magicDoST)
--       =<< untilFixedPoint (return . magicDoEff)
--       =<< untilFixedPoint (return . magicDoEffect) il'
--   where
--     tidyUp :: AST -> AST
--     tidyUp = applyAll
--       [ collapseNestedBlocks
--       , collapseNestedIfs
--       , collapseIfChecks
--       , removeCodeAfterReturnStatements
--       , unThunk
--       , etaConvert
--       , evaluateIifes
--       , inlineVariables
--       ]

untilFixedPoint :: (Monad m, Eq a) => (a -> m a) -> a -> m a
untilFixedPoint f = go
  where
  go a = do
   a' <- f a
   if a' == a then return a' else go a'

collapseIfChecks :: AST -> AST
collapseIfChecks = everywhere collapse where
  collapse :: AST -> AST
  collapse (IfElse (Binary EqualTo (BooleanLiteral True) (BooleanLiteral True)) (Block [exprs]) _) = exprs
  collapse (IfElse (Binary EqualTo (Indexer (Var prop) (Var val)) (BooleanLiteral True)) (Block [exprs]) _)
    | prop == "otherwise" && val == "Data_Boolean" = exprs
  collapse exprs = exprs

ignoreUnusedResults :: AST -> AST
ignoreUnusedResults = everywhere $ removeFromBlock go
  where
  go :: [AST] -> [AST]
  go [] = []
  go (VariableIntroduction var _ (Just s) : sts)
    | not $ any (everything (||) (isUsed var)) sts = sts'
    where
    sts' | App{} <- s = s : (go sts)
         | otherwise = go sts
  go (s:sts) = s : go sts
