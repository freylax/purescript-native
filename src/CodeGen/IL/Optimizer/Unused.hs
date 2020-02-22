-- | Removes unused variables
module CodeGen.IL.Optimizer.Unused
  ( removeCodeAfterReturnStatements
  , removeUndefinedApp
  ) where

import Prelude.Compat

import CodeGen.IL.AST
import CodeGen.IL.Optimizer.Common (removeFromBlock)

import qualified Language.PureScript.Constants as C

removeCodeAfterReturnStatements :: AST -> AST
removeCodeAfterReturnStatements = everywhere (removeFromBlock go)
  where
  go :: [AST] -> [AST]
  go jss | not (any isReturn jss) = jss
         | otherwise = let (body, ret : _) = break isReturn jss in body ++ [ret]
  isReturn (Return _ _) = True
  isReturn (ReturnNoResult _) = True
  isReturn _ = False

removeUndefinedApp :: AST -> AST
removeUndefinedApp = everywhere convert
  where
  convert (App ss fn [Var _ arg]) | arg == C.undefined = App ss fn []
  convert js = js
