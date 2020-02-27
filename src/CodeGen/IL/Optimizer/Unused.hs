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
  isReturn (Return _) = True
  isReturn (ReturnNoResult) = True
  isReturn _ = False

removeUndefinedApp :: AST -> AST
removeUndefinedApp = everywhere convert
  where
  convert (App fn [Var arg]) | arg == C.undefined = App fn []
  convert js = js
