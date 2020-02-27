-- | Optimizer steps for simplifying JavaScript blocks
module CodeGen.IL.Optimizer.Blocks
  ( collapseNestedBlocks
  , collapseNestedIfs
  ) where

import Prelude.Compat

import CodeGen.IL.AST

-- | Collapse blocks which appear nested directly below another block
collapseNestedBlocks :: AST -> AST
collapseNestedBlocks = everywhere collapse where
  collapse :: AST -> AST
  collapse (Block sts) = Block (concatMap go sts)
  collapse js = js
  
  go :: AST -> [AST]
  go (Block sts) = sts
  go s = [s]

collapseNestedIfs :: AST -> AST
collapseNestedIfs = everywhere collapse where
  collapse :: AST -> AST
  collapse (IfElse (BooleanLiteral True) (Block [js]) _) = js
  collapse (IfElse cond1 (Block [IfElse cond2 body Nothing]) Nothing) =
      IfElse (Binary And cond1 cond2) body Nothing
  collapse js = js
