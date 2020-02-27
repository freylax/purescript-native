-- | Common functions used by the various optimizer phases
module CodeGen.IL.Optimizer.Common where

import Prelude.Compat
import Data.Text (Text)
import Data.Maybe (fromMaybe)
import Data.List (find)
import Language.PureScript.PSString (PSString, decodeString)
import Language.PureScript.Crash
import CodeGen.IL.AST
import CodeGen.IL.Common (properToIL)

isDict :: (Text, PSString) -> AST -> Bool
isDict (moduleName, dictName) (Indexer (Var x) (Var y)) =
  Just x == (properToIL <$> decodeString dictName) && y == moduleName
isDict _ _ = False

isDict' :: [(Text, PSString)] -> AST -> Bool
isDict' xs il = any (`isDict` il) xs

removeFromBlock :: ([AST] -> [AST]) -> AST -> AST
removeFromBlock go (Block sts) = Block (go sts)
removeFromBlock _  js = js

isReassigned :: Text -> AST -> Bool
isReassigned var1 = everything (||) check
  where
  check :: AST -> Bool
  check (Function _ _ args _) | not ( find (\tv -> (snd tv) == var1) args == Nothing ) = True
  check (VariableIntroduction arg _ _) | var1 == arg = True
  check (Assignment (Var arg) _) | var1 == arg = True
  check (For arg _ _ _) | var1 == arg = True
  check (ForIn arg _ _) | var1 == arg = True
  check _ = False

isRebound :: AST -> AST -> Bool
isRebound js d = any (\v -> isReassigned v d || isUpdated v d) (everything (++) variablesOf js)
  where
  variablesOf (Var var) = [var]
  variablesOf _ = []

isUpdated :: Text -> AST -> Bool
isUpdated var1 = everything (||) check
  where
  check :: AST -> Bool
  check (Assignment target _) | var1 == targetVariable target = True
  check _ = False

targetVariable :: AST -> Text
targetVariable (Var var) = var
targetVariable (Indexer _ tgt) = targetVariable tgt
targetVariable _ = internalError "Invalid argument to targetVariable"

replaceIdent :: Text -> AST -> AST -> AST
replaceIdent var1 js = everywhere replace
  where
  replace (Var var2) | var1 == var2 = js
  replace other = other

replaceIdents :: [(Text, AST)] -> AST -> AST
replaceIdents vars = everywhere replace
  where
  replace v@(Var var) = fromMaybe v $ lookup var vars
  replace other = other

isUsed :: Text -> AST -> Bool
isUsed var1 = everything (||) check
  where
  check :: AST -> Bool
  check (Var var2) | var1 == var2 = True
  check (Assignment target _) | var1 == targetVariable target = True
  check _ = False
