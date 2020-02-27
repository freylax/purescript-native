-- | This module implements the "Magic Do" optimization, which inlines calls to return
-- and bind for the Eff monad, as well as some of its actions.
module CodeGen.IL.Optimizer.MagicDo (magicDoEffect, magicDoEff, magicDoST, inlineST) where

import Prelude.Compat
import Protolude (ordNub)

import Data.Maybe (fromJust, isJust)
import Data.Text (Text)

--import Language.PureScript.CoreImp.AST
import CodeGen.IL.AST
--import Language.PureScript.CoreImp.Optimizer.Common hiding (isDict)
import Language.PureScript.PSString (PSString, decodeString, mkString)
import qualified Language.PureScript.Constants as C

import CodeGen.IL.Common (unusedName)
import CodeGen.IL.Optimizer.Common

-- | Inline type class dictionaries for >>= and return for the Eff monad
--
-- E.g.
--
--  Prelude[">>="](dict)(m1)(function(x) {
--    return ...;
--  })
--
-- becomes
--
--  function __do {
--    var x = m1();
--    ...
--  }
magicDoEff :: AST -> AST
magicDoEff = magicDo C.eff C.effDictionaries

magicDoEffect :: AST -> AST
magicDoEffect = magicDo C.effect C.effectDictionaries

magicDoST :: AST -> AST
magicDoST = magicDo C.st C.stDictionaries

magicDo :: Text -> C.EffectDictionaries -> AST -> AST
magicDo effectModule C.EffectDictionaries{..} = everywhereTopDown convert
  where
  -- Desugar monomorphic calls to >>= and return for the Eff monad
  convert :: AST -> AST
  -- Desugar pure
  convert (App (App pure' [val]) []) | isPure pure' = val
  -- Desugar discard
  convert (App (App bind [m]) [Function ret Nothing [(_,unused)] (Block il)]) | isDiscard bind && unused == unusedName =
    Function ret Nothing [] $ Block (App m [] : map applyReturns il )
  -- Desugar bind
  convert (App (App bind [m]) [Function ret Nothing [(ty,arg)] (Block il)])
    | isBind bind =
        Function ret Nothing [] $ Block (VariableIntroduction arg ty (Just (App m [])) : map applyReturns il)
  -- Desugar untilE
  convert (App (App f [arg]) []) | isEffFunc edUntil f =
    App (Function (TypeSpecSeq Auto Nothing) Nothing [] (Block [ While (Unary Not (App arg [])) (Block []), Return $ ObjectLiteral []])) []
  -- Desugar whileE
  convert (App (App (App f [arg1]) [arg2]) []) | isEffFunc edWhile f =
    App (Function (TypeSpecSeq Auto Nothing) Nothing [] (Block [ While (App arg1 []) (Block [ App arg2 [] ]), Return $ ObjectLiteral []])) []
  -- -- Inline __do returns
  -- convert (Return _ (App _ (Function _ (Just ident) [] body) [])) | ident == fnName = body
  -- Inline double applications
  convert (App (App (Function ret Nothing [] (Block body)) []) []) =
    App (Function ret Nothing [] (Block (applyReturns `fmap` body))) []
  convert other = other
  -- Check if an expression represents a monomorphic call to >>= for the Eff monad
  isBind (App fn [dict]) | isDict (effectModule, edBindDict) dict && isBindPoly fn = True
  isBind _ = False
  -- Check if an expression represents a call to @discard@
  isDiscard (App (App fn [dict1]) [dict2])
    | isDict (C.controlBind, C.discardUnitDictionary) dict1 &&
      isDict (effectModule, edBindDict) dict2 &&
      isDiscardPoly fn = True
  isDiscard _ = False

  -- Check if an expression represents a monomorphic call to pure or return for the Eff applicative
  isPure (App fn [dict]) | isDict (effectModule, edApplicativeDict) dict && isPurePoly fn = True
  isPure _ = False
  -- Check if an expression represents the polymorphic >>= function
  isBindPoly = isDict (C.controlBind, C.bind)
  -- Check if an expression represents the polymorphic pure function
  isPurePoly = isDict (C.controlApplicative, C.pure')
  -- Check if an expression represents the polymorphic discard function
  isDiscardPoly = isDict (C.controlBind, C.discard)
  -- Check if an expression represents a function in the Effect module
  isEffFunc name (Indexer (StringLiteral name') (Var eff)) = eff == effectModule && name == name'
  isEffFunc _ _ = False

  applyReturns :: AST -> AST
  applyReturns (Return  ret) = Return  (App  ret [])
  applyReturns (Block  ils) = Block  (map applyReturns ils)
  applyReturns (While  cond il) = While  cond (applyReturns il)
  applyReturns (For  v lo hi il) = For  v lo hi (applyReturns il)
  applyReturns (ForIn  v xs il) = ForIn  v xs (applyReturns il)
  applyReturns (IfElse  cond t f) = IfElse  cond (applyReturns t) (applyReturns `fmap` f)
  applyReturns other = other

-- | Inline functions in the ST module
inlineST :: AST -> AST
inlineST = everywhere convertBlock
  where
  -- Look for runST blocks and inline the STRefs there.
  -- If all STRefs are used in the scope of the same runST, only using { read, write, modify }STRef then
  -- we can be more aggressive about inlining, and actually turn STRefs into local variables.
  convertBlock (App f [arg]) | isSTFunc C.runST f =
    let refs = ordNub . findSTRefsIn $ arg
        usages = findAllSTUsagesIn arg
        allUsagesAreLocalVars = all (\u -> let v = toVar u in isJust v && fromJust v `elem` refs) usages
        localVarsDoNotEscape = all (\r -> length (r `appearingIn` arg) == length (filter (\u -> let v = toVar u in v == Just r) usages)) refs
    in App (everywhere (convert (allUsagesAreLocalVars && localVarsDoNotEscape)) arg) []
  convertBlock other = other
  -- Convert a block in a safe way, preserving object wrappers of references,
  -- or in a more aggressive way, turning wrappers into local variables depending on the
  -- agg(ressive) parameter.
  convert agg (App f [arg]) | isSTFunc C.newSTRef f =
   Function (TypeSpecSeq Auto Nothing) Nothing [] (Block [Return $ if agg then arg else ObjectLiteral [(mkString C.stRefValue, arg)]])
  convert agg (App (App f [ref]) []) | isSTFunc C.readSTRef f =
    if agg then ref else Indexer (StringLiteral C.stRefValue) ref
  convert agg (App (App (App f [arg]) [ref]) []) | isSTFunc C.writeSTRef f =
    if agg then Assignment ref arg else Assignment (Indexer (StringLiteral C.stRefValue) ref) arg
  convert agg (App (App (App f [func]) [ref]) []) | isSTFunc C.modifySTRef f =
    if agg then Assignment ref (App func [ref]) else Assignment (Indexer (StringLiteral C.stRefValue) ref) (App func [Indexer (StringLiteral C.stRefValue) ref])
  convert _ other = other
  -- Check if an expression represents a function in the ST module
  isSTFunc name (Indexer (StringLiteral name') (Var st)) = st == C.st && name == name'
  isSTFunc _ _ = False
  -- Find all ST Refs initialized in this block
  findSTRefsIn = everything (++) isSTRef
    where
    isSTRef (VariableIntroduction ident (TypeSpecSeq Auto Nothing)
             (Just (App (App f [_]) []))) | isSTFunc C.newSTRef f = [ident]
    isSTRef _ = []
  -- Find all STRefs used as arguments to readSTRef, writeSTRef, modifySTRef
  findAllSTUsagesIn = everything (++) isSTUsage
    where
    isSTUsage (App (App f [ref]) []) | isSTFunc C.readSTRef f = [ref]
    isSTUsage (App (App (App f [_]) [ref]) []) | isSTFunc C.writeSTRef f || isSTFunc C.modifySTRef f = [ref]
    isSTUsage _ = []
  -- Find all uses of a variable
  appearingIn ref = everything (++) isVar
    where
    isVar e@(Var v) | v == ref = [e]
    isVar _ = []
  -- Convert a AST value to a String if it is a Var
  toVar (Var v) = Just v
  toVar _ = Nothing
