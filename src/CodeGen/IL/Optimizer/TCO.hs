module CodeGen.IL.Optimizer.TCO (tco, tcoLoop) where

import Prelude.Compat

import Data.Text (Text)
import Data.Monoid ((<>))
--import Language.PureScript.CoreImp.AST
import CodeGen.IL.AST
import Language.PureScript.AST.SourcePos (SourceSpan)
import Safe (headDef, tailSafe)
import CodeGen.IL.Common

import qualified Language.PureScript.Constants as C

tcoLoop :: Text
tcoLoop = "_tco_loop_"  

tco :: AST -> AST -> AST
tco mn = everywhere convert where
  tcoVar :: Text -> Text
  tcoVar arg = "_tco_var_" <> arg <> "_"

  copyVar :: Text -> Text
  copyVar arg = "_copy_" <> arg <> "_"

  tcoDone :: Text
  tcoDone = "_tco_done_"

  tcoResult :: Text
  tcoResult = "_tco_result_"

  convert :: AST -> AST
  convert fn@(Function _ (Just name) args _)
      | isTailRecursive name body'
      = replace (toLoop name outerArgs innerArgs body')
    where
      innerArgs = headDef [] argss
      outerArgs = concat . reverse $ tailSafe argss
      (argss, body', replace) = collectAllFunctionArgs [] id fn
  convert (Assignment (Var name) fn@(Function _ Nothing _ _))
      | isTailRecursive name body'
      = Assignment (Var name) (replace (toLoop name outerArgs innerArgs body'))
    where
      innerArgs = headDef [] argss
      outerArgs = concat . reverse $ tailSafe argss
      (argss, body', replace) = collectAllFunctionArgs [] id fn
  convert js = js

  collectAllFunctionArgs :: [[(TypeSpecSeq,Text)]] -> (AST -> AST) -> AST -> ([[(TypeSpecSeq,Text)]], AST, AST -> AST)
  collectAllFunctionArgs allArgs f (Function ret ident args (Block (body@(Return _):_))) =
    collectAllFunctionArgs (args : allArgs) (\b -> f (Function ret ident (map (\t -> (fst t,copyVar $ snd t)) args) (Block [b]))) body
  -- Handle RecLetDecl weak assignment case
  collectAllFunctionArgs allArgs f (Function ret ident args (Block (Var{}:body@(Return _):_))) =
    collectAllFunctionArgs (args : allArgs) (\b -> f (Function ret ident (map (\t -> (fst t,copyVar $ snd t)) args) (Block [b]))) body
  collectAllFunctionArgs allArgs f (Function ret ident args body@(Block _)) =
    (args : allArgs, body, f . Function ret ident (map (\t -> (fst t,copyVar $ snd t)) args))
  collectAllFunctionArgs allArgs f (Return (Function _ ident args (Block [body]))) =
    collectAllFunctionArgs (args : allArgs) (\b -> f (Return (Function (TypeSpecSeq Auto Nothing) ident (map (\t -> (fst t,copyVar (snd t))) args) (Block [b])))) body
  collectAllFunctionArgs allArgs f (Return (Function _ ident args body@(Block _))) =
    (args : allArgs, body, f . Return . Function (TypeSpecSeq Auto Nothing) ident (map (\t -> (fst t,copyVar $ snd t)) args))
  collectAllFunctionArgs allArgs f body = (allArgs, body, f)

  isTailRecursive :: Text -> AST -> Bool
  isTailRecursive ident js = countSelfReferences js > 0 && allInTailPosition js where
    countSelfReferences = everything (+) match where
      match :: AST -> Int
      match (Var ident') | ident == ident' = 1
      match _ = 0

    allInTailPosition (Return expr)
      | isSelfCall ident expr = countSelfReferences expr == 1
      | otherwise = countSelfReferences expr == 0
    allInTailPosition (While js1 body)
      = countSelfReferences js1 == 0 && allInTailPosition body
    allInTailPosition (For _ js1 js2 body)
      = countSelfReferences js1 == 0 && countSelfReferences js2 == 0 && allInTailPosition body
    allInTailPosition (ForIn _ js1 body)
      = countSelfReferences js1 == 0 && allInTailPosition body
    allInTailPosition (IfElse js1 body el)
      = countSelfReferences js1 == 0 && allInTailPosition body && all allInTailPosition el
    allInTailPosition (Block body)
      = all allInTailPosition body
    allInTailPosition (Throw js1)
      = countSelfReferences js1 == 0
    allInTailPosition (ReturnNoResult)
      = True
    allInTailPosition (VariableIntroduction _ _ js1)
      = all ((== 0) . countSelfReferences) js1
    allInTailPosition (Assignment _ js1)
      = countSelfReferences js1 == 0
    allInTailPosition (Comment _ js1)
      = allInTailPosition js1
    allInTailPosition _
      = False

  toLoop :: Text -> [(TypeSpecSeq,Text)] -> [(TypeSpecSeq,Text)] -> AST -> AST
  toLoop ident outerArgs innerArgs js =
    Block $
    concatMap (\arg -> [ VariableIntroduction (tcoVar (snd arg)) (fst arg)
                         (Just (Var (copyVar (snd arg)))) ])
    (outerArgs ++ innerArgs) ++
    [ Assignment (Var $ bool <> " " <> tcoDone) $ BooleanLiteral False
    , VariableIntroduction tcoResult (TypeSpecSeq Auto Nothing) Nothing
    , Assignment (Var $ auto <> " " <> tcoLoop)
      (Function (TypeSpecSeq Auto Nothing) (Just tcoLoop) (outerArgs ++ innerArgs) (Block  [loopify js]))
    , While (Unary Not (Var tcoDone))
      (Block 
        [(Assignment (Var tcoResult)
           (App (Var tcoLoop)
             ((map (\t -> (Var . tcoVar) (snd t)) outerArgs) ++ (map (\t -> (Var  . tcoVar)(snd t)) innerArgs))))])
    , Return  (Var  tcoResult)
    ]
    where
    loopify :: AST -> AST
    loopify (Return ret)
      | isSelfCall ident ret =
        let
          allArgumentValues = concat $ collectArgs [] ret
        in
          Block $
            zipWith (\val arg ->
              Assignment  (Var  (tcoVar (snd arg))) val) allArgumentValues outerArgs
            ++ zipWith (\val arg ->
              Assignment  (Var  (tcoVar (snd arg))) val) (drop (length outerArgs) allArgumentValues) innerArgs
            ++ [ ReturnNoResult  ]
      | otherwise = Block  [ markDone , Return  ret ]
    loopify (ReturnNoResult ) = Block  [ markDone , ReturnNoResult  ]
    loopify (While  cond body) = While  cond (loopify body)
    loopify (For  i js1 js2 body) = For  i js1 js2 (loopify body)
    loopify (ForIn  i js1 body) = ForIn  i js1 (loopify body)
    loopify (IfElse  cond body el) = IfElse  cond (loopify body) (fmap loopify el)
    loopify (Block  body) = Block  (map loopify body)
    loopify other = other

    markDone :: AST
    markDone  = Assignment (Var tcoDone) (BooleanLiteral True)

    collectArgs :: [[AST]] -> AST -> [[AST]]
    collectArgs acc (App fn args') = collectArgs (args' : acc) fn
    collectArgs acc _ = acc

  isSelfCall :: Text -> AST -> Bool
  isSelfCall ident (App (Var ident') _) = ident == ident'
  isSelfCall ident (App (Indexer (Var ident') (Var "")) _) = ident == ident'
  isSelfCall ident (App (Indexer (Var ident') mn') _) = mn' == mn && ident == ident'
  isSelfCall ident (App fn _) = isSelfCall ident fn
  isSelfCall _ _ = False
