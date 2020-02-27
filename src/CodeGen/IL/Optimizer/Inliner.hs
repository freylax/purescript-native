-- | This module performs basic inlining of known functions
module CodeGen.IL.Optimizer.Inliner
  ( etaConvert
  , unThunk
  , evaluateIifes
  , inlineCommonValues
  , inlineVariables
  , inlineCommonOperators
  , inlineFnComposition
  , inlineUnsafeCoerce
  , inlineUnsafePartial
  ) where

import Prelude.Compat

import Control.Monad.Supply.Class (MonadSupply)

import Data.Either (rights)
import Data.Maybe (fromMaybe)
import Data.String (IsString, fromString)
import Data.Text (Text)
import qualified Data.Text as T

import Language.PureScript.PSString (PSString, decodeString, mkString)
--import Language.PureScript.CoreImp.AST
import CodeGen.IL.AST
--import Language.PureScript.CoreImp.Optimizer.Common hiding (isDict, isDict')
import Language.PureScript.CoreImp.Optimizer.Common (applyAll)
import Language.PureScript.AST (SourceSpan(..))
import qualified Language.PureScript.Constants as C

import CodeGen.IL.Common hiding (unbox)
import CodeGen.IL.Optimizer.Common

-- TODO: Potential bug:
-- Shouldn't just inline this case: { var x = 0; x.toFixed(10); }
-- Needs to be: { 0..toFixed(10); }
-- Probably needs to be fixed in pretty-printer instead.
shouldInline :: AST -> Bool
shouldInline (Var _) = True
shouldInline (NumericLiteral _) = True
shouldInline (StringLiteral _) = True
shouldInline (BooleanLiteral _) = True
shouldInline (Indexer index val) = shouldInline index && shouldInline val
shouldInline _ = False

etaConvert :: AST -> AST
etaConvert = everywhere convert
  where
  convert :: AST -> AST
  convert (Block [Return (App (Function _ Nothing idents block@(Block body)) args)])
    | all shouldInline args &&
      not (any (`isRebound` block) (map (\t->Var (snd t)) idents)) &&
      not (any (`isRebound` block) args)
      = Block (map (replaceIdents (zipWith (\t a -> (snd t, a)) idents args)) body)
  convert (Function _ Nothing [] (Block [Return (App fn [])])) = fn
  convert js = js


unThunk :: AST -> AST
unThunk = everywhere convert
  where
  convert :: AST -> AST
  convert (Block []) = Block []
  convert (Block jss) =
    case last jss of
      Return (App (Function (TypeSpecSeq Auto Nothing) Nothing [] (Block body)) []) -> Block $ init jss ++ body
      _ -> Block jss
  convert js = js

evaluateIifes :: AST -> AST
evaluateIifes = everywhere convert
  where
  convert :: AST -> AST
  convert (App (Function _ Nothing [] (Block [Return ret])) []) = ret
  convert (App (Function _ Nothing idents (Block [Return ret])) [])
    | not (any (\t -> (snd t) `isReassigned` ret) idents) =
        replaceIdents (map (\t -> ((snd t), Var C.undefined)) idents) ret
  convert js = js

inlineCommonValues :: AST -> AST
inlineCommonValues = everywhere convert
  where
  convert :: AST -> AST
  convert (App fn [dict])
    | isDict' [semiringNumber, semiringInt] dict && isDict fnZero fn = NumericLiteral (Left 0)
    | isDict' [semiringNumber, semiringInt] dict && isDict fnOne fn = NumericLiteral (Left 1)
    | isDict boundedBoolean dict && isDict fnBottom fn = BooleanLiteral False
    | isDict boundedBoolean dict && isDict fnTop fn = BooleanLiteral True
  convert (App (App fn [dict]) [x])
    | isDict ringInt dict && isDict fnNegate fn = Unary Negate (unbox x $ snd ringInt)
  convert (App (App (App fn [dict]) [x]) [y])
    | isDict semiringInt dict && isDict fnAdd fn = intOp Add semiringInt x y
    | isDict semiringInt dict && isDict fnMultiply fn = intOp Multiply semiringInt x y
    | isDict ringInt dict && isDict fnSubtract fn = intOp Subtract ringInt x y
  convert other = other
  fnZero = (C.dataSemiring, C.zero)
  fnOne = (C.dataSemiring, C.one)
  fnBottom = (C.dataBounded, C.bottom)
  fnTop = (C.dataBounded, C.top)
  fnAdd = (C.dataSemiring, C.add)
  fnMultiply = (C.dataSemiring, C.mul)
  fnSubtract = (C.dataRing, C.sub)
  fnNegate = (C.dataRing, C.negate)
  intOp op (_, d) x y = Binary op (unbox x d) (unbox y d)

inlineVariables :: AST -> AST
inlineVariables = everywhere $ removeFromBlock go
  where
  go :: [AST] -> [AST]
  go [] = []
  go (VariableIntroduction var _ (Just js) : sts)
    | shouldInline js && not (any (isReassigned var) sts) && not (any (isRebound js) sts) && not (any (isUpdated var) sts) =
      go (map (replaceIdent var js) sts)
  go (s:sts) = s : go sts

inlineCommonOperators :: AST -> AST
inlineCommonOperators = everywhereTopDown $ applyAll $
  [ binary semiringNumber opAdd Add
  , binary semiringNumber opMul Multiply

  , binary ringNumber opSub Subtract
  , unary  ringNumber opNegate Negate

  , binary euclideanRingNumber opDiv Divide

  -- , binary eqNumber opEq EqualTo
  , binary eqNumber opNotEq NotEqualTo
  , binary eqInt opEq EqualTo
  , binary eqInt opNotEq NotEqualTo
  , binary eqString opEq EqualTo
  , binary eqString opNotEq NotEqualTo
  , binary eqChar opEq EqualTo
  , binary eqChar opNotEq NotEqualTo
  , binary eqBoolean opEq EqualTo
  , binary eqBoolean opNotEq NotEqualTo

  , binary ordBoolean opLessThan LessThan
  , binary ordBoolean opLessThanOrEq LessThanOrEqualTo
  , binary ordBoolean opGreaterThan GreaterThan
  , binary ordBoolean opGreaterThanOrEq GreaterThanOrEqualTo
  , binary ordChar opLessThan LessThan
  , binary ordChar opLessThanOrEq LessThanOrEqualTo
  , binary ordChar opGreaterThan GreaterThan
  , binary ordChar opGreaterThanOrEq GreaterThanOrEqualTo
  , binary ordInt opLessThan LessThan
  , binary ordInt opLessThanOrEq LessThanOrEqualTo
  , binary ordInt opGreaterThan GreaterThan
  , binary ordInt opGreaterThanOrEq GreaterThanOrEqualTo
  , binary ordNumber opLessThan LessThan
  , binary ordNumber opLessThanOrEq LessThanOrEqualTo
  , binary ordNumber opGreaterThan GreaterThan
  , binary ordNumber opGreaterThanOrEq GreaterThanOrEqualTo
  , binary ordString opLessThan LessThan
  , binary ordString opLessThanOrEq LessThanOrEqualTo
  , binary ordString opGreaterThan GreaterThan
  , binary ordString opGreaterThanOrEq GreaterThanOrEqualTo

  , binary semigroupString opAppend Add

  , binary heytingAlgebraBoolean opConj And
  , binary heytingAlgebraBoolean opDisj Or
  , unary  heytingAlgebraBoolean opNot Not

  , binary' C.dataIntBits C.or BitwiseOr
  , binary' C.dataIntBits C.and BitwiseAnd
  , binary' C.dataIntBits C.xor BitwiseXor
  , binary' C.dataIntBits C.shl ShiftLeft
  , binary' C.dataIntBits C.shr ShiftRight
  , binary' C.dataIntBits C.zshr ZeroFillShiftRight
  , unary'  C.dataIntBits C.complement BitwiseNot

  , inlineNonClassFunction (isModFn (C.dataFunction, C.apply)) $ \f x -> App f [x]
  , inlineNonClassFunction (isModFn (C.dataFunction, C.applyFlipped)) $ \x f -> App f [x]
  --, inlineNonClassFunction (isModFnWithDict (C.dataArray, C.unsafeIndex)) $ flip (Indexer Nothing)
  ] -- ++
  -- [ fn | i <- [0..10], fn <- [ mkFn i, runFn i ] ] ++
  -- [ fn | i <- [0..10], fn <- [ mkEffFn C.controlMonadEffUncurried C.mkEffFn i, runEffFn C.controlMonadEffUncurried C.runEffFn i ] ] ++
  -- [ fn | i <- [0..10], fn <- [ mkEffFn C.effectUncurried C.mkEffectFn i, runEffFn C.effectUncurried C.runEffectFn i ] ]
  where
  binary :: (Text, PSString) -> (Text, PSString) -> BinaryOperator -> AST -> AST
  binary dict@(_, d) fns op = convert where
    convert :: AST -> AST
    convert (App (App (App fn [dict']) [x]) [y])
      | isDict dict dict' && isDict fns fn = Binary op (unbox x d) (unbox y d)
    convert other = other
  binary' :: Text -> PSString -> BinaryOperator -> AST -> AST
  binary' moduleName opString op = convert where
    convert :: AST -> AST
    convert (App (App fn [x]) [y]) | isDict (moduleName, opString) fn = Binary op (unbox x mn) (unbox y mn)
    convert other = other
    mn :: PSString
    mn = mkString moduleName
  unary :: (Text, PSString) -> (Text, PSString) -> UnaryOperator -> AST -> AST
  unary dicts@(_, d) fns op = convert where
    convert :: AST -> AST
    convert (App (App fn [dict']) [x]) | isDict dicts dict' && isDict fns fn = Unary op (unbox x d)
    convert other = other
  unary' :: Text -> PSString -> UnaryOperator -> AST -> AST
  unary' moduleName fnName op = convert where
    convert :: AST -> AST
    convert (App fn [x]) | isDict (moduleName, fnName) fn = Unary op (unbox x fnName)
    convert other = other

  mkFn :: Int -> AST -> AST
  mkFn = mkFn' C.dataFunctionUncurried C.mkFn $ \args il ->
    Function (TypeSpecSeq Auto Nothing) Nothing args (Block [Return il])

  mkEffFn :: Text -> Text -> Int -> AST -> AST
  mkEffFn modName fnName = mkFn' modName fnName $ \args il ->
    Function (TypeSpecSeq Auto Nothing) Nothing args (Block [Return (App il [])])

  mkFn' :: Text -> Text -> ([(TypeSpecSeq,Text)] -> AST -> AST) -> Int -> AST -> AST
  mkFn' modName fnName res 0 = convert where
    convert :: AST -> AST
    convert (App mkFnN [Function (TypeSpecSeq Auto Nothing) Nothing [_] (Block [Return il])]) | isNFn modName fnName 0 mkFnN =
      res [] il
    convert other = other
  mkFn' modName fnName res n = convert where
    convert :: AST -> AST
    convert orig@(App mkFnN [fn]) | isNFn modName fnName n mkFnN =
      case collectArgs n [] fn of
        Just (args, [Return ret]) -> res args ret
        _ -> orig
    convert other = other
    collectArgs :: Int -> [(TypeSpecSeq,Text)] -> AST -> Maybe ([(TypeSpecSeq,Text)], [AST])
    collectArgs 1 acc (Function _ Nothing [oneArg] (Block il)) | length acc == n - 1 = Just (reverse (oneArg : acc), il)
    collectArgs m acc (Function _ Nothing [oneArg] (Block [Return ret])) = collectArgs (m - 1) (oneArg : acc) ret
    collectArgs _ _   _ = Nothing

  isNFn :: Text -> Text -> Int -> AST -> Bool
  isNFn expectMod prefix n (Indexer (Var name) (Var modName)) | modName == expectMod =
    name == fromString (T.unpack prefix <> show n)
  isNFn _ _ _ _ = False

  runFn :: Int -> AST -> AST
  runFn = runFn' C.dataFunctionUncurried C.runFn
    (\f args ->
       let len = length args
           typ = mkString $ "Fn" <> (T.pack . show $ len) in
         if len > 0
         then App (App (StringLiteral typ) [f]) args
         else App f args)
    
  runEffFn :: Text -> Text -> Int -> AST -> AST
  runEffFn modName fnName = runFn' modName fnName $ \fn acc ->
    Function (TypeSpecSeq Auto Nothing) Nothing [] (Block [Return (App fn acc)])

  runFn' :: Text -> Text -> (AST -> [AST] -> AST) -> Int -> AST -> AST
  runFn' modName runFnName res n = convert where
    convert :: AST -> AST
    convert il = fromMaybe il $ go n [] il

    go :: Int -> [AST] -> AST -> Maybe AST
    go 0 acc (App runFnN [fn]) | isNFn modName runFnName n runFnN && length acc == n =
      Just $ res fn acc
    go m acc (App lhs [arg]) = go (m - 1) (arg : acc) lhs
    go _ _   _ = Nothing

  inlineNonClassFunction :: (AST -> Bool) -> (AST -> AST -> AST) -> AST -> AST
  inlineNonClassFunction p f = convert where
    convert :: AST -> AST
    convert (App (App op' [x]) [y]) | p op' = f x y
    convert other = other

  isModFn :: (Text, PSString) -> AST -> Bool
  isModFn (m, op) (Indexer (Var op') (Var m')) =
    m == m' && decodeString op == Just op'
  isModFn _ _ = False

  isModFnWithDict :: (Text, PSString) -> AST -> Bool
  isModFnWithDict (m, op) (App (Indexer (Var op') (Var m')) [Var _]) =
    m == m' && decodeString op == Just op'
  isModFnWithDict _ _ = False

-- (f <<< g $ x) = f (g x)
-- (f <<< g)     = \x -> f (g x)
inlineFnComposition :: forall m. MonadSupply m => AST -> m AST
inlineFnComposition = everywhereTopDownM convert where
  convert :: AST -> m AST
  convert (App (App (App (App fn [dict']) [x]) [y]) [z])
    | isFnCompose dict' fn = return $ App x [App y [z]]
    | isFnComposeFlipped dict' fn = return $ App y [App x [z]]
  convert app@(App (App (App fn [dict']) _) _)
    | isFnCompose dict' fn || isFnComposeFlipped dict' fn = mkApps <$> goApps app <*> freshName'
  convert other = return other

  mkApps :: [Either AST (Text, AST)] -> Text -> AST
  mkApps fns a = App (Function (TypeSpecSeq Auto Nothing) Nothing [] (Block $ vars <> [Return comp])) []
    where
    vars = uncurry (\id b -> VariableIntroduction id (TypeSpecSeq Auto Nothing) b) . fmap Just <$> rights fns
    comp = Function (TypeSpecSeq Auto Nothing) Nothing [((TypeSpecSeq Auto Nothing),a)] (Block [Return apps])
    apps = foldr (\fn acc -> App (mkApp fn) [acc]) (Var a) fns

  mkApp :: Either AST (Text, AST) -> AST
  mkApp = either id $ \(name, arg) -> Var name

  goApps :: AST -> m [Either AST (Text, AST)]
  goApps (App (App (App fn [dict']) [x]) [y])
    | isFnCompose dict' fn = mappend <$> goApps x <*> goApps y
    | isFnComposeFlipped dict' fn = mappend <$> goApps y <*> goApps x
  goApps app@(App {}) = pure . Right . (,app) <$> freshName'
  goApps other = pure [Left other]

  isFnCompose :: AST -> AST -> Bool
  isFnCompose dict' fn = isDict semigroupoidFn dict' && isDict fnCompose fn

  isFnComposeFlipped :: AST -> AST -> Bool
  isFnComposeFlipped dict' fn = isDict semigroupoidFn dict' && isDict fnComposeFlipped fn

  fnCompose :: forall a b. (IsString a, IsString b) => (a, b)
  fnCompose = (C.controlSemigroupoid, C.compose)

  fnComposeFlipped :: forall a b. (IsString a, IsString b) => (a, b)
  fnComposeFlipped = (C.controlSemigroupoid, C.composeFlipped)

inlineUnsafeCoerce :: AST -> AST
inlineUnsafeCoerce = everywhereTopDown convert where
  convert (App (Indexer (Var unsafeCoerceFn) (Var unsafeCoerce)) [ comp ])
    | unsafeCoerceFn == C.unsafeCoerceFn && unsafeCoerce == C.unsafeCoerce
    = comp
  convert other = other

inlineUnsafePartial :: AST -> AST
inlineUnsafePartial = everywhereTopDown convert where
  convert (App fn [ comp ])
    | isDict fnUnsafePartial fn
    = App comp []
    where
      fnUnsafePartial :: forall a b. (IsString a, IsString b) => (a, b)
      fnUnsafePartial = (C.partialUnsafe, C.unsafePartial)
  convert other = other

semiringNumber :: forall a b. (IsString a, IsString b) => (a, b)
semiringNumber = (C.dataSemiring, C.semiringNumber)

semiringInt :: forall a b. (IsString a, IsString b) => (a, b)
semiringInt = (C.dataSemiring, C.semiringInt)

ringNumber :: forall a b. (IsString a, IsString b) => (a, b)
ringNumber = (C.dataRing, C.ringNumber)

ringInt :: forall a b. (IsString a, IsString b) => (a, b)
ringInt = (C.dataRing, C.ringInt)

euclideanRingNumber :: forall a b. (IsString a, IsString b) => (a, b)
euclideanRingNumber = (C.dataEuclideanRing, C.euclideanRingNumber)

eqNumber :: forall a b. (IsString a, IsString b) => (a, b)
eqNumber = (C.dataEq, C.eqNumber)

eqInt :: forall a b. (IsString a, IsString b) => (a, b)
eqInt = (C.dataEq, C.eqInt)

eqString :: forall a b. (IsString a, IsString b) => (a, b)
eqString = (C.dataEq, C.eqString)

eqChar :: forall a b. (IsString a, IsString b) => (a, b)
eqChar = (C.dataEq, C.eqChar)

eqBoolean :: forall a b. (IsString a, IsString b) => (a, b)
eqBoolean = (C.dataEq, C.eqBoolean)

ordBoolean :: forall a b. (IsString a, IsString b) => (a, b)
ordBoolean = (C.dataOrd, C.ordBoolean)

ordNumber :: forall a b. (IsString a, IsString b) => (a, b)
ordNumber = (C.dataOrd, C.ordNumber)

ordInt :: forall a b. (IsString a, IsString b) => (a, b)
ordInt = (C.dataOrd, C.ordInt)

ordString :: forall a b. (IsString a, IsString b) => (a, b)
ordString = (C.dataOrd, C.ordString)

ordChar :: forall a b. (IsString a, IsString b) => (a, b)
ordChar = (C.dataOrd, C.ordChar)

semigroupString :: forall a b. (IsString a, IsString b) => (a, b)
semigroupString = (C.dataSemigroup, C.semigroupString)

boundedBoolean :: forall a b. (IsString a, IsString b) => (a, b)
boundedBoolean = (C.dataBounded, C.boundedBoolean)

heytingAlgebraBoolean :: forall a b. (IsString a, IsString b) => (a, b)
heytingAlgebraBoolean = (C.dataHeytingAlgebra, C.heytingAlgebraBoolean)

semigroupoidFn :: forall a b. (IsString a, IsString b) => (a, b)
semigroupoidFn = (C.controlSemigroupoid, C.semigroupoidFn)

opAdd :: forall a b. (IsString a, IsString b) => (a, b)
opAdd = (C.dataSemiring, C.add)

opMul :: forall a b. (IsString a, IsString b) => (a, b)
opMul = (C.dataSemiring, C.mul)

opEq :: forall a b. (IsString a, IsString b) => (a, b)
opEq = (C.dataEq, C.eq)

opNotEq :: forall a b. (IsString a, IsString b) => (a, b)
opNotEq = (C.dataEq, C.notEq)

opLessThan :: forall a b. (IsString a, IsString b) => (a, b)
opLessThan = (C.dataOrd, C.lessThan)

opLessThanOrEq :: forall a b. (IsString a, IsString b) => (a, b)
opLessThanOrEq = (C.dataOrd, C.lessThanOrEq)

opGreaterThan :: forall a b. (IsString a, IsString b) => (a, b)
opGreaterThan = (C.dataOrd, C.greaterThan)

opGreaterThanOrEq :: forall a b. (IsString a, IsString b) => (a, b)
opGreaterThanOrEq = (C.dataOrd, C.greaterThanOrEq)

opAppend :: forall a b. (IsString a, IsString b) => (a, b)
opAppend = (C.dataSemigroup, C.append)

opSub :: forall a b. (IsString a, IsString b) => (a, b)
opSub = (C.dataRing, C.sub)

opNegate :: forall a b. (IsString a, IsString b) => (a, b)
opNegate = (C.dataRing, C.negate)

opDiv :: forall a b. (IsString a, IsString b) => (a, b)
opDiv = (C.dataEuclideanRing, C.div)

opConj :: forall a b. (IsString a, IsString b) => (a, b)
opConj = (C.dataHeytingAlgebra, C.conj)

opDisj :: forall a b. (IsString a, IsString b) => (a, b)
opDisj = (C.dataHeytingAlgebra, C.disj)

opNot :: forall a b. (IsString a, IsString b) => (a, b)
opNot = (C.dataHeytingAlgebra, C.not)

unbox :: AST -> PSString -> AST
unbox e d = select . inlineCommonValues $ inlineCommonOperators e
  where
  select :: AST -> AST
  select e' =
    case e' of
      Var{} -> unbox' e'
      App{} -> unbox' e'
      Indexer{} -> unbox' e'
      _ -> e'
  unbox' :: AST -> AST
  unbox' e' = maybe e' (\t -> App (StringLiteral t) [e']) $ unboxType d

unboxType :: PSString -> Maybe PSString
unboxType s = do
  t <- decodeString s
  t' <- unboxType' t
  return $ mkString t'
  where
  unboxType' :: Text -> Maybe Text
  unboxType' t
    | t == C.eqInt ||
      t == C.semiringInt ||
      t == C.ringInt ||
      t == C.ordInt ||
      t == C.dataIntBits
      = Just int
    | t == C.semiringNumber ||
      t == C.ringNumber ||
      t == C.ordNumber ||
      t == C.euclideanRingNumber
      = Just float
    | t == C.eqBoolean ||
      t == C.ordBoolean ||
      t == C.heytingAlgebraBoolean
      = Just bool
    | t == C.eqChar ||
      t == C.eqString ||
      t == C.ordChar ||
      t == C.ordString ||
      t == C.semigroupString
      = Just string
    | otherwise = Nothing
