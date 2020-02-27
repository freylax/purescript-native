-- | This module generates code in the core imperative representation from
-- elaborated PureScript code.
module CodeGen.IL
  ( module AST
  , module Common
  , moduleToIL
  ) where

import Prelude.Compat
import Protolude (ordNub)

import Control.Arrow ((&&&))
import Control.Monad (forM, liftM, replicateM, void)
import Control.Monad.Supply.Class

import Data.List ((\\), delete, intersect, nub)
import qualified Data.Foldable as F
import qualified Data.Map as M
import Data.Maybe (fromMaybe, isNothing, mapMaybe)
import Data.Monoid ((<>))
import Data.String (fromString)
import Data.Text (Text)
import qualified Data.Text as T

import Language.PureScript.AST.SourcePos
import Language.PureScript.CoreFn
import Language.PureScript.Comments
import Language.PureScript.Crash
import Language.PureScript.Names
import Language.PureScript.Options
import Language.PureScript.PSString (PSString, mkString, prettyPrintString)
import Language.PureScript.Traversals (sndM)
import qualified Language.PureScript.Constants as C
import Language.PureScript.Environment 
import Language.PureScript.Types 

import System.FilePath.Posix ((</>))

import CodeGen.IL.AST (AST)
import qualified CodeGen.IL.AST as AST
import CodeGen.IL.Common as Common
--import CodeGen.IL.Optimizer
import CodeGen.IL.Printer
import CodeGen.IL.Dump

data DeclType = ModuleDecl | LetDecl | RecLetDecl deriving (Eq)

optimize :: MonadSupply m => AST -> AST -> m AST
optimize mn il = do
  return il

-- | Generate code in the simplified intermediate representation for all declarations in a
-- module.
moduleToIL
  :: forall m
   -- . (Monad m, MonadReader Options m, MonadSupply m, MonadError MultipleErrors m)
   . (Monad m, MonadSupply m)
  => Module Ann
  -> Environment
  -> m (Text, [Text], [AST], Text, Text)
moduleToIL (Module _ coms mn _ imps _ foreigns decls) env@(Environment names _ _ _ _ _ _ ) = do
  let usedNames = concatMap getNames decls
  let mnLookup = renameImports usedNames imps
  let decls' = renameModules mnLookup decls
  ilDecls <- mapM (bindToIL ModuleDecl) decls'
  optimized <- traverse (traverse (optimize modName')) ilDecls
  let optimized' = concat optimized
      values = annotValue <$> optimized'
      foreigns' = identToIL <$> foreigns
      interface = interfaceSource modName values foreigns
      --interface = interfaceSource modName optimized' foreigns
      imports = nub . concat $ importToIL <$> optimized'
      moduleHeader = importToIL' modName
      implHeader = implHeaderSource modName imports moduleHeader
      implFooter = implFooterSource (runModuleName mn) foreigns
  return $ ( interface, foreigns', optimized',
             implHeader
             <> "\n" <> printEnv env
             <> "\n" <> printBinds decls
           , implFooter)
  where
    
    typeLookup :: Ident -> AST.TypeSpecSeq
    typeLookup id =
      let qid = (Qualified (Just mn) id) in
        case M.lookup qid names of
          (Just (st, _, _)) -> getType st
          Nothing -> AST.TypeSpecSeq AST.Auto Nothing
  --      (Nothing)       -> error $ "could not lookup type for name "
  --                           <> T.unpack ( showQualified runIdent qid )

    getType :: SourceType -> AST.TypeSpecSeq
    getType (TypeConstructor _ c) =
      (AST.TypeSpecSeq (AST.Ident
                         (AST.Quali (case getQual c of
                                       (Just mn) -> Just $ AST.NameSpace (runModuleName mn)
                                       Nothing -> Nothing)
                           (runProperName $ disqualify c)))
        Nothing)
    getType _ = (AST.TypeSpecSeq AST.Auto Nothing)
    
    modName = moduleNameToIL mn
    modName' = AST.Var modName

    annotValue :: AST -> (Text, Bool)
    annotValue (AST.Function _ (Just name) [] (AST.Block [AST.Return ret])) | isLiteral ret = (name, True)
    annotValue (AST.Function _ (Just name) [] _) = (name, False)
    annotValue _ = ("XXX",True) ---  error "Unexpected top-level value form"

    -- | Extracts all declaration names from a binding group.
    getNames :: Bind Ann -> [Ident]
    getNames (NonRec _ ident _) = [ident]
    getNames (Rec vals) = map (snd . fst) vals

    -- | Creates alternative names for each module to ensure they don't collide
    -- with declaration names.
    renameImports :: [Ident] -> [(Ann, ModuleName)] -> M.Map ModuleName (Ann, ModuleName)
    renameImports = go M.empty
      where
        go :: M.Map ModuleName (Ann, ModuleName) -> [Ident] -> [(Ann, ModuleName)] -> M.Map ModuleName (Ann, ModuleName)
        go acc used ((ann, mn') : mns') =
          let mni = Ident $ runModuleName mn'
          in if mn' /= mn && mni `elem` used
             then let newName = freshModuleName 1 mn' used
                  in go (M.insert mn' (ann, newName) acc) (Ident (runModuleName newName) : used) mns'
             else go (M.insert mn' (ann, mn') acc) used mns'
        go acc _ [] = acc

        freshModuleName :: Integer -> ModuleName -> [Ident] -> ModuleName
        freshModuleName i mn'@(ModuleName pns) used =
          let newName = ModuleName $ init pns ++ [ProperName $ runProperName (last pns) <> "_" <> T.pack (show i)]
          in if Ident (runModuleName newName) `elem` used
             then freshModuleName (i + 1) mn' used
             else newName

    -- | Generates IL code for a module import
    --
    importToIL :: AST -> [Text]
    importToIL = AST.everything (++) modRef
      where
        modRef (AST.Indexer (AST.Var _) (AST.Var mname))
          | not $ T.null mname = [importToIL' mname]
        modRef _ = []
    importToIL' :: Text -> Text
    importToIL' h = "#include \"" <> h <> ".h\"\n"

    -- | Replaces the `ModuleName`s in the AST so that the generated code refers to
    -- the collision-avoiding renamed module imports.
    renameModules :: M.Map ModuleName (Ann, ModuleName) -> [Bind Ann] -> [Bind Ann]
    renameModules mnLookup binds =
      let (f, _, _) = everywhereOnValues id ilExpr goBinder
      in map f binds
      where
        ilExpr :: Expr a -> Expr a
        ilExpr (Var ann q) = Var ann (renameQual q)
        ilExpr e = e
        goBinder :: Binder a -> Binder a
        goBinder (ConstructorBinder ann q1 q2 bs) = ConstructorBinder ann (renameQual q1) (renameQual q2) bs
        goBinder b = b
        renameQual :: Qualified a -> Qualified a
        renameQual (Qualified (Just mn') a) =
          let (_,mnSafe) = fromMaybe (internalError "Missing value in mnLookup") $ M.lookup mn' mnLookup
          in Qualified (Just mnSafe) a
        renameQual q = q

    -- |
    -- Generate code in the simplified intermediate representation for a declaration
    --
    bindToIL :: DeclType -> Bind Ann -> m [AST]
    bindToIL dt (NonRec a ident val) = return <$> nonRecToIL dt a ident val
    bindToIL dt (Rec vals) = forM vals (uncurry . uncurry $ nonRecToIL dt')
      where
        dt' = if dt == LetDecl then RecLetDecl else dt

    -- | Generate code in the simplified intermediate representation for a single non-recursive
    -- declaration.
    --
    nonRecToIL :: DeclType -> Ann -> Ident -> Expr Ann -> m AST
    nonRecToIL ModuleDecl _ ident val = do
      let ty = typeLookup ident
      il <- valueToIL (Just ty) val
      pure $ decl val (identToIL ident) ty il
      where
        decl :: Expr Ann -> Text -> AST.TypeSpecSeq -> AST -> AST
        decl (Literal _ _) id ty il = AST.VariableIntroduction id ty (Just il)
        decl (Abs _ _ _) id _ il = nameFct il id
        decl _ id _ il = AST.Comment [(LineComment $ "undefined decl mapping for " <> id)] il
        nameFct :: AST -> Text -> AST
        nameFct (AST.Function ty _ args ret) id = AST.Function ty (Just id) args ret
        nameFct (AST.Comment c il) id = AST.Comment c (nameFct il id)
        nameFct a id = AST.Comment [(LineComment $ "undefined nameFct mapping for " <> id)] a 
    nonRecToIL RecLetDecl _ ident val = do
      il <- valueToIL (Just (typeLookup ident)) val
      pure $
        let retainedName = identToIL ident
            retained = AST.Var retainedName
            unretainedName = retainedName <> unretainedSuffix
            unretained = AST.Var $ unretainedName
            boxed = AST.Var . -- Note: prevents optimizer from eliminating this
                    prettyPrintIL1 $
                    AST.VariableIntroduction
                    retainedName
                    (AST.TypeSpecSeq AST.Auto Nothing)
                    (Just unretained)
            alias = AST.Var $ "auto& " <> retainedName <> " = " <> unretainedName
        in
          case il of
            AST.Function ret name args (AST.Block ils) ->
              AST.Assignment 
              retained
              (AST.Function 
                ret
                name
                args 
                (AST.Block (boxed : ils)))
            _ -> AST.Assignment 
                 retained
                 (AST.App 
                   (AST.Function 
                     (AST.TypeSpecSeq AST.Auto Nothing)
                     Nothing
                     []
                     (AST.Block ([ alias , AST.Return il ])))
                   [])
    nonRecToIL _ _ ident val = do
      let ty = typeLookup ident
      il <- valueToIL (Just ty) val
      pure $ AST.VariableIntroduction (identToIL ident) ty (Just il)

    -- | Generate code in the simplified intermediate representation for a variable based on a
    -- PureScript identifier.
    var :: Ident -> AST
    var = AST.Var . identToIL

    accessorString :: PSString -> AST -> AST
    accessorString prop = AST.Indexer (AST.StringLiteral prop)

    -- | Generate code in the simplified intermediate representation for types.
    typeToIL :: SourceType -> AST.TypeSpecSeq
    typeToIL (TypeConstructor _ (Qualified (Just mn) pn)) =
      (AST.TypeSpecSeq
        (AST.Ident
          (AST.Quali (Just (AST.NameSpace $ moduleNameToIL mn)) (runProperName pn)))
        Nothing)
    typeToIL (TypeApp _ (TypeApp _ (TypeConstructor _
                                    (Qualified (Just (ModuleName [ProperName "Prim"]))
                                      (ProperName "Function"))) arg) ret) =
      (AST.TypeSpecSeq (AST.Funct (typeToIL ret) [(typeToIL arg)]) Nothing)
    
             -- | Generate code in nathe simplified intermediate representation for a value or expression.
    valueToIL :: Maybe AST.TypeSpecSeq -> Expr Ann -> m AST
    valueToIL _ (Literal _ l) = literalToValueIL l
    valueToIL _ (Accessor _ prop val) =
      accessorString prop <$> valueToIL Nothing val
    valueToIL _ (ObjectUpdate _ o ps) = do
      obj <- valueToIL Nothing o
      updates <- mapM (sndM (valueToIL Nothing)) ps
      obj' <- freshName'
      let objVar = AST.Var obj'
          copy = AST.VariableIntroduction obj' (AST.TypeSpecSeq AST.Auto Nothing)
                 (Just $ AST.App (AST.Var (unbox dictType)) [obj])
          assign (k, v) = AST.Assignment (accessorString k objVar) v
          sts = copy : (assign <$> updates) ++ [AST.Return objVar]
      return $ AST.App (AST.Function (AST.TypeSpecSeq AST.Auto Nothing) Nothing
                         [] (AST.Block sts)) []
    valueToIL (Just ty) (Abs _ arg val) = do
      ret <- valueToIL Nothing val
      let ilArg = case arg of
                    UnusedIdent -> []
                    _           -> [(ty,identToIL arg)]
      return $ AST.Comment [LineComment $ "type was given "]
       $ AST.Function ty Nothing ilArg (AST.Block [AST.Return ret])
    valueToIL Nothing (Abs _ arg val) = do
      ret <- valueToIL Nothing val
      let ilArg = case arg of
                    UnusedIdent -> []
                    _           -> [((AST.TypeSpecSeq AST.Auto Nothing),identToIL arg)]
      return $ AST.Function (AST.TypeSpecSeq AST.Auto Nothing) Nothing ilArg (AST.Block [AST.Return ret])
    valueToIL _ e@App{} = do
      let (f, args) = unApp e []
      args' <- mapM (valueToIL Nothing) args
      case f of
        Var (_, _, _, Just IsNewtype) _ -> return (head args')
        _ -> flip (foldl (\fn a -> AST.App fn [a])) args' <$> valueToIL Nothing f
      where
        unApp :: Expr Ann -> [Expr Ann] -> (Expr Ann, [Expr Ann])
        unApp (App _ val arg) args = unApp val (arg : args)
        unApp other args = (other, args)
    valueToIL _ (Var _ ident) = return $ varToIL ident
    valueToIL _ (Case (ss, _, _, _) values binders) = do
      vals <- mapM (valueToIL Nothing) values
      bindersToIL ss binders vals
    valueToIL _ (Let _ ds val) = do
      let recurs = concatMap getNames $ filter isRec ds
          recurDs = (\v -> AST.Var $ "boxed::recur " <> identToIL v) <$> recurs
          recurDsWeak = (\v -> AST.Var
                               ("boxed::recur::weak " <> identToIL v <> unretainedSuffix <> "(" <> identToIL v <> ")")
                        ) <$> recurs
          mutualRecurWarning = if any isMutRec $ filter isRec ds
                               then [AST.Var "#pragma message(\"Mutually recursive lets will cause retain cycles (memory leaks)\") //"]
                               else []
      ds' <- concat <$> mapM (bindToIL LetDecl) ds
      ret <- valueToIL Nothing val
      return $
        AST.App 
        (AST.Function
          (AST.TypeSpecSeq AST.Auto Nothing)
          Nothing
          []
          (AST.Block  (recurDs ++ recurDsWeak ++ mutualRecurWarning ++ ds' ++ [AST.Return ret])))
        []
      where
        isRec :: Bind Ann -> Bool
        isRec (Rec _) = True
        isRec _ = False
        isMutRec :: Bind Ann -> Bool
        isMutRec b | (length . nub $ getNames b) > 1 = True
                   | otherwise = False
    valueToIL _ (Constructor (_, _, _, Just IsNewtype) _ (ProperName ctor) _) = error "IsNewtype"
    valueToIL _ (Constructor _ _ (ProperName ctor) fields) =
      let body = AST.ObjectLiteral $ (mkString ctor, AST.BooleanLiteral True) :
                 ((\field -> (mkString (identToIL field), var field)) `map` fields)
          fn = foldr (\f inner -> AST.Function (AST.TypeSpecSeq AST.Auto Nothing) Nothing
                       [((AST.TypeSpecSeq AST.Auto Nothing),identToIL f)]
                       (AST.Block [AST.Return inner])) body fields
      in return fn


    iife :: Text -> [AST] -> AST
    iife v exprs = AST.App (AST.Function (AST.TypeSpecSeq AST.Auto Nothing) Nothing []
                             (AST.Block $ exprs ++ [AST.Return $ AST.Var v])) []

    literalToValueIL :: Literal (Expr Ann) -> m AST
    literalToValueIL (NumericLiteral (Left i)) = return $ AST.NumericLiteral  (Left i)
    literalToValueIL (NumericLiteral (Right n)) = return $ AST.NumericLiteral  (Right n)
    literalToValueIL (StringLiteral s) = return $ AST.StringLiteral  s
    literalToValueIL (CharLiteral c) = return $ AST.StringLiteral  (fromString [c])
    literalToValueIL (BooleanLiteral b) = return $ AST.BooleanLiteral  b
    literalToValueIL (ArrayLiteral xs) = AST.ArrayLiteral  <$> mapM (valueToIL Nothing) xs
    literalToValueIL (ObjectLiteral ps) = AST.ObjectLiteral  <$> mapM (sndM (valueToIL Nothing)) ps

    -- | Generate code in the simplified intermediate representation for a reference to a
    -- variable.
    varToIL :: Qualified Ident -> AST
    varToIL (Qualified Nothing ident) = var ident
    varToIL qual = qualifiedToIL id qual

    -- | Generate code in the simplified intermediate representation for a reference to a
    -- variable that may have a qualified name.
    qualifiedToIL :: (a -> Ident) -> Qualified a -> AST
    qualifiedToIL f (Qualified (Just (ModuleName [ProperName mn'])) a)
      | mn' == C.prim = AST.Var . identToIL $ f a
    -- qualifiedToIL f (Qualified (Just mn') a) | mn /= mn' = AST.Indexer Nothing (AST.Var Nothing . identToIL $ f a) (AST.Var Nothing (moduleNameToIL mn'))
    qualifiedToIL f (Qualified (Just mn') a) =
      AST.Indexer (AST.Var . identToIL $ f a) (AST.Var (moduleNameToIL mn'))
    qualifiedToIL f (Qualified _ a) =
      AST.Indexer (AST.Var . identToIL $ f a) (AST.Var "")

    -- foreignIdent :: Ident -> AST
    -- foreignIdent ident = accessorString (mkString $ runIdent ident) (AST.Var Nothing "$foreign")

    -- | Generate code in the simplified intermediate representation for pattern match binders
    -- and guards.
    bindersToIL :: SourceSpan -> [CaseAlternative Ann] -> [AST] -> m AST
    bindersToIL ss binders vals = do
      valNames <- replicateM (length vals) freshName'
      let assignments =
            zipWith (\id val -> AST.VariableIntroduction id (AST.TypeSpecSeq AST.Auto Nothing) val)
              valNames (map Just vals)
      ils <- forM binders $ \(CaseAlternative bs result) -> do
        ret <- guardsToIL result
        go valNames ret bs
      return $ AST.App (AST.Function (AST.TypeSpecSeq AST.Auto Nothing) Nothing []
                         (AST.Block 
                           (assignments ++ concat ils ++
                             [AST.Throw  (AST.StringLiteral $ mkString failedPatternMessage)])))
        []
      where
        go :: [Text] -> [AST] -> [Binder Ann] -> m [AST]
        go _ done [] = return done
        go (v:vs) done' (b:bs) = do
          done'' <- go vs done' bs
          binderToIL v done'' b
        go _ _ _ = internalError "Invalid arguments to bindersToIL"

        failedPatternMessage :: Text
        failedPatternMessage = "Failed pattern match at " <> runModuleName mn <> " " <> displayStartEndPos ss

        guardsToIL :: Either [(Guard Ann, Expr Ann)] (Expr Ann) -> m [AST]
        guardsToIL (Left gs) = traverse genGuard gs where
          genGuard (cond, val) = do
            cond' <- valueToIL Nothing cond
            val'   <- valueToIL Nothing val
            return $ AST.IfElse (unbox' bool cond') (AST.Block [AST.Return val']) Nothing

        guardsToIL (Right v) = return . AST.Return <$> valueToIL Nothing v

    -- | Generate code in the simplified intermediate representation for a pattern match
    -- binder.
    binderToIL :: Text -> [AST] -> Binder Ann -> m [AST]
    binderToIL _ done NullBinder{} = return done
    binderToIL varName done (LiteralBinder _ l) =
      literalToBinderIL varName done l
    binderToIL varName done (VarBinder _ ident) =
      return (AST.VariableIntroduction (identToIL ident)
               (AST.TypeSpecSeq AST.Auto Nothing) (Just (AST.Var varName)) : done)
    binderToIL varName done (ConstructorBinder (_, _, _, Just IsNewtype) _ _ [b]) =
      binderToIL varName done b
    binderToIL varName done (ConstructorBinder
                             (_, _, _, Just (IsConstructor ctorType fields)) _
                              (Qualified _ (ProperName ctor)) bs) = do
      il <- go (zip fields bs) done
      return $ case ctorType of
        ProductType -> il
        SumType ->
          [AST.IfElse (AST.InstanceOf (AST.Var varName)
                        (AST.StringLiteral (mkString ctor)))
            (AST.Block il)
            Nothing]
      where
        go :: [(Ident, Binder Ann)] -> [AST] -> m [AST]
        go [] done' = return done'
        go ((field, binder) : remain) done' = do
          argVar <- freshName'
          done'' <- go remain done'
          il <- binderToIL argVar done'' binder
          return (AST.VariableIntroduction argVar (AST.TypeSpecSeq AST.Auto Nothing)
                  (Just $ accessorString (mkString $ identToIL field) $ AST.Var varName) : il)
  
    binderToIL _ _ ConstructorBinder{} =
      internalError "binderToIL: Invalid ConstructorBinder in binderToIL"
    binderToIL varName done (NamedBinder _ ident binder) = do
      il <- binderToIL varName done binder
      return (AST.VariableIntroduction (identToIL ident)
              (AST.TypeSpecSeq AST.Auto Nothing) (Just (AST.Var varName)) : il)

    literalToBinderIL :: Text -> [AST] -> Literal (Binder Ann) -> m [AST]
    literalToBinderIL varName done (NumericLiteral num@Left{}) =
      return [AST.IfElse 
               (AST.Binary AST.EqualTo (unbox' int $ AST.Var varName)
                 (AST.NumericLiteral num)) (AST.Block done) Nothing]
    literalToBinderIL varName done (NumericLiteral num@Right{}) =
      return [AST.IfElse 
               (unbox' bool
                 (foldl (\fn a -> AST.App fn [a])
                   (AST.Indexer (AST.Var C.eq) (AST.Var C.dataEq))
                   [ AST.Indexer (AST.Var C.eqNumber) (AST.Var C.dataEq)
                   , AST.Var varName
                   , AST.NumericLiteral num
                   ]))
               (AST.Block done) Nothing]
    literalToBinderIL varName done (CharLiteral c) =
      return [AST.IfElse 
               (AST.Binary AST.EqualTo
                 (unbox' string $ AST.Var varName)
                 (AST.StringLiteral (fromString [c]))) (AST.Block done) Nothing]
    literalToBinderIL varName done (StringLiteral str) =
      return [AST.IfElse 
              (AST.Binary AST.EqualTo (unbox' string $ AST.Var varName)
               (AST.StringLiteral str)) (AST.Block done) Nothing]
    literalToBinderIL varName done (BooleanLiteral True) =
      return [AST.IfElse (unbox' bool $ AST.Var varName)
               (AST.Block done) Nothing]
    literalToBinderIL varName done (BooleanLiteral False) =
      return [AST.IfElse 
               (AST.Unary AST.Not (unbox' bool $ AST.Var varName)) (AST.Block done) Nothing]
    literalToBinderIL varName done (ObjectLiteral bs) = go done bs
      where
        go :: [AST] -> [(PSString, Binder Ann)] -> m [AST]
        go done' [] = return done'
        go done' ((prop, binder):bs') = do
          propVar <- freshName'
          done'' <- go done' bs'
          il <- binderToIL propVar done'' binder
          return (AST.VariableIntroduction propVar (AST.TypeSpecSeq AST.Auto Nothing)
                  (Just (accessorString prop (AST.Var varName))) : il)
    literalToBinderIL varName done (ArrayLiteral bs) = do
      il <- go done 0 bs
      return [AST.IfElse (AST.Binary AST.EqualTo
                           (arrayLength $ AST.Var varName)
                           (AST.NumericLiteral (Left (fromIntegral $ length bs))))
               (AST.Block il) Nothing]
      where
        go :: [AST] -> Integer -> [Binder Ann] -> m [AST]
        go done' _ [] = return done'
        go done' index (binder:bs') = do
          elVar <- freshName'
          done'' <- go done' (index + 1) bs'
          il <- binderToIL elVar done'' binder
          return (AST.VariableIntroduction elVar
                  (AST.TypeSpecSeq AST.Auto Nothing)
                   (Just (AST.Indexer (AST.NumericLiteral (Left index))
                           (AST.Var varName))) : il)
        arrayLength :: AST -> AST
        arrayLength a = AST.App (AST.Var arrayLengthFn) [a]

    unbox' :: Text -> AST -> AST
    unbox' _ v@AST.NumericLiteral{} = v
    unbox' _ v@AST.BooleanLiteral{} = v
    unbox' _ v@AST.StringLiteral{}  = v
    unbox' _ v@AST.Binary{}         = v
    unbox' t v = AST.App (AST.StringLiteral $ mkString t) [v]
