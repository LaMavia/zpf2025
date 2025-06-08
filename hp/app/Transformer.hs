{-# Language TemplateHaskell, TypeSynonymInstances, QuasiQuotes, DoAndIfThenElse, LambdaCase, ViewPatterns #-}
module Transformer where

import Language.Haskell.TH 
import Control.Monad.Trans.State.Lazy (StateT, modify, runStateT, gets, get, put)
import qualified Data.Set as S 
import Data.Set (Set)
import Data.Map (Map)
import qualified Data.Map as M
import qualified Abs as Abs
import Bundler ( Decl (..), Prog, DClause, tupleType )
import Control.Monad.Logic (LogicT, Logic, once)
import Control.Monad.Trans.Class (lift)
import qualified Data.Sequence as Sq
import Data.Sequence (Seq)
import Text.Pretty.Simple (pPrint)
import Data.Maybe (fromMaybe)
import Control.Monad (forM, zipWithM, forM_, when, guard, unless)
import Data.Char (toLower)
import Data.Foldable (toList)
import Data.List (uncons)
import Control.Applicative ((<|>))

type LogicIO = LogicT IO

{- For names use lookupValueName -}
data TransState = 
  TS { tsGroundedVars :: Set Name
     , tsAliases :: Map Name (Set Name)
     , tsGroundedAliases :: Map Name (Set Name)
     , tsDecls :: Prog 
     , tsParams :: [Name]
     , tsOutputs :: [Name]
     , tsProg :: Prog
     }

type TransM = StateT TransState Q 

-- instance Quote TransM where

runTransM :: Prog -> TransM a -> Q a
runTransM prog m = fst <$> runStateT m s0 
  where 
    s0 = TS { tsGroundedVars = S.empty
            , tsDecls = prog
            , tsAliases = M.empty
            , tsGroundedAliases = M.empty
            , tsParams = []
            , tsOutputs = []
            , tsProg = prog
            }

-- stdDecls :: Q [Dec]
-- stdDecls = do
--   -- caseName <- newName 
--   caseDecs <- [d| 
--     cases :: Foldable f => f (TransM a) -> TransM a 
--     cases = foldr interleave mzero
--    |]
--   pure (caseDecs ++ [])
 

transProg :: TransM [Dec] 
transProg = do 
  prog <- gets tsDecls
  fmap concat $ mapM transDecl $ fmap snd $ M.toList prog 

transDecl :: Decl -> TransM [Dec]
transDecl (Decl {dIdent=p, dIn=inArgs, dTypeVars=tvars, dOut=outArgs, dClauses=clauses}) = scoped $ do 
  let pName = mkName p
  sig <- transSignature pName tvars inArgs outArgs
  dec <- transBody pName (length inArgs) (length outArgs) clauses
  pure [sig, dec]

transSignature :: Name -> Set Name -> [Type] -> [Type] -> TransM Dec
transSignature p (toList -> tvars) ins outs = 
  return $ SigD 
    p 
    (
      ForallT 
        [ PlainTV tv InferredSpec | tv <- tvars ] 
        [ ConT ''Eq `AppT` (VarT tv) | tv <- tvars ] 
        (ArrowT `AppT` tupleType ins `AppT` (ConT ''Logic `AppT` (tupleType outs)))
    )
  where
    genTupleT :: [Type] -> Type 
    genTupleT xs = foldl AppT (TupleT (length xs)) xs

transBody :: Name -> Int -> Int -> [DClause] -> TransM Dec 
transBody p nin nout dclauses = do 
  -- paramPatterns <- mapM genParam [1..nin]
  -- reverseParams
  -- params <- getParams
  -- let paramse = tupleExp $ fmap VarE params
  -- let inPattern = [tuplePattern paramPatterns]
  paramn <- lNewName "input"
  let paramse = VarE paramn
  let inPattern = [VarP paramn]

  mapM_ genOutput [1..nout]
  reverseOutputs

  clauses <- mapM (scoped . transClause paramse nin nout) dclauses
  if null clauses
    then 
      return $ FunD p [Clause inPattern (NormalB (UnboundVarE 'mempty)) []]
    else
      return $ 
        FunD 
          p 
          [ Clause inPattern (
            NormalB $ 
              (UnboundVarE 'foldl1) `AppE`
                (ParensE $ UnboundVarE '(<|>)) `AppE`
                (ListE clauses) 
              --
              -- foldr 
              --   (\x u -> UInfixE x (UnboundVarE (mkName "<|>")) u) 
              --   (VarE (mkName "mempty"))
              --   clauses
          ) [] ]
  where 
    genParam :: Int -> TransM Pat
    genParam i = do
      n <- lNewName (showString "arg" $ show i)
      markGrounded n
      prependParam n
      return (VarP n) 

    genOutput :: Int -> TransM Name
    genOutput i = do
      n <- lNewName (showString "out" $ show i)
      prependOutput n
      return n




transClause :: Exp -> Int -> Int -> DClause -> TransM Exp
transClause paramse nin nout (terms, body) = do 
  let (inTerms, outTerms) = partitionInOut nin nout terms 
  patterns <- mapM patternOfAbsTerm inTerms
  params <- getParams
  groundParams
  eqs <- assertEqualAllAliases
  stmts <- transClauseBody body
  epilogue <- generateEpilogue outTerms
  return $ ParensE $ DoE Nothing $ toList $ Sq.fromList [
      BindS (tuplePattern patterns) $ pureE `AppE` paramse  
    ] Sq.>< eqs Sq.>< stmts Sq.>< epilogue
  -- return $ ParensE
  --            (CaseE 
  --               paramse
  --               [
  --                 Match 
  --                   (TupP patterns)
  --                   (NormalB 
  --                     $ DoE Nothing $ toList $ eqs Sq.>< stmts Sq.>< epilogue 
  --                   )
  --                   [],
  --                 Match 
  --                   WildP
  --                   (NormalB $ VarE (mkName  "mempty"))
  --                   []
  --               ]
  --            )
  where 
    generateEpilogue :: [Abs.Term] -> TransM (Seq Stmt)
    generateEpilogue ts = do 
      outs <- getOutputs
      let ret = NoBindS (pureE `AppE` tupleExp (VarE <$> outs))
      pres <- foldr (Sq.><) Sq.empty <$> zipWithM unifyEq outs ts
      return $ pres Sq.:|> ret
      -- es <- mapM transGroundedTerm ts
      -- return $ Sq.fromList [(LetS [ValD (VarP o) (NormalB e) [] | o <- outs, e <- es]), ret]


transClauseBody :: [Abs.Stmt] -> TransM (Seq Stmt)
transClauseBody = fmap (foldr (Sq.><) Sq.empty) . mapM transStmt 

transStmt :: Abs.Stmt -> TransM (Seq Stmt)
transStmt = \case 
  Abs.STrue {} -> return Sq.empty 
  Abs.SFalse {} -> return $ Sq.singleton (NoBindS (UnboundVarE 'mempty))
  Abs.SAss _ (Abs.UIdent (haskifyVarName -> v)) t -> unifyEq (mkName v) t
  Abs.SCall _ (Abs.LIdent p) argTerms -> do 
    (outPats, pn, inExps, outAppend) <- genCallStmt p argTerms
    return $ Sq.fromList [
      BindS (tuplePattern outPats) $ (UnboundVarE pn) `AppE` tupleExp inExps
      ] Sq.>< outAppend 
  Abs.SIs _ (Abs.UIdent (haskifyVarName -> x)) absiexp -> do 
    let xn = mkName x
    mn <- findGroundedName xn 
    exp <- transIExp absiexp
    case mn of 
      Just n -> return $ Sq.singleton $ guardEq (VarE n) exp
      Nothing -> do
        a <- lNewName x 
        addAlias xn a 
        markGrounded a 
        markGrounded xn

        return $ Sq.fromList [
            BindS (VarP a) (pureE `AppE` exp)
          ]
  Abs.SRel _ a op b -> do
    ae <- transIExp a
    be <- transIExp b 
    let opn = case op of 
            Abs.LTH {} -> '(<)
            Abs.LE {} -> '(<=)
            Abs.GTH {} -> '(>)
            Abs.GE {} -> '(>=)
            Abs.EQU {} -> '(==)
            Abs.NE {} -> '(/=)
    return $ Sq.fromList [
      guardE $ ParensE (UInfixE ae (UnboundVarE opn) be)
      ]
  Abs.SMod _ mod ts (Abs.LIdent proc) argTerms -> do
    (rps, ras) <- unzip <$> mapM prepareOutArg ts
    let rp = tuplePattern rps
    let ra = foldr (Sq.><) Sq.empty ras 
    case mod of
      Abs.MExt {} -> do 
        when (length rps /= 1) (error $ showString "Ext call expected exactly 1 output but got«" $ show (length rps))
        argExps <- mapM transGroundedTerm argTerms
        return $ Sq.fromList [
            BindS (rps !! 0) $ pureE `AppE` foldl AppE (UnboundVarE (mkName proc)) argExps
          ] Sq.>< ra
      Abs.MOnce {} -> do
        unless (null rps) $ error $ showString "Once call expected no outputs but got «" $ show (length rps) 
        (outPats, procn, inExps, append) <- genCallStmt proc argTerms        
        return $ Sq.fromList [
            BindS (tuplePattern outPats) $ UnboundVarE 'once `AppE` ((UnboundVarE procn) `AppE` tupleExp inExps)
          ] Sq.>< append
      -- Abs.MCollect {} -> do 
      --   mprocdec <- getDecl proc 
      --   case mprocdec of 
      --     Nothing -> error $ showString "Unknown predicate «" $ showString proc $ "»"
      --     Just (Decl {dIn=pin, dOut=pout}) -> do
      --       let npin = length pin
      --       let npout = length pout
      --       let (inArgs, outArgs) = partitionInOut npin npout argTerms
      --       inExps <- mapM transGroundedTerm inArgs
      --       (outPats, outAppends) <- unzip <$> mapM prepareOutArg outArgs
      --       let outAppend = foldr (Sq.><) Sq.empty outAppends
      --       return $ Sq.fromList [
      --           BindS rp 
      --             $ (UnboundVarE (mkName "pure")) `AppE` 
      --               UnboundVarE (mkName "observeAll") `AppE` 
      --               DoE Nothing (toList retstmts)
      --         ] Sq.>< ra 



  where 
    prepareOutArg :: Abs.Term -> TransM (Pat, Seq Stmt)
    prepareOutArg = \case 
      (Abs.TStr _ str) -> return (LitP (StringL str), Sq.empty)
      (Abs.TInt _ int) -> return (LitP (IntegerL int), Sq.empty)
      (Abs.TVar _ (Abs.UIdent (haskifyVarName -> v))) -> do
        let vn = mkName v
        mgn <- findGroundedName vn 
        case mgn of 
          (Just n) -> do
            temp <- lNewName v 
            let g = guardEq (VarE temp) (VarE n)
            return (VarP temp, Sq.singleton g)
          Nothing -> do
            a <- lNewName v 
            addAlias vn a 
            markGrounded vn 
            return (VarP a, Sq.empty)
      (Abs.TList _ ts) -> do 
        (pats, appends) <- unzip <$> mapM prepareOutArg ts 
        let append = foldr (Sq.><) Sq.empty appends 
        return (ListP pats, append)
      (Abs.TTup _ ts) -> do
        (pats, appends) <- unzip <$> mapM prepareOutArg ts 
        let append = foldr (Sq.><) Sq.empty appends 
        return (tuplePattern pats, append)
      (Abs.TCons _ a b) -> do
        (ap, aa) <- prepareOutArg a 
        (bp, ba) <- prepareOutArg b
        return (UInfixP ap '(:) bp, aa Sq.>< ba)
      (Abs.TIgnore {}) -> return (WildP, Sq.empty)
      (Abs.TConstr _ (Abs.UIdent con) ts) -> do
        let conn = mkName con 
        (tps, tas) <- unzip <$> mapM prepareOutArg ts 
        let ta = foldr (Sq.><) Sq.empty tas 
        return (ConP conn [] tps, ta)

    genCallStmt :: String -> [Abs.Term] -> TransM ([Pat], Name, [Exp], Seq Stmt)
    genCallStmt p argTerms = do 
      let pn = mkName p
      md  <- getDecl p
      case md of 
        Nothing -> error $ showString "Unknown predicate «" $ showString p $ "»"
        Just (Decl {dIn=pin, dOut=pout}) -> do
          let npin = length pin
          let npout = length pout
          let (inArgs, outArgs) = partitionInOut npin npout argTerms
          inExps <- mapM transGroundedTerm inArgs
          (outPats, outAppends) <- unzip <$> mapM prepareOutArg outArgs
          let outAppend = foldr (Sq.><) Sq.empty outAppends
          return (outPats, pn, inExps, outAppend)


transIExp :: Abs.IExp -> TransM Exp
transIExp = \case 
  Abs.IEVar _ (Abs.UIdent (haskifyVarName -> x)) -> do
    let xn = mkName x 
    mxn <- findGroundedName xn 
    case mxn of 
      Nothing -> error $ showString "Free variable in expression: " $ show x 
      Just n -> return (VarE n)
  Abs.IELit _ i -> return (LitE (IntegerL i))
  Abs.IENeg _ t -> (UnboundVarE '(-) `AppE`) <$> transIExp t
  Abs.IEMul _ a op b -> do
    let opn = case op of 
                Abs.Times {} -> '(*)
                Abs.Div {} -> 'div
                Abs.Mod {} -> 'mod
    ae <- transIExp a
    be <- transIExp b 
    return $ UInfixE ae (UnboundVarE opn) be
  Abs.IEAdd _ a op b -> do
    let opn = case op of 
                Abs.Plus {} -> '(+)
                Abs.Minus {} -> '(-)
    ae <- transIExp a
    be <- transIExp b 
    return $ UInfixE ae (UnboundVarE opn) be


transGroundedTerm :: Abs.Term -> TransM Exp
transGroundedTerm = \case 
  Abs.TStr _ s -> return $ LitE $ StringL s 
  Abs.TInt _ i -> return $ LitE $ IntegerL i
  Abs.TVar _ (Abs.UIdent (haskifyVarName -> v)) -> do
    let n = mkName v
    gn <- findGroundedName n
    case gn of 
      Just n' -> return (VarE n')
      Nothing -> error $ showString "Ungrounded term «" . shows v $ "»." 
  Abs.TIgnore _ -> return (VarE (mkName "_"))
  Abs.TList _ ts -> ListE <$> mapM transGroundedTerm ts
  Abs.TCons _ a b -> do 
    ae <- transGroundedTerm a
    be <- transGroundedTerm b 
    return $ ParensE (UInfixE ae (ConE '(:)) be)
  
unifyEq :: Name -> Abs.Term -> TransM (Seq Stmt)
unifyEq n t = do
  gn <- findGroundedName n
  case gn of 
    Just n' -> Sq.singleton . NoBindS . UInfixE (VarE n') (UnboundVarE '(==)) <$> transGroundedTerm t
    Nothing -> do
      addAlias n n
      markGrounded n 
      gt <- transGroundedTerm t
      return $ Sq.singleton $ BindS (VarP n) $ AppE pureE $ gt

patternOfAbsTerm :: Abs.Term -> TransM Pat
patternOfAbsTerm = 
  \case
    Abs.TStr _ s -> return $ LitP (StringL s)
    Abs.TInt _ i -> return $ LitP (IntegerL i)
    Abs.TVar _ (Abs.UIdent (haskifyVarName -> v)) -> do
      let n = mkName v
      a <- lNewName v 
      addAlias n a
      markGrounded a
      markGrounded n
      return $ VarP a
    Abs.TIgnore _ -> return WildP
    Abs.TList _ ts -> ListP <$> mapM patternOfAbsTerm ts
    Abs.TCons _ x r -> do 
      xp <- patternOfAbsTerm x
      rp <- patternOfAbsTerm r
      return $ ParensP $ ConP '(:) [] [xp, rp] 
    Abs.TConstr _ (Abs.UIdent con) ts -> do
      let conn = mkName con 
      tps <- mapM patternOfAbsTerm ts 
      return $ ConP conn [] tps

groundParams :: TransM ()
groundParams = do
  params <- getParams 
  forM_ params markGrounded

markGrounded :: Name -> TransM ()
markGrounded n = do 
  aliases <- getAliases n 
  modify (\s -> s { tsGroundedVars = S.insert n (tsGroundedVars s)
                  , tsGroundedAliases = M.insertWith S.union n aliases (tsGroundedAliases s)
                  })

findGroundedName :: Name -> TransM (Maybe Name)
findGroundedName n = do
  gals <- gets (M.findWithDefault S.empty n . tsGroundedAliases)
  return $ fmap fst $ uncons $ toList gals

prependParam :: Name -> TransM ()
prependParam n = modify (\s -> s { tsParams = n:tsParams s })

reverseParams :: TransM ()
reverseParams = modify (\s -> s { tsParams = reverse (tsParams s) })

prependOutput :: Name -> TransM ()
prependOutput n = modify (\s -> s { tsOutputs = n:tsOutputs s })

reverseOutputs :: TransM ()
reverseOutputs = modify (\s -> s { tsOutputs = reverse (tsOutputs s) })

scoped :: TransM a -> TransM a
scoped m = do
  s <- get 
  r <- m 
  put s
  return r

lNewName :: String -> TransM Name 
lNewName = lift . newName

getAliases :: Name -> TransM (Set Name)
getAliases n = gets (M.findWithDefault S.empty n . tsAliases)

getParams :: TransM [Name]
getParams = gets tsParams

getOutputs :: TransM [Name]
getOutputs = gets tsOutputs

assertEqualAllAliases :: TransM (Seq Stmt)
assertEqualAllAliases = do 
  keys <- gets (fmap fst . M.toList . tsAliases)
  r <- forM keys assertEqualAliases 
  return $ foldr (Sq.><) Sq.empty r

assertEqualAliases :: Name -> TransM (Seq Stmt)
assertEqualAliases n = do
  aliases <- getAliases n 
  case S.toList aliases of
    [] -> pure Sq.empty
    [_] -> pure Sq.empty
    x:xs -> do 
      forM_ (x:xs) markGrounded 
      modify (\s -> s{tsAliases=M.delete n (tsAliases s), tsGroundedAliases=M.insertWith S.union n aliases (tsGroundedAliases s)})
      pure  $ Sq.singleton 
            $ guardE
              $ AppE 
                (UnboundVarE 'and) 
                (ListE [ UInfixE (VarE x) (UnboundVarE '(==)) (VarE x') 
                        | x' <- xs 
                        ]
                )

addAlias :: Name -> Name -> TransM ()
addAlias n a = 
  modify (\s -> s {tsAliases=M.insertWith S.union n (S.fromList [a]) (tsAliases s)})

haskifyVarName :: String -> String
haskifyVarName = fmap toLower

partitionInOut :: Int -> Int -> [a] -> ([a],[a])
partitionInOut nin nout xs = 
  let (ins, rest) = splitAt nin xs 
  in (ins, take nout rest)

getDecl :: String -> TransM (Maybe Decl)
getDecl p = gets (M.lookup p . tsProg)

guardE :: Exp -> Stmt
guardE e = NoBindS $ VarE 'guard `AppE` e

guardEq :: Exp -> Exp -> Stmt
guardEq a b = guardE $ ParensE $ UInfixE a (UnboundVarE '(==)) b

tuplePattern :: [Pat] -> Pat 
tuplePattern [p] = p
tuplePattern ps = TupP ps

tupleExp :: [Exp] -> Exp 
tupleExp [e] = e
tupleExp es = TupE $ fmap Just es

pureE :: Exp
pureE = UnboundVarE 'pure

