{-# Language TemplateHaskell, TypeSynonymInstances, QuasiQuotes, DoAndIfThenElse, LambdaCase, ViewPatterns #-}
module Transformer where

import Language.Haskell.TH 
import Control.Monad.Trans.State.Lazy (StateT, modify, runStateT, gets, get, put)
import qualified Data.Set as S 
import Data.Set (Set)
import Data.Map (Map)
import qualified Data.Map as M
import qualified Abs as Abs
import Bundler ( Decl (..), Prog, DClause )
import Control.Monad.Logic (LogicT, Logic)
import Control.Monad.Trans.Class (lift)
import qualified Data.Sequence as Sq
import Data.Sequence (Seq)
import Text.Pretty.Simple (pPrint)
import Data.Maybe (fromMaybe)
import Control.Monad (forM, zipWithM, forM_)
import Data.Char (toLower)
import Data.Foldable (toList)
import Data.List (uncons)

{- 
RULES:

% V - term vars  
% isGrounded({G}, t) = V(t) `subset` vars(G)
% isVar - is a simple variable, ie []
% tild({G}, t) = if not isGrounded(t) { t } else { tilded(t) }

Stmt:
  (G, [| True |])
  --------------- (True)



  (G, [| False |])
  ---------------- (False) 
  output { empty } % equivalent to `guard False`


  (G, [| p(x1..xn, y1..ym) |]) | p(p1..pn | q1..qm) in G
  ------------------------------------------------------ (Predicate Call) 
  for i = 1..m {
    % dopracuj dla pół ustalonych np. [X_Ungrounded, T_Grounded].
    % jakieś szukanie maksymalnego ustalonego poddrzewa
    if isGrounded(yi) && not isVar(yi) {
      output {
         let $ti = $yi 
      } 
      G.vars += ti
    }
  }

  output {
    (${ map tild {y1..ym} },) <- p (x1..xn)
  }

  for i = 1..m {
    if ti in vars G {
      output { guard (${tilded yi} == ti) }
    } 
  }

  for i = 1..m {
    % precalculate the set of grounded variables
    G.vars = G.vars `union` V(tild yi)
  }


  (G, [| p(x1..xn, y1..ym) |]) | p(p1..pn | q1..qm) not in G
  ---------------------------------------------------------- (Procedure Call) 
  output {
    _ <- p(x1..xn, y1..ym)
  }


  (G, [| X = T |]) | isGrounded(X) && isGrounded(T)
  -------------------------------- (Grounded Ass.)
  output { guard (X == T) }


  (G, [| X = T |]) | not isGrounded(X) && isGrounded(T) 
  ----------------------------------------------------- (Ungrounded Ass.)
  % again, consider semi-grouned X
  output { let X = T }

-}

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
        [ ConT (mkName "Eq") `AppT` (VarT tv) | tv <- tvars ] 
        (ArrowT `AppT` genTupleT ins `AppT` (ConT ''Logic `AppT` (genTupleT outs)))
    )
  where
    genTupleT :: [Type] -> Type 
    genTupleT xs = foldl AppT (TupleT (length xs)) xs

transBody :: Name -> Int -> Int -> [DClause] -> TransM Dec 
transBody p nin nout dclauses = do 
  paramPatterns <- mapM genParam [1..nin]
  reverseParams
  params <- getParams
  let paramse = TupE [Just (VarE p) | p <- params]
  let inPattern = [TupP paramPatterns]

  mapM_ genOutput [1..nout]
  reverseOutputs

  clauses <- mapM (scoped . transClause paramse nin nout) dclauses
  return $ 
    FunD 
      p 
      [ Clause inPattern (
        NormalB $ 
          foldr 
            (\x u -> UInfixE x (UnboundVarE (mkName "interleave")) u) 
            (VarE (mkName "mempty"))
            clauses
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
  return $ ParensE
             (CaseE 
                paramse
                [
                  Match 
                    (TupP patterns)
                    (NormalB 
                      $ DoE Nothing $ toList $ eqs Sq.>< stmts Sq.>< epilogue 
                    )
                    [],
                  Match 
                    WildP
                    (NormalB $ VarE (mkName  "mempty"))
                    []
                ]
             )
  where 
    generateEpilogue :: [Abs.Term] -> TransM (Seq Stmt)
    generateEpilogue ts = do 
      outs <- getOutputs
      pres <- foldr (Sq.><) Sq.empty <$> zipWithM unifyEq outs ts
      return $ pres Sq.:|> (NoBindS (VarE (mkName "pure") `AppE` TupE ((Just . VarE) <$> outs)))


transClauseBody :: [Abs.Stmt] -> TransM (Seq Stmt)
transClauseBody = fmap (foldr (Sq.><) Sq.empty) . mapM transStmt 

transStmt :: Abs.Stmt -> TransM (Seq Stmt)
transStmt = \case 
  Abs.STrue {} -> return Sq.empty 
  Abs.SFalse {} -> return $ Sq.singleton (NoBindS (UnboundVarE (mkName "mempty")))
  Abs.SAss _ (Abs.UIdent (haskifyVarName -> v)) t -> unifyEq (mkName v) t
  Abs.SCall _ (Abs.LIdent p) argTerms -> do 
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
        {- all inArgs need to be grounded, just pass them, no guards -}

        {- for now assume that every outArg is either fully grounded or fully free -}
        {-
          for arg in outArgs {
            if isGrounded(arg) {
              pass new var `temp_arg` in place of arg,
              append { guard (temp_arg == arg) }
            } else if isFree(arg) {
              pass arg to call
              markGrounded arg
            }
          }
        -}
        return $ Sq.fromList [
          BindS (TupP outPats) $ (UnboundVarE pn) `AppE` TupE (Just <$> inExps)
          ] Sq.>< outAppend 
  Abs.SIs _ (Abs.UIdent (haskifyVarName -> x)) absiexp -> do 
    let xn = mkName x
    mn <- findGroundedName xn 
    exp <- transIExp absiexp
    case mn of 
      Just n -> return $ Sq.singleton $ NoBindS $ (UnboundVarE (mkName "guard")) `AppE` (ParensE (UInfixE (VarE n) (UnboundVarE (mkName "==")) exp)) 
      Nothing -> do
        a <- lNewName x 
        addAlias xn a 
        markGrounded a 
        markGrounded xn

        return $ Sq.fromList [
            BindS (VarP a) (UnboundVarE (mkName "pure") `AppE` exp)
          ]
  Abs.SRel _ a op b -> do
    ae <- transIExp a
    be <- transIExp b 
    let opn = mkName $ case op of 
            Abs.LTH {} -> "<"
            Abs.LE {} -> "<="
            Abs.GTH {} -> ">"
            Abs.GE {} -> ">="
            Abs.EQU {} -> "=="
            Abs.NE {} -> "/="
    return $ Sq.fromList [
      NoBindS (UnboundVarE (mkName "guard") `AppE` ParensE (UInfixE ae (UnboundVarE opn) be))
      ]

  where 
    isTermGrounded :: Abs.Term -> TransM Bool 
    isTermGrounded = \case 
      Abs.TStr {} -> pure True 
      Abs.TInt {} -> pure True 
      Abs.TIgnore {} -> pure False 
      Abs.TList _ ts -> and <$> traverse isTermGrounded ts
      Abs.TCons _ a b -> and <$> traverse isTermGrounded [a, b]
      Abs.TVar _ (Abs.UIdent (haskifyVarName -> v)) -> do 
        let n = mkName v 
        mgn <- findGroundedName n 
        case mgn of 
          Nothing -> pure False 
          Just {} -> pure True

    freeTermName :: Abs.Term -> TransM (Maybe Name) 
    freeTermName = \case 
      Abs.TVar _ (Abs.UIdent (haskifyVarName -> v)) -> do
        let n = mkName v
        mgn <- findGroundedName n
        case mgn of 
          Nothing -> pure $ Just n 
          Just {} -> pure Nothing
      _ -> pure Nothing

    prepareOutArg :: Abs.Term -> TransM (Pat, Seq Stmt)
    prepareOutArg t = do
      -- temp <- lNewName "temp"
      -- let tempP = VarP temp
      -- let tempE = VarE temp
      -- (p, appends) <- unifCetBind t tempE 
      -- return (tempP, appends Sq.>< Sq.fromList [
      --     BindS p tempE
      --   ])
      itg <- isTermGrounded t 
      mtn <- freeTermName t
      if itg 
        then (do 
          te <- transGroundedTerm t
          temp <- lNewName "temp"
          markGrounded temp
          return (
            VarP temp,
            Sq.singleton $ NoBindS $ (UnboundVarE (mkName "guard")) `AppE` (ParensE $ UInfixE (VarE temp) (UnboundVarE (mkName "==")) te) 
            )
        )
        else case mtn of 
              Just n -> do 
                addAlias n n -- ???
                markGrounded n
                return (VarP n, Sq.empty)
              Nothing -> error $ showString "Complicated term: " $ shows t "."
                
transIExp :: Abs.IExp -> TransM Exp
transIExp = \case 
  Abs.IEVar _ (Abs.UIdent (haskifyVarName -> x)) -> do
    let xn = mkName x 
    mxn <- findGroundedName xn 
    case mxn of 
      Nothing -> error $ showString "Free variable in expression: " $ show x 
      Just n -> return (VarE n)
  Abs.IELit _ i -> return (LitE (IntegerL i))
  Abs.IENeg _ t -> (UnboundVarE (mkName "-") `AppE`) <$> transIExp t
  Abs.IEMul _ a op b -> do
    let opn = mkName $ case op of 
                Abs.Times {} -> "*"
                Abs.Div {} -> "div"
                Abs.Mod {} -> "mod"
    ae <- transIExp a
    be <- transIExp b 
    return $ UInfixE ae (UnboundVarE opn) be
  Abs.IEAdd _ a op b -> do
    let opn = mkName $ case op of 
                Abs.Plus {} -> "+"
                Abs.Minus {} -> "-"
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
  Abs.TIgnore _ -> do
    gs <- gets tsGroundedVars
    gks <- gets tsGroundedAliases
    return (VarE (mkName "_"))
    -- error $ "Ungrounded term «_». Grounded: " <> show gs <> "|" <> show gks
  Abs.TList _ ts -> ListE <$> mapM transGroundedTerm ts
  Abs.TCons _ a b -> do 
    ae <- transGroundedTerm a
    be <- transGroundedTerm b 
    return $ ParensE (UInfixE ae (ConE (mkName ":")) be)
  
unifyEq :: Name -> Abs.Term -> TransM (Seq Stmt)
unifyEq n t = do
  gn <- findGroundedName n
  case gn of 
    Just n' -> Sq.singleton . NoBindS . UInfixE (VarE n') (UnboundVarE (mkName "==")) <$> transGroundedTerm t
    Nothing -> do
      addAlias n n
      markGrounded n 
      gt <- transGroundedTerm t
      return $ Sq.singleton $ BindS (VarP n) $ (AppE (UnboundVarE (mkName "pure"))) $ gt

unifCetBind :: Abs.Term -> Exp -> TransM (Pat, Seq Stmt)
unifCetBind targ srce = do
  case targ of
    (Abs.TStr {}) -> auxGrounded 
    (Abs.TInt {}) -> auxGrounded 
    (Abs.TIgnore {}) -> return (WildP, Sq.empty)
    (Abs.TVar _ (Abs.UIdent (haskifyVarName -> v))) -> do
      let vn = mkName v
      mgn <- findGroundedName vn 
      case mgn of 
        Just n -> do 
          tempn <- lNewName v
          gs <- guardEq (VarE n) srce
          return (VarP tempn, Sq.singleton gs)
        Nothing -> do 
          n <- lNewName v 
          addAlias vn n 
          markGrounded n 
          return (VarP n, Sq.empty)
    (Abs.TList _ ts) -> do 
      temps <- mapM (\_ -> lNewName "temp") ts 
      rs <- zipWithM unifCetBind ts $ fmap VarE $ temps
      let (pats, appends) = unzip rs
      return (
        ListP (VarP <$> temps), 
        foldr (Sq.><) (
          Sq.fromList [
            BindS (ListP pats) (ListE $ fmap VarE temps) 
          ]
          ) appends 
        )

    
  where 
    auxGrounded :: TransM (Pat, Seq Stmt)
    auxGrounded = do
      targe <- transGroundedTerm targ
      guards <- guardEq targe srce
      pat <- patternOfAbsTerm targ
      return (pat, Sq.singleton guards)


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
      return $ ParensP $ ConP (mkName ":") [] [xp, rp] 

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
            $ NoBindS 
            $ AppE 
              (VarE (mkName "guard"))
              $ AppE 
                (VarE (mkName "and")) 
                (ListE [ UInfixE (VarE x) (UnboundVarE (mkName "==")) (VarE x') 
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

guardEq :: Exp -> Exp -> TransM Stmt
guardEq a b = return $ NoBindS $ VarE (mkName "guard") `AppE` (ParensE $ UInfixE a (UnboundVarE (mkName "==")) b)
