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
import Debug.Trace (traceShow, trace)
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
            (\x u -> UInfixE x (UnboundVarE (mkName "<|>")) u) 
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
  traceShow params groundParams
  eqs <- assertEqualAllAliases
  stmts <- transClauseBody body
  epilogue <- generateEpilogue outTerms
  return $ traceShow stmts $ ParensE
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
      traceShow (outs, pres) $ return $ pres Sq.:|> (NoBindS (VarE (mkName "pure") `AppE` TupE ((Just . VarE) <$> outs)))


transClauseBody :: [Abs.Stmt] -> TransM (Seq Stmt)
transClauseBody = fmap (foldr (Sq.><) Sq.empty) . mapM transStmt 

transStmt :: Abs.Stmt -> TransM (Seq Stmt)
transStmt = \case 
  Abs.STrue {} -> return Sq.empty 
  Abs.SFalse {} -> return $ Sq.singleton (NoBindS (UnboundVarE (mkName "mempty")))
  Abs.SAss _ (Abs.UIdent (haskifyVarName -> v)) t -> unifyEq (mkName v) t
    
  _ -> return $ Sq.singleton $ NoBindS (VarE (mkName "pure") `AppE` TupE [])
-- transStmt _ = 

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
unifyEq n t = traceShow ("AAA", n, t) $ do
  gn <- findGroundedName n
  case gn of 
    Just n' -> Sq.singleton . NoBindS . UInfixE (VarE n') (UnboundVarE (mkName "==")) <$> transGroundedTerm t
    Nothing -> do
      addAlias n n
      trace "I'm here" $ markGrounded n 
      gt <- transGroundedTerm t
      return $ Sq.singleton $ BindS (VarP n) $ (AppE (UnboundVarE (mkName "pure"))) $ gt


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
