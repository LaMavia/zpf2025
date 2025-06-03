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
import Control.Monad (forM)
import Data.Char (toLower)
import Data.Foldable (toList)

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
     , tsDecls :: Prog 
     , tsParams :: [Name]
     }

type TransM = StateT TransState Q 

-- instance Quote TransM where

runTransM :: Prog -> TransM a -> Q a
runTransM prog m = fst <$> runStateT m s0 
  where 
    s0 = TS { tsGroundedVars = S.empty
            , tsDecls = prog
            , tsAliases = M.empty
            , tsParams = []
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
  let inPattern = [TupP paramPatterns]
  clauses <- mapM (scoped . transClause) dclauses
  return $ FunD p [ Clause inPattern (GuardedB $ clauses <> [(NormalG (ConE (mkName "True")), VarE (mkName "mempty"))]) [] ]
  where 
    genParam :: Int -> TransM Pat
    genParam i = do
      n <- lNewName (showString "arg" $ show i)
      markGrounded n
      prependParam n
      return (VarP n) 

transClause :: DClause -> TransM (Guard, Exp)
transClause (terms, body) = do 
  params <- getParams
  patterns <- mapM patternOfAbsTerm terms
  eqs <- assertEqualAllAliases
  return (
    PatG (zipWith BindS patterns $ fmap VarE params), 
    DoE Nothing $ toList $ eqs Sq.>< Sq.fromList [
      NoBindS $ VarE (mkName "pure") `AppE` TupE []
    ])

patternOfAbsTerm :: Abs.Term -> TransM Pat
patternOfAbsTerm = 
  \case
    Abs.TStr _ s -> return $ LitP (StringL s)
    Abs.TInt _ i -> return $ LitP (IntegerL i)
    Abs.TVar _ (Abs.UIdent (haskifyVarName -> v)) -> do
      let n = mkName v
      a <- lNewName v 
      addAlias n a
      return $ VarP a
    Abs.TIgnore _ -> return WildP
    Abs.TList _ ts -> ListP <$> mapM patternOfAbsTerm ts
    Abs.TCons _ x r -> do 
      xp <- patternOfAbsTerm x
      rp <- patternOfAbsTerm r
      return $ ParensP $ ConP (mkName ":") [] [xp, rp] 

markGrounded :: Name -> TransM ()
markGrounded n = modify (\s -> s { tsGroundedVars = S.insert n (tsGroundedVars s) })

prependParam :: Name -> TransM ()
prependParam n = modify (\s -> s { tsParams = n:tsParams s })

reverseParams :: TransM ()
reverseParams = modify (\s -> s { tsParams = reverse (tsParams s) })

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
      modify (\s -> s{tsAliases=M.delete n (tsAliases s)})
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
