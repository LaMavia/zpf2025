{-# Language TemplateHaskell, TypeSynonymInstances #-}
module Transformer where

import Language.Haskell.TH 
import Control.Monad.Trans.State.Lazy (StateT, modify, runStateT, gets)
import qualified Data.Set as S 
import Data.Set (Set)
import Data.Map (Map)
import qualified Data.Map as M
import qualified Abs as Abs
import Bundler ( Decl (..), Prog )
import Control.Monad.Logic (LogicT)
import Control.Monad.Trans.Class (lift)

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
  TS { tsGroundedVars :: Set String
     , tsAliases :: Map String (Set String)
     , tsDecls :: Prog 
     }

type TransM = StateT TransState Q 

-- instance Quote TransM where

runTransM :: Prog -> TransM a -> Q a
runTransM prog m = fst <$> runStateT m (TS { tsGroundedVars = S.empty, tsDecls = prog, tsAliases = M.empty})

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
transDecl (Decl {dIdent=p, dIn=inArgs, dOut=outArgs, dClauses=clauses}) = do 
  let pName = mkName p
  sig <- transSignature pName inArgs outArgs
  dec <- transBody pName 
  pure [sig, dec]

transSignature :: Name -> [Type] -> [Type] -> TransM Dec
transSignature p ins outs = 
  return $ SigD p (ArrowT `AppT` genTupleT ins `AppT` (ConT ''TransM `AppT` (genTupleT outs)))
  where
    genTupleT :: [Type] -> Type 
    genTupleT xs = foldl AppT (TupleT (length xs)) xs

transBody :: Name -> TransM Dec 
transBody p = return $ FunD p [ Clause [ WildP ] (NormalB (VarE (mkName "undefined"))) [] ]

