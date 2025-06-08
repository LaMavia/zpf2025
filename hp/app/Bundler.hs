{-# LANGUAGE LambdaCase, TemplateHaskell #-}
module Bundler where

import Data.Functor.Identity
import Control.Monad.Trans.State.Lazy (StateT, modify, runStateT)
import qualified Abs as A
import Data.Map (Map)
import qualified Data.Map as Map
import Language.Haskell.TH
import qualified Data.Set as S 
import Data.Set (Set)

failure :: a -> b
failure _ = undefined

type B = StateT BState Identity

type Prog = Map String Decl

data BState = BS { bsDecls :: Map String Decl }

type DClause = ([A.Term], [A.Stmt]) 

data Decl
  = Decl { dIdent :: String
         , dIn :: [Type]
         , dOut :: [Type]
         , dTypeVars :: Set Name
         , dClauses :: [DClause]
         }
    deriving (Show)

runB :: B a -> Map String Decl
runB m = Map.map (\d -> d {dClauses=reverse (dClauses d)}) 
       . bsDecls 
       . snd 
       . runIdentity 
       $ runStateT m (BS (Map.empty) )

bundle :: A.Program -> B ()
bundle (A.Program _ defs) = mapM_ bundleDef defs

bundleDef :: A.Def -> B ()
bundleDef = \case
  A.TDef _ (A.LIdent name) typeargs1 typeargs2 -> 
    let dec = Decl { dIdent=name
                   , dIn=(haskt <$> typeargs1)
                   , dOut=(haskt <$> typeargs2)
                   , dTypeVars=(foldr S.union S.empty $ fmap typeVars $ typeargs1 <> typeargs2)
                   , dClauses = []
                   }
    in modify (\s -> s { bsDecls = Map.insert name dec (bsDecls s) })
  A.DFact _ (A.DHeader _ (A.LIdent name) args) -> 
    modify (\s -> s {
      bsDecls=Map.update (\d -> Just (d{
        dClauses=(args, []):dClauses d
      })) name (bsDecls s)
    })
  A.DRule _ (A.DHeader _ (A.LIdent name) args) stmts -> 
    modify (\s -> s {
      bsDecls=Map.update (\d -> Just (d{
        dClauses=(args, stmts):dClauses d
      })) name (bsDecls s)
    })  


haskt :: A.TypeArg -> Type
haskt = \case
  A.TALit _ (A.UIdent x) -> ConT (mkName x)
  A.TAGen _ (A.LIdent x) -> VarT (mkName x)
  A.TAList _ t -> ListT `AppT` (haskt t)
  A.TAApp _ ft xs ->  foldl AppT (haskt ft) $ fmap haskt xs
  A.TATup _ ts -> foldl AppT (TupleT (length ts)) $ fmap haskt ts 

typeVars :: A.TypeArg -> Set Name
typeVars = \case
  A.TALit {} -> S.empty 
  A.TAGen _ (A.LIdent x) -> S.singleton (mkName x)
  A.TAList _ t -> typeVars t
  A.TAApp _ ft xs -> foldr S.union (typeVars ft) $ fmap typeVars xs
  A.TATup _ ts -> foldr S.union S.empty $ fmap typeVars ts


