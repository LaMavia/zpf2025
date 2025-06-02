{-# LANGUAGE LambdaCase, TemplateHaskell #-}
module Bundler where

import Data.Functor.Identity
import Control.Monad.Trans.State.Lazy (StateT, modify, runStateT)
import qualified Abs as A
import Data.Map (Map)
import qualified Data.Map as Map
import Language.Haskell.TH

failure :: a -> b
failure _ = undefined

type B = StateT BState Identity

type Prog = Map String Decl

data BState = BS { bsDecls :: Map String Decl }

data Decl
  = Decl { dIdent :: String
         , dIn :: [Type]
         , dOut :: [Type]
         , dClauses :: [([A.Term], [A.Stmt])] 
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
  A.TAApp _ ft xs ->  foldr AppT (haskt ft) $ fmap haskt xs

