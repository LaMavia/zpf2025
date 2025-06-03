{-# LANGUAGE TemplateHaskell #-}

module QQ where

import Language.Haskell.TH.Quote (QuasiQuoter (..))
import Language.Haskell.TH
import Text.Pretty.Simple (pPrint)
import Control.Monad.IO.Class (liftIO)

import Transformer 
import Bundler
import Par ( pProgram, myLexer )

hp :: QuasiQuoter 
hp = QuasiQuoter {
      quoteDec = qd,
      quotePat = notHandled "patterns",
      quoteExp = notHandled "expressions",
      quoteType = notHandled "types"
     } 
  where 
    notHandled things = error $
          things ++ " are not handled by the regex quasiquoter."
    qd :: String -> Q [Dec]
    qd s = case pProgram (myLexer s) of
            Left err -> error (show err)
            Right tree -> do 
              q <- runTransM (runB $ bundle tree) transProg
              pPrint q
              liftIO (print (ppr_list q))
              -- pPrint (ppr_list q)
              return q
