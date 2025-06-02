{-# LANGUAGE TemplateHaskell #-}

module Main where

import Control.Monad
import Language.Haskell.TH
import Control.Applicative
import Control.Monad.Logic

cases :: Foldable f => f (Logic a) -> Logic a
cases = foldr interleave mzero 

{-
  % parent(out String, out String)
  parent("sarah", "john").
  parent("arnold", "john").
  parent("john", "anne").

  ----------------------
  forall a, b. parent(|a, b) <-> (a = "sarah", b = "john")
                              ;  (a = "arnold", b = "john")
                              ;  (a = "john", b = "anne")

  ---------------------- 
  parent :: () -> Logic (String, String)
  parent () = pure ("sarah", "john") `interleave` pure ("arnold", "john") `interleave` ("john", "anne")
-}
{-
  % grandparent(in String, out String)
  grandparent(Person, Grandchild) :- parent(Person, X), parent(X, Grandchild).

  ---------------------- 
  forall a, b. grandparent(a|b) <-> (exists x, y. x = a. y = parent(x), b = parent(y))

  ---------------------- 
  grandparent :: String -> Logic String 
  grandparent a =
    cases [
      (case a of 
        x -> do { (x1, y) <- parent (); guard (x1 == x)
                ; (y1, b) <- parent (); guard (y1 == y)
                ; pure b 
                }
        _ -> mzero
      )
    ]
-}

{-
  % last(in a, in [a])
  last(X, [X]).
  last(X, _:L) :- last(X, L).

  --------------------------
  forall a, b. last a b <-> (exists x. x = a, [x] = b)
                         ;  (exists x, l. x = a, (_:l) = b, last x l)

  -------------------------- 
  last :: a -> [a] -> Logic ()
  last a b 
    | x <- a, [x] <- b = pure ()
    | x <- a, (_:l) <- b = last x l
-}

parent :: () -> Logic (String, String)
parent () = 
  cases [
    pure ("sarah", "john"),
    pure ("arnold", "john"),
    pure ("john", "anne")
  ]

grandparent :: String -> Logic String 
grandparent a =
  cases [
    (case a of 
      x -> do { (x1, y) <- parent (); guard (x1 == x)
              ; (y1, b) <- parent (); guard (y1 == y)
              ; pure b 
              }
      _ -> mzero
    )
  ]


last_ :: Eq a => a -> [a] -> Logic ()
last_ a b =
  cases [
    (case (a, b) of
      (x1, [x2]) -> do { guard (x1 == x2); pure () }
      _          -> mzero
    ),
    (case (a, b) of
      (x1, (_:l1)) -> do { last_ x1 l1 }
      _            -> mzero 
    )
  ]
  -- | x1 <- a, [x2] <- b = do 
  --   guard (x1 == x2)
  --   pure ()
  -- | x <- a, (_:l) <- b = last_ x l
  -- | otherwise = mzero

-- if term `t` used for an output variable `x` is grounded, append `guard (t == xi)`

main :: IO ()
main = do 
  -- let grandparents = observeAll (do 
  --                                 (a, b) <- grandparent 
  --                                 guard (b == "Anne")
  --                                 pure (a, b)
  --                               )
  -- putStrLn $ "Anne's grandparents are: " <> show grandparents
  let rs = observeAll (last_ 2 [3,2,1])
  print rs
