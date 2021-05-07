module Homomorphism where

{-
Homomorphism f G H <=> f (lit a) <^> f (lit b) = f (lit a <^> lit b)
                       f (lit a)               = lit a

f (lit 2) <^> f (lit 3) = f (lit a <^> lit b)
(2, 'f') <^> (3, 'f')   = f (2 * 3)
(2 * 3, 'f')            = (2 * 3, 'f')

f (lit a) = lit a
(a, 'f')  = (a, 'f')
-}

class Structure k where
  lit :: Int -> k Int
  (<^>) :: k Int -> k Int -> k Int

newtype G a = G a         deriving (Show)
newtype H a = H (a, Char) deriving (Show)

instance Structure G where
  lit = G
  G l <^> G r = G (l * r)

instance Structure H where
  lit = f . G
  H (l,_) <^> H (r,_) = f (G (l * r))

f (G l) = H (l, 'f')

myprog :: Structure s => Int -> Int -> s Int
myprog x y = lit x <^> lit y

printG :: G Int -> String
printG = show

printH :: H Int -> String
printH = show