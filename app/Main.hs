module Main where

import qualified Data.Map as Map (Map(..), empty, lookup, insert)

import System.IO
import Data.Char (isAlpha, isAlphaNum, isNumber, isLower)
import Control.Applicative (Alternative(..))
import Control.Monad ((>=>))

data UnOp
  = Negate
  | Not
  deriving (Eq, Ord, Show)

data BinOp
  = Add
  | Mul
  | Sub
  | And
  | Or
  deriving (Eq, Ord, Show)

data TernOp
  = Cond
  deriving (Eq, Ord, Show)

data E
  = Var Char
  | Bool Bool
  | Nat Int
  | RecNat E E E -- target: Nat, base: τ, step: (Nat → τ → τ)
  | Lambda Char T E
  | Apply E E
  | UnaryOp UnOp
  | BinaryOp BinOp
  | TernaryOp TernOp
  | Partial BinOp E
  | Pair E E
  | Fst T -- T is really a type annotation
  | Snd T -- T is really a type annotation
  | Inl E T
  | Inr E T
  | Case E E T -- Ts are really type annotations
  deriving (Eq, Ord)

data T
  = Boolean
  | NaturalNumber
  | Arrow T T
  | Product T T
  | Sum T T
  deriving (Eq, Ord)

instance Show E where
  show (Var c)        = [ c ]
  show (Bool b)       = show b
  show (Nat n)        = show n
  show (RecNat t b s) = "(recnat " ++ show t ++ " " ++ show b ++ " "  ++ show s ++ ")"
  show (Lambda c t e) = "λ" ++ [ c ] ++ ":" ++ show t ++ "." ++ show e
  show (Apply u v)    = "(" ++ show u ++ " " ++ show v ++ ")"
  show (UnaryOp o)    = show o
  show (BinaryOp o)   = show o
  show (TernaryOp o)  = show o
  show (Partial o l)  = show o ++ " " ++ show l
  show (Pair l r)     = "(" ++ show l ++ "," ++ show r ++ ")"
  show (Fst τ)        = "Fst:" ++ show τ
  show (Snd τ)        = "Snd:" ++ show τ
  show (Inl l τ)      = "Inl:" ++ show τ ++ "." ++ show l
  show (Inr r τ)      = "Inr:" ++ show τ ++ "." ++ show r
  show (Case l r τ)   = "[" ++ show l ++ " , " ++ show r ++ "]:" ++ show τ

instance Show T where
  show Boolean       = "B"
  show NaturalNumber = "N"
  show (Arrow l r)   = "(" ++ show l ++ " → " ++ show r ++ ")"
  show (Product l r) = "(" ++ show l ++ " × " ++ show r ++ ")"
  show (Sum l r)     = "(" ++ show l ++ " + " ++ show r ++ ")"



-- TYPECHECKING
when b a = if b then Right a else Left ""

-- TODO: Could probably make this more elegant mapping from Maybe -> Either
typeOf env (Bool b)             = return Boolean
typeOf env (Nat b)              = return NaturalNumber
typeOf env (Fst (Product τ τ')) = return $ Arrow (Product τ τ') τ
typeOf env (Snd (Product τ τ')) = return $ Arrow (Product τ τ') τ'
typeOf env (UnaryOp Negate)     = return $ Arrow NaturalNumber NaturalNumber
typeOf env (UnaryOp Not)        = return $ Arrow Boolean Boolean
typeOf env (BinaryOp Add)       = return $ Arrow NaturalNumber (Arrow NaturalNumber NaturalNumber)
typeOf env (BinaryOp Sub)       = return $ Arrow NaturalNumber (Arrow NaturalNumber NaturalNumber)
typeOf env (BinaryOp Mul)       = return $ Arrow NaturalNumber (Arrow NaturalNumber NaturalNumber)
typeOf env (BinaryOp And)       = return $ Arrow Boolean (Arrow Boolean Boolean)
typeOf env (BinaryOp Or)        = return $ Arrow Boolean (Arrow Boolean Boolean)

typeOf env (Var v) = case Map.lookup v env of
  (Just τ) -> Right τ
  _        -> Left ""

typeOf env (RecNat n e f) = do
  NaturalNumber                        <- typeOf env n
  σ                                    <- typeOf env e
  (Arrow NaturalNumber (Arrow σ' σ'')) <- typeOf env f
  when (σ == σ' && σ == σ'') σ

typeOf env (Apply (Apply (Apply (TernaryOp Cond) e) e') b) = do
  τ  <- typeOf env e
  τ' <- typeOf env e'
  σ  <- typeOf env b
  when (τ == τ' && σ == Boolean) τ

typeOf env (Inl l (Sum τ τ')) = do
  etl <- typeOf env l
  when (etl == τ) (Sum τ τ')

typeOf env (Inr r (Sum τ τ')) = do
  etr <- typeOf env r
  when (etr == τ') (Sum τ τ')

typeOf env (Partial b l) = case (b, typeOf env l) of
  (Add, Right NaturalNumber) -> return $ Arrow NaturalNumber NaturalNumber
  (Sub, Right NaturalNumber) -> return $ Arrow NaturalNumber NaturalNumber
  (Mul, Right NaturalNumber) -> return $ Arrow NaturalNumber NaturalNumber
  (And, Right Boolean)       -> return $ Arrow Boolean Boolean
  (Or,  Right Boolean)       -> return $ Arrow Boolean Boolean
  _                          -> Left ""

typeOf env (Case l r (Arrow (Sum τ τ') σ)) = do
  let etl = Arrow τ σ
  let etr = Arrow τ' σ
  atl <- typeOf env l
  atr <- typeOf env r
  when (etl == atl && etr == atr) (Arrow (Sum τ τ') σ)

typeOf env (Lambda c τ e) = do
  let env' = Map.insert c τ env
  τ' <- typeOf env' e
  return (Arrow τ τ')

typeOf env (Apply e e') = do
  (Arrow a b) <- typeOf env e
  τ'          <- typeOf env e'
  when (a == τ') b

typeOf env (Pair l r) = do
  τ  <- typeOf env l
  τ' <- typeOf env r
  return (Product τ τ')

typeOf env _ = Left ""



-- EVALUATION
walk f (Var x)        = f $ Var x
walk f (Bool b)       = f $ Bool b
walk f (Nat n)        = f $ Nat n
walk f (RecNat t b s) = f $ RecNat (walk f t) (walk f b) (walk f s)
walk f (Lambda v τ b) = f $ Lambda v τ (walk f b)
walk f (Apply l r)    = f $ Apply (walk f l) (walk f r)
walk f (UnaryOp o)    = f $ UnaryOp o
walk f (BinaryOp o)   = f $ BinaryOp o
walk f (TernaryOp o)  = f $ TernaryOp o
walk f (Partial o e)  = f $ Partial o (walk f e)
walk f (Pair l r)     = f $ Pair (walk f l) (walk f r)
walk f (Fst τ)        = f $ Fst τ
walk f (Snd τ)        = f $ Snd τ
walk f (Inl e τ)      = f $ Inl (walk f e) τ
walk f (Inr e τ)      = f $ Inr (walk f e) τ
walk f (Case l r τ)   = f $ Case (walk f l) (walk f r) τ

substitute v t (Var v') = if v == v' then t else Var v'
substitute v t e        = e

reduce (Lambda c τ e) = Lambda c τ (reduce e)
reduce (Partial o l)  = Partial o (reduce l)
reduce (Pair l r)     = Pair (reduce l) (reduce r)
reduce (Case l r τ)   = Case (reduce l) (reduce r) τ
reduce (RecNat n b s) = reducerecnat (reduce n) (reduce b) (reduce s)
reduce (Apply l r)    = reduceapp (reduce l) (reduce r)
reduce e              = e

reducerecnat (Nat 0) b _ = b
reducerecnat (Nat n) b s = reduce $ Apply (Apply s (Nat (n-1))) (RecNat (Nat (n-1)) b s)
reducerecnat n b s       = RecNat n b s

reduceapp (BinaryOp o) l                                     = Partial o (reduce l)
reduceapp (Lambda c τ e) r                                   = reduce (walk (substitute c r) e)
reduceapp (Fst τ) (Pair l r)                                 = l
reduceapp (Snd τ) (Pair l r)                                 = r
reduceapp (Case l _ _) (Inl a _)                             = reduce (Apply l a)
reduceapp (Case _ r _) (Inr b _)                             = reduce (Apply r b)
reduceapp (Apply (Apply (TernaryOp Cond) e) e') (Bool True)  = e
reduceapp (Apply (Apply (TernaryOp Cond) e) e') (Bool False) = e'
reduceapp (UnaryOp o) l                                      = reduceappunary o l
reduceapp (Partial o l) r                                    = reduceapppartial o l r
reduceapp l r                                                = Apply l r

reduceappunary Negate (Nat a) = Nat (-a)
reduceappunary Not (Bool b)   = Bool (not b)
reduceappunary o l            = Apply (UnaryOp o) l

reduceapppartial Add (Nat a) (Nat b)   = Nat (a + b)
reduceapppartial Mul (Nat a) (Nat b)   = Nat (a * b)
reduceapppartial Sub (Nat a) (Nat b)   = Nat (a - b)
reduceapppartial And (Bool a) (Bool b) = Bool (a && b)
reduceapppartial Or (Bool a) (Bool b)  = Bool (a || b)
reduceapppartial o l r                 = Apply (Partial o l) r

-- PARSING
newtype Parser m a = Parser (String -> m (a, String))

instance Monad m => Functor (Parser m) where
  fmap f p = Parser $ parse p >=> \(l,s') -> return (f l, s')

instance Monad m => Applicative (Parser m) where
  pure    = return
  f <*> a = f >>= \f' -> f' <$> a

instance Monad m => Monad (Parser m) where
  return a = Parser $ return . mkpair a
  m >>= f  = Parser $ parse m >=> \(l,s') -> parse (f l) s'

instance (Monad m, Alternative m) => Alternative (Parser m) where
  empty   = empty
  a <|> b = Parser $ \s -> parse a s <|> parse b s

instance Alternative (Either a) where
  empty          = empty
  (Left _) <|> r = r
  l        <|> r = l

instance MonadFail (Either a) where
  fail s = empty


mkpair a b  = (a,b)
parse (Parser p) = p
readChar c = read [ c ]
expected s x xs = "EXPECTED: " ++ s ++ ". FOUND:" ++ [ x ] ++ ". BEFORE: " ++ take 15 xs ++ "..."

-- Generic parsers
satisfy msg f = Parser p where
  p (x: xs) = if f x then Right (x, xs) else Left (msg x xs)
  p []      = Left "Nothing to parse."
pany = Parser p where
  p (x:xs) = Right (x, xs)
  p []     = Left "EXPECTED: Any. ENCOUNTERED: End of input."
peof = Parser p where
  p [] = Right ((), "")
  p xs = Left $ "EXPECTED: End Of File. ENCOUNTERED " ++ take 15 xs ++ "..."

pchar c               = satisfy (expected [ c ]) (c ==)
pword                 = foldr ((>>) . pchar) (pure ())
optional p            = Just <$> p <|> return Nothing
p_a_b l a m b f       = l >> a >>= \a' -> m >> b >>= \b' -> return (f a' b')
p_a_b_ l a m b r f    = l >> a >>= \a' -> m >> b >>= \b' -> r >> return (f a' b')
p_a_b_c l a m b r c f = l >> a >>= \a' -> m >> b >>= \b' -> r >> c >>= \c' -> return (f a' b' c')

pkeyword w τ          = pword w >> pure τ
pidentifier           = satisfy (expected "Identifier") isAlpha
pnumber               = satisfy (expected "Number") isNumber
pλ                    = pchar 'λ'
plparen               = pchar '('
prparen               = pchar ')'
plbracket             = pchar '['
prbracket             = pchar ']'
pcolon                = pchar ':'
pcross                = pword " × "
pplus                 = pword " + "
parrow                = pword " → "
pcomma                = pchar ','
pperiod               = pchar '.'
pspace                = pchar ' '

-- Term parsing
pe
  =   pnegate
  <|> pnot
  <|> padd
  <|> pmul
  <|> psub
  <|> pand
  <|> por
  <|> pfst
  <|> psnd
  <|> ppair
  <|> pinl
  <|> pinr
  <|> pcase
  <|> pcond <|> pifte
  <|> plambda <|> plet
  <|> papplication
  <|> pnat
  <|> pbool
  <|> pvar
  <|> precnat

pnegate      = pkeyword "negate" (UnaryOp Negate)
pnot         = pkeyword "not" (UnaryOp Not)
padd         = pkeyword "add" (BinaryOp Add)
pmul         = pkeyword "mul" (BinaryOp Mul)
psub         = pkeyword "sub" (BinaryOp Sub)
pand         = pkeyword "and" (BinaryOp And)
por          = pkeyword "or" (BinaryOp Or)
ppair        = p_a_b_ plparen pe pcomma pe prparen Pair
pfst         = pword "fst:" >> Fst <$> pProduct
psnd         = pword "snd:" >> Snd <$> pProduct
pinl         = p_a_b (pword "inl ") pe pcolon pType Inl
pinr         = p_a_b (pword "inr ") pe pcolon pType Inr
pcase        = p_a_b_c plbracket pe pcomma pe (prbracket >> pcolon) pType Case
plambda      = p_a_b_c pλ pidentifier pcolon pType pperiod pe Lambda
papplication = p_a_b_ plparen pe pspace pe prparen Apply
pvar         = Var <$> pidentifier
pnat         = Nat . readChar <$> pnumber
pbool        = (pword "True" >> return (Bool True)) <|> (pword "False" >> return (Bool False))

plet = do
  optional $ many $ pchar '\n'
  pword "let"
  pspace
  v <- pidentifier
  pcolon
  τ <- pType
  optional (many $ pchar ' ')
  pchar '≡'
  optional (many $ pchar ' ')
  e <- pe
  pspace
  pword "in"
  al1 (pchar '\n' <|> pchar ' ')
  i <- pe
  return (Apply (Lambda v τ i) e)

pcond = do
  plparen
  pword "cond"
  pspace
  e <- pe
  pspace
  e' <- pe
  pspace
  b <- pe
  prparen
  return (Apply (Apply (Apply (TernaryOp Cond) e) e') b)

pifte = do
  plparen
  pword "if"
  pspace
  b <- pe
  pword " then "
  e <- pe
  pword " else "
  e' <- pe
  pword ")"
  return (Apply (Apply (Apply (TernaryOp Cond) e) e') b)

precnat = do
  plparen
  pword "recnat"
  pspace
  t <- pe
  pspace
  b <- pe
  pspace
  s <- pe
  prparen
  return (RecNat t b s)

-- Type parsing
pBool    = pkeyword "B" Boolean
pNat     = pkeyword "N" NaturalNumber
pArrow   = p_a_b_ plparen pType parrow pType prparen Arrow
pProduct = p_a_b_ plparen pType pcross pType prparen Product
pSum     = p_a_b_ plparen pType pplus pType prparen Sum

pType
  =   pArrow
  <|> pProduct
  <|> pSum
  <|> pBool
  <|> pNat

run s = do
  (t, s') <- parse pe s
  τ       <- typeOf Map.empty t
  return (reduce t, τ)

nosugar = "(λf:N.(negate f) 5)"
lettest = "let f:N ≡ 5 in (negate f)"
letnested = "let f:(N → N) ≡ negate in \nlet n:N ≡ 5 in (f 5)"

s = pchar ' '
nl = pchar '\n'
ws = s <|> nl
ows = optional ws
al1 p = (:) <$> p <*> many p
parselet = al1 ws >> pword "let" >> al1 ws >> return "let"

-- fake type and parser to check parsing type aliases
data TypeVar = TypeVar String T deriving (Show)

atleast1Space = al1 (pchar ' ' <|> pchar '\n')
plettype = do
  pword "let"
  atleast1Space
  τ <- al1 (satisfy (expected "Type Variable") isAlpha)
  atleast1Space
  pchar '≡'
  atleast1Space
  τ' <- pType
  atleast1Space
  pword "in"
  atleast1Space
  return $ TypeVar τ τ'

{-
There are a few problems we need to solve related to user-defined types.

The first is the ability to define recursive types:

data Tree
  = Node N Tree Tree
  | Leaf N

Following our pattern from before we might try to convert it as follows:

let Tree ≡ ((N × (Tree × Tree)) + N) in
let Node ≡ λx:N.λl:Tree.λr:Tree.(inl (x, (l, r)):Tree) in
let Leaf ≡ λx:N.(inr x):Tree in
... program ...

This definition is clearly not adequate as Tree is defined in terms of itself
( it's a recursive data type so who is really surprised ... ).

Let's think about the definition of primitive recursion over the naturals 
and see if we can intuit what might be needed to define these recursive structures.

We know that primitive recursion takes a sort of "iterator" which is guaranteed to
eventually terminate because it takes the value of a natural number always down by one.
Additionally, we can say that a datatype.

It seems that a definition which is known to never recurse is one in which there are
no terms in the sum that do NOT contain a reference to the type itself.

Maybe we could invent something...

recnat initialValue base step(n-1, accum)

Basically, we encode the number of times we will recurse statically.

sum = λx.λn.x + n + 1
recnat 3 0 sum

3 + 2 + 1 = 6

sum 2 (recnat 2 0 sum)
sum 2 (sum 1 (recnat 1 0 sum))
sum 2 (sum 1 (sum 0 (recnat 0 0 sum)))
sum 2 (sum 1 (sum 0 0))
sum 2 (sum 1 1)
sum 2 3
6

Reading a bit about type theory the following claim may be found:

  data List a = Nil | Cons a (List a)

is represented in type theory as:

  λα.μβ.1 + α × β
    with two constructors
  nilα      = roll (inl ())
  consα x l = roll (inr (x,l))

We also find:

  data Nat = Zero | Succ Nat

In type theory:

  nat = μα.1 + α

You read this as:
  μ denotes a recursive data type
  α denotes the name of the whole type
  1 is the unit type representing the constructor Zero that takes no arguments
  α is the constructor Succ that takes an argument which is the type α itself

We could look at Monomorphic List of Int in the same way:

  data List = Nil | Cons Int List

In type theory, this is represented:

  μα.1 + (Nat × α)

Isorecursive are defined as a relation between 
  μα.T 
and its unroll 
  T[α := μα.T]
in which the two terms are considered two distinct and disjoint types with 
special constructs roll and unroll which form an ismorphism between them. 
  roll:T[α := μα.T] -> μα.T
  unroll:μα.T -> T[α := μα.T]

Structural recurion vs Generative recursion:

  Generative recursion is a recursive function which invokes itself on 
  something calculated from some or all of the original input data.

  Structural recursion is a recursive function which invokes itself on
  a subset of the original input data.

Importantly, all structurally recursive functions on finite data structures can be shown
to terminate via structural induction. This means that these data structures have a sound 
and definite type.

Maybe it's not a problem to say the following:

  μMaybe.Nothing | Just N

In type theory, this desugars to the following:

  μMaybe.() + N

If we defined this in our type environment:

  Γ,Maybe:() + N
-}


main = do
  handle   <- openFile "kane/program.kane" ReadMode
  hSetEncoding handle utf8
  contents <- hGetContents handle
  print $ parse pe contents
  print $ run contents
  hClose handle
  print $ run nosugar
  print $ run lettest
  print $ run letnested
  print $ parse parselet "  \nlet\n "
  print $ parse plettype "let Maybe ≡ (N + N) in "