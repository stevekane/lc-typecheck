import Data.Maybe (Maybe(..), fromMaybe)

type VariableName = String

type Environment = [(VariableName, Term)]

data Substitution 
  = VariableName := Term 
  deriving (Eq, Show)

data Term
  = Universe
  | NaturalNumber
  | Zero
  | Successor Term
  | RecNat Term Term Term Term
  | PI VariableName Term Term
  | Lambda VariableName Term Term
  | Application Term Term
  | Variable VariableName
  deriving (Eq)

-- Lookup term bound to variable name in environment. may fail.
(⊢) :: Environment -> VariableName -> Maybe Term
e ⊢ s = foldl matchKey Nothing e where
  matchKey (Just t) p                = Just t
  matchKey Nothing (s', t) | s == s' = Just t
  matchKey _ _                       = Nothing

-- Substitute instances of bound variables found in term e with new term u
(→) :: Substitution -> Term -> Term
s@(v' := e') → e = case e of 
  Variable v | v == v'   -> e'
  Universe               -> Universe
  PI v ρ ρ' | v /= v'    -> PI v (s → ρ) (s → ρ')
  Lambda v τ e | v /= v' -> Lambda v (s → τ) (s → e) 
  Application e e'       -> Application (s → e) (s → e')
  NaturalNumber          -> NaturalNumber
  Zero                   -> Zero
  Successor n            -> Successor (s → n)
  RecNat m z f n         -> RecNat (s → m) (s → z) (s → f) (s → n)
  _                      -> e

-- Evaluation in an environment
(↓) :: Environment -> Term -> Term
env ↓ e = case e of
  Variable v       -> fromMaybe (Variable v) (env ⊢ v)
  Universe         -> Universe
  PI v ρ ρ'        -> PI v (env ↓ ρ) (env ↓ ρ')
  Lambda v τ e     -> Lambda v τ (env ↓ e)
  Application e e' ->
    case (env ↓ e, env ↓ e') of
      (Lambda x τ b, u') -> (x := u') → b
      (u, u')            -> Application u u'
  NaturalNumber    -> NaturalNumber
  Zero             -> Zero
  Successor n      -> Successor (env ↓ n)
  RecNat m z s n ->
    case env ↓ n of 
      Zero         -> env ↓ z
      Successor n' -> env ↓ Application s (env ↓ RecNat m z s n')
      _            -> RecNat m z s n

-- Type-checking in an environment
(∈) :: Environment -> Term -> Maybe Term
env ∈ e = case e of
  Variable v    -> env ⊢ v
  Universe      -> return Universe
  PI x ρ ρ' -> do
    let τ     = env ↓ ρ
    Universe <- env ∈ ρ
    let env'  = (x,τ) : env
    Universe <- env' ∈ ρ'
    return Universe
  Lambda x τ e -> do
    let env' = (x,τ) : env
    τ'      <- env' ∈ e
    return (PI x τ τ')            
  Application e e' -> do
    PI x τ τ' <- env ∈ e
    σ         <- env ∈ e'
    require (σ == τ)
    let τ'' = (x := e') → τ'
    return τ''
  NaturalNumber -> Just Universe
  Zero -> Just NaturalNumber
  Successor n -> do
    NaturalNumber <- env ∈ n
    return NaturalNumber
  RecNat m z s n -> do
    error "YOU HAVE NOT IMPLEMENTED TypeChecking of RecNat"

require :: Bool -> Maybe ()
require b = if b then Just () else Nothing

instance Show Term where
  show (Variable v)       = v
  show Universe           = "U"
  show NaturalNumber      = "ℕ"
  show (PI α ρ ρ')        = "Π(" ++ α ++ ":" ++ show ρ ++ ")" ++ show ρ'
  show Zero               = "Z"
  show (Successor n)      = "S" ++ show n
  show (RecNat τ z s n)   = "RecNat " ++ show τ ++ " " ++ show z ++ " " ++ show s ++ " " ++ show n
  show (Lambda v τ e)     = "(λ" ++ v ++ ":" ++ show τ ++ "." ++ show e ++ ")"
  show (Application e e') = "(" ++ show e ++ " " ++ show e' ++ ")"

env = []

polymorphicid = 
  Lambda "t" Universe $ 
  Lambda "x" (Variable "t") $
  Variable "x"

add1 = 
  Lambda "n" NaturalNumber $ 
  Successor (Variable "n")

evaluateAndCheck env p = do
  τ <- env ∈ p
  let t = env ↓ p
  return (p, t, τ)

main = do
  print $ env ∈ polymorphicid
  print $ env ↓ polymorphicid

  print $ env ∈ Application polymorphicid NaturalNumber
  print $ env ↓ Application polymorphicid NaturalNumber
  print $ env ∈ Application (Application polymorphicid NaturalNumber) (Successor Zero)
  print $ env ↓ Application (Application polymorphicid NaturalNumber) (Successor Zero)
  print $ env ∈ Application add1 (Application (Application polymorphicid NaturalNumber) (Successor Zero))
  print $ env ↓ Application add1 (Application (Application polymorphicid NaturalNumber) (Successor Zero))

  print $ env ∈ RecNat NaturalNumber Zero (Lambda "x" NaturalNumber (Variable "x")) (Successor Zero)