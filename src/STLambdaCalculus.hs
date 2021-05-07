module STLambdaCalculus where

-- λ→ from paper
data CheckableTerm
  = Inferable InferableTerm
  | Abstraction CheckableTerm
  deriving (Show, Eq)

data InferableTerm
  = Annotated CheckableTerm Type
  | Free Name
  | Bound Int
  | InferableTerm :@: CheckableTerm
  deriving (Show, Eq)

data Name
  = Global String
  | Local Int
  | Quote Int
  deriving (Show, Eq)

data Type
  = Base Name
  | Function Type Type
  deriving (Show, Eq)

data Value
  = VLambda (Value -> Value)
  | VNeutral Neutral

data Neutral
  = NFree Name
  | NApplication Neutral Value

data Kind 
  = Star 
  deriving (Show)

data Info
  = HasKind Kind
  | HasType Type
  deriving (Show)

type Context = [ (Name, Info) ]

type Environment = [ Value ]

throwError         = Left
typeMismatch       = throwError "type mismatch"
unknownIdentifier  = throwError "unknown identifier"
illegalApplication = throwError "illegal application"
unless b err       = if b then Right () else err

typeCheckable i ctx (Inferable inf) τ = do 
  τ' <- typeInferable i ctx inf
  unless (τ == τ') typeMismatch
typeCheckable i ctx (Abstraction e) (Function τ τ') = 
  let i'   = i + 1
      ctx' = (Local i, HasType τ) : ctx
      e'   = substituteCheckable 0 (Free (Local i)) e
  in  typeCheckable i' ctx' e' τ'
typeCheckable i ctx _ _ = typeMismatch
typeInferable i ctx (Annotated ct t) = do 
  kind ctx t Star
  typeCheckable i ctx ct t
  return t
typeInferable i ctx (Free name) = case lookup name ctx of 
  Just (HasType τ) -> return τ
  _                -> unknownIdentifier
typeInferable i ctx (inf :@: chk) = do
  inf' <- typeInferable i ctx inf
  case inf' of
    Function τ τ' -> do 
      typeCheckable i ctx chk τ
      return τ'
    _             -> illegalApplication
kind ctx (Base x) Star = case lookup x ctx of
  Just (HasKind Star) -> return ()
  Nothing             -> unknownIdentifier 
kind ctx (Function k k') Star = do 
  kind ctx k Star
  kind ctx k' Star
substituteCheckable i r (Inferable e)   = Inferable $ substituteInferable i r e
substituteCheckable i r (Abstraction e) = Abstraction (substituteCheckable (i + 1) r e)
substituteInferable i r (Annotated e τ) = Annotated (substituteCheckable i r e) τ
substituteInferable i r (Bound j)       = if i == j then r else Bound j
substituteInferable i r (Free  y)       = Free y
substituteInferable i r (e:@:e')        = substituteInferable i r e :@: substituteCheckable i r e'



-- Evaluation
evalCheckable (Inferable i) d   = evalInferable i d
evalCheckable (Abstraction e) d = evalAbstraction e d
evalInferable (Annotated e _) d = evalCheckable e d
evalInferable (Bound i) d       = evalBound d i
evalInferable (Free x) d        = evalFreeVariable x
evalInferable (e:@:e') d        = evalApplication (evalInferable e d) (evalCheckable e' d)
evalAbstraction e d             = VLambda $ \x -> evalCheckable e (x : d)
evalBound                       = (!!)
evalFreeVariable                = VNeutral . NFree
evalApplication (VLambda f) v   = f v
evalApplication (VNeutral n) v  = VNeutral $ NApplication n v



-- Quotation
quote0                            = quote 0
quote i (VLambda f)               = Abstraction $ quote (i + 1) (f (evalFreeVariable (Quote i)))
quote i (VNeutral n)              = Inferable $ quoteNeutral i n 
quoteNeutral i (NFree x)          = boundfree i x
quoteNeutral i (NApplication n v) = quoteNeutral i n :@: quote i v
boundfree i (Quote k)             = Bound (i - k - 1)
boundfree i x                     = Free x



-- Examples
identity      = Abstraction (Inferable (Bound 0))
typedidentity = Annotated identity $ Function (Base (Global "α")) (Base (Global "α"))
selfapp       = Inferable (typedidentity :@: identity)
environment   = []
redid         = quote0 $ evalCheckable selfapp environment