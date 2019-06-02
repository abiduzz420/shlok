module Shlok where

-- representation of variables
data Name
    = Const String
    | Bound Int
    | Unquoted Int
    deriving (Show, Eq)

{-
    Four kinds of terms
    e := e :: τ (annotated term)
        | x (variable)
        | e1 e2 (function application)
        | λx → e (lambda abstraction)
-}

-- Inferable Term
data ITerm
    = Ann CTerm Type
    | Var Int -- integers are used to represent locally bound variables (de Bruijn indicies)
    | Par Name -- free variables
    | ITerm :@: CTerm -- :@: denotes application
    deriving (Show, Eq)

-- Checkable Term
data CTerm
    = Inf ITerm
    | Lam CTerm
    deriving (Show, Eq)

{-
    Two kinds of types
    τ := a (type identifier TPar)
      | τ -> τ'(function arrow)

    As there are no names at type level, TVar constructor is not needed
-}

data Type
    = TPar Name -- type idenitifier for free variables 
    | Fun Type Type
    deriving (Show, Eq)

{-
    Terms can be evaluated to values. A value is either
        - neutral term
        - lambda abstraction

    A neutral term is a variable applied to sequence of values (possibly empty).
    Hence a variable or an application.

    The term const (:: λx → λy → x) – if evaluated – results in the 
    value VLam (λx → VLam (λy → x))
-}

data Value
    = VLam (Value -> Value)
    | VNeutral Neutral

data Neutral
    = NPar Name
    | NApp Neutral Value

-- | Evaluation

type Env = [Value]

iEval :: ITerm -> Env -> Value
iEval (Ann e _) d = cEval e d
iEval (Var i) d = d !! i
iEval (Par x) d = vpar x
iEval (e1 :@: e2) d = vapp (iEval e1 d) (cEval e2 d)

cEval :: CTerm -> Env -> Value
cEval (Inf i) d = iEval i d
cEval (Lam e) d = VLam (\x -> cEval e (x:d))

-- | Helper functions

-- Creates value corresponding to a free variable
vpar :: Name -> Value
vpar n = VNeutral (NPar n)

vapp :: Value -> Value -> Value
vapp (VLam f) v = f v
vapp (VNeutral n) v = VNeutral (NApp n v)