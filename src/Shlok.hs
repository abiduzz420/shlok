module Shlok where

import Control.Monad
import Control.Monad.Except

-- representation of free variables
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

    From the type rules, we can infer the types of
    annotated terms, variables and application constructs.
    Lambda abstractions can only be checked but not inferred.
    Hence we make syntactic distiction between inferrable terms
    and checkable terms

    For bound variables we are using de Bruijn indicies to save
    the work of implementing alpha-conversion and alpha-equivalence,
    which is renaming of variables, preventing name-capture etc
    
    https://en.wikipedia.org/wiki/De_Bruijn_index
-}

-- Inferable Term
data ITerm
    = Ann CTerm Type
    | Var Int -- integers are used to represent locally bound variables (de Bruijn indicies)
    | Par Name -- free variables
    | ITerm :@: CTerm -- :@: denotes application
    deriving (Show, Eq)

{-
    Lambda abstractions do not introduce explicit
    variables due to use of de Bruijn indicies.
-}
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
    Hence a free variable or an application.

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

-- Handles substitution of bound variables
type Env = [Value]

{-
    Evaluation rules in λ->
        - Type annotations are ignored
        - Variable evaluates to themselves
        - λx -> e evaluates to λx -> v where e evaluates to v
        - In the case of application,
            if e1 is a lambda 
                then beta-reduce (λx. e1) e2 ⇒ e1[e2/x]
                But in the given implementation we use Haskell's own function application
                to represent function values
            else (e1 is neutral term)
                then create a netural value (NApp) of it
-}

-- Evaluators for well-typed expressions
iEval :: ITerm -> Env -> Value
iEval (Ann e _) d = cEval e d
iEval (Var i) d = d !! i
iEval (Par x) d = vpar x
iEval (e1 :@: e2) d = vapp (iEval e1 d) (cEval e2 d)

{-
    Since e1, e2 (in e1 :@: e2) are evaluated
    before the substitution (see iEval), does this mean it
    comes under call-by-value case (Refere beta-law for CBV) ?
-}

cEval :: CTerm -> Env -> Value
cEval (Inf i) d = iEval i d
cEval (Lam e) d = VLam (\x -> cEval e (x:d))

-- | Helper functions

-- Creates value corresponding to a free variable
vpar :: Name -> Value
vpar n = VNeutral (NPar n)

{-
    not using beta-reduction to implement function application
    Instead using Haskell's own function application
-}

vapp :: Value -> Value -> Value
vapp (VLam f) v = f v
vapp (VNeutral n) v = VNeutral (NApp n v)

-- | Contexts

data Kind = Star
    deriving (Show)

data Info
    = HasKind Kind
    | HasType Type
    deriving (Show)

type Context = [(Name, Info)]

-- | Type Checker for λ-> terms

-- Graceful Error Monad
type Result = Either String

-- well-formedness of types is checked
kind :: Context -> Type -> Kind -> Result ()
kind cxt (TPar x) Star
    = case lookup x cxt of
        Just (HasKind Star) -> return ()
        Nothing             -> throwError "unknown identifier"
kind cxt (Fun ty ty') Star
    = do kind cxt ty Star
         kind cxt ty' Star

iType :: Int -> Context -> ITerm -> Result Type
iType i cxt (Ann e t)
    = do kind cxt t Star
         cType i cxt e t
         return t
iType i cxt (Par x)
    = case lookup x cxt of
        Just (HasType t) -> return t
        Nothing          -> throwError "unknown identifier"
iType i cxt (e1 :@: e2)
    = do sigma <- iType i cxt e1
         case sigma of
            Fun t t' ->  do cType i cxt e2 t
                            return t'
            _        -> throwError "illegal exception"

cType :: Int -> Context -> CTerm -> Type -> Result ()
cType i cxt (Inf e) t
    = do t' <- iType i cxt e
         unless (t == t') (throwError "type mismatch")
cType i cxt (Lam e) (Fun t t')
    = cType (i+1) ((Bound i, HasType t):cxt)
            (cSubst 0 (Par (Bound i)) e) t'
cType i cxt _ _
    = throwError "type mismatch"

iType0 :: Context -> ITerm -> Result Type
iType0 = iType 0

-- Substitution
iSubst :: Int -> ITerm -> ITerm -> ITerm
iSubst i r (Ann e t) = Ann (cSubst i r e) t
iSubst i r (Var j) = if i==j then r else Var j
iSubst i r (Par y) = Par y
iSubst i r (e1 :@: e2) = iSubst i r e1 :@: cSubst i r e2

cSubst :: Int -> ITerm -> CTerm -> CTerm
cSubst i r (Inf e) = Inf (iSubst i r e)
cSubst i r (Lam e) = Lam (cSubst (i+1) r e)