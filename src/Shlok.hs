module Shlok where

data Name
    = Const String
    | Bound Int
    | Unquoted Int
    deriving (Show, Eq)

-- Inferable Term
data ITerm
    = Ann CTerm Type -- annotated terms
    | Var Int -- integers are used to represent bound variables
    | Par Name -- free variables
    | ITerm :@: CTerm -- :@: denotes application
    deriving (Show, Eq)

-- Checkable Term
data CTerm
    = Inf ITerm
    | Lam CTerm
    deriving (Show, Eq)

data Type
    = TPar Name -- type idenitifier for free variables 
    | Fun Type Type
    deriving (Show, Eq)

data Value
    = VLam (Value -> Value)
    | VNeutral Neutral

data Neutral
    = NPar Name
    | NApp Neutral Value

vpar :: Name -> Value
vpar n = VNeutral (NPar n)