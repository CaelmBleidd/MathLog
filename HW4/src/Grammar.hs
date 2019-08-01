module Grammar where

import Data.List

data BExpr = Impl
             | Or
             | And
             deriving (Ord, Eq)

instance Show BExpr where
    show Impl = "->"
    show Or   = "|"
    show And  = "&"

data Expr = Binary BExpr Expr Expr
          | Not Expr
          | Var String
          deriving (Ord)

instance Show Expr where
    show (Binary op a b) = "(" ++ show a ++ " " ++ show op ++ " " ++ show b ++ ")"
    show (Not e)         = "!" ++ show e
    show (Var variable)  = variable

instance Eq Expr where
    (==) (Var a)            (Var b)            = a == b
    (==) (Not a)            (Not b)            = a == b
    (==) (Binary Impl a a') (Binary Impl b b') = a == b && a' == b'
    (==) (Binary Or a a')   (Binary Or b b')   = a == b && a' == b'
    (==) (Binary And a a')  (Binary And b b')  = a == b && a' == b'
    (==) _ _                                   = False
