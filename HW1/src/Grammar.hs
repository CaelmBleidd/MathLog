module Grammar where

import Data.List

data BExpr = Impl | Or | And

instance Show BExpr where
    show Impl = "->"
    show Or   = "|"
    show And  = "&"

data Expr = Binary BExpr Expr Expr    -- operator (Expr Expr)
          | Not Expr                  -- !Expression
          | Var String                -- variable

instance Show Expr where
    show (Binary operator a b) = "("  ++ intercalate "," [show operator, show a, show b] ++ ")"
    show (Not expr)            = "(!" ++ show expr                                       ++ ")"
    show (Var variable)        = variable