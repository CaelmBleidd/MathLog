module Main where

import Grammar (Expr(..))
import Lexer (alexScanTokens)
import Parser (parseExpr)
import Annotate

inputFile :: String
inputFile = "input"

outputFile :: String
outputFile = "output.txt"

main :: IO ()
main = annotate inputFile outputFile
