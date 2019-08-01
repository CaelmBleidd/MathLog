module Main where

import Grammar (Expr(..))
import Lexer (alexScanTokens)
import Parser (parseExpr)
import Proof

inputFile :: String
inputFile = "input"

outputFile :: String
outputFile = "output.txt"

main :: IO ()
main = proofAndWrite inputFile outputFile
