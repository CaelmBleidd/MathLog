module Glivenko where

import           Data.List
import           Control.Monad
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import           Grammar
import           Lexer           (alexScanTokens)
import           Parser          (parseExpr)
import           System.IO
import           Splitter
import           Proofs

isHypo :: Set.Set Expr -> Expr -> Bool
isHypo hypos expr = Set.member expr hypos

isAxiomOneToNine :: Expr -> Bool
isAxiomOneToNine (Binary Impl a (Binary Impl b a'))
  | a == a'                                    = True
isAxiomOneToNine (Binary Impl (Binary Impl a b) (Binary Impl (Binary Impl a' (Binary Impl b' c)) (Binary Impl a'' c')))
  | a == a' && a' == a'' && b == b' && c == c' = True
isAxiomOneToNine (Binary Impl a (Binary Impl b (Binary And a' b')))
  | a == a' && b' == b                         = True
isAxiomOneToNine (Binary Impl (Binary And a b) b')
  | b == b'                                    = True
isAxiomOneToNine (Binary Impl (Binary And a b) a')
  | a == a'                                    = True
isAxiomOneToNine (Binary Impl a (Binary Or a' b))
  | a == a'                                    = True
isAxiomOneToNine (Binary Impl b (Binary Or a' b'))
  | b == b'                                    = True
isAxiomOneToNine (Binary Impl (Binary Impl a c) (Binary Impl (Binary Impl b c') (Binary Impl (Binary Or a' b') c'')))
  | a == a' && b == b' && c == c' && c' == c'' = True
isAxiomOneToNine (Binary Impl (Binary Impl a b) (Binary Impl (Binary Impl a' (Not b')) (Not a'')))
  | a == a' && b == b' && a' == a''            = True
isAxiomOneToNine _                             = False

isAxiomTen :: Expr -> Bool
isAxiomTen (Binary Impl (Not (Not a)) a')
  | a == a'                                    = True
isAxiomTen _                                   = False


splitImplToPair :: Expr -> Maybe (Expr, Expr)
splitImplToPair (Binary Impl a b) = Just (a, b)
splitImplToPair _                 = Nothing

getExpr :: String -> Expr
getExpr s = case parseExpr (alexScanTokens s) of
  Left  err  -> error "ERROR"
  Right expr -> expr

replaceOnA :: (Expr, [Char]) -> [Char]
replaceOnA (expr, line) = concat $ map (\c -> if c == 'A' then show expr ; else [c]) line

replaceOnAAndB :: Expr ->  Expr -> [Char] -> [Char]
replaceOnAAndB a b line = concat $ map (\c -> if c == 'A' then show a; else if c == 'B' then show b; else [c]) line

printAxiom :: Expr -> [Char]
printAxiom expr = replaceOnA (expr, getNotAProof)

printHypo :: Expr -> [Char]
printHypo expr = replaceOnA (expr, getNotAProof)

printAxiomTen :: Expr -> [Char]
printAxiomTen expr = case splitImplToPair expr of
  Just (a, b) -> replaceOnA (b, getNotTenthProof)
  Nothing     -> ""

isImpl :: Expr -> Bool
isImpl (Binary Impl a b) = True
isImpl _                 = False

getMP :: [Expr] -> Expr -> Maybe (Expr, Expr)
getMP list expr =  splitImplToPair $ head $ dropWhile (wasn'tInProofAbove sublist) ((filter (isRightPart expr) (filter isImpl sublist))) where
  sublist = takeWhile (/= expr) list

isRightPart :: Expr -> Expr -> Bool
isRightPart template expr = case splitImplToPair expr of
  Just (a, b) -> b == template
  Nothing     -> False

wasn'tInProofAbove :: [Expr] -> Expr -> Bool
wasn'tInProofAbove proof expr = case splitImplToPair expr of
  Just (a, b) -> case find (== a) proof of
                    Just a  -> False
                    Nothing -> True
  Nothing     -> True

printMP :: (Expr, Expr) -> [Char]
printMP (a, b) = replaceOnAAndB a b getMPProof

printForAll :: Set.Set Expr -> [Expr] -> Expr -> [Char]
printForAll set list expr = if isAxiomOneToNine expr
                          then printAxiom expr
                          else if isHypo set expr
                                   then printHypo expr
                                   else if isAxiomTen expr
                                        then printAxiomTen expr
                                        else case getMP list expr of
                                          Just (a, b) -> printMP (a, b)
                                          Nothing     -> ""


glivenko :: String -> String -> IO ()
glivenko inputFile outputFile = do

  
  --------writeFile outputFile ""
  --------file <- readFile inputFile

  file            <- getContents
  linesOfOldProof <- return $ lines file

  firstLine       <- return $ Splitter.splitOn ("|-") $ head linesOfOldProof
  newFirstLine    <- return $ head firstLine ++ "|- !!" ++ show (getExpr (last firstLine)) ++ "\n"
  firstLine       <- return $ if head firstLine == [] then [""] else firstLine

  hypos           <- return $ Splitter.splitOn "," $ head firstLine
  hypos           <- return $ if hypos == [""] then [] else map getExpr hypos
  let setHypos     = Set.fromList hypos

  linesOfOldProof <- return $ drop 1 linesOfOldProof
  linesOfOldProof <- return $ map getExpr linesOfOldProof

  let partPrintForAll = printForAll setHypos linesOfOldProof

  --------appendFile outputFile (newFirstLine)
  --------appendFile outputFile (Data.List.intercalate "\n" (map partPrintForAll linesOfOldProof))
  putStr newFirstLine
  putStr $ Data.List.intercalate "\n" (map partPrintForAll linesOfOldProof)
