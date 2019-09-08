module Annotate where

import           Data.List
import           Control.Monad
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import           Grammar
import           Lexer           (alexScanTokens)
import           Parser          (parseExpr)
import           System.IO
import           Splitter

data Statement = Statement {
                   index         :: Int,
                   expr          :: Expr,
                   numberOfAxiom :: Maybe Int,
                   numberOfHypos :: Maybe Int,
                   numberOfMP    :: Maybe (Int, Int) }
                 deriving (Eq, Ord)

isHypo :: Set.Set Expr -> Expr -> Bool
isHypo hypos expr = Set.member expr hypos

isAxiom :: Expr -> Maybe Int
isAxiom (Binary Impl a (Binary Impl b a'))
  | a == a'                                    = Just 1
isAxiom (Binary Impl (Binary Impl a b) (Binary Impl (Binary Impl a' (Binary Impl b' c)) (Binary Impl a'' c')))
  | a == a' && a' == a'' && b == b' && c == c' = Just 2
isAxiom (Binary Impl a (Binary Impl b (Binary And a' b')))
  | a == a' && b' == b                         = Just 3
isAxiom (Binary Impl (Binary And a b) b')
  | b == b'                                    = Just 4
isAxiom (Binary Impl (Binary And a b) a')
  | a == a'                                    = Just 5
isAxiom (Binary Impl a (Binary Or a' b))
  | a == a'                                    = Just 6
isAxiom (Binary Impl b (Binary Or a' b'))
  | b == b'                                    = Just 7
isAxiom (Binary Impl (Binary Impl a c) (Binary Impl (Binary Impl b c') (Binary Impl (Binary Or a' b') c'')))
  | a == a' && b == b' && c == c' && c' == c'' = Just 8
isAxiom (Binary Impl (Binary Impl a b) (Binary Impl (Binary Impl a' (Not b')) (Not a'')))
  | a == a' && b == b' && a' == a''            = Just 9
isAxiom (Binary Impl (Not (Not a)) a')
  | a == a'                                    = Just 10
isAxiom          _                             = Nothing

toStatement :: (Int, Expr) -> Statement
toStatement (i, exprFromSource) = Statement {
                                             index = i,
                                             expr = exprFromSource,
                                             numberOfAxiom = Nothing,
                                             numberOfHypos = Nothing,
                                             numberOfMP = Nothing }

linesToStatements :: [Expr] -> [Statement]
linesToStatements exprs = map toStatement (zip [1..] exprs)

splitImplToPair :: Expr -> Maybe (Expr, Expr)
splitImplToPair (Binary Impl a b) = Just (a, b)
splitImplToPair _                 = Nothing

getExpr :: String -> Expr
getExpr s = case parseExpr (alexScanTokens s) of
  Left  err  -> error "ERROR"
  Right expr -> expr

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


annotateAll :: [Expr] -> [String]
annotateAll exprs = map annotateExpr exprs

annotateExpr :: Expr -> String
annonateExpr expr =


findAxioms :: [Statement] -> --TODO


annotate :: String -> String -> IO ()
annotate inputFile outputFile = do

  writeFile outputFile ""
  file <- readFile inputFile

  --------file            <- getContents
  linesOfOldProof <- return $ lines file

  -- :t firstLine :: String -> [String]
  firstLine       <- return $ Splitter.splitOn ("|-") $ head linesOfOldProof
  newFirstLine    <- return $ show (getExpr (head firstLine)) ++ " |- " ++ show (getExpr (last firstLine)) ++ "\n"
  toProof         <- return $ last firstLine
  firstLine       <- return $ if head firstLine == [] then [""] else $ head firstLine

  -- :t firstLine :: String
  -- I know the reflections from Exprs to their numbers3
  hypos           <- return $ Splitter.splitOn "," firstLine
  hypos           <- return $ if hypos == [""] then [] else map getExpr hypos
  hypos           <- return $ Map.fromList $ zip hypos [1..]
  -- now we have hypos like ((a, 1), (b, 2), ...)
  -- newFirstLine is ready for output
  -- firstLine unused???

  -- :t linesOfOldProof :: [Expr]
  linesOfOldProof <- return $ drop 1 linesOfOldProof
  linesOfOldProof <- return $ map getExpr linesOfOldProof

  linesOfOldProof <- return $ linesToStatements linesOfOldProof

  --let partPrintForAll = printForAll setHypos linesOfOldProof
  linesOfOldProof <- return $ findAxioms linesOfOldProof


  appendFile outputFile (newFirstLine)
  --appendFile outputFile (Data.List.intercalate "\n" (map partPrintForAll linesOfOldProof))
  -------putStr newFirstLine
  -------putStr $ Data.List.intercalate "\n" (map partPrintForAll linesOfOldProof)
