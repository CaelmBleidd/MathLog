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
    index        :: Int,
    expr         :: Expr,
    indexOfAxiom :: Maybe Int,
    indexOfHypo  :: Maybe Int,
    mp           :: Maybe (Int, Int) }
    deriving (Eq, Ord)

--isHypo :: Set.Set Expr -> Expr -> Bool
--isHypo hypos expr = Set.member expr hypos

getHypoNumber :: Statement -> Map Statement Int -> Int
getHypoNumber statement hypos = lookup (expr statement) hypos

isAxiom :: Expr -> Int
isAxiom (Binary Impl a (Binary Impl b a'))
  | a == a'                                    = True
isAxiom (Binary Impl (Binary Impl a b) (Binary Impl (Binary Impl a' (Binary Impl b' c)) (Binary Impl a'' c')))
  | a == a' && a' == a'' && b == b' && c == c' = True
isAxiom (Binary Impl a (Binary Impl b (Binary And a' b')))
  | a == a' && b' == b                         = True
isAxiom (Binary Impl (Binary And a b) b')
  | b == b'                                    = True
isAxiom (Binary Impl (Binary And a b) a')
  | a == a'                                    = True
isAxiom (Binary Impl a (Binary Or a' b))
  | a == a'                                    = True
isAxiom (Binary Impl b (Binary Or a' b'))
  | b == b'                                    = True
isAxiom (Binary Impl (Binary Impl a c) (Binary Impl (Binary Impl b c') (Binary Impl (Binary Or a' b') c'')))
  | a == a' && b == b' && c == c' && c' == c'' = True
isAxiom (Binary Impl (Binary Impl a b) (Binary Impl (Binary Impl a' (Not b')) (Not a'')))
  | a == a' && b == b' && a' == a''            = True
isAxiom _                             = False

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

--printForAll :: Set.Set Expr -> [Expr] -> Expr -> [Char]
--printForAll set list expr = if isAxiom expr
--                          then printAxiom expr
--                          else if isHypo set expr
--                                   then printHypo expr
--                                   else if isAxiomTen expr
--                                        then printAxiomTen expr
--                                        else case getMP list expr of
--                                          Just (a, b) -> printMP (a, b)
--                                          Nothing     -> ""

checkAndRemoveDuplicates :: [Statement]

annotate :: String -> String -> IO ()
annotate inputFile outputFile = do


  --------writeFile outputFile ""
  --------file <- readFile inputFile

  file            <- getContents
  linesOfOldProof <- return $ lines file

  firstLine       <- return $ Splitter.splitOn ("|-") $ head linesOfOldProof
  newFirstLine    <- return $ head firstLine ++ "|- !!" ++ show (getExpr (last firstLine)) ++ "\n"
  toProof         <- return $ last firstLine
  firstLine       <- return $ if head firstLine == [] then [""] else firstLine

  hypos           <- return $ Splitter.splitOn "," $ head firstLine
  hypos           <- return $ if hypos == [""] then [] else map getExpr hypos
  let setHypos     = Set.fromList hypos
  hypos           <- return $ Map.fromList (zip hypos ([1..]::[Int]))

  linesOfOldProof <- return $ drop 1 linesOfOldProof
  linesOfOldProof <- return $ map getExpr linesOfOldProof


--  let partPrintForAll = printForAll setHypos linesOfOldProof

  --------appendFile outputFile (newFirstLine)
  --------appendFile outputFile (Data.List.intercalate "\n" (map partPrintForAll linesOfOldProof))
--  putStr newFirstLine
--  putStr $ Data.List.intercalate "\n" (map partPrintForAll linesOfOldProof)
