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
                   leftMpExpr    :: Maybe Expr}
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
                                             leftMpExpr = Nothing}

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

getExprFromStatement :: Statement -> Expr
getExprFromStatement statement = expr statement


getMP :: [Statement] -> Expr -> Maybe (Expr, Expr)
getMP list expr = do
  sublist <- return $ takeWhile (/= expr) (map getExprFromStatement list)
  result <- return $ dropWhile (wasn'tInProofAbove sublist) ((filter (isRightPart expr) (filter isImpl sublist)))
  if length result > 0 then
    splitImplToPair $ head $ result
  else
    Nothing


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

getHypoNumber :: Statement -> Map.Map Expr Int -> Maybe Int
getHypoNumber statement map = Map.lookup (expr statement) map

addElement :: [Statement] -> [Statement] -> Map.Map Expr Int -> Int -> [Statement]
addElement lines result hypos number = do
  firstElem <- return $ head lines
  firstElem <- return $ firstElem{index = number,
                                  numberOfAxiom = (isAxiom (expr firstElem)),
                                  numberOfHypos = (getHypoNumber firstElem hypos),
                                  leftMpExpr = case (getMP lines (expr firstElem)) of
                                                 Just (a, b) -> Just a
                                                 Nothing -> Nothing }
  result    <- return $ result ++ [firstElem]
  result

-- Забыл про аннотирование, пока только удаляю дубликаты
goUp :: [Statement] -> [Statement] -> Set.Set Expr -> Map.Map Expr Int -> Int -> ([Statement], Set.Set Expr)
goUp linesOfProof result alreadyExists hypos numberOfLine =
  if length linesOfProof == 1
    then if Set.member (expr (head linesOfProof)) alreadyExists
           then (result, alreadyExists)
           else ((addElement linesOfProof result hypos numberOfLine), (Set.insert (expr (head linesOfProof)) alreadyExists))
    else if Set.member (expr (head linesOfProof)) alreadyExists
           then goUp (tail linesOfProof) result alreadyExists hypos numberOfLine
           else goUp
                  (tail linesOfProof)
                  (addElement linesOfProof result hypos numberOfLine)
                  (Set.insert (expr (head linesOfProof)) alreadyExists)
                  hypos
                  (numberOfLine + 1)

goDown :: [Statement] -> Set.Set Expr -> Set.Set Expr
goDown lines used = do
  let elem = last lines
  if length lines == 1 then
    used
  else
    if Set.member (expr elem) used then
      case (numberOfAxiom elem) of
        Just i -> used
        Nothing -> case (numberOfHypos elem) of
                     Just i -> used
                     Nothing -> case (leftMpExpr elem) of
                                  Just left -> goDown (init lines) (Set.insert (Binary Impl (left) (expr elem)) used)
                                  Nothing -> error (show (expr elem))
    else
      goDown (init lines) used


printAll :: [(Statement, Int)] -> Map.Map Statement Int -> [Char] -> [Char]
--printAll statement mpMap line  = ""
printAll statement mpMap line  = do
  if length statement > 0 then do
    realStatement <- return $ fst (head statement)
    case (numberOfAxiom realStatement) of
      Just a -> printAll (tail statement) mpMap (line ++
                                                 "\n" ++
                                                 "[" ++
                                                 (show (snd (head statement))) ++
                                                 ". Ax. sch. " ++
                                                 (show (numberOfAxiom realStatement))) ++
                                                 "]" ++
                                                 (show (expr realStatement))
      Nothing ->
        case (numberOfHypos realStatement) of
          Just a -> printAll (tail statement) mpMap (line ++
                                                     "\n" ++
                                                     "[" ++
                                                     (show (snd (head statement))) ++
                                                     ". Hypothesis " ++
                                                     (show (numberOfHypos realStatement))) ++
                                                     "]" ++
                                                     (show (expr realStatement))
          Nothing ->
            case (leftMpExpr realStatement) of
                Just a -> printAll (tail statement) mpMap (line ++
                                                                 "\n" ++
                                                                 "[" ++
                                                                 (show (snd (head statement))) ++
                                                                 ". M.P. " ++
                                                                 "" ++
                                                                 "]" ++
                                                                 (show (expr realStatement)))
                Nothing -> error "ERROR IN PRINT FUNCTION"
  else line

containsIn :: Set.Set Expr -> Statement -> Bool
containsIn set statement = Set.member (expr statement) set

--data Statement = Statement {
--                   index         :: Int,
--                   expr          :: Expr,
--                   numberOfAxiom :: Maybe Int,
--                   numberOfHypos :: Maybe Int,
--                   numberOfMP    :: Maybe (Int, Int),
--                   leftMpExpr    :: Maybe Expr,
--                   used          :: Bool }
--                 deriving (Eq, Ord)

annotate :: String -> String -> IO ()
annotate inputFile outputFile = do

  writeFile outputFile ""
  file <- readFile inputFile

  --------file            <- getContents
  linesOfOldProof <- return $ lines file

  -- :t firstLine :: String -> [String]
  firstLine       <- return $ Splitter.splitOn ("|-") $ head linesOfOldProof
  newFirstLine    <- return $ head firstLine ++ " |- " ++ show (getExpr (last firstLine)) ++ "\n"
  toProof         <- return $ last firstLine
  firstLine       <- return $ if head firstLine == [] then "" else (head firstLine)

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
  -- теперь есть лист из statement, по которому нужно сделать проход вверх, аннотируя и убирая дубликаты

--  --let partPrintForAll = printForAll setHypos linesOfOldProof
----  linesOfOldProof <- return $  goUp linesOfOldProof
  tmp <- return $ goUp linesOfOldProof [] Set.empty hypos 1


  linesOfOldProof <- return $ fst tmp
----  alreadyExists <- return $ snd tmp
--


  used <- return $ goDown linesOfOldProof (Set.fromList [expr (last linesOfOldProof)])

  writeFile outputFile ""
  appendFile outputFile (newFirstLine)


  linesOfOldProof <- return $ zip ((filter (containsIn (used))) linesOfOldProof) [1..]

  putStr "asda"
  putStr (show (length linesOfOldProof))
  mpMap <- return $ Map.fromList(linesOfOldProof)
--  appendFile outputFile ""

  appendFile outputFile (printAll (linesOfOldProof) mpMap "")
----  appendFile outputFile (Data.List.intercalate "\n" (map partPrintForAll linesOfOldProof))
--  -------putStr newFirstLine
--  -------putStr $ Data.List.intercalate "\n" (map partPrintForAll linesOfOldProof)