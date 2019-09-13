module Annotate where

import           Control.Monad
import           Data.List
import qualified Data.Map.Strict as Map
import qualified Data.Set        as Set
import           Grammar
import           Lexer           (alexScanTokens)
import           Parser          (parseExpr)
import           Splitter
import           System.IO

data Statement =
  Statement
    { expr          :: Expr
    , numberOfAxiom :: Maybe Int
    , numberOfHypos :: Maybe Int
    , leftMpExpr    :: Maybe Expr
    }
  deriving (Eq, Ord)

isAxiom :: Expr -> Maybe Int
isAxiom (Binary Impl a (Binary Impl b a'))
  | a == a' = Just 1
isAxiom (Binary Impl (Binary Impl a b) (Binary Impl (Binary Impl a' (Binary Impl b' c)) (Binary Impl a'' c')))
  | a == a' && a' == a'' && b == b' && c == c' = Just 2
isAxiom (Binary Impl a (Binary Impl b (Binary And a' b')))
  | a == a' && b' == b = Just 3
isAxiom (Binary Impl (Binary And a b) b')
  | b == b' = Just 4
isAxiom (Binary Impl (Binary And a b) a')
  | a == a' = Just 5
isAxiom (Binary Impl a (Binary Or a' b))
  | a == a' = Just 6
isAxiom (Binary Impl b (Binary Or a' b'))
  | b == b' = Just 7
isAxiom (Binary Impl (Binary Impl a c) (Binary Impl (Binary Impl b c') (Binary Impl (Binary Or a' b') c'')))
  | a == a' && b == b' && c == c' && c' == c'' = Just 8
isAxiom (Binary Impl (Binary Impl a b) (Binary Impl (Binary Impl a' (Not b')) (Not a'')))
  | a == a' && b == b' && a' == a'' = Just 9
isAxiom (Binary Impl (Not (Not a)) a')
  | a == a' = Just 10
isAxiom _ = Nothing

toStatement :: (Int, Expr) -> Statement
toStatement (i, exprFromSource) =
  Statement {expr = exprFromSource, numberOfAxiom = Nothing, numberOfHypos = Nothing, leftMpExpr = Nothing}

linesToStatements :: [Expr] -> [Statement]
linesToStatements exprs = map toStatement (zip [1 ..] exprs)

splitImplToPair :: Expr -> Maybe (Expr, Expr)
splitImplToPair (Binary Impl a b) = Just (a, b)
splitImplToPair _                 = Nothing

getExpr :: String -> Expr
getExpr s =
  case parseExpr (alexScanTokens s) of
    Left err   -> error "ERROR"
    Right expr -> expr

isImpl :: Expr -> Bool
isImpl (Binary Impl a b) = True
isImpl _                 = False

getExprFromStatement :: Statement -> Expr
getExprFromStatement statement = expr statement

getMP :: [Statement] -> Expr -> Maybe (Expr, Expr)
getMP list expr = do
  sublist <- return $ map getExprFromStatement list
  result <- return $ dropWhile (wasn'tInProofAbove sublist) ((filter (isRightPart expr) (filter isImpl sublist)))
  if (length result) == 0
    then Nothing
    else splitImplToPair $ head $ result

isRightPart :: Expr -> Expr -> Bool
isRightPart template expr =
  case splitImplToPair expr of
    Just (a, b) -> b == template
    Nothing     -> False

wasn'tInProofAbove :: [Expr] -> Expr -> Bool
wasn'tInProofAbove proof expr =
  case splitImplToPair expr of
    Just (a, b) ->
      case find (== a) proof of
        Just a  -> False
        Nothing -> True
    Nothing -> True

getHypoNumber :: Statement -> Map.Map Expr Int -> Maybe Int
getHypoNumber statement map = Map.lookup (expr statement) map

addElement :: [Statement] -> [Statement] -> Map.Map Expr Int -> [Statement]
addElement lines result hypos = do
  firstElem <- return $ head lines
  firstElem <-
    return $
    firstElem
      { numberOfAxiom = (isAxiom (expr firstElem))
      , numberOfHypos = (getHypoNumber firstElem hypos)
      , leftMpExpr =
          case (getMP result (expr firstElem)) of
            Just (a, b) -> Just a
            Nothing     -> Nothing
      }
  result <- return $ result ++ [firstElem]
  result

goUp :: [Statement] -> [Statement] -> Set.Set Expr -> Map.Map Expr Int -> ([Statement], Set.Set Expr)
goUp linesOfProof result alreadyExists hypos =
  if length linesOfProof == 1
    then if Set.member (expr (head linesOfProof)) alreadyExists
           then (result, alreadyExists)
           else ((addElement linesOfProof result hypos), (Set.insert (expr (head linesOfProof)) alreadyExists))
    else if Set.member (expr (head linesOfProof)) alreadyExists
           then goUp (tail linesOfProof) result alreadyExists hypos
           else goUp
                  (tail linesOfProof)
                  (addElement linesOfProof result hypos)
                  (Set.insert (expr (head linesOfProof)) alreadyExists)
                  hypos

addElemsToSet :: Expr -> Expr -> Set.Set Expr -> Set.Set Expr
addElemsToSet first second set = Set.insert second (Set.insert first set)

goDown :: [Statement] -> Set.Set Expr -> [Char] -> (Set.Set Expr, [Char])
goDown lines used info = do
  let elem = last lines
  if length lines == 1
    then ( used
         , case (numberOfAxiom elem) of
             Just i -> info
             Nothing ->
               case (numberOfHypos elem) of
                 Just i -> info
                 Nothing ->
                   case (leftMpExpr elem) of
                     Just i  -> info
                     Nothing -> "fail")
    else if Set.member (expr elem) used
           then case (numberOfAxiom elem) of
                  Just i -> goDown (init lines) used info
                  Nothing ->
                    case (numberOfHypos elem) of
                      Just i -> goDown (init lines) used info
                      Nothing ->
                        case (leftMpExpr elem) of
                          Just left ->
                            goDown (init lines) (addElemsToSet (Binary Impl (left) (expr elem)) left used) info
                          Nothing -> goDown (init lines) used "fail"
           else goDown (init lines) used info


printAll :: Map.Map Expr Int -> [(Statement, Int)] -> IO ()
--printAll statement mpMap line  = ""
printAll mpMap statement = do
  if length statement > 0
    then do
      realStatement <- return $ fst (head statement)
      case (numberOfAxiom realStatement) of
        Just a ->
          putStr
            ("[" ++
             (show (snd (head statement))) ++ ". Ax. sch. " ++ show (a) ++ "] " ++ (show (expr realStatement)) ++ "\n")
        Nothing ->
          case (numberOfHypos realStatement) of
            Just a ->
              putStr
                ("[" ++
                 (show (snd (head statement))) ++
                 ". Hypothesis " ++ (show (a)) ++ "] " ++ (show (expr realStatement)) ++ "\n")
            Nothing ->
              case (leftMpExpr realStatement) of
                Just a ->
                  putStr
                    ("[" ++
                     (show (snd (head statement))) ++
                     ". M.P. " ++
                     (show
                        (case (Map.lookup (Binary Impl (a) (expr realStatement)) mpMap) of
                           Just b  -> b
                           Nothing -> (-1))) ++
                     ", " ++
                     (show
                        (case (Map.lookup a mpMap) of
                           Just b  -> b
                           Nothing -> (-1))) ++
                     "] " ++ (show (expr realStatement)) ++ "\n")
                Nothing -> error ("ERROR IN PRINT FUNCTION " ++ (show (expr realStatement)))
      printAll mpMap (tail statement)
    else putStr ""

containsIn :: Set.Set Expr -> Statement -> Bool
containsIn set statement = Set.member (expr statement) set

annotate :: String -> String -> IO ()
annotate inputFile outputFile
--   writeFile outputFile ""
--   file <- readFile inputFile
 = do
  file <- getContents
  linesOfOldProof <- return $ lines file
  firstLine <- return $ Splitter.splitOn ("|-") $ head linesOfOldProof
  newFirstLine <- return $ head firstLine ++ " |- " ++ show (getExpr (last firstLine))
  toProof <- return $ getExpr (last firstLine)
  firstLine <-
    return $
    if head firstLine == []
      then ""
      else (head firstLine)
  hypos <- return $ Splitter.splitOn "," firstLine
  hypos <-
    return $
    if hypos == [""]
      then []
      else map getExpr hypos
  hypos <- return $ Map.fromList $ zip hypos [1 ..]
  linesOfOldProof <- return $ drop 1 linesOfOldProof
  linesOfOldProof <- return $ map getExpr linesOfOldProof
  if (last linesOfOldProof) /= toProof
    then putStr "Proof is incorrect"
    else do
      linesOfOldProof <- return $ linesToStatements linesOfOldProof
      linesOfOldProof <- return $ fst $ goUp linesOfOldProof [] Set.empty hypos
      used <- return $ goDown linesOfOldProof (Set.fromList [expr (last linesOfOldProof)]) ""
      if (snd used == "fail")
        then putStr "Proof is incorrect"
        else do
--           writeFile outputFile ""
--           appendFile outputFile (newFirstLine)
--         appendFile outputFile (printAll (zip ((filter (containsIn (used))) linesOfOldProof) [1..]) (Map.fromList(zip (map getExprFromStatement ((filter (containsIn (used))) linesOfOldProof)) [1..])) "")
          putStr (newFirstLine ++ "\n")
          (printAll
             (Map.fromList (zip (map getExprFromStatement ((filter (containsIn (fst used))) linesOfOldProof)) [1 ..])))
            (zip ((filter (containsIn (fst used))) linesOfOldProof) [1 ..])
