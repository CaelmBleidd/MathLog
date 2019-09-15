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

getMP :: [Statement] -> Expr -> Set.Set Expr -> Maybe (Expr, Expr)
getMP list exprs alreadyExists = do
   let result = ((find $! (\x -> Set.member (case (splitImplToPair (expr x)) of
                                          Just i -> fst i
                                          Nothing -> (expr x))
                                          alreadyExists)) $! sublist) where
                                                                   sublist = ((filter $! (\x -> isRightPart exprs (expr x))) $! (filter (\x -> isImpl (expr x)) list))
   case result of
     Nothing -> Nothing
     Just i -> splitImplToPair $ expr i

isRightPart :: Expr -> Expr -> Bool
isRightPart template expr =
  case splitImplToPair expr of
    Just (a, b) -> b == template
    Nothing     -> False

goUp :: [Statement] -> Set.Set Expr -> Map.Map Expr Int -> IO (([Statement], Set.Set Expr))
goUp result alreadyExists hypos = do
  end <- isEOF
  if end
    then
      return (result, alreadyExists)
    else do
      line <- getLine
      let exprs = getExpr line
      if Set.member exprs alreadyExists
        then
          (goUp result alreadyExists hypos)
        else
          ((((goUp $!
            (result ++ [Statement{numberOfAxiom = isAxiom exprs, expr = exprs, numberOfHypos = (Map.lookup exprs hypos), leftMpExpr =
                                                                                                                          case (getMP result exprs alreadyExists) of
                                                                                                                            Just (a, b) -> Just a
                                                                                                                            Nothing -> Nothing }])) $!
            (Set.insert exprs alreadyExists)) $!
            hypos))


addElemsToSet :: Expr -> Expr -> Set.Set Expr -> Set.Set Expr
addElemsToSet first second set = (Set.insert second $!) (Set.insert first set)



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
                  Just i -> (goDown $! (init lines)) used info
                  Nothing ->
                    case (numberOfHypos elem) of
                      Just i -> (goDown $! (init lines)) used info
                      Nothing ->
                        case (leftMpExpr elem) of
                          Just left -> do
                              used <- return $! Set.insert left $! (Set.insert((Binary Impl (left) (expr elem))) used)
                              (goDown $! (init lines)) used info
                          Nothing -> (goDown $! (init lines)) used "fail"
           else (goDown $! (init lines)) used info

isOk :: Expr -> Statement -> Bool
isOk exprs statement = exprs == (expr statement)

printAll :: [Statement] -> Statement -> IO ()
--printAll statement mpMap line  = ""
printAll mpMap statement = do
  case (numberOfAxiom statement) of
    Just a ->
      putStr
        ("[" ++
         (show ((case (findIndex ((isOk) (expr statement)) mpMap) of
                  Just i -> i
                  Nothing -> -1) + 1)) ++ ". Ax. sch. " ++ show (a) ++ "] " ++ (show (expr statement)) ++ "\n")
    Nothing ->
      case (numberOfHypos statement) of
        Just a ->
          putStr
            ("[" ++
             (show ((case (findIndex ((isOk) (expr statement)) mpMap) of
                                      Just i -> i
                                      Nothing -> -1) + 1)) ++
             ". Hypothesis " ++ (show (a)) ++ "] " ++ (show (expr statement)) ++ "\n")
        Nothing ->
          case (leftMpExpr statement) of
            Just a ->
              putStr
                ("[" ++
                 (show ((case (findIndex ((isOk) (expr statement)) mpMap) of
                                          Just i -> i
                                          Nothing -> -1) + 1)) ++
                 ". M.P. " ++
                 (show
                    ((case (findIndex ((isOk) (Binary Impl (a) (expr statement))) mpMap) of
                       Just b  -> b
                       Nothing -> (-1)) + 1)) ++
                 ", " ++
                 (show
                    ((case (findIndex ((isOk) a) mpMap) of
                       Just b  -> b
                       Nothing -> (-1)) + 1)) ++
                 "] " ++ (show (expr statement)) ++ "\n")
            Nothing -> error ("ERROR IN PRINT FUNCTION " ++ (show (expr statement)))



annotate :: String -> String -> IO ()
annotate inputFile outputFile
--   writeFile outputFile ""
--   file <- readFile inputFile
 = do
--  file <- getContents
--  let linesOfOldProof = lines file
  firstLine <- getLine
  firstLine <- return $! Splitter.splitOn ("|-") $ firstLine
  newFirstLine <- return $! head firstLine ++ " |- " ++ show (getExpr (last firstLine))
  toProof <- return $! getExpr (last firstLine)
  firstLine <-
    return $!
    if head firstLine == []
      then ""
      else (head firstLine)

  hypos <- return $! Splitter.splitOn "," firstLine
  hypos <- return $!
    if hypos == [""]
      then []
      else map getExpr hypos
  hypos <- return $! Map.fromList $ zip hypos [1 ..]

  (exprs, alreadyExists) <-  (goUp [] Set.empty hypos)

  if (expr (last exprs)) /= toProof
    then putStr "Proof is incorrect"
    else do
      used <- return $! (goDown exprs $! (Set.fromList [expr (last exprs)])) ""
      if (snd used == "fail")
        then putStr "Proof is incorrect"
        else do
--           writeFile outputFile ""
--           appendFile outputFile (newFirstLine)
--         appendFile outputFile (printAll (zip ((filter (containsIn (used))) linesOfOldProof) [1..]) (Map.fromList(zip (map getExprFromStatement ((filter (containsIn (used))) linesOfOldProof)) [1..])) "")
--          putStr (newFirstLine ++ "\n")
          used <- return $! (filter $! (\x -> Set.member (expr x) (fst used))) exprs
          let result = map (\x -> printAll used x) used
          let result' = foldl (>>) (return ()) result
          (putStrLn newFirstLine) >> result'
