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
import           System.Exit     (exitSuccess)


data Statement
  = Hypo !Int !Int
  | Axiom !Int !Int
  | ModusPonens !(Int, Int) !Int
  deriving (Eq)

instance Show Statement where
  show (Hypo a b)  = "Hypothesis " ++ show a
  show (Axiom a b)       = "Ax. sch. " ++ show a
  show (ModusPonens a b) = "M.P. " ++ show a


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

isRightPart :: Expr -> Expr -> Bool
isRightPart template expr =
  case splitImplToPair expr of
    Just (a, b) -> b == template
    Nothing     -> False

containsLeftPart :: Map.Map Expr Int -> Expr -> Bool
containsLeftPart earlierExprs expr  =
  case splitImplToPair expr of
    Just (a, b) -> Map.member a earlierExprs
    Nothing -> False

findMP :: Map.Map Expr [Expr] -> Map.Map Expr Int -> Expr -> Maybe (Int, Int)
findMP rightPartsToPositions earlierExprs expr = do
  if Map.notMember expr rightPartsToPositions
    then Nothing
    else do
      let to = rightPartsToPositions Map.! expr
      let curExpr = find (containsLeftPart earlierExprs) to
      case curExpr of
        Nothing -> Nothing
        Just i -> case splitImplToPair i of
                    Nothing -> Nothing
                    Just (a, b) -> Just (earlierExprs Map.! a, earlierExprs Map.! i)

goUp :: Map.Map Int Expr ->  Map.Map Expr Int -> Map.Map Expr [Expr] -> Map.Map Expr Int -> Int -> Map.Map Int Statement -> Expr -> IO(Map.Map Int Expr , Map.Map Expr Int, Int, Map.Map Int Statement, Expr)
goUp exprs exprToPosition rightPartsToPositions hypos number numberToStatement last = do
  marker <- isEOF
  if marker
    then return $ (exprs, exprToPosition, number, numberToStatement, last)
    else do
      line <- getLine
      let expression = getExpr line

      if Map.member expression exprToPosition
        then goUp exprs exprToPosition rightPartsToPositions hypos number numberToStatement expression
        else
          do
            let axiom = case isAxiom expression of
                          Just i  -> i
                          Nothing -> -1
            let hypo  = case Map.lookup expression hypos of
                          Just i  -> i
                          Nothing -> -1
            let mp    = case findMP rightPartsToPositions exprToPosition expression of
                          Just (a, b) -> (a, b)
                          Nothing -> (-1, -1)
            if axiom < 0 && hypo < 0 && fst mp < 0
              then do
                putStrLn "Proof is incorrect"
                exitSuccess
              else
                do
                  let statement = if axiom > 0
                                    then Axiom axiom number
                                    else if hypo > 0
                                           then Hypo hypo number
                                           else ModusPonens mp number
                  let exprToPosition' = Map.insert expression number exprToPosition
                  let rightPartsToPositions' = case expression of
                                                 (Binary Impl a b) -> Map.insertWith (++) b [expression] rightPartsToPositions
                                                 otherwise         -> rightPartsToPositions
                  let exprs' = Map.insert number expression exprs
                  let numberToStatement' = Map.insert (number - 1 ) statement numberToStatement
                  goUp exprs' exprToPosition' rightPartsToPositions' hypos (number + 1) numberToStatement' expression

goDown :: Int -> Map.Map Int Statement -> Set.Set Int  -> Set.Set Int
goDown number statements used = do
  let used' = Set.insert number used
  case statements Map.! number of
    Axiom a b -> used'
    Hypo b c -> used'
    ModusPonens (a, b) c -> (Set.union $! goDown (a - 1) statements used') $! goDown (b - 1) statements used'

annotate :: String -> String -> IO ()
annotate inputFile outputFile = do

  firstLine <- getLine
  firstLine <- return $! Splitter.splitOn ("|-") $ firstLine
  newFirstLine <- return $! head firstLine ++ " |- " ++ show (getExpr (last firstLine))
  toProof <- return $! getExpr (last firstLine)
  firstLine <- return $! if head firstLine == [] then "" else (head firstLine)

  hypos <- return $! Splitter.splitOn "," firstLine
  hypos <- return $! if hypos == [""] then [] else map getExpr hypos
  hypos <- return $! Map.fromList $ zip hypos [1 ..]

  (numberToExpr, exprToNumber, number', numberToStatement, last) <- goUp Map.empty Map.empty Map.empty hypos 1 Map.empty (Var "L")
  let number = number' - 1

  if last /= toProof
    then do
      putStrLn "Proof is incorrect"
      exitSuccess
    else do
      let used = Set.toAscList $! goDown ((exprToNumber Map.! last) - 1) numberToStatement Set.empty
      putStrLn newFirstLine
      showResult 1 used numberToStatement Map.empty numberToExpr

getInfo :: Statement -> Int -> Map.Map Int Int -> Map.Map Int Expr -> String
getInfo (Axiom a b) number oldToNew numberToExpr = "[" ++ show (number) ++ ". Ax. sch. " ++ show (a) ++ "] " ++ show (numberToExpr Map.! b)
getInfo (Hypo b c) number oldToNew numberToExpr = "[" ++ show (number) ++ ". Hypothesis " ++ show (b) ++ "] " ++ show (numberToExpr Map.! c)
getInfo (ModusPonens (c, d) e) number oldToNew numberToExpr = "[" ++ show (number) ++ ". M.P. "
                                                            ++ show (oldToNew Map.! d) ++ ", " ++ show (oldToNew Map.! c) ++ "] "
                                                            ++ show (numberToExpr Map.! e)

showResult :: Int  -> [Int] -> Map.Map Int Statement -> Map.Map Int Int -> Map.Map Int Expr -> IO()
showResult number [] statements oldToNew numberToExpr = putStr ""
showResult number (x: xs) statements oldToNew numberToExpr = do
  let oldToNew' = Map.insert (x + 1) number oldToNew
  putStrLn $! getInfo (statements Map.! x) number oldToNew' numberToExpr
  showResult (number + 1) xs statements oldToNew' numberToExpr


-- |- (A -> A)
--[1. Ax. sch. 1] (A -> (A -> A))
--[2. Ax. sch. 1] (A -> ((A -> A) -> A))
--[3. Ax. sch. 2] ((A -> (A -> A)) -> ((A -> ((A -> A) -> A)) -> (A -> A)))
--[4. M.P. 3, 1] ((A -> ((A -> A) -> A)) -> (A -> A))
--[5. M.P. 4, 2] (A -> A)