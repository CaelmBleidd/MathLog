module Proof where

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
import           Tables
import           Deductor

evaluate :: (Map.Map String Bool) -> Expr -> Bool
evaluate table (Binary Impl a b) = (not (evaluate table a)) || (evaluate table b)
evaluate table (Binary And  a b) = (     evaluate table a)  && (evaluate table b)
evaluate table (Binary Or   a b) = (     evaluate table a)  || (evaluate table b)
evaluate table (Not         a  ) = (not (evaluate table a))
evaluate table (Var         a  ) =
  case Map.lookup a table of
    Just a -> a
    Nothing -> error (show a ++ " " ++ show table)

getVariables :: Expr -> Set.Set String
getVariables (Binary Impl a b) = Set.union (getVariables a) (getVariables b)
getVariables (Binary And a b) = Set.union (getVariables a) (getVariables b)
getVariables (Binary Or a b) = Set.union (getVariables a) (getVariables b)
getVariables (Not a) = getVariables a
getVariables (Var a) = Set.fromList [a]

proofExpr :: Map.Map String Bool -> Expr -> (Bool, [String])
proofExpr table (Binary Impl a b) =
  let
    (val_a, proof_a) = proofExpr table a
    (val_b, proof_b) = proofExpr table b
    value = not val_a || val_b
    proof = case val_a of
              True -> case val_b of
                        True -> get_one_one_impl
                        False -> get_one_zero_impl
              False -> case val_b of
                        True -> get_zero_one_impl
                        False -> get_zero_zero_impl
    proof' = [replaceOnAAndB a b proof]
  in
    (value, proof_a ++ proof_b ++ proof')

proofExpr table (Binary And a b) =
  let
    (val_a, proof_a) = proofExpr table a
    (val_b, proof_b) = proofExpr table b
    value =  val_a && val_b
    proof = case val_a of
              True -> case val_b of
                        True -> get_one_one_and
                        False -> get_one_zero_and
              False -> case val_b of
                        True -> get_zero_one_and
                        False -> get_zero_zero_and
    proof' = [replaceOnAAndB a b proof]
  in
    (value, proof_a ++ proof_b ++ proof')

proofExpr table (Binary Or a b) =
  let
    (val_a, proof_a) = proofExpr table a
    (val_b, proof_b) = proofExpr table b
    value = val_a || val_b
    proof = case val_a of
              True -> case val_b of
                        True -> get_one_one_or
                        False -> get_one_zero_or
              False -> case val_b of
                        True -> get_zero_one_or
                        False -> get_zero_zero_or
    proof' = [replaceOnAAndB a b proof]

  in
    (value, proof_a ++ proof_b ++ proof')

proofExpr table (Not a) =
  let
    (val_a, proof_a) = proofExpr table a
    value = not val_a
    proof = case val_a of
              True -> get_one
              False -> ""
    proof' = [replaceOnA (a, proof)]
  in
    (value, proof_a ++ proof')

proofExpr table (Var a) =
  let
    val = case Map.lookup a table of
            Just x -> x
            Nothing -> error "ERROR IN PROOF VAR"
    proof = if val then get_one else get_zero
    proof' = [replaceOnA (Var a, proof)]
  in
    (val, proof')

getTruthTable :: Set.Set String -> [[Bool]]
getTruthTable variables = replicateM (length variables) [False, True]

isGenerallyValid :: Map.Map String Bool -> Expr -> Bool
isGenerallyValid map expr = evaluate map expr

getHyposTable :: [[Map.Map String Bool]] -> [Map.Map String Bool]
getHyposTable tables = if (length tables == 0) then [] else (head tables)

getHypos :: [[Bool]] -> [String] -> [String]
getHypos table list = case table of
    [[False], [True]] -> []
    [[True], [True]] -> ["A"]
    [[False], [False]] -> ["!A"]
    [[False, False],[False, True],[True, False],[True, True]] -> []
    [[True, False], [True, True],[True, False], [True, True]] -> ["A"]
    [[False, True], [True, True],[False, True], [True, True]] -> ["B"]
    [[True, True], [True, True],[True, True], [True, True]] -> ["A", "B"]
    [[False, False], [False, True],[False, False], [False, True]] -> ["!A"]
    [[False, False], [True, False],[False, False], [True, False]] -> ["!B"]
    [[False, False], [False, False],[False, False], [False, False]] -> ["!A", "!B"]
    [[False, False, False],[False, False, True],[False, True, False],[False, True, True],[True, False, False],[True, False, True],[True, True, False],[True, True, True]]  -> []
    [[True, False, False], [True, False, True],[True, True, False], [True, True, True], [True, False, False],[True, False, True], [True, True, False],[True, True, True]] -> ["A"]
    [[False, True, False], [False, True, True],[False, True, False], [False, True, True], [True, True, False],[True, True, True], [True, True, False],[True, True, True]] -> ["B"]
    [[False, False, True], [False, False, True],[False, True, True], [False, True, True], [True, False, True],[True, False, True], [True, True, True],[True, True, True]] -> ["C"]
    [[True, True, False], [True, True, True],[True, True, False], [True, True, True], [True, True, False],[True, True, True], [True, True, False],[True, True, True]] -> ["A", "B"]
    [[True, False, True], [True, False, True],[True, True, True], [True, True, True], [True, False, True],[True, False, True], [True, True, True],[True, True, True]] -> ["A", "C"]
    [[False, True, True], [False, True, True],[False, True, True], [False, True, True], [True, True, True],[True, True, True], [True, True, True],[True, True, True]] -> ["B", "C"]
    [[True, True, True], [True, True, True],[True, True, True], [True, True, True], [True, True, True],[True, True, True], [True, True, True],[True, True, True]] -> ["A", "B", "C"]
    [[False, False, False], [False, False, True],[False, True, False], [False, True, True], [False, False, False],[False, False, True], [False, True, False],[False, True, True]] -> ["!A"]
    [[False, False, False], [False, False, True],[False, False, False], [False, False, True], [True, False, False],[True, False, True], [True, False, False],[True, False, True]] -> ["!B"]
    [[False, False, False], [False, False, False],[False, True, False], [False, True, False], [True, False, False],[True, False, False], [True, True, False],[True, True, False]] -> ["!C"]
    [[False, False, False], [False, False, True],[False, False, False], [False, False, True], [False, False, False],[False, False, True], [False, False, False],[False, False, True]] -> ["!A", "!B"]
    [[False, False, False], [False, False, False],[False, True, False], [False, True, False], [False, False, False],[False, False, False], [False, True, False],[False, True, False]] -> ["!A", "!C"]
    [[False, False, False], [False, False, False],[False, False, False], [False, False, False], [True, False, False],[True, False, False], [True, False, False],[True, False, False]] -> ["!B", "!C"]
    [[False, False, False], [False, False, False],[False, False, False], [False, False, False], [False, False, False],[False, False, False], [False, False, False],[False, False, False]] -> ["!A", "!B", "!C"]

    otherwise -> []

addHyposToMap :: [String] -> String -> (String, Bool)
addHyposToMap hypos hypo =
  let
    hypos' = Set.fromList hypos
    val = Set.member hypo hypos'
    (result, value) = case val of
                        True -> (hypo, True)
                        False -> (hypo, False)
  in
    (result, value)

getHyposForExpr variablesAmount  variablesSet expr =
  let
    tables = case variablesAmount of
                         1 -> [one, one_a]
                         2 -> [two, two_a, two_b, two_a_b]
                         3 -> [three, three_a, three_b, three_c, three_a_b, three_a_c, three_b_c, three_a_b_c]
                         otherwise -> error "ОШИБКА"

    truthTablesWithVariables = map (\y -> map (\elem -> Map.fromList (zip (Set.toList variablesSet) elem)) y) tables

    truthTablesWithVariables' = filter (\x -> all (\y -> isGenerallyValid y expr) x) truthTablesWithVariables
  in
    case (length truthTablesWithVariables') of
      0 -> Nothing
      otherwise -> Just truthTablesWithVariables'

getHyposForNotExpr variablesAmount variablesSet expr =
  let
    new_tables = case variablesAmount of
                             1 -> [one, one_not_a]
                             2 -> [two, two_not_a, two_not_b, two_not_a_b]
                             3 -> [three, three_not_a, three_not_b, three_not_c, three_not_a_b,three_not_a_c, three_not_b_c, three_not_a_b_c]
                             otherwise -> error "ОШИБКА"

    xxx =  map (\y -> map (\elem -> Map.fromList (zip (Set.toList variablesSet) elem)) y) new_tables

    xxx' = filter (\x -> all (\y -> isGenerallyValid y (Not expr)) x) xxx
  in
    case (length xxx') of
      0 -> Nothing
      otherwise -> Just xxx'

printHypos hypos = Data.List.intercalate ", " hypos

collapse :: (Set.Set String, [[String]]) -> Set.Set String -> (Set.Set String, [[String]])
collapse (freeVars, proofs) hypos =
  let
        halves x = splitAt ((length x) `div` 2) x
        subj = head $ Set.toList freeVars
        freeVars' = Set.drop 1 freeVars
        (a, b) = halves proofs
        a' = map (\x -> commonDeduce subj hypos freeVars x) a
        b' = map (\x -> commonDeduce ("!" ++ subj) hypos freeVars x) b
        pairs = zip a' b'
        pairs' = zip pairs a
        proofs' = map (\(x,y) -> mergeProofs (subj,("!" ++ subj), let a = last y in a) (fst x) (snd x)) pairs'
    in
        (freeVars', proofs')

mergeProofs :: (String, String, String) -> [String] -> [String] -> [String]
mergeProofs (a,nega,expr) proof1 proof2 =
    let
        proof' = proof1 ++ proof2
    in
        proof'

printProof :: [String] -> String
printProof proof = concat proof


collapseAll :: (Set.Set String, [[String]]) -> Set.Set String -> [String]
collapseAll (freeVars, proofs) hypos = if Set.null freeVars then head proofs else collapseAll (collapse (freeVars, proofs) hypos) hypos

proofAndWrite :: String -> String -> IO ()
proofAndWrite inputFile outputFile = do

    exprString <- getLine
    expr <- return $ getExpr exprString

    variablesSet <- return $ getVariables expr

    variablesAmount <- return $ length variablesSet

    case getHyposForExpr variablesAmount variablesSet expr of
      Just a -> do
                  hyposTable <- return $ getHyposTable a
                  hyposTableWithoutVariables <- return $ if (length hyposTable == 0) then [] else map Map.elems hyposTable

                  -- [String] гипотезы на вывод
                  hypos <- return $ getHypos hyposTableWithoutVariables (Set.toList variablesSet)
                  -- [сет гипотез]
                  hyposVars <- return $ Set.unions $ map getVariables (map getExpr hypos)
                  -- переменные, которые не вошли в гипотезы
                  notInHypos <- return $ Set.difference variablesSet hyposVars

                  -- мапка из гипотез в их значения
                  mapHypos <- return $ map (addHyposToMap hypos) (Set.toList hyposVars)
                  mapHypos <- return $ Map.fromList mapHypos

                  -- таблица истинности для свободных переменных
                  oneMoreTruthTable <- return $ replicateM (length notInHypos) [True, False]
                  -- Таблица истинности для всех переменных, включая гипотезы
                  fullOneMoreTruthTable <- return $ map (\x -> Map.union mapHypos (Map.fromList (zip (Set.toList notInHypos) x))) oneMoreTruthTable

                  -- для каждой строчки таблицы истинности возвращаем своё доказательство
                  -- [[String]]
                  proofs <- return $ map (\x -> snd (proofExpr x expr)) fullOneMoreTruthTable

                  -- передаю свободные перменные и доказательства в виде списка списков строк (где каждая строка -- доказательство одного шага)
                  --result <- return $ collapseAll (notInHypos, proofs) (Set.fromList hypos)

                  putStr $ printHypos hypos
                  putStrLn $ " |- " ++ (show expr)

                  proofs <- return $ (collapseAll (notInHypos, proofs) (Set.fromList hypos))

                  putStrLn $ printProof $ proofs
                  --putStrLn $ Data.List.intercalate "" ( collapseAll (notInHypos, proofs) (Set.fromList hypos))
                   --putStrLn $ printProof $ ["A", "B"]


      Nothing ->
                case getHyposForNotExpr variablesAmount variablesSet expr of
                  Just b -> do
                    hyposTable <- return $ getHyposTable b
                    hyposTableWithoutVariables <- return $ if (length hyposTable == 0) then [] else map Map.elems hyposTable
                    hypos <- return $ getHypos hyposTableWithoutVariables (Set.toList variablesSet)
                    hyposVars <- return $ Set.unions $ map getVariables (map getExpr hypos)
                    notInHypos <- return $ Set.difference variablesSet hyposVars

                    mapHypos <- return $ map (addHyposToMap hypos) (Set.toList hyposVars)
                    mapHypos <- return $ Map.fromList mapHypos

                    oneMoreTruthTable <- return $ replicateM (length notInHypos) [True, False]
                    fullOneMoreTruthTable <- return $ map (\x -> Map.union mapHypos (Map.fromList (zip (Set.toList notInHypos) x))) oneMoreTruthTable

                    -- [String], where each String is concat subProof
                    proofs <- return $ map (\x -> snd (proofExpr x (Not expr))) fullOneMoreTruthTable

                    putStr $ printHypos hypos
                    putStrLn $ " |- " ++ (show (Not expr))

                    putStrLn $ Data.List.intercalate "" ( collapseAll (notInHypos, proofs) (Set.fromList hypos))



                  Nothing -> putStrLn(":(")
