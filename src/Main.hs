module Main where

import Text.Parsec
import Text.Parsec.String (Parser)
import Data.List (intercalate)

data Formula
    = Var String
    | Not Formula
    | And Formula Formula
    | Or Formula Formula
    | Implies Formula Formula
    deriving (Eq, Show)

data Label = V | F deriving (Eq, Show)

data Tableaux
    = Leaf Label Formula
    | Node Label Formula [Tableaux]
    deriving (Eq, Show)

expand :: Label -> Formula -> [Tableaux]
expand V (Implies a b) = [Node F a [], Node V b []]
expand F (Implies a b) = [Node V a [], Node F b []]
expand V (And a b) = [Node V a [], Node V b []]
expand F (And a b) = [Node F a [], Node F b []]
expand V (Or a b) = [Node V a [], Node V b []]
expand F (Or a b) = [Node F a [], Node F b []]
expand V (Not a) = [Node F a []]
expand F (Not a) = [Node V a []]
expand _ (Var _) = []

buildTableaux :: Label -> Formula -> Tableaux
buildTableaux label formula = build (Node label formula [])
  where
    build node@(Leaf _ _) = node
    build (Node lbl frm children) =
        let newChildren = expand lbl frm
        in Node lbl frm (map build newChildren)

isContradiction :: [Tableaux] -> Bool
isContradiction [] = False
isContradiction (Leaf V (Var x) : rest) = any (\(Leaf F (Var y)) -> x == y) rest || isContradiction rest
isContradiction (Leaf F (Var x) : rest) = any (\(Leaf V (Var y)) -> x == y) rest || isContradiction rest
isContradiction (_:rest) = isContradiction rest

isTautology :: Tableaux -> Bool
isTautology tableaux = not (isContradiction (flatten tableaux))
  where
    flatten (Leaf lbl frm) = [Leaf lbl frm]
    flatten (Node _ _ children) = concatMap flatten children

parseFormula :: Parser Formula
parseFormula = parseImplies

parseImplies :: Parser Formula
parseImplies = try (do
    left <- parseOr
    _ <- string "->"
    right <- parseImplies
    return (Implies left right))
  <|> parseOr

parseOr :: Parser Formula
parseOr = try (do
    left <- parseAnd
    _ <- string "|"
    right <- parseOr
    return (Or left right))
  <|> parseAnd

parseAnd :: Parser Formula
parseAnd = try (do
    left <- parseNot
    _ <- string "&"
    right <- parseAnd
    return (And left right))
  <|> parseNot

parseNot :: Parser Formula
parseNot = try (do
    _ <- string "~"
    Not <$> parseNot)
  <|> parseVar

parseVar :: Parser Formula
parseVar = Var <$> many1 letter

parseFormulaFromString :: String -> Either ParseError Formula
parseFormulaFromString = parse parseFormula ""

printTableaux :: Tableaux -> String
printTableaux tableaux = unlines (printTableaux' "" tableaux)
  where
    printTableaux' :: String -> Tableaux -> [String]
    printTableaux' prefix (Leaf lbl frm) = [prefix ++ show lbl ++ ": " ++ show frm]
    printTableaux' prefix (Node lbl frm children) =
      (prefix ++ show lbl ++ ": " ++ show frm) : concatMap (printTableaux' (prefix ++ "  ")) children

main :: IO ()
main = do
    putStrLn "Digite uma fórmula proposicional (ou 'sair' para terminar):"
    input <- getLine
    if input == "sair"
        then return ()
        else do
            case parseFormulaFromString input of
                Left err -> print err
                Right formula -> do
                    let tableaux = buildTableaux F formula
                    putStrLn "Árvore de prova/refutação:"
                    putStrLn (printTableaux tableaux)
                    if isTautology tableaux
                        then putStrLn "A fórmula é uma tautologia."
                        else putStrLn "A fórmula é falsificável."
            main
