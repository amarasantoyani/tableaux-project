module Main (main) where

import Text.Parsec
import Text.Parsec.String (Parser)

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
expand F (Not (Implies a b)) = [Node V a [], Node F b []]
expand F (Not (And a b)) = [Node V (Not a) [], Node V (Not b) []]
expand F (Not (Or a b)) = [Node V (Not a) [], Node V (Not b) []]
expand F (Not a) = [Node V a []]
expand lbl (Var x) = [Leaf lbl (Var x)]

buildTableaux :: Label -> Formula -> Tableaux
buildTableaux lbl formula = 
    case expand lbl formula of
        [] -> Leaf lbl formula
        children -> Node lbl formula (map build children)
  where
    build (Node l f _) = buildTableaux l f
    build (Leaf l f) = Leaf l f

isContradiction :: [Tableaux] -> Bool
isContradiction [] = False
isContradiction (Leaf V (Var x) : rest) =
    any (\t -> case t of
                 Leaf F (Var y) -> x == y
                 _ -> False) rest || isContradiction rest
isContradiction (Leaf F (Var x) : rest) =
    any (\t -> case t of
                 Leaf V (Var y) -> x == y
                 _ -> False) rest || isContradiction rest
isContradiction (Node _ _ children : rest) = isContradiction (children ++ rest)
isContradiction (_:rest) = isContradiction rest

checkBranch :: [Tableaux] -> Bool
checkBranch [] = False
checkBranch (Leaf V (Var x) : rest) =
    any (\t -> case t of
                 Leaf F (Var y) -> x == y
                 _ -> False) rest || checkBranch rest
checkBranch (Leaf F (Var x) : rest) =
    any (\t -> case t of
                 Leaf V (Var y) -> x == y
                 _ -> False) rest || checkBranch rest
checkBranch (Node _ _ children : rest) = checkBranch (children ++ rest)
checkBranch (_:rest) = checkBranch rest

isTautology :: Tableaux -> Bool
isTautology tableaux =
    allBranchesContainContradiction (branches tableaux)
  where
    branches :: Tableaux -> [[Tableaux]]
    branches (Leaf lbl frm) = [[Leaf lbl frm]]
    branches (Node lbl frm children) = concatMap branches children

    allBranchesContainContradiction :: [[Tableaux]] -> Bool
    allBranchesContainContradiction = all (\branch -> isContradiction branch || checkBranch branch)

parseImplies :: Parser Formula
parseImplies = try (do
    left <- parseOr
    _ <- string "->"
    right <- parseImplies
    return (Implies left right))
  <|> parseOr

parseOr :: Parser Formula
parseOr = chainl1 parseAnd (spaces *> char '|' *> spaces *> return Or)

parseAnd :: Parser Formula
parseAnd = chainl1 parseNot (spaces *> char '&' *> spaces *> return And)

parseNot :: Parser Formula
parseNot = (spaces *> char '~' *> spaces *> parseNot >>= \f -> return (Not f))
  <|> parseParen

parseParen :: Parser Formula
parseParen = between (char '(' *> spaces) (spaces *> char ')') parseExpr <|> parseVar

parseVar :: Parser Formula
parseVar = Var <$> many1 letter

parseExpr :: Parser Formula
parseExpr = parseImplies

parseFormulaFromString :: String -> Either ParseError Formula
parseFormulaFromString = parse (spaces *> parseExpr <* spaces <* eof) ""

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
                    putStrLn (printTableaux tableaux)
                    if isTautology tableaux
                        then putStrLn "A fórmula é uma tautologia."
                        else putStrLn "A fórmula é falsificável."
            main
