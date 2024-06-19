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
    | Contracted [Tableaux]
    | Null
    deriving (Eq, Show)

buildTableaux :: Label -> Formula -> Tableaux -> Tableaux
buildTableaux lbl formula Null = case formula of
    Implies a b -> 
        if lbl == F
        then Node lbl formula [buildTableaux V a (buildTableaux F b Null)]  -- Corrigindo a expansão para F
        else Node lbl formula [buildTableaux F a Null, buildTableaux V b Null]  -- Corrigindo a expansão para V
    And a b ->
        if lbl == F
        then Node lbl formula [buildTableaux F a Null, buildTableaux F b Null]  -- Corrigindo a expansão para F
        else Node lbl formula [buildTableaux V a (buildTableaux V b Null)]  -- Corrigindo a expansão para V
    Or a b ->
        if lbl == F
        then Node lbl formula [buildTableaux F a (buildTableaux F b Null)]  -- Corrigindo a expansão para F
        else Node lbl formula [buildTableaux V a Null, buildTableaux V b Null]  -- Corrigindo a expansão para V
    Not a ->
        Node lbl formula [buildTableaux (flipLabel lbl) a Null]
    Var x -> Leaf lbl (Var x)
  where
    flipLabel V = F
    flipLabel F = V

buildTableaux lbl formula tab = case formula of
    Implies a b -> 
        if lbl == F
        then Node lbl formula (tab:[buildTableaux V a (buildTableaux F b Null)])  -- Corrigindo a expansão para F
        else Node lbl formula (tab:[buildTableaux F a Null, buildTableaux V b Null])  -- Corrigindo a expansão para V
    And a b ->
        if lbl == F
        then Node lbl formula (tab:[buildTableaux F a Null, buildTableaux F b Null])  -- Corrigindo a expansão para F
        else Node lbl formula (tab:[buildTableaux V a (buildTableaux V b Null)])  -- Corrigindo a expansão para V
    Or a b ->
        if lbl == F
        then Node lbl formula (tab:[buildTableaux F a (buildTableaux F b Null)])  -- Corrigindo a expansão para F
        else Node lbl formula (tab:[buildTableaux V a Null, buildTableaux V b Null])  -- Corrigindo a expansão para V
    Not a ->
        Node lbl formula (tab:[buildTableaux (flipLabel lbl) a Null])
    Var x -> Contracted [Leaf lbl (Var x), tab]
  where
    flipLabel V = F --inverte v or f e f por v
    flipLabel F = V

isTautology :: Tableaux -> Bool --usa allBranchesContainContradiction para verificar se todos os ramos derivados do tableaux contêm uma contradição
isTautology (Node l f children) = checkBranches (accumulateBranches children []) 

accumulateBranches :: [Tableaux] -> [Tableaux] -> [[Tableaux]]
accumulateBranches (start:rest) tab = case start of 
    Node _ _ (s:r) -> ((accumulateBranches r (s:tab)) ++ (accumulateBranches rest tab))
    Contracted (s:r) -> (accumulateBranches r ((s:r)++tab)) ++ (accumulateBranches rest tab)
    Leaf l f -> (accumulateBranches [] ((Leaf l f):tab)) ++ (accumulateBranches rest tab)
accumulateBranches [] tab = [tab, []]

checkBranches :: [[Tableaux]] -> Bool -- processa múltiplos ramos e verifica se todos eles são contraditórios usando a função checkBranch
checkBranches (start: rest) = (checkBranch start True) && (checkBranches rest)
checkBranches [[]] = True
checkBranches [] = True

checkBranch:: [Tableaux] -> Bool -> Bool -- analisa um único ramo e utiliza a função hasContradiction para verificar a existência de contradições dentro dele.
checkBranch (start:rest) v = (hasContradiction start rest) || (checkBranch rest False)
checkBranch [] v = v

hasContradiction:: Tableaux -> [Tableaux] -> Bool --verifica se há contradições diretas entre folhas (Leaf) que afirmam e negam 
                                                   -- a mesma variável ou entre nós (Node) que representam operações contraditórias sobre a mesma fórmula
hasContradiction tab (start:rest) = case tab of
    Leaf V (Var x) -> case start of
        Leaf F (Var y) -> x==y
        _ -> False || (hasContradiction tab rest)
    Leaf F (Var x) -> case start of
        Leaf V (Var y) -> x==y
        _ -> False || (hasContradiction tab rest)
    Node V f _ -> case start of
        Node F g _ -> f==g
        _ -> False || (hasContradiction tab rest)
    Node F f _ -> case start of 
        Node V g _ -> f==g
        _ -> False || (hasContradiction tab rest)
    Contracted _ -> False

hasContradiction _ [] = False

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
    printTableaux' prefix (Contracted children) = concatMap (printTableaux' prefix) children

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
                    let tableaux = buildTableaux F formula Null
                    putStrLn (printTableaux tableaux)
                    if isTautology tableaux
                        then putStrLn "A fórmula é uma tautologia."
                        else putStrLn "A fórmula é falsificável."
            main
