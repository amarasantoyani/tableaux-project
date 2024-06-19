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

expand :: Label -> Formula -> [Tableaux]
expand V (Implies a b) = [Node F a [Node V b []]]
expand F (Implies a b) = [Node V a [], Node F b []]
expand V (And a b) = [Node V a [Node V b []]]
expand F (And a b) = [Node F a [], Node F b []]
expand V (Or a b) = [Node V a [], Node V b []]
expand F (Or a b) = [Node F a [Node F b []]]
expand V (Not a) = [Node F a []]
expand F (Not (Implies a b)) = [Node V a [], Node F b []]
expand F (Not (And a b)) = [Node V (Not a) [], Node V (Not b) []]
expand F (Not (Or a b)) = [Node V (Not a) [], Node V (Not b) []]
expand F (Not a) = [Node V a []]
expand lbl (Var x) = [Leaf lbl (Var x)]

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
    flipLabel V = F
    flipLabel F = V

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

f1 :: Tableaux -> Bool
f1 (Node l f children) = f3 (f2 children [])

f2 :: [Tableaux] -> [Tableaux] -> [[Tableaux]]
f2 (start:rest) tab = case start of 
    Node _ _ (s:r) -> ((f2 [s] tab) ++ (f2 r tab))
    Contracted (s:r) -> f2 r (s:tab)
    Leaf l f -> f2 rest ((Leaf l f):tab)
f2 [] tab = [tab, []]

f3 :: [[Tableaux]] -> Bool
f3 (start: rest) = (f4 start) && (f3 rest)
f3 [[]] = True

f4:: [Tableaux] -> Bool
f4 (start:rest) = (f5 start rest) || (f4 rest)
f4 [] = False

f5:: Tableaux -> [Tableaux] -> Bool
f5 (Leaf V (Var x)) ((Leaf F (Var y)):rest) = (x==y) || (f5 (Leaf V (Var x)) rest)
f5 (Leaf F (Var x)) ((Leaf V (Var y)):rest) = (x==y) || (f5 (Leaf F (Var x)) rest)
f5 (Leaf F (Var x)) ((Leaf F (Var y)):rest) = (f5 (Leaf F (Var x)) rest)
f5 (Leaf V (Var x)) ((Leaf V (Var y)):rest) = (f5 (Leaf V (Var x)) rest)
f5 _ [] = False

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
                    if f1 tableaux
                        then putStrLn "A fórmula é uma tautologia."
                        else putStrLn "A fórmula é falsificável."
            main
