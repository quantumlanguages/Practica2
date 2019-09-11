{--
Practica 2
El lenguaje EAB (Sintaxis)
Autores:
Edgar Quiroz Castañeda
Sandra del Mar Soto Corderi
--}

module BAE.Sintax where

    -- Importing some useful list functions
    import Data.List

    -- Extending the sintax

    -- | Renaming String to Identifier in order to use text as variables' name.
    type Identifier = String

    -- | Defining the expresions of the language. Same as before, but now with
    -- variables
    data Expr = V Identifier | I Int | B Bool -- ^ Basic expresions
                | Add Expr Expr | Mul Expr Expr -- ^ Binary arithmetic operations
                | Succ Expr | Pred Expr -- ^ Unary arithmetic operations
                | Not Expr | And Expr Expr | Or Expr Expr -- ^ Logical operations
                | Lt Expr Expr | Gt Expr Expr | Eq Expr Expr -- ^ Comparaison operations
                | If Expr Expr Expr -- ^ If operation
                | Let Identifier Expr Expr -- ^ Variable declaration and bounding operation
                deriving (Eq)

    -- | Implementing the Show class to make expression visualization prettier.
    instance Show Expr where
      show e = case e of
            (V x) -> "V[" ++ x ++ "]"
            (I n) -> "N[" ++ (show n) ++ "]"
            (B b) -> "B[" ++ (show b) ++ "]"
            (Add e1 e2) -> "add("++ (show e1) ++ " , " ++ (show e2) ++ ")"
            (Mul e1 e2) -> "mul("++ (show e1) ++ " , " ++ (show e2) ++ ")"
            (Succ e) -> "suc(" ++ (show e) ++ ")"
            (Pred e) -> "pred(" ++ (show e) ++ ")"
            (Not e) -> "not(" ++ (show e) ++ ")"
            (And e1 e2) -> "and["++ (show e1) ++ " , " ++ (show e2) ++ ")"
            (Or e1 e2) -> "or("++ (show e1) ++ " , " ++ (show e2) ++ ")"
            (Lt e1 e2) -> "lt("++ (show e1) ++ " , " ++ (show e2) ++ ")"
            (Gt e1 e2) -> "gt("++ (show e1) ++ " , " ++ (show e2) ++ ")"
            (Eq e1 e2) -> "eq("++ (show e1) ++ " , " ++ (show e2) ++ ")"
            (If ec e1 e2) -> "if("++ (show ec) ++ " , " ++ (show e1) ++ " , "
                           ++ (show e2) ++ ")"
            (Let x e1 e2) -> "let(" ++ (show e1) ++ " , " ++ (show x) ++ "." ++ (show e2) ++ ")"

    -- Defining some semantics

    -- | Variable asignation will be emulated using textual sustitution
    type Substitution = (Identifier, Expr)

    -- | Obtaining the free variables from an expression
    frVars :: Expr -> [Identifier]
    frVars ex =
        case ex of
            (V x) -> [x]
            (I _) -> []
            (B _) -> []
            (Add e f) -> union (frVars e) (frVars f)
            (Mul e f) -> union (frVars e) (frVars f)
            (Succ e) -> frVars e
            (Pred e) -> frVars e
            (Not e) -> frVars e
            (And e f) -> union (frVars e) (frVars f)
            (Or e f) -> union (frVars e) (frVars f)
            (Lt e f) -> union (frVars e) (frVars f)
            (Gt e f) -> union (frVars e) (frVars f)
            (Eq e f) -> union (frVars e) (frVars f)
            (If e f g) -> union (union (frVars e) (frVars f)) (frVars g)
            (Let i e f) -> union (frVars e) ((frVars f) \\ [i])

    -- | Applying subtition if semantically possible
    subst :: Expr -> Substitution -> Expr
    subst ex s =
        case ex of
            (V x) ->
                if x == y then r else ex
                where (y, r) = s
            (I _) -> ex
            (B _) -> ex
            (Add e f) -> Add (st e) (st f)
            (Mul e f) -> Mul (st e) (st f)
            (Succ e) -> Succ (st e)
            (Pred e) -> Pred (st e)
            (Not e) -> Not (st e)
            (And e f) -> And (st e) (st f)
            (Or e f) -> Or (st e) (st f)
            (Lt e f) -> Lt (st e) (st f)
            (Gt e f) -> Gt (st e) (st f)
            (Eq e f) -> Eq (st e) (st f)
            (If e f g) -> If (st e) (st f) (st g)
            (Let i e f) ->
                if i /= j && not (elem i (frVars r))
                    then Let i (st e) (st f)
                    else let i' = safeName f in (Let i' e (subst f (i, V i')))

                where (j, r) = s
        where st = (flip subst) s

    -- | Determining if two expressions are alpha-equivalent
    alphaEq :: Expr -> Expr -> Bool
    alphaEq (V x) (V y) = x == y
    alphaEq (I n) (I m) = n == m
    alphaEq (B p) (B q) = p == q
    alphaEq (Add e f) (Add g h) = (alphaEq e g) && (alphaEq f h)
    alphaEq (Mul e f) (Mul g h) = (alphaEq e g) && (alphaEq f h)
    alphaEq (Succ e) (Succ f) = alphaEq e f
    alphaEq (Pred e) (Pred f) = alphaEq e f
    alphaEq (Not e) (Not f) = alphaEq e f
    alphaEq (And e f) (And g h) = (alphaEq e g) && (alphaEq f h)
    alphaEq (Or e f) (Or g h) = (alphaEq e g) && (alphaEq f h)
    alphaEq (Lt e f) (Lt g h) = (alphaEq e g) && (alphaEq f h)
    alphaEq (Gt e f) (Gt g h) = (alphaEq e g) && (alphaEq f h)
    alphaEq (Eq e f) (Eq g h) = (alphaEq e g) && (alphaEq f h)
    alphaEq (If e f g) (If h i j) = (alphaEq e h) && (alphaEq f i) && (alphaEq g j)
    alphaEq (Let i e f) (Let j g h) =
        if i == j
            then (alphaEq e g) && (alphaEq f h)
            else (alphaEq e g) && (alphaEq (rename i s f) (rename j s h))
        where s = max (safeName f) (safeName h)
    alphaEq _ _ = False

    -- | Renames a variable in an expression
    rename :: String -> String -> Expr -> Expr
    rename s1 s2 ex =
        case ex of
            (V x) -> if x == s1 then (V s2) else ex
            (I _) -> ex
            (B _) -> ex
            (Add e f) -> Add (r e) (r f)
            (Mul e f) -> Mul (r e) (r f)
            (Succ e) -> Succ (r e)
            (Pred e) -> Pred (r e)
            (Not e) -> Not (r e)
            (And e f) -> And (r e) (r f)
            (Or e f) -> Or (r e) (r f)
            (Lt e f) -> Lt (r e) (r f)
            (Gt e f) -> Gt (r e) (r f)
            (Eq e f) -> Eq (r e) (r f)
            (If e f g) -> If (r e) (r f) (r g)
            (Let i e f) -> Let j (r e) (r f)
                where j = if i == s1 then s2 else i
        where r = rename s1 s2


    -- | Given an expression, find a variable name that is no currently in the
    -- expression.
    safeName :: Expr -> String
    safeName ex = (foldr (max) "" (vars ex)) ++ "'"

    -- | Get all the variable names in an expression.
    vars :: Expr -> [String]
    vars ex =
        case ex of
            (V x) -> [x]
            (I _) -> []
            (B _) -> []
            (Add e f) -> union (vars e) (vars f)
            (Mul e f) -> union (vars e) (vars f)
            (Succ e) -> vars e
            (Pred e) -> vars e
            (Not e) -> vars e
            (And e f) -> union (vars e) (vars f)
            (Or e f) -> union (vars e) (vars f)
            (Lt e f) -> union (vars e) (vars f)
            (Gt e f) -> union (vars e) (vars f)
            (Eq e f) -> union (vars e) (vars f)
            (If e f g) -> union (union (vars e) (vars f)) (vars g)
            (Let i e f) -> union (union (vars e) (vars f)) [i]
