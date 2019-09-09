
{--
Semanal 1
El lenguaje EAB (Sintaxis)
Autora: Sandra del Mar Soto Corderi
--}

module BAE.Sintax where
  --Importamos las funciones de data list
  import Data.List

  --Renombramos el tipo de daros String a Identifier para representar al conjunto
  --de nombres de variables como cadenas de texto
  type Identifier = String

  --Definimos la sintaxis de las expresiones EAB
  data Expr = V Identifier | I Int | B Bool
              | Add Expr Expr | Mul Expr Expr
              | Succ Expr | Pred Expr
              | Not Expr | And Expr Expr | Or Expr Expr
              | Lt Expr Expr | Gt Expr Expr | Eq Expr Expr
              | If Expr Expr Expr
              | Let Identifier Expr Expr deriving (Eq)

--1. Crea una instancia de la clase Show que muestre las expresiones en sintaxis
--abstracta de orden superior.
  instance Show Expr where
    show e = case e of
          (V x) -> "V[" ++ x ++ "]"
          (I n) -> "N[" ++ (show n) ++ "]"
          (B b) -> "B[" ++ (show b) ++ "]"
          (Add e1 e2) -> "SUMA["++ (show e1) ++ " , " ++ (show e2) ++ "]"
          (Mul e1 e2) -> "PROD["++ (show e1) ++ " , " ++ (show e2) ++ "]"
          (Succ e1) -> "S[" ++ (show e1) ++ "]"
          (Pred e1) -> "P[" ++ (show e1) ++ "]"
          (Not e1) -> "NOT[" ++ (show e1) ++ "]"
          (And e1 e2) -> "&["++ (show e1) ++ " , " ++ (show e2) ++ "]"
          (Or e1 e2) -> "|["++ (show e1) ++ " , " ++ (show e2) ++ "]"
          (Lt e1 e2) -> "<["++ (show e1) ++ " , " ++ (show e2) ++ "]"
          (Gt e1 e2) -> ">["++ (show e1) ++ " , " ++ (show e2) ++ "]"
          (Eq e1 e2) -> "=["++ (show e1) ++ " , " ++ (show e2) ++ "]"
          (If x e1 e2) -> "IF["++ (show x) ++ " , " ++ (show e1) ++ " , "
                         ++ (show e2) ++ "]"
          (Let x e1 e2) -> "LET[" ++ (show e1) ++ " , " ++ (show x) ++ "." ++ (show e2) ++ "]"

--Definiremos el tipo sustitución del siguiente modo∷
  type Substitution = (Identifier, Expr)

--2. Función que obtiene el conjunto de variables libres de una expresión
  frVars :: Expr -> [Identifier]
  frVars e =  case e of
          (V x) -> [x]
          (I _) -> []
          (B _) -> []
          (Add e1 e2) -> union (frVars e1) (frVars e2)
          (Mul e1 e2) -> union (frVars e1) (frVars e2)
          (Succ e1)-> frVars e1
          (Pred e1)-> frVars e1
          (Not e1)-> frVars e1
          (And e1 e2) -> union (frVars e1) (frVars e2)
          (Or e1 e2) -> union (frVars e1) (frVars e2)
          (Lt e1 e2) -> union (frVars e1) (frVars e2)
          (Gt e1 e2) -> union (frVars e1) (frVars e2)
          (Eq e1 e2) -> union (frVars e1) (frVars e2)
          (If x e1 e2) -> union (union (frVars e1) (frVars e2)) (frVars x)
          --Quitamos las variables ligadas al let
          (Let x e1 e2) -> union (frVars e1) ((frVars e2) \\ [x])

--3. Función que aplica la sustitución a la expresión dada en caso de ser posible
  subst :: Expr -> Substitution -> Expr
  subst (V x) (y, e) = if x==y then e else V x
  subst (I n) _ = I n
  subst (B b) _ = B b
  subst (Add e1 e2) sus = Add (subst e1 sus) (subst e2 sus)
  subst (Mul e1 e2) sus = Mul (subst e1 sus) (subst e2 sus)
  subst (Succ e) sus = Succ (subst e sus)
  subst (Pred e) sus = Pred (subst e sus)
  subst (Not e) sus = Not (subst e sus)
  subst (And e1 e2) sus = And (subst e1 sus) (subst e2 sus)
  subst (Or e1 e2) sus = Or (subst e1 sus) (subst e2 sus)
  subst (Lt e1 e2) sus = Lt (subst e1 sus) (subst e2 sus)
  subst (Gt e1 e2) sus = Gt (subst e1 sus) (subst e2 sus)
  subst (Eq e1 e2) sus = Eq (subst e1 sus) (subst e2 sus)
  subst (If x e1 e2) sus = If (subst x sus) (subst e1 sus) (subst e2 sus)
  subst (Let x e1 e2) s@(y, e) = if ( (not (elem x (frVars e))) && (x/=y)) then
                                    Let x (subst e1 s) (subst e2 s)
                               else error "No se puede aplicar la sustitucion"

--4. Función que determina si dos expresiones son alfa equivalentes.
  alphaEq :: Expr -> Expr -> Bool
  alphaEq (V x) (V y) = x == y
  alphaEq (I n) (I m) = n == m
  alphaEq (B b) (B d) = b == d
  alphaEq (Add e1 e2) (Add x1 x2) = (alphaEq e1 x1) && (alphaEq e2 x2)
  alphaEq (Mul e1 e2) (Mul x1 x2) = (alphaEq e1 x1) && (alphaEq e2 x2)
  alphaEq (Succ e1) (Succ e2) = alphaEq e1 e2
  alphaEq (Pred e1) (Pred e2) = alphaEq e1 e2
  alphaEq (Not e1) (Not e2) = alphaEq e1 e2
  alphaEq (And e1 e2) (And x1 x2) = (alphaEq e1 x1) && (alphaEq e2 x2)
  alphaEq (Or e1 e2) (Or x1 x2) = (alphaEq e1 x1) && (alphaEq e2 x2)
  alphaEq (Lt e1 e2) (Lt x1 x2) = (alphaEq e1 x1) && (alphaEq e2 x2)
  alphaEq (Gt e1 e2) (Gt x1 x2) = (alphaEq e1 x1) && (alphaEq e2 x2)
  alphaEq (Eq e1 e2) (Eq x1 x2) = (alphaEq e1 x1) && (alphaEq e2 x2)
  alphaEq (If x e1 e2) (If y x1 x2) = (alphaEq x y) && (alphaEq e1 x1) && (alphaEq e2 x2)
  --Este es el caso que nos importa, ya que están las variables ligadas
  alphaEq (Let x e1 e2) (Let y x1 x2) =
      if x == y --Si la variable de ligado es la misma, comparamos las expresiones directament
          then (alphaEq e1 x1) && (alphaEq e2 x2)
          --Si no son la misma variable de ligado, renombramos las variables de ligado y las ligadas
          else (alphaEq e1 x1) && (alphaEq (renombra x sus e2) (renombra y sus x2))
          where sus = max (encuentraSust e2) (encuentraSust x2)
  alphaEq _ _ = False

--Funciones auxiliares utilizadas para alphaEq

  -- Función que obtiene los nombres de las variables en una expresión
  varsF :: Expr -> [String]
  varsF (V x) = [x]
  varsF (I _) = []
  varsF (B _) = []
  varsF (Add e1 e2) =  union (varsF e1) (varsF e2)
  varsF (Mul e1 e2) =  union (varsF e1) (varsF e2)
  varsF (Succ e)=  varsF e
  varsF (Pred e)=  varsF e
  varsF (Not e)=  varsF e
  varsF (And e1 e2) =  union (varsF e1) (varsF e2)
  varsF (Or e1 e2) =  union (varsF e1) (varsF e2)
  varsF (Lt e1 e2) =  union (varsF e1) (varsF e2)
  varsF (Gt e1 e2) =  union (varsF e1) (varsF e2)
  varsF (Eq e1 e2) =  union (varsF e1) (varsF e2)
  varsF (If x e1 e2) =  union (union (varsF e1) (varsF e2)) (varsF x)
  varsF (Let x e1 e2) =  union (varsF e1) (union (varsF e2) [x])

  --Función que renombra las variables de una expresión
  renombra :: String -> String -> Expr -> Expr
  renombra sus1 sus2 (V x) = if x == sus1 then (V sus2) else V x
  renombra _ _ (I n) = I n
  renombra _ _ (B b) = B b
  renombra sus1 sus2 (Add e1 e2) = Add (renombra sus1 sus2 e1) (renombra sus1 sus2 e2)
  renombra sus1 sus2 (Mul e1 e2) = Mul (renombra sus1 sus2 e1) (renombra sus1 sus2 e2)
  renombra sus1 sus2 (Succ e) = Succ (renombra sus1 sus2 e)
  renombra sus1 sus2 (Pred e) = Pred (renombra sus1 sus2 e)
  renombra sus1 sus2 (Not e) = Not (renombra sus1 sus2 e)
  renombra sus1 sus2 (And e1 e2) = And (renombra sus1 sus2 e1) (renombra sus1 sus2 e2)
  renombra sus1 sus2 (Or e1 e2) = Or (renombra sus1 sus2 e1) (renombra sus1 sus2 e2)
  renombra sus1 sus2 (Lt e1 e2) = Lt (renombra sus1 sus2 e1) (renombra sus1 sus2 e2)
  renombra sus1 sus2 (Gt e1 e2) = Gt (renombra sus1 sus2 e1) (renombra sus1 sus2 e2)
  renombra sus1 sus2 (Eq e1 e2) = Eq (renombra sus1 sus2 e1) (renombra sus1 sus2 e2)
  renombra sus1 sus2 (If x e1 e2) = If (renombra sus1 sus2 x) (renombra sus1 sus2 e1) (renombra sus1 sus2 e2)
  renombra sus1 sus2 (Let x e1 e2) = Let y (renombra sus1 sus2 e1) (renombra sus1 sus2 e2)
                                  where y = if x == sus1 then sus2 else y

  --Función que sirve para encontrar una variable nueva
  encuentraSust :: Expr -> String
  encuentraSust e = (foldr (\ x xs -> if length x > length xs then x else xs) "" (varsF e)) ++ "'"
