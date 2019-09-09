module BAE.Semantic where

  import BAE.Sintax

  data Type = Integer | Boolean deriving (Eq, Show)

  type Decl = (Identifier, Type)

  type Ctx = [Decl]

  eval1 :: Expr -> Expr
  eval1 expr =
    case expr of
      I n -> error "blocked state"
      B p -> error "blocked state"
      V x -> error "blocked state"
      Add (I n) (I m) -> I (n + m)
      Add (I n) e -> let e' = eval1 e in Add (I n) e'
      Add e1 e2 -> let e1' = eval1 e1 in Add e1' e2
      Mul (I n) (I m) -> I (n * m)
      Mul (I n) e -> let e' = eval1 e in Mul (I n) e'
      Mul e1 e2 -> let e1' = eval1 e1 in Mul e1' e2
      Succ (I n) -> I (n + 1)
      Succ e -> Succ (eval1 e)
      Pred (I 0) -> error "blocked state"
      Pred (I n) -> I (n - 1)
      Pred e -> Pred (eval1 e)
      Not (B p) -> B (not p)
      Not e -> Not (eval1 e)
      And (B p) (B q) -> B (p && q)
      And (B p) e -> let e' = eval1 e in And (B p) e'
      And e1 e2 -> let e1' = eval1 e1 in And e1' e2
      Or (B p) (B q) -> B (p || q)
      Or (B p) e -> let e' = eval1 e in Or (B p) e'
      Or e1 e2 -> let e1' = eval1 e1 in Or e1' e2
      Lt (I n) (I m) -> B (n < m)
      Lt (I n) e -> let e' = eval1 e in Lt (I n) e'
      Lt e1 e2 -> let e1' = eval1 e1 in Lt e1' e2
      Gt (I n) (I m) -> B (n > m)
      Gt (I n) e -> let e' = eval1 e in Gt (I n) e'
      Gt e1 e2 -> let e1' = eval1 e1 in Gt e1' e2
      Eq (I n) (I m) -> B (n == m)
      Eq (I n) e -> let e' = eval1 e in Eq (I n) e'
      Eq e1 e2 -> let e1' = eval1 e1 in Eq e1' e2
      If (B q) e1 e2 -> if q then e1 else e2
      If e1 e2 e3 -> If (eval1 e1) e2 e3
      Let i (I n) e2 -> subst e2 (i, (I n))
      Let i (B p) e2 -> subst e2 (i, (B p))
      Let i e1 e2 -> Let i (eval1 e1) e2

  evals :: Expr -> Expr
  evals expr =
    case expr of
      I n -> I n
      B p -> B p
      e -> evals (eval1 e)

  evale :: Expr -> Expr
  evale ex = 
    case evals ex of
      I n -> I n
      B p -> B p
      _ -> error "Evaluation failed"

  vt :: Ctx -> Expr -> Type -> Bool
  vt ctx (V i) t = searchDecl ctx i t
  vt ctx (If e1 e2 e3) t = (vt ctx e1 Boolean) && (vt ctx e1 t) && (vt ctx e1 t)
  vt ctx (Let i e1 e2) t =
      if (vt ctx e1 Integer)
        then vt ((i, Integer):ctx) e2 t
        else vt ((i, Boolean):ctx) e2 t
  vt ctx e t =
    case t of
      Integer -> case e of
        I n -> True
        Add e1 e2 -> (vt ctx e1 t) && (vt ctx e2 t)
        Mul e1 e2 -> (vt ctx e1 t) && (vt ctx e2 t)
        Succ e -> vt ctx e t
        Pred e -> vt ctx e t
        _ -> False
      Boolean -> case e of
        B p -> True
        Not e -> vt ctx e t
        And e1 e2 -> (vt ctx e1 t) && (vt ctx e2 t)
        Or e1 e2 -> (vt ctx e1 t) && (vt ctx e2 t)
        Lt e1 e2 -> (vt ctx e1 Integer) && (vt ctx e2 Integer)
        Gt e1 e2 -> (vt ctx e1 Integer) && (vt ctx e2 Integer)
        Eq e1 e2 -> (vt ctx e1 Integer) && (vt ctx e2 Integer)
        _ -> False

  searchDecl :: Ctx -> Identifier -> Type -> Bool
  searchDecl [] _ _  = False
  searchDecl ((i', t'):xs) i t =
    if i == i'
      then t == t'
      else searchDecl xs i t

  eval :: Expr -> Type -> Expr
  eval e t =
    if vt [] e t
      then evals e
      else error "incorrect type"
