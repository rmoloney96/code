
Inductive Expr : Set -> Type := 
| In : forall B, (Expr B -> A) -> Expr A.

data Expr f = In (f (Expr f ))
