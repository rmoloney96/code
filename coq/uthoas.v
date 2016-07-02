
Inductive Exp_ : Type -> Type :=
| Lam : forall A, (A -> Exp_ A) -> Exp_ A
| App : forall A, Exp_ A -> Exp_ A -> Exp_ A
| Var : forall A, A -> Exp_ A.
Implicit Arguments Lam [A]. 
Implicit Arguments App [A]. 
Implicit Arguments Var [A].
Definition Exp := forall a, Exp_ a.

Inductive Ev : forall A B, Exp_ A -> Exp_ B := 
| eval_beta : forall A B (f : A -> Exp_ A) (t : Exp_ A), 
  Ev A (Exp_ A) (App (Lam f) t) (f t).