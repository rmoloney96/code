

Inductive Ty : Type := 
| B : Ty
| N : Ty
| Imp : Ty -> Ty -> Ty.

Inductive Term : Type := 
| V : nat -> Term
| App : Term -> Term -> Term
| Lam : Term -> Term
| Rec : forall a, (a -> a) -> Term.
Implicit Arguments Rec [a].

Check Rec (fun a => (App a a)).
