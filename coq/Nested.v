
Inductive Maybe : Set -> Set := 
| None : forall A, Maybe A
| Just : forall A, A -> Maybe A. 

Inductive Ty : Set := 
| Arr : Ty -> Ty -> Ty.

Inductive Term : Set :=  
| v : nat -> Term 
| lam : Ty -> Term -> Term
| app : Term -> Term -> Term.

Fixpoint shiftat (d : nat) (x : Term) {struct x} : Term := 
  match x with
    | v m => if le_lt_dec d m then v (S m) else v m
    | lam ty t => lam ty (shiftat (S d) t)
    | app r s => app (shiftat d r) (shiftat d s)
  end.

Reserved Notation "G |= t @ ty [n]" (at level 40, no associativity).

Inductive Deriv : Ctx -> Term -> Ty -> Set -> Prop := 
| P : forall G t ty A, G |= t ty A
| Lam : forall A, Deriv G t ty A  
| App : forall A, Deriv A -> Deriv A -> Deriv A
where "G |= t @ ty [A]" := (Deriv G t ty A)