
Require Import List. 
Open Scope list_scope.

Definition plus (plus : nat -> nat -> nat) (n : nat) (m : nat) := 
  match n with 
    | 0 => m 
    | S n' => S (plus n' m) 
  end.

Eval compute in 
  (fun (plus' : nat -> nat -> nat) => 
    plus (plus plus')).

Section vars.

Variable type : Type.
Variable TArrow : type -> type -> type. 

Variable var : type -> Type.
Variable TBool : type. 

Inductive term : type -> Type :=
| EVar : forall t, var t -> term t
| EApp : forall t1 t2, term (TArrow t1 t2) -> term t1 -> term t2
| EAbs : forall t1 t2, (var t1 -> term t2) -> term (TArrow t1 t2).

Theorem sub : forall v, term (term v) -> term v.

End vars.


Inductive term : type -> Type :=
| Var : forall t, var t -> term t
| App : forall t1 t2, term (TArrow t1 t2) -> term t1 -> term t2
| Abs : forall t1 t2, (var t1 -> term t2) -> term (TArrow t1 t2).

Implicit Arguments Var [t].
Implicit Arguments App [t1 t2]. 
Implicit Arguments Abs [t1 t2]. 

Definition id := Abs (fun x : Type => Var x).  

Definition Term1 := forall v, v -> term v.

Theorem sub : forall t, term (term t) -> term t.



Check term (



Inductive Ty t := 
| And Ty Ty
| All forall t : Type, Ty
| 

CoInductive Derivation : Type -> Type -> Type := 
| ImpIntro : Rule 
| 

CoInductive Equiv : Type -> Type -> Type := 
| Eq : forall t s, t = s -> Equiv t s
| Next : forall t s,  