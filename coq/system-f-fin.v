
Require Import Arith.
Require Import List. 

(*
Require Import Peano.
Require Import Peano_dec.
*) 

Inductive Ty : nat -> Set := 
| TV : forall n, Ty (S n)
| Imp : forall n, Ty n -> Ty n -> Ty n
| All : forall n, Ty (S n) -> Ty n
| TW : forall n, Ty n -> Ty (S n).

Implicit Arguments TW [n]. 
Implicit Arguments Imp [n].
Implicit Arguments All [n].

Inductive Term : Set := 
| V : nat -> Term 
| App : Term -> Term -> Term 
| TApp : forall n, Term -> Ty n -> Term
| Abs : forall n, Ty n -> Term -> Term
| Lam : Term -> Term.

Implicit Arguments TApp [n]. 
Implicit Arguments Abs [n].

Inductive Holds : Set := 
| H : forall n, list (Ty n) -> Term -> Ty n -> Holds. 

Notation "n ; l |= t @ ty" := (H n l t ty) (at level 60).
Open Scope list_scope.

Definition tyshift : forall i (ty : Ty i) (d : nat), Ty (S i).
Proof. 
  refine 
    (fix tyshift (i : nat) (ty : Ty i) (d : nat) {struct ty} : Ty (S i) := 
      (match ty in Ty i' return (i=i' -> Ty (S i)) with  
         | TV m => 
           (fun p => 
             if le_lt_dec d m 
               then _
               else _)
         | Imp i' t s => (fun t' s' p => _) (tyshift i' t d) (tyshift i' s d)
         | All i' t => (fun t' p => All _) (tyshift (S i') t (d+1))
         | TW i' t => (fun t' p => TW _) (tyshift i' t d)
       end) (refl_equal i)).
  (* d <= m *)
  rewrite p. exact (TV (S m)).
  (* d > m *)
  rewrite p. exact (TW (TV m)).
  (* Imp *)
  rewrite p. exact (Imp t' s').
  (* All *)
  rewrite p. exact t'.
  (* TW *)
  rewrite p. exact t'. 
Defined.
  
Print tyshift.

Eval compute in (tyshift.

(*
Fixpoint tyshift (i : nat) (ty : Ty i) (d : nat) {struct ty} : Ty (S i):= 
  match ty with 
    | TV m => if le_lt_dec d m then TV (m+1) else TV m
    | Imp t s => Imp (tyshift t d) (tyshift s d) 
    | All t => All (tyshift t (d+1)) 
  end.
  *) 

Fixpoint tysub (ty : Ty) (d : nat) (n : nat) (s : Ty) {struct ty} : Ty := 
  match ty with 
    | TV m => 
      if eq_nat_dec n m
        then s
        else if le_lt_dec d m 
          then TV m
          else TV (m+1) 
    | Imp ty1 ty2 => Imp (tysub ty1 d n s) (tysub ty2 d n s) 
    | All t => All (tysub t (d+1) (n+1) (tyshift s d))
  end.

Fixpoint tysubt (t : Term) (d : nat) (n : nat) (s : Ty) {struct t} : Term := 
  match t with 
    | V m => V m
    | Abs ty t => Abs (tysub ty d n s) (tysubt t d n s)
    | Lam t => Lam (tysubt t (d+1) n s)
    | App f g => App (tysubt f d n s) (tysubt g d n s)
    | TApp f ty => TApp (tysubt f d n s) (tysub ty d n s)
  end.

Inductive Derivation : Holds -> Set := 
| ImpIntro : forall n l t ty xty,
  Derivation (n  ; l |= t @ ty) -> 
  Derivation (n ; xty::l |= (Abs xty t) @ (Imp xty ty))
| ImpElim : forall n l t f ty xty,
  Derivation (n ; l |= t @ xty) ->
  Derivation (n ; l |= f @ (Imp xty ty)) -> 
  Derivation (n ; l |= (App f t) @ ty)
| AllIntro : forall n l t ty,
  Derivation (S n ; l |= t @ ty) -> 
  Derivation (n ; l |= (Lam t) @ All ty)
| AllElim : forall n l t ty tyx,
  Derivation (n ; l |= (TApp t tyx) @ ty) -> 
  Derivation (S n ; l |= t @ (tysub ty n n tyx))
| VarIntro : forall n l ty,
  Derivation (n ; ty::l |= V (length l) @ ty)
| Weaken : forall n l t ty,
  Derivation (n ; l |= t @ ty) -> 
  Derivation (


Definition Zero := (All (TV 0)).
Definition One := (Imp Zero Zero).

Definition check : forall n l t ty, option (Derivation (n ; l |= t @ ty)).
Proof. 
  induction t.  



