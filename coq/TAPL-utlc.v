
Require Import String. 
Require Import List. 

(* 
Inductive var : Set := 
| mv : nat -> var
| mnv : string -> nat -> var.
*) 
Definition var := nat.

Inductive term : Set :=
| tvar : var -> term
| lam : term -> term 
| appl : term -> term -> term.

Notation "# n" := (tvar n) (at level 1).

Require Import Coq.Arith.Compare_dec.

Definition raise (c : nat) (k : nat) (n : nat) := 
  if le_lt_dec c n then k+n else n.

Definition raise_var (c : nat) (k : nat) (v : var) : var := 
  raise c k v.

(* 
Definition raise_var (c : nat) (k :nat) (v : var) : var := 
  match v with 
    | mv n => mv (raise c k n)
    | mnv s n => mnv s (raise c k n) 
  end.
*) 

Fixpoint lift_aux (c : nat) (k : nat) (t : term) {struct t} : term := 
  match t with 
    | tvar v => tvar (raise_var c k v) 
    | lam t => lam (lift_aux (S c) k t)
    | appl t t' => appl (lift_aux c k t) (lift_aux c k t')
  end.

Definition lift (k : nat) (t : term) : term := lift_aux 0 k t.

(* performs index lowering, and substitution *) 
Definition subst_var (v : var) (k : nat) (N : term) : term := 
  match lt_eq_lt_dec k v with 
    | inleft (left _) => tvar (pred v) (* k<v *) 
    | inleft _        => lift k N      (* k=v *)
    | inright _       => tvar v        (* v<k *) 
  end.

Fixpoint subst_aux (M : term) (N : term) (k : nat) {struct M} : term := 
  match M with
    | tvar v => subst_var v k N
    | lam t => subst_aux t N (S k)
    | appl t t' => appl (subst_aux t N k) (subst_aux t' N k)
  end. 

Definition subst (M : term) (N : term) := subst_aux M N 0.

Inductive R : term -> term -> Set := 
| betaR : forall M N, R (appl (lam M) N) (subst N M) 
| applR_r : forall M M' N, R M M' -> R (appl M N) (appl M' N). 

Inductive Rstar : term -> term -> Set := 
| refl_Rstar : forall M, Rstar M M
| onestep_Rstar : forall M N, R M N -> Rstar M N
| trans_Rstar : forall M N O, Rstar M N -> R N O -> Rstar M O.

Definition Om := (appl (lam (appl #0 #0))(lam (appl #0 #0))). 

Lemma reducable : R Om Om.
Proof. 
  firstorder.  unfold Om. apply betaR.  