Require Import Arith.
Require Import List.
Require Import ListSet.

Inductive Ty : Set := 
| Bas : nat -> Ty
| Arr : Ty -> Ty -> Ty.
Notation "T ⇒ S" := (Arr T S) (at level 30, right associativity).

Inductive Term : Set := 
| v : nat -> Term 
| ƛ : Ty -> Term -> Term
| app : Term -> Term -> Term.
Notation "t · s" := (app t s) (at level 20, left associativity).

Fixpoint Free (n : nat) (A : Set) : Set := 
  match n with 
    | O => A
    | S n' => Term -> Free n' A
  end.

Notation "[]" := nil.
Notation "[ x ]" := (cons x nil).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) .. ).

Fixpoint idx (A : Set) (n : nat) (G : list A) : option A := 
  match G with 
    | [] => None
    | (x::t) => match n with 
                  | O => Some x 
                  | S n' => idx A n' t
                end
  end.
Implicit Arguments idx [A].

Definition Ctx := list Ty.

(* Note : is \colon, using TeX mode, and not : *)
Reserved Notation "Γ ⊢ t @ A" (at level 70, no associativity).
Inductive Derivation : Ctx -> Term -> Ty -> Set := 
| VarIntro : forall Γ n A, 
  idx n Γ = Some A -> 
  Γ ⊢ (v n) @ A
| ImpIntro : forall Γ t A B,
  A::Γ ⊢ t @ B ->
  Γ ⊢ ƛ A t @ A ⇒ B
| ImpElim : forall Γ f t A B, 
  Γ ⊢ f @ A ⇒ B -> 
  Γ ⊢ t @ A -> 
  Γ ⊢ f · t @ B
 where "Γ ⊢ r @ A " := (Derivation Γ r A) : type_scope.

Hint Constructors Derivation : derivation.

Fixpoint shiftat (d : nat) (x : Term) {struct x} : Term := 
  match x with
    | v m => if le_lt_dec d m then v (S m) else v m
    | ƛ A t => ƛ A (shiftat (S d) t)
    | r · s => (shiftat d r) · (shiftat d s)
  end.
Definition shift := shiftat 0.

Definition sub : forall (t : Term) (n : nat) (u : Term), Term.
Proof.
  refine 
    (fix sub (t : Term) (n : nat) (u : Term) := 
      match t with 
        | v m => match le_lt_dec n m with 
                   | left p => 
                     match eq_nat_dec n m with 
                       | left _ => u 
                       | right p' => 
                         (match m as m' return (m = m' -> Term) with
                            | 0 => (fun p'' => False_rec _ _ )
                            | S m' => (fun _ => v m')
                          end) (refl_equal m)
                     end
                   | right _ => v m
                 end
        | ƛ A t => ƛ A (sub t (S n) (shift u))
        | r · s => (sub r n u) · (sub s n u)
      end) ; subst ; auto. 
  destruct n. apply le_n_O_eq in p. apply p'. reflexivity.
  inversion p.
Defined.

Inductive Ev : Term -> Term -> Prop := 
| ev_app : forall r s t, Ev r s -> Ev (r · t) (s · t)
| ev_beta : forall r s A, Ev ((ƛ A r) · s) (sub r 0 s).

Inductive Value : Term -> Prop := 
| Value_lam : forall A r, Value (ƛ A r).

Require Import Relations.

Notation "r ↝ s" := (Ev r s) (at level 40, no associativity).
Definition Evplus := clos_trans Term Ev.
Notation "r ↝⁺ s" := (Evplus r s) (at level 40, no associativity). 
Definition Evstar := clos_refl_trans Term Ev.
Notation "r ↝* s" := (Evstar r s) (at level 40, no associativity). 
Notation "r ⇓ s" := (r ↝* s /\ Value s) (at level 40, no associativity). 
Notation "t ⇓" := (exists s, t ⇓ s) (at level 40, no associativity). 
