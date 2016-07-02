
Require Import List.

Inductive Ty : Set := 
| Nat : Ty
| Arr : Ty -> Ty -> Ty. 

Notation "T ==> S" := (Arr T S) (at level 30, right associativity).

Inductive Term : Set :=
| v : nat -> Term 
| f : nat -> Term 
| succ : Term -> Term
| zero : Term 
| natcase : Term -> Term -> Term -> Term
| lam : Ty -> Term -> Term
| app : Term -> Term -> Term.

Definition Ctx := list Ty.

Inductive Holds (G : Ctx) (t : Term) (ty : Ty) : Set := 
| holds : Holds G t ty. 

Notation "G |= t @ ty" := (Holds G t ty) (at level 40, no associativity).

Check forall G t ty P, P (G |= t @ ty).

Variable Delta : nat -> Term.

CoInductive PreProof

CoInductive Deduction : Set -> Set := 
| ImpElim : forall G A B r s, 
  Deduction ( G |= r @ A ==> B) -> Deduction ( G |= s @ A ) -> 
  Deduction ( G |= app r s @ B )
| ImpIntro : forall G A B r, Deduction ( (A::G) |=  r @ B) -> 
  Deduction ( G |= lam A r @ A ==> B ) 
| NatIntroS : forall G r, Deduction ( G |= r @ Nat ) -> Deduction ( G |= succ r @ Nat ) 
| NatIntroZ : forall G, Deduction ( G |= zero @ Nat )
| NatElim : forall G C r s t, 
  Deduction ( G |= r @ Nat ) -> Deduction ( G |= s @ C ) -> Deduction ( (Nat::G) |= t @ C ) -> 
  Deduction ( G |= natcase r s t @ C)
| DeltaRule : forall G C r s t, Deduction (G |= s @ C ) -> Deduction (G |= s @ C).
