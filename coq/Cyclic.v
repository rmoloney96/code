
Require Import List.

Inductive Ty : Set := 
| Bool : Ty
| Stream : Ty
| Nat : Ty
| Arr : Ty -> Ty -> Ty.

Notation "T ==> S" := (Arr T S) (at level 30, right associativity).

Inductive Term : Set :=
| v : nat -> Term 
| f : nat -> Term 
| succ : Term -> Term
| zero : Term 
| natcase : Term -> Term -> Term -> Term
| snil : Term
| scons : Term -> Term -> Term  
| streamcase : Term -> Term -> Term -> Term
| true : Term 
| false : Term
| boolcase : Term -> Term  -> Term -> Term
| lam : Ty -> Term -> Term
| app : Term -> Term -> Term.

Definition Ctx := list Ty.

Inductive Holds (G : Ctx) (t : Term) (ty : Ty) : Set := 
| holds : Holds G t ty. 

Notation "G |= t @ ty" := (Holds G t ty) (at level 40, no associativity).

Check forall G t ty P, P (G |= t @ ty).

Variable Delta : nat -> Term.

CoInductive Deduction : Set -> Set := 
| ImpElim : forall G A B r s, 
  Deduction ( G |= r @ A ==> B) -> Deduction ( G |= s @ A ) -> 
  Deduction ( G |= app r s @ B )
| ImpIntro : forall G A B r, Deduction ( (A::G) |=  r @ B) -> 
  Deduction ( G |= lam A r @ A ==> B ) 
| BoolIntroTrue : forall G, Deduction ( G |= true @ Bool )
| BoolIntroFalse : forall G, Deduction ( G |= false @ Bool )
| BoolElim : forall G C r s t,  
  Deduction ( G |= r @ Bool ) -> Deduction ( G |= s @ C ) -> Deduction ( G |= t @ C  ) ->
  Deduction ( G |= boolcase r s t @ C)
| NatIntroS : forall G r, Deduction ( G |= r @ Nat ) -> Deduction ( G |= succ r @ Nat ) 
| NatIntroZ : forall G, Deduction ( G |= zero @ Nat )
| NatElim : forall G C r s t, 
  Deduction ( G |= r @ Nat ) -> Deduction ( G |= s @ C ) -> Deduction ( (Nat::G) |= t @ C ) -> 
  Deduction ( G |= natcase r s t @ C)
| StreamIntroNil : forall G,  Deduction ( G |= snil @ Stream ) 
| StreamIntroCons : forall G n s, ( G |= n @ Nat ) -> Deduction ( G |= s @ Stream ) -> Deduction ( G |= scons n s @ Stream )
| StreamElim : forall G C r s t, 
  Deduction ( G |= r @ Stream ) -> Deduction ( G |= s @ C ) -> Deduction ( (Nat::G) |= t @ C ) -> 
  Deduction ( G |= natcase r s t @ C)
| DeltaRule : forall G C r s t, Deduction (G |= s @ C ) -> Deduction (G |= s @ C).
