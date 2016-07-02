Inductive Fin : nat -> Set :=
| fzero : forall n, Fin (S n)
| fsucc : forall {n}, Fin n -> Fin (S n). 

Inductive L : nat -> Set :=
| var : forall {n}, Fin n -> L n
| lam : forall {n}, L (S n) -> L n
| app : forall {n}, L n -> L n -> L n.

Check (lam (lam (var (fsucc (fzero 0))))).
Check (lam (var (fzero 0))).

Require Import List.

Inductive Ty : Set := 
| Bool : Ty
| Stream : Ty
| Nat : Ty
| Arr : Ty -> Ty -> Ty.

Notation "T ==> S" := (Arr T S) (at level 30, right associativity).

Inductive Term : Set := 
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
| app : Term -> Term -> Term
| rec : Term -> Term.

Definition Ctx := list Ty.

Inductive Holds (G : Ctx) (t : Term) (ty : Ty) : Set := 
| holds : Holds G t ty. 

Notation "G |= t @ ty" := (Holds G t ty) (at level 40, no associativity).

Check forall G t ty P, P (G |= t @ ty).

Notation "[]" := nil.
Notation "[ x ]" := (cons x nil).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) .. ).
 
Open Scope list_scope.

(*  Inductive Chain : (S )  *)

Inductive Derivation : list Set -> 


CoInductive Preproof : list Set -> Set -> Set := 
| ImpElim : forall G A B r s, 
  Preproof [(G |= r @ A ==> B) ; (G |= s @ A) ] ( G |= app r s @ B )
| ImpIntro : forall G A B r, 
  Preproof [ (A::G) |= r @ B ] (G |= lam A r @ A ==> B)
| BoolIntroTrue : forall G, Preproof [] (G |= true @ Bool) 
| BoolIntroFalse : forall G, Preproof [] (G |= false @ Bool)
| BoolElim : forall G C r s t, 
  Preproof [( G |= r @ Bool ) ; ( G |= s @ C ) ; ( G |= t @ C ) ] (G |= boolcase r s t @ C)
| NatIntroZero : forall G, Preproof [] (G |= zero @ Nat) 
| NatIntroSucc : forall G r, Preproof [G |= r @ Nat] (G |= succ r @ Nat) 
| NatElim : forall G C r s t, 
  Preproof [( G |= r @ Nat ) ; (G |= s @ C) ; (G |= t @ C ) ] (G |= natcase r s t @ C)
| StreamIntroNil : forall G,  PreProof [] ( G |= snil @ Stream ) 
| StreamIntroCons : forall G n s, PreProof [ ( G |= n @ Nat ) ; (G |= s @ Stream) ] (G |= scons n s @ Stream) 
| StreamElim : forall G C r s t, [( G |= r @ Stream ) ; ( G |= s @ C ) ; ( (Nat::G) |= t @ C )] ( G |= natcase r s t @ C)
| Repeat : forall F G H C r s t sigma,
  Deduction [F++(sigma (G |= s @ C))::H] (G |= s @ C) -> Deduction [] (G |= s @ C).





