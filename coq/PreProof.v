Require Import Arith.
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

Fixpoint shiftn (n : nat) (d : nat) (x : Term) {struct x} : Term := 
  match x with
    | v m => if le_lt_dec d m then v (n+m) else v m
    | f m => f m
    | succ t => succ (shiftn n d t)
    | zero => zero
    | natcase r s t => natcase (shiftn n d r) (shiftn n d r) (shiftn n (S d) t)
    | snil => snil
    | scons h t => scons (shiftn n d h) (shiftn n d t)
    | streamcase r s t => streamcase (shiftn n d r) (shiftn n d s) (shiftn n (S (S d)) t)
    | true => true
    | false => false
    | boolcase r s t => boolcase (shiftn n d r) (shiftn n d s) (shiftn n d t)
    | lam ty t => lam ty (shiftn n (S d) t)
    | app r s => app (shiftn n d r) (shiftn n d s)
  end.

Definition shift := shiftn 1 0.

Definition sub : forall (t : Term) (n : nat) (u : Term), Term.
Proof. 
  refine 
    (fix sub (t : Term) (n : nat) (u : Term) :=
      match t with
        | v m => match le_lt_dec n m with 
                   | left p => match eq_nat_dec n m with
                                 | left _ => u 
                                 | right p' => 
                                   (match m as m' return (m = m' -> Term) with 
                                      | 0 => (fun p'' => False_rec _ _)
                                      | S m' => (fun _ => v m')
                                    end) (refl_equal m)
                               end
                   | right _ => v m
                 end
        | f m => f m
        | succ t => succ (sub t n u)
        | zero => zero
        | natcase r s t => natcase (sub r n u) (sub s n u) (sub t (S n) (shift u))
        | snil => snil
        | scons h t => scons (sub h n u) (sub t n u)
        | streamcase r s t => streamcase (sub r n u) (sub s n u) (sub t (S (S n)) (shiftn 2 0 u))
        | true => true
        | false => false
        | boolcase r s t => boolcase (sub r n u) (sub s n u) (sub t n u)
        | lam ty t => lam ty (sub t n (shift u))
        | app r s => app (sub r n u) (sub s n u)
      end).
  destruct m. apply le_n_O_eq in p. apply p'. auto. inversion p''.
Defined.

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

Variable Delta : nat -> Term.

Fixpoint idx (n : nat) (G : Ctx) : option Ty := 
  match G with 
    | [] => None
    | (x::t) => match n with 
                  | O => Some x 
                  | S n' => idx n' t
                end
  end.

CoInductive Preproof : list Set -> Set -> Set := 
| VarIntro : forall G n ty, 
  idx n G = Some ty -> Preproof [] (G |= v n @ ty)
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
| StreamIntroNil : forall G,  Preproof [] ( G |= snil @ Stream ) 
| StreamIntroCons : forall G n s, Preproof [ ( G |= n @ Nat ) ; (G |= s @ Stream) ] (G |= scons n s @ Stream) 
| StreamElim : forall G C r s t, 
  Preproof [( G |= r @ Stream ) ; ( G |= s @ C ) ; ( (Nat::G) |= t @ C )] ( G |= natcase r s t @ C)
| Unfold : forall G C n,
  Preproof [G |= f n @ C] (G |= Delta n @ C). 

Inductive Child : Set -> Set -> Type := 
| ChildStep : forall F G c d, Preproof (F++c::G) d -> Child c d
| ChildJump : forall F G c d e, Preproof (F++c::G) d -> Child d e ->  Child c e.

Inductive FinitePreproof : list Set -> Set -> Type := 
| FPCopy : forall h c, Preproof h c -> FinitePreproof h c
| FPRepeat : forall c, Child c c -> FinitePreproof [] c.

Inductive HasProof : Set -> Type := 
| HasProof_witness : forall G l t A, FinitePreproof l ( G |= t @ A ) -> HasProof ( G |= t @ A ).

Fixpoint typecheck : forall G A memo (t : Term) -> option (Preproof (G |= t @ A)) :=
  match t with 
    | v n => (match idx n G as mty return (idx n G = mty -> option (Preproof (G |= t @ A))) with 
                | None => (fun _ => None)
                | Some ty => (fun mty => VarIntro G n ty mty)
              end) (refl (idx n G))
    | f m => match idx n memo with 
               
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

Inductive EvalHNF : Set -> Set -> Set := 
| Eval_app : forall t s, Eval (app (lam t) s) ( 

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




