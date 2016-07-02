Require Import Lang.

Require Import ListSet.

Definition raise (e : set nat) : (set nat) := set_map eq_nat_dec S e.

Definition singleton (e : nat) := set_add eq_nat_dec e (empty_set nat).

Fixpoint expand' (n : nat) (s : set nat) : set nat := 
  match n with
    | O => s
    | S n => expand' n (set_add eq_nat_dec n s)
  end.

Definition expand (n : nat) := expand' n (empty_set nat).

Fixpoint lower (lst : set nat) := 
  match lst with 
    | nil => nil 
    | (cons a lst') => 
      match a with
        | 0 => lower lst'
        | S n' => cons n' (lower lst')
      end
    end.

Fixpoint positive (ctx : nat) (ty : Ty) : set nat := 
   match ty with 
     | TV n => singleton n
     | Imp tya tyb => set_inter eq_nat_dec (negative ctx tya) (positive ctx tyb)
     | All tya => lower (positive ctx tya) 
   end
with negative (ctx : nat) (ty : Ty) : set nat := 
   match ty with 
     | TV n => (set_remove eq_nat_dec n (expand ctx))
     | Imp tya tyb => set_inter eq_nat_dec (positive ctx tya) (negative ctx tyb)
     | All tya => lower (negative ctx tya) 
   end.


(* Pos ty n, type is positive wrt free var n *)
Inductive Pos : nat -> Ty := 
| pos_tv : forall n m,  Pos (TV n) m (singleton n) (set_remove eq_nat_dec n (expand m))
| pos_imp : forall m tyA tyB positiveA positiveB negativeA negativeB, 
  Pos tyA m positiveA negativeA -> 
  Pos tyB m positiveB negativeB -> 
  Pos (Imp tyA tyB) m
  (set_inter eq_nat_dec negativeA positiveB) 
  (set_inter eq_nat_dec positiveA negativeB) 
| pos_all : forall m ty positive negative, 
  Pos ty (S m) (raise positive) (raise negative) -> 
  Pos (All ty) m positive negative.

Definition Nat := (All (Imp (Imp (Imp (TV 0) (TV 0)) (TV 0)) (TV 0))).

Theorem NatOK : exists pos, exists neg, Pos Nat 0 pos neg.
Proof.
  
