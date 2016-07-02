Require Import Monad.
Export Monad.

Definition bind_option (A : Type) (B : Type) (e : option A) (f : A -> option B) : option B :=
  match e with
    | None => None
    | Some a => (f a)
  end.

Definition ret_option (A : Type) := fun a : A => Some a.

Hint Unfold ret_option bind_option.

Program Instance Monad option := 
  ret := ret_option ;
  bind := bind_option.

  Next Obligation. (* bind left unit *)
  Proof.
    induction x ; auto.
  Qed.

  Next Obligation. (* bind right unit *) 
  Proof.
    induction x ; auto.
  Qed. 

