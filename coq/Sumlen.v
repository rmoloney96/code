
CoInductive Nat : Type := 
| Zero : Nat
| Succ : Nat -> Nat.
 
CoFixpoint plus (x : Nat) (y : Nat) : Nat := 
  match x with 
    | Zero => y 
    | Succ x' => Succ (plus x' y)
  end.

Require Import List. 

CoFixpoint sumlen (xs : list Nat) : Nat := 
  match xs with
    | nil => Zero
    | cons x xs' => Succ (plus x (Succ (sumlen xs')))
  end. 


(* 
CoFixpoint sumlen (xs : list Nat) : Nat := 
  match xs with
    | nil => Zero
    | cons x xs' => Succ(plus x (sumlen xs')) 
  end. 

(* Supercompiled *) 
CoFixpoint sumlen (xs : list Nat) : Nat := 
  match xs with
    | cons x' xs' => 
      Succ
      ((cofix f (x' : Nat) (xs' : list Nat) : Nat:=
        match x' with
          | Succ x' => Succ(f x' xs')
          | Zero => sumlen xs'
        end) x' xs')
    | nil => Zero
  end.

Inductive D : Set := 
d : ((nat -> nat) -> D) -> D.*) 
