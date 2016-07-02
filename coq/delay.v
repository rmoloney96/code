
CoInductive delay (A : Set) : Set := 
| Now : A -> delay A
| Later : delay A -> delay A.
Implicit Arguments Later [A].
Implicit Arguments Now [A].

CoFixpoint never (A : Set) : delay A := Later (never A).
Implicit Arguments never [A].

CoFixpoint minimFrom (p : nat -> bool) (n : nat) : delay nat := 
  match p n with 
    | true => Now n
    | false => Later (minimFrom p n)
  end.

Definition minim (p : nat -> bool) : delay nat := 
  minimFrom p 0.

CoFixpoint race (A : Set) (x : delay A) (y : delay A) : delay A := 
  match x,y with 
    | Now x', _ => Now x'
    | _, Now y' => Now y'
    | Later x', Later y' => Later (race A x' y')
  end.
Implicit Arguments race [A].

Require Import Streams.

CoFixpoint oneormore (A : Set) (x : delay A) (s : Stream (delay A)) : delay A := 
  match x with 
    | Now x' => Now x' 
    | Later x' => match s with 
                    | Cons y s' => Later (oneormore A (race x' y) s')
                  end
  end.
Implicit Arguments oneormore [A]. 

Definition omegarace (A : Set) (s : Stream (delay A)) : delay A := 
  match s with 
    | Cons x' s' => oneormore x' s'
  end.
Implicit Arguments omegarace [A].

CoFixpoint mapP (A : Set) (B : Set) (P : A -> B) (s : Stream A) : Stream B  := 
  match s with 
    | Cons x s' => Cons (P x) (mapP A B P s')
  end.
Implicit Arguments mapP.

Inductive Serpinsky : Set := 
| T : Serpinsky.

Definition Ex (A : Set) (s : Stream A) (p : A -> delay Serpinsky)  := omegarace (mapP p s).
Implicit Arguments Ex [A].

CoFixpoint fromN (n : nat) : Stream nat := Cons n (fromN (S n)).

CoFixpoint naturals : Stream nat := fromN O.

CoFixpoint even (n : nat) : delay Serpinsky := 
  match n with 
    | O => Now T
    | S n' => match n' with 
                | O => never
                | S n'' => Later (even n'')
              end
  end.

Require Import List.


Definition trans (n : nat) : list nat := (S n)::(S (S n))::nil. 

(* 
Definition diam (n : nat) (P : nat -> delay Serpinsky) := 
  omegarace (diam )
*)

Definition setence := Ex naturals (fun n => even n).



(* 





Looking at truth 

¬ Ex ¬ P

*)
