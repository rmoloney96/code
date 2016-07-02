
CoInductive CoNat : Set := 
| Zero : CoNat
| Succ : CoNat -> CoNat.

CoFixpoint plus (x: CoNat) (y: CoNat) : CoNat := 
  match x with 
    | Zero => y 
    | Succ x' => Succ (plus x' y)
  end.

CoInductive CoList : Set := 
| CoNil : CoList 
| CoCons : CoNat -> CoList -> CoList.

Definition decompl (xs : CoList) : CoList := 
  match xs with 
    | CoNil => CoNil
    | CoCons x' xs' => CoCons x' xs'
  end.

Lemma decompl_eql : forall x, x = decompl x.
  intro x. case x. simpl. auto.
  intros. simpl. auto.
Defined.    

(* 
CoFixpoint sumlen (xs: CoList) : CoNat := 
  match xs with 
    | CoNil => Zero 
    | CoCons x' xs' => Succ (plus x' (sumlen xs'))
  end.
*)

CoFixpoint f (x : CoNat) (xs : CoList) := 
  match x with 
    | Zero => match xs with 
                | CoNil => Zero
                | CoCons x' xs' => Succ (f x' xs')
              end
    | Succ x' => Succ (f x' xs)
  end.

Definition sumlen (xs : CoList) := 
  match xs with
    | CoNil => Zero 
    | CoCons x' xs' => Succ (f x' xs')
  end.

Require Import List.

Definition sum : list CoNat -> CoNat :=
  fix sum (xs : list CoNat) {struct xs} : CoNat :=
  match xs with
    | nil => Zero
    | cons Zero xs => sum xs
    | cons (Succ x) xs =>
      Succ 
      ((cofix f (n : CoNat) (xs : list CoNat) sum_xs : CoNat :=
          match n with
            | Zero => sum_xs
            | Succ x => Succ (f x xs sum_xs)
          end) x xs (sum xs))
  end.





Infix "::" := CoCons (at level 60, right associativity).

Lemma test : sumlen (Zero::Zero::(Succ((Succ(Zero))))::CoNil) = Succ(Succ(Succ(Zero))).
Proof.
  intros. rewrite (decomp_eql (sumlen (Zero :: Zero :: Succ (Succ Zero) ::CoNil))). simpl.
  rewrite (decomp_eql (f Zero (Zero :: Succ (Succ Zero) :: CoNil))). simpl.
  rewrite (decomp_eql (f Zero (Succ (Succ Zero) :: CoNil))). simpl.
  rewrite (decomp_eql (f (Succ (Succ Zero)) CoNil)). simpl.
  rewrite (decomp_eql (f (Succ Zero) CoNil)). simpl.
  rewrite (decomp_eql (f Zero CoNil)). simpl.


g = (% x'. (% xs'. (case x' of 
                      | Succ(x') => Succ(((g x') xs'))
                      | Zero => (f xs'))));

f = (% xs. (case xs of 
              | Cons(x',xs') => case x' of 
                                  | Zero => Succ(f xs')
                                  | Succ(x') => Succ(Succ(g x' xs'))
              | Nil => Zero));

