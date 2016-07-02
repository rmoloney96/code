
CoInductive CoNat : Set := 
| Zero : CoNat
| Succ : CoNat -> CoNat.

CoInductive CoEq : CoNat -> CoNat -> Prop := 
| coeq_base : CoEq Zero Zero
| coeq_next : forall x y, CoEq x y -> CoEq (Succ x) (Succ y).

(* assists with deconstruction in proofs *)
Definition decomp (x : CoNat) : CoNat := 
  match x with 
    | Zero => Zero
    | Succ x' => Succ x'
  end.

Lemma decomp_eql : forall x, x = decomp x.
  intro x. case x. simpl. auto.
  intros. simpl. auto.
Defined.    

CoFixpoint plus (x: CoNat) (y: CoNat) : CoNat := 
  match x with 
    | Zero => y 
    | Succ x' => Succ (plus x' y)
  end.

Require Import List. 
Fixpoint sum (xs:list CoNat) : CoNat := 
  match xs with 
    | nil => Zero
    | cons x xs' => plus x (sum xs')
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

CoFixpoint f (x : CoNat) (xs : CoList) := 
  match x with 
    | Zero => match xs with 
                | CoNil => Zero
                | CoCons x' xs' => Succ (f x' xs')
              end
    | Succ x' => Succ (f x' xs)
  end.

Definition sum (xs : List) := 
  match xs with
    | CoNil => Zero 
    | CoCons x' xs' => Succ (f x' xs')
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

