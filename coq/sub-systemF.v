(* Encoding of Types *)
Definition Zero := forall (a : Prop), a.
Notation "'0" := Zero (at level 1).

Lemma Zero_uninhabited : forall t : '0, False.
  intros. 
  unfold Zero in t. apply t.
Defined. 

Definition One := forall (a : Prop), a -> a.
Notation "'1" := One (at level 1).
Definition unit : '1 := (fun (a : Prop) (x : a) => x).
Implicit Arguments unit [a].
Notation "'()" := unit (at level 1).

Definition And (a : Prop) (b : Prop) := forall (z : Prop), 
(* pair *) (a -> b -> z) -> 
z.
Notation "a |*| b" := (And a b) (at level 90, b at next level).

Definition pair : forall (a b : Prop), a -> b -> And a b :=
    fun (a b : Prop) => 
      fun (x : a) (y : b) => 
        fun (z : Prop) (f : a -> b -> z) => f x y.
Implicit Arguments pair [a b].
Notation "[ x , y ]" := (pair x y) (at level 1, y at next level).

Definition fst : forall (a b : Prop), a |*| b -> a :=
  fun (a b : Prop) => 
    fun (p : forall (z : Prop), (a -> b -> z) -> z) => 
      p a (fun (x : a) (y : b) => x).
Implicit Arguments fst [a b].

Definition snd : forall (a b : Prop), a |*| b -> b :=
  fun (a b : Prop) => 
    fun (p : forall (z : Prop), (a -> b -> z) -> z) => 
      p b (fun (x : a) (y : b) => y).
Implicit Arguments snd [a b]. 

Definition Or (a : Prop) (b : Prop) := forall (z : Prop), 
(* inl *) (a -> z) -> 
(* inr *) (b -> z) -> 
z.
Notation "a |+| b" := (Or a b) (at level 90, b at next level).

Definition inl : forall (a b : Prop), a -> a |+| b :=
    fun (a b : Prop) => 
      fun (x : a) => 
        fun (z : Prop) (left : a -> z) (right : b -> z) => left x.
Implicit Arguments inl [a].
Definition inr : forall (a b : Prop), b -> a |+| b :=
    fun (a b : Prop) => 
      fun (y : b) => 
        fun (z : Prop) (left : a -> z) (right : b -> z) => right y.
Implicit Arguments inr [b].

Definition Nat := forall n : Prop, 
(* z *) n -> 
(* s *) (n -> n) -> 
n.
Definition z : Nat := fun (n : Prop) (z : n) (s : n -> n) => z.
Definition s : Nat -> Nat := 
  fun (m : Nat) => 
    fun (n : Prop) (z : n) (s : n -> n) => s (m n z s).

Definition Bool := forall (n : Prop), 
(* true  *) n -> 
(* false *) n -> 
n.
Definition true : Bool := fun (b : Prop) (t : b) (f : b) => t.
Definition false : Bool := fun (b : Prop) (t : b) (f : b) => f.
Definition andb : Bool -> Bool -> Bool := 
  fun (x : Bool) (y : Bool) => 
    x Bool y false.
Definition orb : Bool -> Bool -> Bool := 
  fun (x : Bool) (y : Bool) => 
    x Bool true y.

Definition List (A : Prop) := forall (X : Prop), X -> (A -> X -> X) -> X.
Definition nil := fun (A : Prop) (X : Prop) (n : X) (c : A -> X -> X) => n.
Definition cons := fun (A : Prop) (a : A) (l : List A) => 
  fun (X : Prop) (n : X) (c : A -> X -> X) => c a (l X n c).
Implicit Arguments cons [A].

Definition iszero : Nat -> Bool := 
  fun (n : Nat) =>
    n Bool true (fun _ => false).

Definition plus : Nat -> Nat -> Nat := 
  fun (n m: Nat) => 
    n Nat m s.

Definition aux : Nat -> (Nat |*| Nat) :=
  fun (n : Nat) =>
    n (Nat |*| Nat) 
    [z,z]
    (fun p : Nat |*| Nat =>
      [s (fst p),fst p]).

Definition pred : Nat -> Nat := 
  fun (n : Nat) => snd (aux n).

Definition monus : Nat -> Nat -> Nat := 
  fun (n m : Nat) => m Nat n pred. 

Definition eqn : Nat -> Nat -> Bool :=
  fun (n m: Nat) =>
    andb (iszero (monus n m)) (iszero (monus m n)).

Definition le : Nat -> Nat -> Bool :=
  fun (n m : Nat) => iszero (monus n m).

Definition Lambda := forall (X : Prop),
(* var *) (Nat -> X) -> 
(* app *) (X -> X -> X) -> 
(* abs *) (X -> X) -> 
X.
Definition var : Nat -> Lambda:= 
  fun (n : Nat) => 
    fun (X : Prop) (var : Nat -> X) (app : X -> X -> X) (abs : X -> X) => 
      var n.
Definition app : Lambda -> Lambda -> Lambda := 
  fun (x y : Lambda) => 
    fun (X : Prop) (var : Nat -> X) (app : X -> X -> X) (abs : X -> X) => 
      app (x X var app abs) (y X var app abs).
Definition abs : Lambda -> Lambda :=
  fun (x : Lambda) => 
    fun (X : Prop) (var : Nat -> X) (app : X -> X -> X) (abs : X -> X) => 
      abs (x X var app abs).

Definition shift_below : Nat -> Lambda -> Lambda.
Proof. 
  refine 
    (fun (c : Nat) (l : Lambda) => 
      l (Nat |*| Lambda)
      (fun (n : Nat) => (*if *)(le c n)
                        (*then*)(var (s n)) 
var (s n))
      (fun (f : Lambda) (g : Lambda) => app f g)
      (fun (t : Lambda) => abs t)).

Definition shift (abs (var z)).
  

Definition sub : Lambda -> 