
(* Experiment with Church *)
Definition Nat := forall n : Prop, n -> (n -> n) -> n.
Definition z : Nat := fun (n : Prop) (z : n) (s : n -> n) => z.
Definition s : Nat -> Nat := 
  fun (m : Nat) => 
    fun (n : Prop) (z : n) (s : n -> n) => s (m n z s).

(* Encoding of Types *)
Definition Zero := forall (a : Prop), a.
Notation "'0" := Zero (at level 1).

Definition One := forall (a : Prop), a -> a.
Notation "'1" := One (at level 1).
Definition unit : '1 := (fun (a : Prop) (x : a) => x).
Notation "'()" := unit (at level 1).

Definition And (a : Prop) (b : Prop) := forall (z : Prop), (a -> b -> z) -> z.
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

Definition snd : forall (a b : Prop), a |*| b -> a :=
  fun (a b : Prop) => 
    fun (p : forall (z : Prop), (a -> b -> z) -> z) => 
      p a (fun (x : a) (y : b) => x).
Implicit Arguments snd [a b]. 

Definition Or (a : Prop) (b : Prop) := forall (z : Prop), (a -> z) -> (b -> z) -> z.
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

Definition ex (a : Prop -> Prop) := forall y: Prop, (forall x : Prop, a x -> y) -> y.

Definition pack (a : Prop -> Prop) : forall (x : Prop), a x -> ex a := 
  fun (x : Prop) =>
    fun (e : a x) =>
      fun (y: Prop) =>
        fun (f : forall (z : Prop), a z -> y) => f x e.

Definition unpack (a : Prop -> Prop) 
  : ex a -> forall (y : Prop), (forall (x : Prop), a x -> y) -> y := 
    fun (u : ex a) (y : Prop) (f : forall (x : Prop), a x -> y) => 
      u y f.

Definition phi (a : Prop -> Prop) := (fun (x : Prop) => (x -> a x) |*| x).
Definition nu (a : Prop -> Prop) := ex (fun (x : Prop) => (x -> a x) |*| x).
Definition unfold (a : Prop -> Prop) 
  : forall (x : Prop), (x -> a x) -> (x -> nu (fun x => a x)) := 
    fun (x : Prop) => 
      fun (f : x -> a x) => 
        fun (e : x) => 
          pack (fun x => (x -> a x) |*| x) x [f,e].

Definition out (a : Prop -> Prop) : nu (fun z => a z) -> a (nu (fun z => a z)) :=
  fun (u : nu (fun z => a z)) => 
    unpack (fun x => (x -> a x) |*| x) u (a (nu (fun z => a z))) 
      (fun x (w : (x -> a x) |*| x) => 
        (a (unfold x (fst w))) ((fst w) (snd w))).
         

Definition Conat := nu (fun N => '1 |+| N).

Definition cz : Conat.
Proof. 
  unfold Conat. unfold nu. unfold ex. intros.
  apply (H '1).
  intros. exact '().
Defined.

Definition cs : Conat -> Conat.
Proof.
  unfold Conat. unfold nu. unfold ex.
  intros.
  pack 

  intros. unfold Conat in H. unfold nu in H. unfold ex in H.
  unfold Conat. unfold nu. unfold ex.
  intros. apply (H0 Conat).
  intros. apply H1. exact.

Definition cs : nu (fun N => 

Definition Stream := nu (fun S => Nat |*| S).


forall x : Prop, (forall s : Prop, ((s -> Nat * s) -> s) -> x) -> x.

Lemma Stream 