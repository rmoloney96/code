
(* Experiment with Church *)
(* 
Definition Nat := forall n : Prop, n -> (n -> n) -> n.
Definition z : Nat := fun (n : Prop) (z : n) (s : n -> n) => z.
Definition s : Nat -> Nat := 
  fun (m : Nat) => 
    fun (n : Prop) (z : n) (s : n -> n) => s (m n z s).
*) 

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

Definition snd : forall (a b : Prop), a |*| b -> b :=
  fun (a b : Prop) => 
    fun (p : forall (z : Prop), (a -> b -> z) -> z) => 
      p b (fun (x : a) (y : b) => y).
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

(* extraneous *)  
Definition case : forall (a b c: Prop), a |+| b -> (a -> c) -> (b -> c) -> c := 
  fun (a b c : Prop) => 
    fun (x : a |+| b) (f : a -> c) (g : b -> c) => 
      x c f g.

Lemma or_inl : forall (a b c : Prop) (f : a -> c) (g : b -> c) (x : a),  
  case a b c (inl b x) f g = f x.
Proof.
  unfold case.
  unfold inl. auto.
Defined.

Lemma or_inr : forall (a b c : Prop) (f : a -> c) (g : b -> c) (x : a),  
  case a b c (inl b x) f g = f x.
Proof.
  unfold case.
  unfold inl. auto.
Defined.

Definition bool := '1 |+| '1.
Definition true := inl '1 '().
Definition false := inr '1 '().

Definition natF := (fun x : Prop => x |+| '1).
Definition mu (F: Prop -> Prop) := all (fun (x : Prop) => (F x -> x) -> x).

Definition fold (F : Prop -> Prop) : forall (x : Prop), (F x -> x) -> mu F -> x.
  intros F x k t.
  apply (t x k).
Defined.

Definition inmu (F : Prop -> Prop) (FM : forall (a b : Prop), (a -> b) -> (F a -> F b))
  : F (mu F) -> mu F.
Proof. 
  intros F FM s.
  unfold mu. unfold all.
  intro x. intro k. 
  refine (k (FM (mu F) x (fold F x k) s)).
Defined.

Print inmu.
 
Definition inmu' (F : Prop -> Prop) (FM : forall (a b : Prop), (a -> b) -> (F a -> F b))
  : F (mu F) -> mu F.
Proof. 
  intros F FM s.
  unfold mu. unfold all.
  intro x. intro k. 
  refine (k (FM (mu F) x (fun t : mu F => t x k) s)).
Defined.
 
Definition outmu (F : Prop -> Prop) (FM : forall (a b : Prop), (a -> b) -> (F a -> F b))
  : mu F -> F (mu F).
Proof.
  intros F FM s.
  apply (fold F).
  apply FM. apply inmu. auto. auto.
Defined.

Print outmu.

Definition outmu' (F : Prop -> Prop) (FM : forall (a b : Prop), (a -> b) -> (F a -> F b))
  : mu F -> F (mu F).
Proof.
  intros F FM s.
  refine (s (F (mu F)) (FM (F (mu F)) (mu F) (inmu F FM))).
Defined.
Print outmu'.


Definition ex (F : Prop -> Prop) := forall y: Prop, (forall x : Prop, F x -> y) -> y.

Definition pack (F : Prop -> Prop) : forall (x : Prop), F x -> ex F := 
  fun (x : Prop) =>
    fun (e : F x) =>
      fun (y: Prop) =>
        fun (f : forall (z : Prop), F z -> y) => f x e.

Definition unpack (F : Prop -> Prop) 
  : ex F -> forall (y : Prop), (forall (x : Prop), F x -> y) -> y := 
    fun (u : ex F) (y : Prop) (f : forall (x : Prop), F x -> y) => 
      u y f.

Definition nu (F : Prop -> Prop) := ex (fun (x : Prop) => (x -> F x) |*| x).
Definition unfold (F : Prop -> Prop) 
  : forall (x : Prop), (x -> F x) -> (x -> nu F) := 
    fun (x : Prop) => 
      fun (f : x -> F x) => 
        fun (e : x) => 
          pack (fun x => (x -> F x) |*| x) x [f,e].

Definition outnu (F : Prop -> Prop) (FM : forall (a b : Prop), (a -> b) -> (F a -> F b))
  : nu F -> F (nu F).
Proof. 
  intros F FM.
  refine 
    (fun (u : nu F) => 
      unpack _ u (F (nu F)) 
      (fun (x : Prop) (w : (x -> F x) |*| x) => 
        FM _ _ (unfold _ x (fst w)) ((fst w) (snd w)))).
Defined.

Print outnu. 

Definition innu (F : Prop -> Prop) (FM : forall (a b : Prop), (a -> b) -> (F a -> F b))
  : F (nu (fun z => F z)) -> nu (fun z => F z).
Proof.
  intros F FM.
  refine (unfold _ (F (nu (fun z => F z))) (FM _ _ (outnu F FM))).
Defined.

(** Examples **)

(* Naturals *)
Definition NatF := fun n : Prop => '1 |+| n.
Definition NatFM : forall a b : Prop, (a -> b) -> NatF a -> NatF b.
Proof. 
  unfold NatF. intros a b f n. unfold Or in n. apply n. 
  intros. apply inl. auto.
  intros. apply inr. apply f. exact H.
Defined. 
Definition Nat := mu NatF.
Definition z : Nat := inmu NatF NatFM (inl Nat '()). 
Definition s : Nat -> Nat := fun n : Nat => inmu NatF NatFM (inr '1 n).

(* Nat Streams *)
 
Definition FL := (fun N => '1 |+| (Nat |*| N)). 
Definition CoList := nu FL.

Definition FML : forall (a b : Prop), (a -> b) -> (FL a -> FL b).
Proof. 
  unfold FL.
  intros a b f c.
  refine (c ('1 |+| (Nat |*| b)) (fun x : '1 => inl (Nat |*| b) '()) (fun x : (Nat |*| a) => inr _ _)).
  refine [_,_].
  exact (fst x).
  exact (f (snd x)).
Defined. 

(* Conaturals *) 

Definition FN := (fun N => '1 |+| N). 
Definition Conat := nu FN.

Definition FMN : forall (a b : Prop), (a -> b) -> (FN a -> FN b).
Proof. 
  unfold FN.
  intros a b f c.
  apply (c ('1 |+| b) (fun x : '1 => inl b '()) (fun x : a => inr '1 (f x))).
Defined. 
  
Definition out_FN := outnu FN FMN. 
Definition inn_FN := innu FN FMN.

Definition cz : Conat.
Proof. 
  unfold Conat. unfold FN. 
  cut '1. apply unfold. intros. apply inl. auto. 
  exact '().
Defined. 

Definition cs : Conat -> Conat.
Proof.
  unfold Conat.
  intros.
  apply (fun (c : nu FN) => inr '1 c) in H. 
  change (FN (nu FN)) in H.
  apply inn_FN.
  unfold FN at 2.  
  change (FN (nu FN)). auto.
Defined.

Definition inf : Conat := unfold FN Conat (fun x : Conat => inr '1 x) cz.

Definition clt (n : nat) (c : Conat) : bool.
Proof. 
  refine 
    (fix clt (n : nat) (c : Conat) : bool := 
      match n with 
        | 0 => true
        | S n' => (out_FN c) bool (fun x : '1 => false) (fun y => clt n' y)
      end).
Defined.
 
Lemma inf_infinity : forall (n : nat), clt n inf = true.
Proof.
  induction n.
  simpl. auto.
  simpl.
  unfold out_FN.
  unfold outnu. unfold unpack. 
  unfold inf at 1.
  unfold unfold at 1. unfold pack at 1. 
  unfold FMN. unfold fst at 1.
  unfold pair at 1. unfold inr at 1.
  unfold inr at 1. 
  unfold fst at 1. unfold pair at 1. 
  unfold snd at 1. unfold pair at 1. unfold inf in IHn.
  auto.
Defined.

(* Cleaner proof using normalisation *)
Lemma inf_infinity2 : forall (n : nat), clt n inf = true.
Proof. 
  induction n ; compute in * ; auto.
Defined.

(* Lists *)

Definition List (A : Prop) := forall (X : Prop), X -> (A -> X -> X) -> X.
Definition nil := fun (A : Prop) (X : Prop) (n : X) (c : A -> X -> X) => n.
Definition cons := fun (A : Prop) (a : A) (l : List A) => 
  fun (X : Prop) (n : X) (c : A -> X -> X) => c a (l X n c).
Implicit Arguments cons [A].
Eval compute in cons z (cons z (nil Nat)).
Definition mapl : forall (a b : Prop), (a -> b) ->  List a -> List b.
Proof. 
  refine
    (fun (a b : Prop) =>
      (fun (f : a -> b) (foldr : List a) => 
        foldr (List b) (nil b) (fun (x : a) (l : List b) => cons (f x) l))).
Defined.     

Definition foldr : forall (a b : Prop), (a -> b -> b) -> b -> List a -> b.
Proof. 
  refine 
    (fun (a b : Prop) => 
      fun (f : a -> b -> b) (n : b) (l : List a) =>
        l b n (fun (x : a) (y : b) => f x y)). 
Defined.
