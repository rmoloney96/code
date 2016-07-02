
Require Import List.
Require Import String.

Theorem pair_eq_dec : forall (A B:Type), 
  (forall (a a':A), {a = a'} + {a <> a'}) -> 
  (forall (b b':B), {b = b'} + {b <> b'}) -> 
  (forall (c c':A*B), {c = c'} + {c <> c'}).
Proof.
  decide equality.
Defined.
Implicit Arguments pair_eq_dec [A B].

Inductive t : Set := 
| bvar : nat -> t
| fvar : string -> t
| abs : t -> t
| con : string -> list t -> t
| app : t -> t -> t
| cas : t -> list (string * nat * t) -> t.

Reset t_rect.

Require Import Peano_dec. 
 
Definition t_eq_dec : forall (t0 t1:t), {t0 = t1} + {t0 <> t1}.
  refine 
    (fix t_eq_dec (t':t) (t'':t) {struct t'} : {t' = t''} + {t' <> t''} := 
      match t', t'' return {t' = t''} + {t' <> t''} with 
        | bvar n, bvar n' => match eq_nat_dec n n' with | left _ => _ | right _ => _ end
        | fvar s, fvar s' => match string_dec s s' with | left _ => _ | right _ => _ end
        | abs t0, abs t1 => match t_eq_dec t0 t1 with | left _ => _ | right _ => _ end
        | con c lt0, con c' lt1 => match string_dec c c' return {con c lt0 = con c' lt1} + {con c lt0 <> con c' lt1} with 
                                     | left _ => _ | right _ => _ 
                                   end
        | app M N, app M' N' => match t_eq_dec M M' with 
                                  | left _ => match t_eq_dec N N' with | left _ => _ | right _ => _ end
                                  | right _ => _ 
                                end 
        | cas t0 trip, cas t1 trip' => match t_eq_dec t0 t1 with
                                         | left _ => _
                                         | right _ => _ 
                                       end
        | _,_ => right _ _
      end) ; try (right ; congruence) ; try (congruence) ; try (subst ; left ; clear t_eq_dec ; auto; fail).
  (* constructors *)
  subst. generalize dependent lt1 ; generalize dependent lt0 ; induction lt0.
  destruct lt1. left ; clear t_eq_dec ; auto. right ; congruence.
  induction lt1. right ; congruence. case (t_eq_dec a a0). intros. subst.
  case (IHlt0 lt1). intros. inversion e. rewrite <- H0. left. reflexivity. 
  intros. right. congruence.
  intros. right. congruence.
  (* case *)
  subst. generalize dependent trip' ; generalize dependent trip ; induction trip.
  destruct trip'. left. clear t_eq_dec ; auto. right ; congruence.
  induction trip'. right ; congruence. 
  generalize dependent a0. generalize dependent a. destruct a. destruct a0.
  case (t_eq_dec t0 t2). intros. subst.
  case ((pair_eq_dec string_dec eq_nat_dec) p p0).
  intros. subst. case (IHtrip trip'). intros. inversion e. subst. left. reflexivity.
  intros. right. congruence. intros. right. congruence. intros. right. congruence.
Defined. 

Definition Member : forall (A : Type) (eq_dec : forall (a b:A), {a = b} + {a <> b}) (a : A) (l : list A), Prop.
  intros A eq_dec.
  refine 
    (fix Member (a : A) (l : list A) {struct l} : Prop :=
      match l with
        | nil => False
        | b :: m => match eq_dec a b with 
                      | left p => True
                      | right p => Member a m
                    end
      end) ; try (right ; clear Member ; auto ; fail).
Defined.
Implicit Arguments Member [A].

Definition trip_dec := (pair_eq_dec (pair_eq_dec string_dec eq_nat_dec) t_eq_dec).  

Definition t_rect :  
  forall P : t -> Type,
    (forall n : nat, P (bvar n)) ->
    (forall s : string, P (fvar s)) ->
    (forall t : t, P t -> P (abs t)) ->
    (forall (s : string) (l : list t), (forall t, Member t_eq_dec t l -> P t) -> P (con s l)) ->
    (forall t0 : t, P t0 -> forall t : t, P t -> P (app t0 t)) ->
    (forall t0 : t, P t0 -> 
      forall l : list (string * nat * t), 
        (forall triple, Member trip_dec triple l -> P (snd triple)) -> P (cas t0 l)) -> 
    forall t : t, P t. 
Proof.
  intros P Hbvar Hfvar Habs Hcon Happ Hcas. 
  refine (fix IH (t:t) {struct t} := _).
  case t0. 
  apply Hbvar.
  apply Hfvar.
  intros. apply Habs. apply IH. 

  intros. apply Hcon. 
    induction l. intros t' Hin. inversion Hin.  
    intros t' Hin. simpl in Hin. destruct (t_eq_dec t' a).
    subst t'. apply IH.  
    apply IHl. exact Hin.

  intros. apply Happ. apply IH. apply IH.

  intros. apply Hcas. apply IH. 
    induction l. intros triple Hin. inversion Hin.
    intros triple Hin. simpl in Hin. destruct (trip_dec triple a).
    subst triple. apply IH.
    apply IHl. exact Hin.
Defined.

Definition t_rec :  
  forall P : t -> Set,
    (forall n : nat, P (bvar n)) ->
    (forall s : string, P (fvar s)) ->
    (forall t : t, P t -> P (abs t)) ->
    (forall (s : string) (l : list t), (forall t, Member t_eq_dec t l -> P t) -> P (con s l)) ->
    (forall t0 : t, P t0 -> forall t : t, P t -> P (app t0 t)) ->
    (forall t0 : t, P t0 -> 
      forall l : list (string * nat * t), 
        (forall triple, Member trip_dec triple l -> P (snd triple)) -> P (cas t0 l)) -> 
    forall t : t, P t. 
Proof.
  intros P Hbvar Hfvar Habs Hcon Happ Hcas. 
  refine (fix IH (t:t) {struct t} := _).
  case t0. 
  apply Hbvar.
  apply Hfvar.
  intros. apply Habs. apply IH. 

  intros. apply Hcon. 
    induction l. intros t' Hin. inversion Hin.  
    intros t' Hin. simpl in Hin. destruct (t_eq_dec t' a).
    subst t'. apply IH.  
    apply IHl. exact Hin.

  intros. apply Happ. apply IH. apply IH.

  intros. apply Hcas. apply IH. 
    induction l. intros triple Hin. inversion Hin.
    intros triple Hin. simpl in Hin. destruct (trip_dec triple a).
    subst triple. apply IH.
    apply IHl. exact Hin.
Defined.

Definition t_ind :  
  forall P : t -> Prop,
    (forall n : nat, P (bvar n)) ->
    (forall s : string, P (fvar s)) ->
    (forall t : t, P t -> P (abs t)) ->
    (forall (s : string) (l : list t), (forall t, In t l -> P t) -> P (con s l)) ->
    (forall t0 : t, P t0 -> forall t : t, P t -> P (app t0 t)) ->
    (forall t0 : t, P t0 -> 
      forall l : list (string * nat * t), 
        (forall triple, In triple l -> P (snd triple)) -> P (cas t0 l)) -> 
    forall t : t, P t. 
Proof.
  intros P Hbvar Hfvar Habs Hcon Happ Hcas. 
  refine (fix IH (t:t) {struct t} := _).
  case t0. 
  apply Hbvar.
  apply Hfvar.
  intros. apply Habs. apply IH. 
  intros. apply Hcon. 
    induction l. intros t' Hin. inversion Hin.  
    intros t' Hin. inversion Hin. subst t'. apply IH.    
    apply IHl. exact H.
  intros. apply Happ. apply IH. apply IH. 
  intros. apply Hcas. apply IH. 
    intros trip Hin. induction l. inversion Hin. 
    inversion Hin. subst trip. apply IH. apply IHl. exact H.   
Defined.

