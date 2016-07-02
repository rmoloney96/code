
Definition Id := nat. 

Inductive Ty : Type := 
| TArr : Ty -> Ty -> Ty
| TC : Id -> Ty.

Parameter Delta : Id -> Ty.

Inductive Term : nat -> Type := 
| Const : nat -> Term 0
| Var : forall n, Term (S n)
| App : forall n, Term n -> Term n -> Term n
| Abs : forall n, Term (S n) -> Term n
| We  : forall n, Term n -> Term (S n)
| Error : Term 0.
Implicit Arguments Var.
Implicit Arguments App [n]. 
Implicit Arguments Abs [n]. 
Implicit Arguments We [n].
Coercion Var : nat >-> Term.

Require Import Peano_dec.
Require Import Le.

Lemma le_ne_Sle : forall n m, n <= m -> n <> m -> (S n) <= m.
Proof.
  induction 1. intros. congruence.
  intros. apply le_n_S. auto. 
Defined.

Function raise (n m : nat) (t : Term m) {struct n} : Term (n + m) := 
  match n with 
    | 0 => t
    | S n' => We (raise n' m t)
  end.

(* done for transparency *)
Lemma my_plus_n_O : forall n:nat, n = n + 0.
Proof.
  induction n; simpl in |- *; auto.
Defined.

Lemma my_plus_n_Sm : forall n m:nat, S (n + m) = n + S m.
Proof.
  intros n m; induction n; simpl in |- *; auto.
Defined.

(* Require Import Omega. *)
Lemma le_r : forall n m, n <= m -> {r | r + n = m}.
Proof. 
  induction n. intros. exists m. apply sym_eq. apply my_plus_n_O.
  intros.
  cut (n <= m). intros. apply IHn in H0. 
  inversion H0. exists (x-1). rewrite <- H1.
  simpl. 
  cut ((x-1+S n) = (S (x-1) + n)). intros. rewrite H2.
  induction x. simpl in H1. rewrite H1 in H. 
  apply le_Sn_n in H. inversion H.
  simpl.  
  induction x. compute. auto.
  compute. auto.
  apply sym_eq.
  apply my_plus_n_Sm.
  apply le_Sn_le. auto.
Defined.

(* Omega gives ugly terms!
Proof. 
  induction n. intros. exists m. auto.
  intros.
  cut (n <= m). intros. apply IHn in H0. inversion H0.
  exists (x-1).  rewrite <- H1. omega. omega.
Defined. 
*) 

Definition weaken_n : forall n m, n <= m -> Term n -> Term m.
Proof.
  intros.  
  apply le_r in H. inversion H. apply (raise x) in H0. rewrite H1 in H0.
  auto.
Defined.

Definition weaken : forall m, Term 0 -> Term m.
Proof. 
  induction m. intros. auto. 
  intros. apply (weaken_n (S m)). auto. apply We. apply IHm. auto.
Defined. 

Require Import Arith.
Definition sub : forall n, Term (S n) -> Term 0 -> Term n.
Proof.
  refine 
    (fix sub (n : nat) (u : Term (S n)) (t : Term 0) {struct u} : Term n := 
      (match u as u' in Term n0 return (n0 = (S n) -> Term n) with 
         | Const n' => 
           (fun (pc : 0 = S n) => 
             match eq_nat_dec n' n with 
               | left p => weaken n t
               | right p => (eq_rect _ Term (Const n') _ _)
             end)
         | Var n' => 
           (fun (pv : S n' = S n) => 
             match eq_nat_dec n' n with 
               | left p => (weaken n t)
               | right p => (eq_rect _ Term (Var n') _ _)
             end)
         | App n' u0 u1 => 
           (fun (pa : n' = S n) => 
             App (sub n (eq_rect n' Term u0 _ _) t)
                 (sub n (eq_rect n' Term u1 _ _) t))
         | Abs n' u0 => 
           (fun (pb : n' = S n) => 
             Abs (sub (S n) (eq_rect _ Term u0 _ _) t))
         | We n' u0 => 
           (fun (pw : S n' = S n) => 
             match le_lt_dec n n' with 
               | left p => (eq_rect n' Term u0 _ _)
               | right p => (eq_rect _ Term (We (sub n (eq_rect _ Term u0 _ _) t)) _ _)
             end)
         | Error => (fun _ : _ => weaken n Error)
       end) (refl_equal (S n))).
  (* const *) 
  inversion pc.
  (* var *) 
  inversion pv. unfold not in p. apply p in H0. inversion H0. 
  (* app *) 
  inversion pa. reflexivity. exact pa.
  (* abs *)
  subst. reflexivity. 
  (* weak *)
  inversion pw. auto.
  inversion pw. rewrite H0 in p. 
  apply lt_irrefl in p. inversion p.
  inversion pw. rewrite H0 in p. 
  apply lt_irrefl in p. inversion p.
  (* error *)
Defined.

Parameter delta : nat -> nat -> nat.

Inductive Ev : Term 0 -> Term 0 -> Type :=
| Ev_app_lft : forall M N M', Ev M M' -> Ev (App M N) (App M' N)
| Ev_app_rgt : forall M N N', Ev N N' -> Ev (App M N) (App M N')
| Ev_app : forall t u, Ev (App (Abs u) t) (sub 0 u t)
| Ev_appc : forall n m, Ev (App (Const n) (Const m)) (Const (delta n m)).

Inductive Ev_plus : Term 0 -> Term 0 -> Type := 
| Ev_plus_trans : forall t t' t'', Ev t t' -> Ev t' t'' -> Ev_plus t t''. 

Inductive Ev_star : Term 0 -> Term 0 -> Type := 
| Ev_star_refl : forall t t', Ev_star t t'
| Ev_star_trans : forall t t', Ev_plus t t' -> Ev_star t t'. 

Inductive active : Term 0 -> Prop := 
| active_prod : forall t1 t2, lc (prod t1 t2) -> active (prod t1 t2)
| active_inl : forall t, lc (inl t) -> active (inl t)
| active_inr : forall t, lc (inr t) -> active (inr t).

Inductive passive : term -> Prop := 
| passive_unit : passive unit
| passive_abs : forall t, lc (abs t) -> passive (abs t)
| passive_fp : forall t, lc (fp t) -> passive (fp t).

Inductive label : Set := 
| label_fvar : forall (b : atom), label
| label_fst 
| label_snd 
| label_inl 
| label_inr
| label_fp
| label_app : forall (b : term), label.

(* we need an arbitrary divergent term of active type *)
Definition inf := inl (fp (inl 0)).

(* create a transition system for our functional programs *)
Inductive trans : term -> label -> term -> Prop :=
| trans_fvar : forall (x : atom), trans x (label_fvar x) x
| trans_fst : forall t1 t2, lc (prod t1 t2) -> trans (prod t1 t2) label_fst t1
| trans_snd : forall t1 t2, lc (prod t1 t2) -> trans (prod t1 t2) label_snd t2
| trans_inl : forall t, lc (inl t) -> trans (inl t) label_inl t 
| trans_inr : forall t, lc (inr t) -> trans (inr t) label_inr t
(* | trans_fp : forall t, lc (fp t) -> trans (fp t) label_fp  (open t (fp t)) *)
| trans_app : forall t1 t2, lc (abs t1) -> lc t2 -> trans (abs t1) (label_app t2) (app (abs t1) t2)
| trans_next : forall t1 t2 t3 l, eval t1 t2 -> trans t2 l t3 -> trans t1 l t3.


CoInductive simulates : term -> term -> Prop := 
| simulates_base : forall a b, 
  (forall a' l, 
    trans a l a' -> 
    (exists b', trans b l b' /\ simulates a' b')) -> 
  simulates a b.

CoInductive bisimulates : term -> term -> Prop := 
| bisimulates_base : forall a b, 
  (forall a' l, 
    trans a l a' -> 
    (exists b', trans b l b' /\ bisimulates a' b')) -> 
  (forall b' l, 
    trans b l b' -> 
    (exists a', trans a l a' /\ bisimulates a' b')) -> 
  bisimulates a b.


Inductive Simulation : Term 0 -> Term 0 -> Type := 
| Simulation_refl : forall t, Simulation t t
| Simulation_ev : forall t t' u, Ev t t' -> Simulation t u -> Simulation t' u.

Inductive Bisimulation : Term 0 -> Term 0 -> Type := 
| Bisimulation_refl : forall t, Bisimulation 


Definition eval : Term 0 -> Term 0.
Proof. 
  refine 
    (fun (t : Term 0) =>
      (match t as t0 in Term n0 return (n0 = 0 -> Term 0) with 
         | Var n' => (fun _ : _ => t)
         | App n' u u' => 
           (fun _ : _ => 
             match u as u0 in Term n1 return (n1 = 0 -> Term 0) with 
               | Var n'' => _
               | App n'' u'' u''' => _
               | Abs n'' u'' => (fun h : n'' = 0 => sub 0 (eq_rect _ _ u'' _ _) 
                                                          (eq_rect _ _ u' _ _))
               | We n' u'' => _ 
               | Error => (fun _ : _ => Error)
             end) (refl_equal 0)
         | Abs n' u => (fun _ : _ => t)
         | We n' u => (fun _ : _ => t)
         | Error => (fun _ : _ => t)
       end) (refl_equal 0)).  exact t.  
