Require Import Lang.
Require Import Arith.
  
(*
Lemma subsub_pre : forall ty1 ty2 n m d,
  tyshiftn (S n) 0 (tysub ty1 m ty2) =
  tysub (tyshiftn (S n) 0 ty1) (S (m + n + d)) (tyshiftn (S n) d ty2).
Proof.
  induction ty1. 
  (* TV *)
  simpl ; intros ; numerical. subst. intros.
  destruct n ; numerical. simpl. numerical.
  destruct n ; numerical.
  
  intros. simpl. rewrite IHty1_1. rewrite IHty1_2. auto.

  intros. simpl. 
  cut (S ( S (m+ n + d)) = S (m+ n+ (S d))). 
  intros. rewrite H. 
  intros.
  intros.
Defined.

Lemma subsub : forall m n ty ty1 ty2, 
  tysub (tysub ty (S (m + n)) (tyshiftn (S n) 0 ty2)) n (tyshiftn n 0 (tysub ty1 m ty2)) = 
  tysub (tysub ty n (tyshiftn n 0 ty1)) (m+n) (tyshiftn n 0 ty2).
Proof.
  induction ty.
  (* TV *)
  intros ; simpl ; numerical.
  destruct n0 ; numerical. simpl. subst. numerical.
  rewrite tyshiftn_z_id. rewrite tyshiftn_z_id.
  rewrite tyshiftn_z_id. simpl. rewrite plus_comm. simpl. auto.
  subst. 
  
  rewrite tysub_into_hole. 
  destruct n ; numerical. simpl.
  unfold tyshift.
  rewrite tysub_into_hole. 
  rewrite tyshiftn_z_id. auto. firstorder.
  
  (* Imp *)
  simpl. intros. 
  rewrite IHty1. rewrite IHty2. auto.

  (* All *)
  intros. simpl.

Defined.
*)

Require Import List. 

Theorem tysub_preservation : forall t m n l ty xty, 
  Derivation (S(m+n); map (tyshiftn 1 m) l |= t @ ty) -> 
  Derivation (m+n; l |= tysubt t m xty @ tysub ty m xty).
Proof.
  induction t ; intros.
  
  (* V *) 
  inversion H ; subst.
  simpl. 
  apply VarIntro. rewrite map_length in H2. auto. 
  apply nth_tysub_tyshift. auto.

  (* App *) 
  inversion H. subst.
  simpl.
  apply ImpElim with (xty:=tysub xty0 m xty). 
  apply IHt2. auto.
  change (Imp (tysub xty0 m xty) (tysub ty m xty)) with (tysub (Imp xty0 ty) m xty).
  apply IHt1. auto. 

  (* TApp *) 
  inversion H. subst. simpl.
  destruct m. 
  apply IHt with (xty:=xty) in H7. simpl in H7.
  simpl.
  apply AllElim with (xty:=tysub t0 0 xty) in H7.

tysub (tysub ty0 1 (tyshift xty)) 0 (tysub t0 0 xty))
tysub (tysub ty0 0 t0) 0 xty)  

  Check AllElim.
  intros. rewrite <- H1.
  auto. auto.
Defined.

Inductive Ev : Term -> Term -> Set :=
| Ev_beta : forall xty t1 t2, Ev (App (Abs xty t1) t2) (sub t1 0 t2)
| Ev_app : forall t1 t1' t2, Ev t1 t1' -> Ev (App t1 t2) (App t1' t2)
| Ev_tybeta : forall t xty, Ev (TApp (Lam t) xty) (tysubt t 0 xty).

Theorem Ev_preservation : forall n l t1 t2 ty, 
  Derivation (n ; l |= t1 @ ty) -> 
  Ev t1 t2 ->
  Derivation (n ; l |= t2 @ ty).
Proof.
  refine 
    (fix Ev_preservation n l (t1 t2 : Term) ty 
      (d : Derivation (n ; l |= t1 @ ty))
      (ev : Ev t1 t2) {struct t1} 
      : Derivation (n ; l |= t2 @ ty) :=
      (match t1 as t1' return (t1 = t1' -> Derivation (n ; l |= t2 @ ty))
         with
         | V n => _
         | App f g => _ 
         | Abs ty r => _ 
         | TApp r ty => _
         | Lam r => _
       end) (refl_equal t1)) ; intros ; subst.
  
  (* V *)
  inversion ev.

  (* App *) 
  inversion ev ; subst.
  inversion d ; subst. 

  apply sub_preservation_basic with (xty:=xty0).
  inversion H6 ; subst ; auto. auto.

  inversion d ; subst.
  apply ImpElim with (xty:=xty). auto.
  apply (Ev_preservation n l f t1'). auto. auto.

  (* TApp *)
  inversion ev ; subst.
  inversion d ; subst.
  apply (Ev_preservation n l (TApp (Lam t) ty0) (tysubt t 0 ty0)).
  auto. auto.

  (* Abs *) 
  inversion ev ; subst.
  inversion d ; subst. 
  apply (Ev_preservation n l (Lam r) t2).
  auto. auto.
Defined.
