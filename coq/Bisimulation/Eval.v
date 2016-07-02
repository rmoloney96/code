Require Import SystemF.
Require Import List.
Require Import Utils.
  
Section Evaluation. 

  Variable Delta : nat -> Term.
  Variable Xi : nat -> Ty.  
  Variable Prog : forall n l m, Derivation Xi [n ; l |= F m @ Xi m] -> Derivation Xi [n ; l |= Delta m @ Xi m]. 
  Variable ProgTy : forall m, valid (Xi m) 0.

  Inductive Ev : Term -> Term -> Set :=
  | ev_f : forall n, Ev (F n) (Delta n)
  | ev_app : forall t t' s, Ev t t' -> Ev (App t s) (App t' s)
  | ev_abs : forall t s ty, Ev (App (Abs ty t) s) (sub t 0 s)
  | ev_tapp : forall t t' ty, Ev t t' -> Ev (TApp t ty) (TApp t' ty)
  | ev_lam : forall t ty, Ev (TApp (Lam t) ty) (tysubt t 0 ty).


Theorem ev_preservation : forall t t' n l ty, Derivation Xi [n ; l |= t @ ty] ->  Ev t t' -> Derivation Xi [n ; l |= t' @ ty].
Proof. 
  refine (fix ev_preservation t t' n l ty (D : Derivation Xi [n ; l |= t @ ty]) (EvH : Ev t t') : Derivation Xi [n ; l |= t' @ ty] := _)
    ; case_eq t ; intros; subst. 
  (* F *)  
  inversion EvH ; subst. 
  inversion D ; subst. apply Prog ; auto.
  (* V *)
  inversion EvH.
  (* App *) 
  inversion EvH ; subst.
  inversion D ; subst. 
  apply ImpElim with (xty:=xty). auto.
  apply ev_preservation with (t:=t0) ; auto.
  inversion D ; subst.
  inversion H5 ; subst.
  apply sub_preservation_basic with (xty:=xty) ; auto. 
  (* TApp *) 
  inversion EvH ; subst.
  inversion D ; subst. 
  apply AllElim ; auto. 
  apply ev_preservation with (t:=t0) ; auto.
  inversion D ; subst.
  inversion H5 ; subst.
  apply tysub_derivation_simple. auto. auto. auto.
  (* Abs *) 
  inversion EvH. 
  (* Lam *) 
  inversion EvH.
Defined. 

Inductive Evplus : Term -> Term -> Set := 
| Evplus_base : forall t t', Ev t t' -> Evplus t t' 
| Evplus_next : forall t t' t'', Evplus t t' -> Ev t' t'' -> Evplus t t''.

(*
Inductive Evplus : Term -> Term -> Set := 
| Evplus_base : forall t t', Ev t t' -> Evplus t t' 
| Evplus_next : forall t t' t'', Ev t t' -> Evplus t' t'' -> Evplus t t''.
*)

Inductive Evstar : Term -> Term -> Set := 
| Evstar_refl : forall t t', t = t' -> Evstar t t'
| Evstar_plus : forall t t', Evplus t t' -> Evstar t t'. 

Notation "t ~> t'" := (Ev t t') (at level 60).  
Notation "t ~>+ t'" := (Evplus t t') (at level 60).
Notation "t ~>* t'" := (Evstar t t') (at level 60). 

Theorem evplus_preservation : forall t t' n l ty, Derivation Xi [n ; l |= t @ ty] ->  t ~>+ t' -> Derivation Xi [n ; l |= t' @ ty].
Proof.
  intros t t' n l ty Hty. induction 1. 
  apply ev_preservation with (t:=t) ; auto.   
  apply ev_preservation with (t:=t') ; auto.   
Defined.

Theorem evstar_preservation : forall t t' n l ty, Derivation Xi [n ; l |= t @ ty] ->  t ~>* t' -> Derivation Xi [n ; l |= t' @ ty].
Proof. 
  intros t t' n l ty Hty. induction 1. 
  subst. auto.   
  apply evplus_preservation with (t:=t) ; auto.   
Defined.

Theorem evplus_trans : forall r s t, r ~>+ s -> s ~>+ t -> r ~>+ t.
Proof.  
  intros r s t; induction 2. subst. auto. 
  apply Evplus_next with (t':=t). auto. auto.
  apply IHEvplus in H. 
  apply Evplus_next with (t':=t'). auto. auto. 
Defined. 

Theorem evstar_trans : forall r s t, r ~>* s -> s ~>* t -> r ~>* t.
  intros r s t Hrs Hst. 
  inversion Hrs ; subst. auto. 
  inversion Hst ; subst. auto.
  apply Evstar_plus. apply evplus_trans with (s:=s) ; auto. 
Defined. 
 
Inductive Value : Term -> Set := 
| Value_Lam : forall t, Value (Lam t)
| Value_Abs : forall t ty, Value (Abs ty t).

Lemma evstar_evplus_or_eq : forall t t', t ~>* t' -> (t ~>+ t') + {t = t'}.
Proof. 
  induction 1. 
  subst. right. auto.
  left. auto.
Defined.

Lemma evplus_app : forall t t' s, t ~>+ t' -> App t s ~>+ App t' s.
Proof.
  induction 1.
  apply Evplus_base ; apply ev_app ; auto.
  apply Evplus_next with (t':=App t' s). auto. 
  apply ev_app. auto. 
Defined.  

Lemma evstar_app : forall t t' s, t ~>* t' -> App t s ~>* App t' s.
Proof.
  intros t t' s Hevstar.
  inversion Hevstar ; subst ; [ apply Evstar_refl ; auto | idtac ].
  apply Evstar_plus. apply evplus_app. auto.   
Defined. 

Lemma evplus_tapp : forall t t' ty, t ~>+ t' -> TApp t ty ~>+ TApp t' ty.
Proof.
  induction 1.
  apply Evplus_base ; apply ev_tapp ; auto.
  apply Evplus_next with (t':=TApp t' ty). auto.
  apply ev_tapp. auto. 
Defined.  

Lemma evstar_tapp : forall t t' ty, t ~>* t' -> TApp t ty ~>* TApp t' ty.
Proof.
  intros t t' s Hevstar.
  inversion Hevstar ; subst ; [ apply Evstar_refl ; auto | idtac ].
  apply Evstar_plus. apply evplus_tapp. auto.   
Defined. 

Lemma evstar_lam : forall f r ty, f ~>* (Lam r) -> TApp f ty ~>* tysubt r 0 ty.
Proof.
  intros f r ty Hev.
  inversion Hev ; subst.
  apply Evstar_plus ; apply Evplus_base ; apply ev_lam ; auto.
  apply Evstar_plus ; apply Evplus_next with (t':=TApp (Lam r) ty).
  apply evplus_tapp. auto.
  apply ev_lam.
Defined.

Lemma evstar_abs : forall f r s ty, f ~>* (Abs ty r) -> App f s ~>* sub r 0 s.
Proof.
  intros f r s ty Hev.
  inversion Hev ; subst.
  apply Evstar_plus ; apply Evplus_base ; apply ev_abs.
  apply Evstar_plus ; apply Evplus_next with (t':=App (Abs ty r) s).
  apply evplus_app. auto.
  apply ev_abs. 
Defined.

Definition eval : forall (bound : nat) (t : Term), { t' : Term & t ~>* t'}.
Proof.
  refine (fix eval (bound : nat) (t : Term) : { t' : Term & t ~>* t'} := 
    (match bound as bound0 return (bound = bound0 -> { t' : Term & t ~>* t'}) with 
       | O => (fun _ => existT (fun t' : Term => t ~>* t') t (Evstar_refl t t (refl_equal t)))
       | S bound' => 
         (fun (Heq : bound = S bound') =>  
           (match t as t0 return (t = t0 -> { t' : Term & t0 ~>* t'}) with
              | V n => (fun (Heq : t = V n) => existT (fun t' : Term => V n ~>* t') (V n) _)
              | F n => 
                (fun (Heq : t = F n) => 
                  match eval bound' (Delta n) with 
                    | existT s P => existT (fun t' : Term => F n ~>* t') s _
                  end)
              | App f g => 
                (fun (Heq : t = App f g) =>
                  match eval bound' f with 
                    | existT s P => 
                      (match s as s0 return (s = s0 -> {t' : Term & App f g ~>* t'}) with 
                         | (Abs ty s') => 
                           (fun (Heq : s = Abs ty s') => 
                             match eval bound' (sub s' 0 g) with 
                               | existT sub_ev P' => 
                                 existT (fun t' : Term => App f g ~>* t') sub_ev _
                             end)
                         | _ => (fun (Heq : _) => existT (fun t' : Term => App f g ~>* t') (App s g) _)
                       end) (refl_equal s)
                  end)
              | Abs ty r =>  
                (fun (Heq : t = Abs ty r) => 
                  existT (fun t' : Term => Abs ty _ ~>* t' ) (Abs ty r) _)                  
              | TApp r ty => 
                (fun (Heq : t = TApp r ty) =>
                  match eval bound' r with 
                    | existT s P => 
                      (match s as s0 return (s = s0 -> {t' : Term & TApp r ty ~>* t'}) with 
                         | (Lam s') => 
                           (fun (Heq : s = Lam s') => 
                             match eval bound' (tysubt s' 0 ty) with 
                               | existT sub_ev P' => 
                                 existT (fun t' : Term => TApp r ty ~>* t') sub_ev _
                             end)
                         | _ => (fun (Heq : _) => existT (fun t' : Term => TApp r ty ~>* t') (TApp s ty) _)
                       end) (refl_equal s)
                  end)
              | Lam r => 
                (fun (Heq : t = Lam r) => 
                  existT (fun t' : Term => Lam _  ~>* t') (Lam r) _)                  
            end) (refl_equal t))
     end) (refl_equal bound)); subst ; try (apply evstar_app ; auto) ; try (apply evstar_tapp ; auto).
  (* F *) 
  apply evstar_trans with (s:=Delta n). 
  apply Evstar_plus. apply Evplus_base. apply ev_f. auto.  
  (* V *) 
  apply Evstar_refl. auto.
  (* App *)
  apply evstar_trans with (s:=sub s' 0 g). 
  apply evstar_abs with (ty:=ty). auto. auto. 
  (* TApp *)
  apply evstar_trans with (s:=tysubt s' 0 ty). 
  apply evstar_lam. auto. auto.
  (* Abs *) 
  apply Evstar_refl ; auto.
  (* Lam *) 
  apply Evstar_refl ; auto.
Defined.

Definition eval_weak : forall (bound : nat) (t : Term), Term.
Proof.
  refine 
    (fix eval_weak (bound : nat) (t : Term) : Term := 
      match bound with 
        | O => t 
        | S bound' => 
          match t with
            | V n => (V n)
            | F n => match bound' with 
                       | 0 => F n 
                       | S bound'' => eval_weak bound'' (Delta n)
                     end
            | App f g => 
              match eval_weak bound' f with 
                | (Abs ty s') => 
                  match bound' with 
                    | 0 => App (Abs ty s') g
                    | S bound'' => eval_weak bound'' (sub s' 0 g)
                  end
                | s => (App s g)
              end
            | Abs ty r => Abs ty r
            | TApp r ty => 
              match eval_weak bound' r with 
                | (Lam s') =>                   
                  match bound' with 
                    | 0 => TApp (Lam s') ty
                    | S bound'' => eval_weak bound'' (tysubt s' 0 ty) 
                  end                
                | s => TApp s ty
              end
            | Lam r => Lam r
          end
      end).
Defined. 

Theorem compute_eval : forall (bound : nat) (t t': Term), eval_weak bound t = t' -> t ~>* t'.
Proof.
  refine (fix compute_eval (bound : nat) (t t': Term) (Hevalw : eval_weak bound t = t') : t ~>* t' := _) ; destruct bound. 
  (* zero *)
  simpl in Hevalw. subst. apply Evstar_refl. auto.
  (* next *)
  simpl in Hevalw.
  (* Term by Term *)
  destruct t. 
  (* F *)
  destruct bound.
    (* Z *) 
    subst. apply Evstar_refl. auto.
    (* S n *)
    simpl in Hevalw.
    apply compute_eval in Hevalw.
    apply evstar_trans with (s:=Delta n).
    apply Evstar_plus. apply Evplus_base. apply ev_f. auto.  
  (* V *) 
  subst. apply Evstar_refl. auto. 
  (* App *)
  case_eq (eval_weak bound t1) ; intros ;
    try (rewrite H in Hevalw ; subst ; apply compute_eval in H ; apply evstar_app ; exact H). 
    (* App *) 
    rewrite H in Hevalw. apply compute_eval in H. 
    destruct bound.
      (* Z *) 
      subst. apply evstar_app. auto. 
      (* S bound *) 
      apply compute_eval in Hevalw.
      apply evstar_trans with (sub t0 0 t2). 
      apply evstar_abs with (ty:=t). auto. auto.  
  (* TApp *)
  case_eq (eval_weak bound t) ; intros ; 
    try (rewrite H in Hevalw ; subst ; apply compute_eval in H ; apply evstar_tapp ; exact H). 
    (* TApp *)
    rewrite H in Hevalw. apply compute_eval in H.  
    destruct bound.
      (* eq *) 
      subst. apply evstar_tapp. auto.
      (* neq *) 
      apply compute_eval in Hevalw. 
      apply evstar_trans with (tysubt t1 0 t0). 
      apply evstar_lam. auto. auto.  
  (* Abs *) 
  subst.
  apply Evstar_refl ; auto.
  (* Lam *) 
  subst.
  apply Evstar_refl ; auto.
Defined.

Theorem ev_progress : forall t A, Derivation Xi [0; nil |= t @ A] -> { s : Term & t ~> s} + (Value t).
Proof.
  induction t; intros A HD. 
  (* F *) 
  apply inl. exists (Delta n). apply ev_f.
  (* V *)    
  inversion HD ; subst. simpl in H4. elimtype False. firstorder.
  (* App *) 
  inversion HD as [ | |n l t f ty xty Ht Hf | | |] ; subst.
  apply IHt1 in Hf. apply IHt2 in Ht. 
  apply inl.
  inversion Hf as [Hleft | Hright]. 
    (* Left *) 
    inversion Hleft as [x P]. 
    exists (App x t2). apply ev_app. auto.
    (* Right *)
    inversion Hright as [tyabs | f ] ; subst.
     (* Lam *) 
     inversion HD as [ | |n l t f ty xty' Ht' Hf' | | |] ; subst; inversion Hf'. 
     (* Abs *) 
     exists (sub f 0 t2). apply ev_abs.
  (* TApp *) 
  inversion HD as [ | | | | n l t' ty xty Hv Hall |] ; subst.
  apply IHt in Hall. 
  apply inl.
  inversion Hall as [Hleft | Hright]. 
    (* Left *) 
    inversion Hleft as [x P].
    exists (TApp x t0). apply ev_tapp. auto.   
    (* Right *) 
    inversion Hright as [r | abs] ; subst. 
      (* Lam *) 
      exists (tysubt r 0 t0).
      apply ev_lam.
      (* Abs *)   
      inversion HD as [ | | | | n l t' ty' xty Hv' Hall' |] ; subst ; inversion Hall'.
  (* Abs *) 
  apply inr. 
  apply Value_Abs.
  (* Lam *) 
  apply inr. 
  apply Value_Lam.
Defined.   

Lemma evplus_progress_lemma : forall t, { s : Term & t ~> s} + (Value t) -> { s : Term & t ~>+ s} + (Value t).
Proof.
  intros t Hor.
  inversion Hor as [Hleft | Hright].
  apply inl. 
  inversion Hleft as [x P].
  exists x. apply Evplus_base. auto.
  apply inr. auto.
Defined.     

Theorem evplus_progress : forall t A, Derivation Xi [0; nil |= t @ A] -> { s : Term & t ~>+ s} + (Value t).
Proof.
  intros t A HD.
  apply evplus_progress_lemma. apply ev_progress with (A:=A). auto.
Defined.  

Lemma evplus_value_stuck : forall t s A, Derivation Xi [0; nil |= t @ A] -> Value t -> notT (t ~>+ s).
Proof.
  unfold notT. induction 3.
  inversion H0 ; subst.
  (* Lam *)
  inversion e.
  inversion e.
  apply IHEvplus ; auto. 
Defined.

Lemma stuck_imp_value : forall t A, Derivation Xi [0; nil |= t @ A] -> notT {s : Term & t ~>+ s} -> Value t.
Proof. 
  unfold notT. 
  induction t ; intros A HD Hnoreduce.
  (* F *) 
  elimtype False ; apply Hnoreduce.
  exists (Delta n). apply Evplus_base ; apply ev_f. 
  (* V *) 
  clear Hnoreduce.
  inversion HD as [ | | | | | n0 l ty i Hv Hl Heq Hv] ; simpl in Hl ; elimtype False ; firstorder.
  (* App *) 
  elimtype False. apply Hnoreduce.
  inversion HD as [ | | n0 l t f ty xty Hx Hf | | |] ; subst.
  apply IHt1 in Hf. 
  inversion Hf ; subst.
    (* Lam *) 
    inversion HD as [ | | n0 l t' f' ty xty' Hx' Hf' | | |] ; inversion Hf'.
    (* Abs *) 
    exists (sub t 0 t2). apply Evplus_base. apply ev_abs.  
    (* Ev *)
    intros H. apply Hnoreduce.
    inversion H as [x P].
    exists (App x t2). apply evplus_app. auto.
  (* TApp *)   
  elimtype False. apply Hnoreduce.
  inversion HD as [ | | | | n0 l r ty xty Hv Ht | ] ; subst.
  apply IHt in Ht.
  inversion Ht; subst.
    (* Lam *) 
    exists (tysubt t1 0 t0). apply Evplus_base. apply ev_lam.
    (* Abs *) 
    inversion HD as [ | | | | n0 l r ty' xty Hv' Ht' | ] ; inversion Ht'.
    (* Ev *) 
    intros H.  
    apply Hnoreduce.
    inversion H as [x P]. 
    exists (TApp x t0). apply evplus_tapp. auto.
  (* Abs *) 
  apply Value_Abs.
  (* Lam *) 
  apply Value_Lam.
Defined. 

Lemma Value_refl : forall t s A, Derivation Xi [0 ; nil |= t @ A] -> Value t -> t ~>* s -> t = s.
Proof.
  intros t s A Hd Hv Hev. 
  inversion Hv ; inversion Hev ; subst ; auto.
  elimtype False. apply evplus_value_stuck with (s:=s) (A:=A) in Hv. apply Hv. auto.
  auto.
  elimtype False. apply evplus_value_stuck with (s:=s) (A:=A) in Hv. apply Hv. auto. 
  auto.
Defined.

Lemma ev_det : forall a b c, a ~> b -> a ~> c -> b = c.
Proof. 
  refine 
    (fix ev_det a b c (Hab : a ~> b) (Hac : a ~> c) {struct Hab} : b = c := 
      (match Hab in (a0 ~> b0) return (a = a0 -> b = b0 -> b0 = c) with 
         | ev_f n  => _
         | ev_app t t' s Hev' => _
         | ev_abs t s ty => _
         | ev_tapp t t' ty Hev' => _
         | ev_lam t ty => _ 
       end) (refl_equal a) (refl_equal b)) ; intros Heqa Heqb.

  (* F *) 
  rewrite Heqa in Hac. inversion Hac. auto.
  (* App *) 
  rewrite Heqa in Hac. inversion Hac.
  cut (t' = t'0). intros. subst. auto. 
  apply ev_det with (a:=t) ; auto.
    (* Subcases *) 

    subst. inversion Hab. inversion H0. auto.
    subst. inversion Hac. subst. inversion H2. 
    auto.
 (* Tapp *)
  rewrite Heqa in Hac. inversion Hac.
  cut (t' = t'0). intros. rewrite H3. auto.
  apply ev_det with (a:=t) ; auto.
    (* subcases *) 
    subst. inversion Hev'.
    subst. inversion Hac. subst. inversion H2.
    auto.
Defined.

Lemma ev_inter_evplus : forall a b c, a ~> b -> a ~>+ c -> b ~>* c.
Proof.
  induction 2.
  apply ev_det with (b:=t') in H. subst.
  apply Evstar_refl. auto. auto.
  cut (b ~>* t').
  intros. apply Evplus_base in e. apply Evstar_plus in e.
  apply evstar_trans with (r:=b) in e. auto. auto.
  apply IHEvplus. auto.
Defined.

Lemma evplus_det : forall a b c, a ~>+ b -> a ~>+ c -> (b ~>+ c) + (c ~>+ b) + (b = c). 
Proof.
  induction 1.
  intros Htc.
  inversion Htc. 
  (* Evplus_base *)
  subst. 
  apply ev_det with (b:=t') in H. 
  right. auto. auto.
  (* Evplus_next *)
  inversion H. subst.
  apply ev_inter_evplus with (c:=t'0) in e.
    inversion e. 
    (* refl *)
    left. left. subst ; auto.
    apply Evplus_base. auto.
    (* next *) 
    subst. 
    left. left. apply Evplus_next with (t':=t'0). auto. auto. auto.
    (* base *) 
    subst.
    apply ev_inter_evplus with (c:=c) in e.
    inversion e. subst. 
    (* next *)
    right ; auto. 
    subst.
    left. left. auto. auto.
  (* Ev 2 *) 
  intros Htc.
  apply IHEvplus in Htc.  
    inversion Htc.
    (* (t' ~>+ c) + (c ~>+ t') *)
    inversion H0.
    (* (t' ~>+ c) *) 
      (* eq *)
      apply ev_inter_evplus with (b:=t'') in H1.
      inversion H1. subst.
      right. auto.
      (* plus *) 
      subst. 
      left. left. auto. auto.
    (* c ~>+ t' *) 
    left. right. apply Evplus_next with (t':=t'). auto. auto.
    (* t' = c *)
    subst.
  (* Ev 3 *)
  left. right. apply Evplus_base. auto.
Defined.

Lemma evstar_det : forall a b c, a ~>* b -> a ~>* c -> (b ~>* c) + (c ~>* b).
Proof. 
  intros a b c Hab Hac ; inversion Hab ; inversion Hac ; subst. 
  left ; auto. 
  left ; auto.
  right ; auto.
  apply evplus_det with (c:=c) in H. 
  inversion H. 
  inversion H0. 
  (*  (b ~>+ c) *) 
  left. apply Evstar_plus. auto.
  (*  (c ~>+ b) *) 
  right. apply Evstar_plus. auto.
  (* b = c *) 
  subst. 
  left. apply Evstar_refl. auto. auto. 
Defined.

Inductive EvDeep :=
| evdeep_base : forall t t', Ev t t' -> EvDeep t t'
| evdeep_app2 : forall t t' s, Ev s s' -> EvDeep (App t s) (App t s')
| evdeep_abs : forall t s ty, Ev t t' -> EvDeep (Abs ty t) (Abs ty t')
| evdeep_lam : forall t t' ty, Ev t t' -> EvDeep (Lam t) (Lam t').

Inductive StrongNormalisation := 
  

End Evaluation. 