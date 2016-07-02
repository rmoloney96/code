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
  | ev_lam : forall t ty, Ev (TApp (Lam t) ty) (tysubt t 0 ty)
  | ev_fold : forall t ty ty', Ev (Unfold (Fold t ty') ty) t
  | ev_unfold : forall t t' ty, Ev t t' -> Ev (Unfold t ty) (Unfold t' ty)
  | ev_inl : forall t r s ty, Ev (Case (Inl t ty) r s) (sub r 0 t)
  | ev_inr : forall t r s ty, Ev (Case (Inr t ty) r s) (sub s 0 t)
  | ev_case : forall t t' r s, Ev t t' -> Ev (Case t r s) (Case t' r s)
  | ev_pair : forall t s u, Ev (Split (Pair t s) u) (sub (sub u 0 (shift 0 t)) 0 s)
  | ev_split: forall t t' u, Ev t t' -> Ev (Split t u) (Split t' u). 

Theorem ev_preservation : forall t t' n l ty, Derivation Xi [n ; l |= t @ ty] ->  Ev t t' -> Derivation Xi [n ; l |= t' @ ty].
Proof. 
  refine (fix ev_preservation t t' n l ty (D : Derivation Xi [n ; l |= t @ ty]) (EvH : Ev t t') : Derivation Xi [n ; l |= t' @ ty] := _)
    ; case_eq t ; intros; subst ; inversion EvH ; subst ; inversion D ; subst. 
  (* F *)  
  apply Prog ; auto.
  (* App *) 
  apply ImpElim with (xty:=xty). auto.
  apply ev_preservation with (t:=t0) ; auto.
  inversion H5 ; subst.
  apply sub_preservation_basic with (xty:=xty) ; auto. 
  (* TApp *) 
  apply AllElim ; auto. 
  apply ev_preservation with (t:=t0) ; auto.
  inversion H5 ; subst.
  apply tysub_derivation_simple. auto. auto. auto.
  (* Unfold *) 
    (* Fold *) 
      (* Mu *)  
      inversion H5 ; subst. auto.
      (* Nu *)   
      inversion H5 ; subst. auto.
    (* trans *) 
      (* Mu *) 
      apply MuElim. auto. 
      apply ev_preservation with (t:=t0) ; auto.   
      (* Nu *) 
      apply NuElim. auto. 
      apply ev_preservation with (t:=t0) ; auto.
  (* Case *) 
    (* inl *)
    inversion H2 ; subst.
    apply sub_preservation_basic with (xty:=A) ; auto. 
    (* Inr *) 
    inversion H2 ; subst. 
    apply sub_preservation_basic with (xty:=B) ; auto.
    (* trans *) 
    apply OrElim with (A:=A) (B:=B) ; auto.
    apply ev_preservation with (t := t0) ; auto.
  (* Split *) 
    (* pair *) 
    inversion H1 ; subst. 
    apply sub_preservation_basic with (xty:=B) ; auto.
    apply sub_preservation_basic with (xty:=A) ; auto.
    change 0 with (length (@nil Ty)).
    change (B :: l) with (nil ++ B :: l).  
    apply shift_correct. auto. simpl. auto.
    (* trans *) 
    apply AndElim with (A:=A) (B:=B) ; auto.
    apply ev_preservation with (t:=t0) ; auto.   
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
| Value_Abs : forall t ty, Value (Abs ty t)
| Value_Fold : forall t ty, Value (Fold t ty)
| Value_Pair : forall t s, Value (Pair t s)
| Value_Inl : forall t ty, Value (Inl t ty)
| Value_Inr : forall t ty, Value (Inr t ty)
| Value_Unit : Value Unit.

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

Lemma evplus_split : forall t t' s, t ~>+ t' -> Split t s ~>+ Split t' s.
Proof.
  induction 1.
  apply Evplus_base ; apply ev_split ; auto.
  apply Evplus_next with (t':=Split t' s). auto. 
  apply ev_split. auto. 
Defined.  

Lemma evplus_case : forall t t' s u, t ~>+ t' -> Case t s u ~>+ Case t' s u.
Proof.
  induction 1.
  apply Evplus_base ; apply ev_case ; auto.
  apply Evplus_next with (t':=Case t' s u). auto. 
  apply ev_case. auto. 
Defined.  

Lemma evplus_unfold : forall t t' ty, t ~>+ t' -> Unfold t ty ~>+ Unfold t' ty.
Proof.
  induction 1.
  apply Evplus_base ; apply ev_unfold ; auto.
  apply Evplus_next with (t':=Unfold t' ty). auto. 
  apply ev_unfold. auto. 
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

Lemma evstar_case : forall t t' u v, t ~>* t' -> Case t u v ~>* Case t' u v.
Proof.
  intros t t' u v Hevstar.
  inversion Hevstar ; subst ; [ apply Evstar_refl ; auto | idtac ].
  apply Evstar_plus. apply evplus_case. auto.   
Defined. 

Lemma evstar_split : forall t t' u, t ~>* t' -> Split t u ~>* Split t' u.
Proof.
  intros t t' u Hevstar.
  inversion Hevstar ; subst ; [ apply Evstar_refl ; auto | idtac ].
  apply Evstar_plus. apply evplus_split. auto.   
Defined. 

Lemma evstar_unfold : forall t t' ty, t ~>* t' -> Unfold t ty ~>* Unfold t' ty.
Proof.
  intros t t' ty Hevstar.
  inversion Hevstar ; subst ; [ apply Evstar_refl ; auto | idtac ].
  apply Evstar_plus. apply evplus_unfold. auto.   
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

Lemma evstar_pair : forall f r s u, f ~>* (Pair r s) -> Split f u ~>* sub (sub u 0 (shift 0 r)) 0 s.
Proof. 
  intros f r s u Hev. 
  inversion Hev ; subst.
  apply Evstar_plus ; apply Evplus_base ; apply ev_pair.
  apply Evstar_plus ; apply Evplus_next with (t':=Split (Pair r s) u).
  apply evplus_split. auto.
  apply ev_pair.
Defined. 

Lemma evstar_fold : forall f t ty ty', f ~>* (Fold t ty) -> Unfold f ty' ~>* t.
Proof.
  intros f t ty ty' Hev.
  inversion Hev ; subst.
  apply Evstar_plus ; apply Evplus_base ; apply ev_fold.
  apply Evstar_plus ; apply Evplus_next with (t':=Unfold (Fold t ty) ty').
  apply evplus_unfold. auto.
  apply ev_fold.
Defined. 

Lemma evstar_inl : forall f r s u B, f ~>* (Inl r B) -> Case f s u ~>* sub s 0 r.
Proof. 
  intros f r s u B Hev. 
  inversion Hev ; subst.
  apply Evstar_plus ; apply Evplus_base ; apply ev_inl.
  apply Evstar_plus ; apply Evplus_next with (t':=Case (Inl r B) s u).
  apply evplus_case. auto.
  apply ev_inl.
Defined. 

Lemma evstar_inr : forall f r s u B, f ~>* (Inr r B) -> Case f s u ~>* sub u 0 r.
Proof. 
  intros f r s u B Hev. 
  inversion Hev ; subst.
  apply Evstar_plus ; apply Evplus_base ; apply ev_inr.
  apply Evstar_plus ; apply Evplus_next with (t':=Case (Inr r B) s u).
  apply evplus_case. auto.
  apply ev_inr.
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
              | Pair r s => 
                (fun (Heq : t = Pair r s) => 
                  existT (fun t' : Term => Pair _ _ ~>* t') (Pair r s) _)
              | Inl r ty => 
                (fun (Heq : t = Inl r ty) => 
                  existT (fun t' : Term => Inl _ _ ~>* t') (Inl r ty) _)
              | Inr r ty => 
                (fun (Heq : t = Inr r ty) => 
                  existT (fun t' : Term => Inr _ _ ~>* t') (Inr r ty) _)      
              | Unit => 
                (fun (Heq : t = Unit) => 
                  existT (fun t' : Term => Unit ~>* t') Unit _)
              | Fold s ty => 
                (fun (Heq : t = Fold s ty) => 
                  existT (fun t' : Term => Fold s ty ~>* t') (Fold s ty) _)
              | Unfold f ty => 
                (fun (Heq : t = Unfold f ty) =>
                  match eval bound' f with 
                    | existT s P => 
                      (match s as s0 return (s = s0 -> {t' : Term & Unfold f ty ~>* t'}) with 
                         | (Fold s' ty') => 
                           (fun (Heq : s = Fold s' ty') => 
                             match eval bound' s' with 
                               | existT sub_ev P' => 
                                 existT (fun t' : Term => Unfold f ty ~>* t') sub_ev _
                             end)
                         | _ => (fun (Heq : _) => existT (fun t' : Term => Unfold f ty ~>* t') (Unfold s ty) _)
                       end) (refl_equal s)
                  end)
              | Case f u v =>
                (fun (Heq : t = Case f u v) =>
                  match eval bound' f with 
                    | existT s P => 
                      (match s as s0 return (s = s0 -> {t' : Term & Case f u v ~>* t'}) with 
                         | (Inl s' ty) => 
                           (fun (Heq : s = Inl s' ty) => 
                             match eval bound' (sub u 0 s') with 
                               | existT sub_ev P' => 
                                 existT (fun t' : Term => Case f u v ~>* t') sub_ev _
                             end)
                         | (Inr s' ty) => 
                           (fun (Heq : s = Inr s' ty) => 
                             match eval bound' (sub v 0 s') with 
                               | existT sub_ev P' => 
                                 existT (fun t' : Term => Case f u v ~>* t') sub_ev _
                             end)
                         | _ => (fun (Heq : _) => existT (fun t' : Term => Case f u v ~>* t') (Case s u v) _)
                       end) (refl_equal s)
                  end)
              | Split f u =>                 
                (fun (Heq : t = Split f u) =>
                  match eval bound' f with 
                    | existT s P => 
                      (match s as s0 return (s = s0 -> {t' : Term & Split f u ~>* t'}) with 
                         | (Pair s' t') => 
                           (fun (Heq : s = Pair s' t') => 
                             match eval bound' (sub (sub u 0 (shift 0 s')) 0 t') with 
                               | existT sub_ev P' => 
                                 existT (fun t' : Term => Split f u ~>* t') sub_ev _
                             end)
                         | _ => (fun (Heq : _) => existT (fun t' : Term => Split f u ~>* t') (Split s u) _)
                       end) (refl_equal s)
                  end)
            end) (refl_equal t))
     end) (refl_equal bound)) 
  ; subst 
    ; try (apply evstar_app ; auto) 
      ; try (apply evstar_tapp ; auto)
        ; try (apply evstar_case ; auto) 
          ; try (apply evstar_split ; auto) 
            ; try (apply evstar_unfold ; auto).
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
  (* Fold *) 
  apply Evstar_refl ; auto.
  (* Unfold *) 
  apply evstar_trans with (s:=s').
  apply evstar_fold with (ty:=ty'). auto. auto.
  (* Inl *) 
  apply Evstar_refl ; auto.
  (* Inr *) 
  apply Evstar_refl ; auto.
  (* Case *) 
  apply evstar_trans with (s:=sub u 0 s').
  apply evstar_inl with (B:=ty). auto. auto.
  apply evstar_trans with (s:=sub v 0 s').
  apply evstar_inr with (B:=ty). auto. auto.
  (* Pair *) 
  apply Evstar_refl ; auto.
  (* Split *) 
  apply evstar_trans with (s:=sub (sub u 0 (shift 0 s')) 0 t').
  apply evstar_pair. auto. auto. 
  (* Unit *) 
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
            | Pair r s => Pair r s
            | Inl r ty => Inl r ty
            | Inr r ty => Inr r ty
            | Unit => Unit
            | Fold s ty => Fold s ty
            | Unfold f ty => 
              match eval_weak bound' f with 
                | (Fold s' ty') =>
                  match bound' with 
                    | 0 => Unfold (Fold s' ty') ty
                    | S bound'' => eval_weak bound'' s'
                  end
                | s => Unfold s ty
              end
            | Case f u v =>
              match eval_weak bound' f with 
                | (Inl s' ty) => 
                  match bound' with 
                    | 0 => Case (Inl s' ty) u v
                    | S bound'' => eval_weak bound'' (sub u 0 s')
                  end
                | (Inr s' ty) => 
                  match bound' with 
                    | 0 => Case (Inr s' ty) u v
                    | S bound'' => eval_weak bound'' (sub v 0 s')
                  end
                | s => Case s u v
              end
            | Split f u =>                 
              match eval_weak bound' f with 
                | (Pair s' t') => 
                  match bound' with 
                    | 0 => Split (Pair s' t') u
                    | S bound'' => eval_weak bound'' (sub (sub u 0 (shift 0 s')) 0 t') 
                  end
                | s => Split s u
              end
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
  (* Fold *) 
  subst.
  apply Evstar_refl ; auto.
  (* Unfold *)
  case_eq (eval_weak bound t) ; intros ; 
    try (rewrite H in Hevalw ; subst ; apply compute_eval in H ; apply evstar_unfold with (ty:=t0) ; exact H).
    (* Unfold *) 
    rewrite H in Hevalw. apply compute_eval in H. 
    destruct bound.
      (* Z *)  
      subst. apply evstar_unfold with (ty:=t0). auto.
      (* S bound *) 
      apply compute_eval in Hevalw.
      apply evstar_trans with t1. 
      apply evstar_fold with (ty:=t2). auto. auto.  
  (* Inl *) 
  subst.
  apply Evstar_refl ; auto.
  (* Inr *) 
  subst.
  apply Evstar_refl ; auto.
  (* Case *)
  case_eq (eval_weak bound t1) ; intros ; 
    try (rewrite H in Hevalw ; subst ; apply compute_eval in H ; apply evstar_case ; exact H).
    (* Inl *) 
    rewrite H in Hevalw. apply compute_eval in H. 
    destruct bound.
      (* Z *)  
      subst. apply evstar_case. auto.
      (* S bound *) 
      apply compute_eval in Hevalw.
      apply evstar_trans with (sub t2 0 t). 
      apply evstar_inl with (B:=t0). auto. auto.
    (* Inr *) 
    rewrite H in Hevalw. apply compute_eval in H. 
    destruct bound.
      (* Z *)  
      subst. apply evstar_case. auto.
      (* S bound *) 
      apply compute_eval in Hevalw.
      apply evstar_trans with (sub t3 0 t). 
      apply evstar_inr with (B:=t0). auto. auto.
  (* Pair *) 
  subst.
  apply Evstar_refl ; auto.
  (* Split *) 
  case_eq (eval_weak bound t1) ; intros ; 
    try (rewrite H in Hevalw ; subst ; apply compute_eval in H ; apply evstar_split ; exact H).
    (* Inl *) 
    rewrite H in Hevalw. apply compute_eval in H. 
    destruct bound.
      (* Z *)  
      subst. apply evstar_split. auto.
      (* S bound *) 
      apply compute_eval in Hevalw.
      apply evstar_trans with (sub (sub t2 0 (shift 0 t)) 0 t0). 
      apply evstar_pair. auto. auto.
  (* Unit *) 
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
  inversion HD as [ | |n l t f ty xty Ht Hf | | | | | | | | | | | | |] ; subst.
  apply IHt1 in Hf. apply IHt2 in Ht. 
  apply inl.
  inversion Hf as [Hleft | Hright]. 
    (* Left *) 
    inversion Hleft as [x P]. 
    exists (App x t2). apply ev_app. auto.
    (* Right *)
    inversion Hright as [tyabs | f | | | | | ] ; subst
      ; try  (inversion HD as [ | |n l t' f' ty' xty' Ht' Hf'| | | | | | | | | | | | |] ; subst; inversion Hf' ; fail).
     (* Abs *) 
     exists (sub f 0 t2). apply ev_abs.
  (* TApp *) 
  inversion HD as [ | | | | n l t' ty xty Hv Hall | | | | | | | | | | | ] ; subst.
  apply IHt in Hall. 
  apply inl.
  inversion Hall as [Hleft | Hright]. 
    (* Left *) 
    inversion Hleft as [x P].
    exists (TApp x t0). apply ev_tapp. auto.   
    (* Right *) 
    inversion Hright as [r | abs | | | | | ] ; subst 
      ; try (inversion HD as [ | | | | n l t' ty' xty Hv' Hall' | | | | | | | | | | | ] ; subst ; inversion Hall' ; fail).
      (* Lam *) 
      exists (tysubt r 0 t0).
      apply ev_lam.
  (* Abs *) 
  apply inr. 
  apply Value_Abs.
  (* Lam *) 
  apply inr. 
  apply Value_Lam.
  (* Fold *) 
  apply inr. 
  apply Value_Fold.
  (* Unfold *) 
  inversion HD as [ | | | | | | | | | | | |  n l t' A' val Hf | | n l t' A' val Hf |] ; subst.
    (* Mu *) 
    apply IHt in Hf. 
    apply inl.
    inversion Hf as [Hleft | Hright]. 
    (* Left *) 
    inversion Hleft as [x P].
    exists (Unfold x (Mu A')). apply ev_unfold. auto.   
    (* Right *) 
    inversion Hright as [r | abs | fol | par | inleft | inright | unit ] ; subst
      ; try (inversion HD as [ | | | | | | | | | | | |  n l t'' A'' val' Hf' | | n l t'' A'' val' Hf' |] ; subst ; inversion Hf' ; fail).
      (* Fold *) 
      exists fol.
      apply ev_fold.
    (* Nu *) 
    apply IHt in Hf. 
    apply inl.
    inversion Hf as [Hleft | Hright]. 
    (* Left *) 
    inversion Hleft as [x P].
    exists (Unfold x (Nu A')). apply ev_unfold. auto.   
    (* Right *) 
    inversion Hright as [r | abs | fol | par | inleft | inright | unit ] ; subst
      ; try (inversion HD as [ | | | | | | | | | | | |  n l t'' A'' val' Hf' | | n l t'' A'' val' Hf' |] ; subst ; inversion Hf' ; fail).
      (* Fold *) 
      exists fol.
      apply ev_fold.
  (* Inl *) 
  apply inr. 
  apply Value_Inl.
  (* Inr *) 
  apply inr. 
  apply Value_Inr.
  (* Case *) 
  inversion HD as [ | | | | | | | | | |  n l t u v A' B C Ht Hu Hv  | | | | | ] ; subst.
    apply IHt1 in Ht. 
    apply inl.
    inversion Ht as [Hleft | Hright]. 
    (* Left *) 
    inversion Hleft as [x P].
    exists (Case x t2 t3). apply ev_case. auto.   
    (* Right *) 
    inversion Hright as [r | abs | fol | par | inleft | inright | unit ] ; subst 
      ; try (inversion HD as [ | | | | | | | | | |  n' l' t' u' v' A'' B' C' Ht' Hu' Hv'  | | | | | ] ; subst ; inversion Ht' ; fail).
      (* Inl *) 
      exists (sub t2 0 inleft).
      apply ev_inl.
      (* Inr *) 
      exists (sub t3 0 inright).
      apply ev_inr.
  (* Pair *) 
  apply inr. 
  apply Value_Pair.
  (* Split *) 
  inversion HD as [ | | | | | | | n l t u A' B C Ht Hu | | | | | | | | ] ; subst.
    apply IHt1 in Ht. 
    apply inl.
    inversion Ht as [Hleft | Hright]. 
    (* Left *) 
    inversion Hleft as [x P].
    exists (Split x t2). apply ev_split. auto.   
    (* Right *) 
    inversion Hright as [r | abs | fol | par1 par2 | inleft | inright | unit ] ; subst 
      ; try (inversion HD as [ | | | | | | | n' l' t' u' A'' B' C' Ht' Hu' | | | | | | | | ] ; subst ; inversion Ht' ; fail).
      (* Pair *) 
      exists (sub (sub t2 0 (shift 0 par1)) 0 par2).
      apply ev_pair.
  (* Unit *) 
  apply inr. 
  apply Value_Unit.
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
  inversion H0 ; subst ; inversion e.
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
  inversion HD ; simpl in * ; elimtype False ; firstorder.
  (* App *) 
  elimtype False. apply Hnoreduce.
  inversion HD as [ | | n0 l t f ty xty Hx Hf | | | | | | | | | | | | | ] ; subst.
  apply IHt1 in Hf. 
  inversion Hf ; subst ; 
    try (inversion HD as [ | | n0 l t' f' ty' xty' Hx' Hf' | | | | | | | | | | | | | ] ; inversion Hf' ; fail).
    (* Abs *) 
    exists (sub t 0 t2). apply Evplus_base. apply ev_abs.  
    (* Ev *)
    intros. apply Hnoreduce. 
    inversion H as [x P].
    exists (App x t2). apply evplus_app. auto.
  (* TApp *)   
  elimtype False. apply Hnoreduce.
  inversion HD as [ | | | | n0 l r ty xty Hv Ht | | | | | | | | | | |] ; subst.
  apply IHt in Ht.
  inversion Ht; subst ; 
    try (inversion HD as [ | | | | n0 l r ty' xty Hv' Ht' | | | | | | | | | | |] ; inversion Ht' ; fail).
    (* Lam *) 
    exists (tysubt t1 0 t0). apply Evplus_base. apply ev_lam.
    (* Ev *) 
    intros H.  
    apply Hnoreduce.
    inversion H as [x P]. 
    exists (TApp x t0). apply evplus_tapp. auto.
  (* Abs *) 
  apply Value_Abs.
  (* Lam *) 
  apply Value_Lam.
  (* Fold *) 
  apply Value_Fold.
  (* Unfold *) 
  elimtype False. apply Hnoreduce.
  inversion HD as [ | | | | | | | | | | | |  n l t1 A1 val Hf | | n l t1 A1 val Hf |] ; subst. 
     (* Mu *) 
     apply IHt in Hf.
     inversion Hf; subst ; 
       try (inversion HD as [ | | | | | | | | | | | |  n' l' t1' A1' val' Hf' | | n' l' t1' A1' val' Hf' |] ; inversion Hf' ; fail).
      (* Fold *) 
      exists t0. apply Evplus_base. apply ev_fold.
      (* Ev *) 
      intros H.  
      apply Hnoreduce.
      inversion H as [x P]. 
      exists (Unfold x (Mu A1)). apply evplus_unfold. auto.
     (* Nu *) 
     apply IHt in Hf.
     inversion Hf; subst ; 
       try (inversion HD as [ | | | | | | | | | | | |  n' l' t1' A1' val' Hf' | | n' l' t1' A1' val' Hf' |] ; inversion Hf' ; fail).
      (* Fold *) 
      exists t0. apply Evplus_base. apply ev_fold.
      (* Ev *) 
      intros H.  
      apply Hnoreduce.
      inversion H as [x P]. 
      exists (Unfold x (Nu A1)). apply evplus_unfold. auto.
  (* Inl *) 
  apply Value_Inl.
  (* Inr *) 
  apply Value_Inr.
  (* Case *) 
  elimtype False. apply Hnoreduce.
  inversion HD as [ | | | | | | | | | |  n l t u v A' B C Ht Hu Hv  | | | | | ] ; subst.
  apply IHt1 in Ht.
  inversion Ht; subst ; 
    try (inversion HD as [ | | | | | | | | | |  n' l' t' u' v' A'' B' C' Ht' Hu' Hv'  | | | | | ] ; inversion Ht' ; fail).
      (* Inl *) 
      exists (sub t2 0 t). apply Evplus_base. apply ev_inl.
      (* Inr *) 
      exists (sub t3 0 t). apply Evplus_base. apply ev_inr.
      (* Ev *) 
      intros H.  
      apply Hnoreduce.
      inversion H as [x P]. 
      exists (Case x t2 t3). apply evplus_case. auto.
  (* Pair *) 
  apply Value_Pair ; auto.
  (* Split *)
  elimtype False. apply Hnoreduce.
  inversion HD as [ | | | | | | | n l t u A' B C Ht Hu | | | | | | | | ] ; subst.
  apply IHt1 in Ht.
  inversion Ht; subst ; 
    try (inversion HD as [ | | | | | | | n' l' t' u' A'' B' C' Ht' Hu' | | | | | | | | ] ; inversion Ht' ; fail).
      (* Pair *) 
      exists (sub (sub t2 0 (shift 0 t)) 0 s). apply Evplus_base. apply ev_pair.
      (* Ev *) 
      intros H.  
      apply Hnoreduce.
      inversion H as [x P]. 
      exists (Split x t2). apply evplus_split. auto.
  (* Unit *) 
  apply Value_Unit.
Defined. 

Lemma Value_refl : forall t s A, Derivation Xi [0 ; nil |= t @ A] -> Value t -> t ~>* s -> t = s.
Proof.
  intros t s A Hd Hv Hev. 
  inversion Hv ; inversion Hev ; subst ; auto ; 
    elimtype False ; apply evplus_value_stuck with (s:=s) (A:=A) in Hv 
      ; try (apply Hv ; elimtype False ; apply evplus_value_stuck with (s:=s) (A:=A) in Hv ; apply Hv ; auto ; fail) ; auto.
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
         | ev_fold t ty ty' => _
         | ev_unfold t t' ty Hev' => _
         | ev_inl t r s ty => _ 
         | ev_inr t r s ty => _
         | ev_case t t' r s Hev' => _ 
         | ev_pair t s u => _ 
         | ev_split t t' u Hev' => _
       end) (refl_equal a) (refl_equal b)) ; intros Heqa Heqb ; rewrite Heqa in Hac ; inversion Hac ; subst ;auto.

  (* App *) 
  cut (t' = t'0). intros. subst. auto. 
  apply ev_det with (a:=t) ; auto.
    (* Subcases *) 
    subst. inversion Hab. inversion H0. auto.
    subst. inversion Hac. subst. inversion H2. 
    auto.
 (* Tapp *)
  cut (t' = t'0). intros. rewrite H. auto.
  apply ev_det with (a:=t) ; auto.
    (* subcases *) 
    subst. inversion Hev'.
    subst. inversion Hac. subst. inversion H2.
    auto.
 (* Unfold *)
 inversion Hac. apply refl_equal. subst.
    (* subcases *) 
    subst. inversion H0.
    subst. inversion Hev'.
    cut (t' = t'0). intros. rewrite H. auto.
    apply ev_det with (a:=t) ; auto.
 (* Case *) 
 inversion H3. inversion H3. inversion Hev'. inversion Hev'.
 cut (t' = t'0). intros. rewrite H. auto.
 apply ev_det with (a:=t) ; auto.
 (* Split *) 
 inversion H2. inversion Hev'. 
 cut (t' = t'0). intros. rewrite H. auto.
 apply ev_det with (a:=t) ; auto.
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

(* 
Inductive EvDeep :=
| evdeep_base : forall t t', Ev t t' -> EvDeep t t'
| evdeep_app2 : forall t t' s, Ev s s' -> EvDeep (App t s) (App t s')
| evdeep_abs : forall t s ty, Ev t t' -> EvDeep (Abs ty t) (Abs ty t')
| evdeep_lam : forall t t' ty, Ev t t' -> EvDeep (Lam t) (Lam t').
  *)

End Evaluation. 