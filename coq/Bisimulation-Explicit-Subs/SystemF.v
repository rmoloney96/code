Require Import Arith.
Require Import List. 

Require Import Omega.

Ltac numerical :=
  let XP := fresh "XP" in
    let XW := fresh "XW" in
  match goal with 
    | H : False |- _ => inversion H
    | _ : _ |- context [ eq_nat_dec ?x ?y ] => 
      case_eq (eq_nat_dec x y) ; intros XP XW ; 
        try (rewrite XW in *) ; clear XW ; simpl in * ; numerical
    | _ : _ |- context [ le_lt_dec ?x ?y ] => 
      case_eq (le_lt_dec x y) ; intros XP XW ; 
        try (rewrite XW in *) ; clear XW ; simpl in * ; numerical
    | H : context [ eq_nat_dec ?x ?y ] |- _ => 
      case_eq (eq_nat_dec x y) ; intros XP XW ; 
        rewrite XW in * ; clear XW ; simpl in * ; numerical
    | H : context [ le_lt_dec ?x ?y ] |- _ => 
      case_eq (le_lt_dec x y) ; intros XP XW ; 
            rewrite XW in * ; clear XW ; simpl in * ; numerical
    | _ : _ |- ?x = ?y => auto ; try (elimtype False ; simpl in * ; firstorder ; fail)
    | _ : _ |- context [ False_rec ?x ?y ] => elimtype False ; numerical
(*  | _ : _ |- context [ False_rec ?x ?y ] => elimtype False ; simpl in * ; omega
    | _ : _ |- ?x = ?y => elimtype False ; simpl in * ; omega *)
    | _ : _ |- False => firstorder
    | _ : _ |- _ => auto
  end.

Ltac fast_numerical :=
  match goal with 
    | H : False |- _ => inversion H
    | _ : _ |- context [ eq_nat_dec ?x ?y ] => 
      case (eq_nat_dec x y) ; intros; simpl in * ; subst; fast_numerical
    | _ : _ |- context [ le_lt_dec ?x ?y ] => 
      case (le_lt_dec x y) ; intros;
        simpl in * ; subst; fast_numerical
    | H : context [ eq_nat_dec ?x ?y ] |- _ => 
      case (eq_nat_dec x y) ; intros;
        simpl in * ; subst; fast_numerical
    | H : context [ le_lt_dec ?x ?y ] |- _ => 
      case (le_lt_dec x y) ; intros XP XW ; 
        simpl in * ; subst; fast_numerical
    | _ : _ |- ?x = ?y => auto ; try (elimtype False ; simpl in * ; firstorder ; fail)
    | _ : _ |- context [ False_rec ?x ?y ] => elimtype False ; fast_numerical
    | _ : _ |- False => firstorder
    | _ : _ |- _ => auto
  end.

(*
Require Import Peano.
Require Import Peano_dec.
*) 

Inductive Ty : Set := 
| TV : nat -> Ty
| One : Ty
| Imp : Ty -> Ty -> Ty 
| All : Ty -> Ty
| And : Ty -> Ty -> Ty 
| Or : Ty -> Ty -> Ty 
| Nu : Ty -> Ty
| Mu : Ty -> Ty.

Lemma ty_eq_dec : forall (ty1 ty2 : Ty), {ty1 = ty2} + {ty1 <> ty2}.
Proof. 
  decide equality. decide equality.
Defined.

Inductive Term : Set := 
| F : nat -> Term
| V : nat -> Term 
| App : Term -> Term -> Term 
| TApp : Term -> Ty -> Term
| Abs : Ty -> Term -> Term
| Lam : Term -> Term
| Fold : Term -> Ty -> Term 
| Unfold : Term  -> Ty -> Term 
| Inl : Term -> Ty -> Term 
| Inr : Term -> Ty -> Term 
| Case : Term -> Term -> Term -> Term 
| Pair : Term -> Term -> Term
| Split : Term -> Term -> Term
| Unit : Term 
| Label : Term -> Term -> Term. 

Lemma term_eq_dec : forall (t1 t2 : Term), {t1 = t2} + {t1 <> t2}.
Proof.
  refine (fix term_eq_dec (t1 t2 : Term) : {t1 = t2} + {t1 <> t2} := _) ; destruct t1 ; destruct t2 ; try (right ; congruence).
  (* F *)
  cut ({n = n0} + {n <> n0}) ; [ intros H1 | apply eq_nat_dec ].
  clear term_eq_dec. 
  inversion H1 ; subst ; try (right ; congruence) ; try (left ; auto).
  (* V *)
  cut ({n = n0} + {n <> n0}) ; [ intros H1 | apply eq_nat_dec ].
  clear term_eq_dec. 
  inversion H1 ; subst ; try (right ; congruence) ; try (left ; auto).
  (* App *)
  cut ({t1_1 = t2_1} + {t1_1 <> t2_1}) ; [ intros H1 | apply term_eq_dec ]. 
  cut ({t1_2 = t2_2} + {t1_2 <> t2_2}) ; [ intros H2 | apply term_eq_dec ]. 
  clear term_eq_dec. 
  inversion H1 ; inversion H2 ; subst ; try (right ; congruence) ; try (left ; auto).
  (* TApp *) 
  cut ({t1 = t2} + {t1 <> t2}) ; [ intros H1 | apply term_eq_dec ]. 
  cut ({t = t0} + {t <> t0}) ; [ intros H2 | apply ty_eq_dec ]. 
  clear term_eq_dec. 
  inversion H1 ; inversion H2 ; subst ; try (right ; congruence) ; try (left ; auto).
  (* Abs *) 
  cut ({t1 = t2} + {t1 <> t2}) ; [ intros H1 | apply term_eq_dec ]. 
  cut ({t = t0} + {t <> t0}) ; [ intros H2 | apply ty_eq_dec ]. 
  clear term_eq_dec. 
  inversion H1 ; inversion H2 ; subst ; try (right ; congruence) ; try (left ; auto).
  (* Lam *) 
  cut ({t1 = t2} + {t1 <> t2}) ; [ intros H1 | apply term_eq_dec ]. 
  clear term_eq_dec. 
  inversion H1 ; subst ; try (right ; congruence) ; try (left ; auto).
  (* Fold *) 
  cut ({t1 = t2} + {t1 <> t2}) ; [ intros H1 | apply term_eq_dec ].
  cut ({t = t0} + {t <> t0}) ; [ intros H2 | apply ty_eq_dec ]. 
  clear term_eq_dec. 
  inversion H1 ; inversion H2 ; subst ; try (right ; congruence) ; try (left ; auto).
  (* Unfold *) 
  cut ({t1 = t2} + {t1 <> t2}) ; [ intros H1 | apply term_eq_dec ].
  cut ({t = t0} + {t <> t0}) ; [ intros H2 | apply ty_eq_dec ]. 
  clear term_eq_dec. 
  inversion H1 ; inversion H2 ; subst ; try (right ; congruence) ; try (left ; auto).
  (* Inl *) 
  cut ({t1 = t2} + {t1 <> t2}) ; [ intros H1 | apply term_eq_dec ].
  cut ({t = t0} + {t <> t0}) ; [ intros H2 | apply ty_eq_dec ]. 
  clear term_eq_dec. 
  inversion H1 ; inversion H2 ; subst ; try (right ; congruence) ; try (left ; auto).
  (* Inr *) 
  cut ({t1 = t2} + {t1 <> t2}) ; [ intros H1 | apply term_eq_dec ].
  cut ({t = t0} + {t <> t0}) ; [ intros H2 | apply ty_eq_dec ]. 
  clear term_eq_dec. 
  inversion H1 ; inversion H2 ; subst ; try (right ; congruence) ; try (left ; auto).
  (* Case *) 
  cut ({t1_1 = t2_1} + {t1_1 <> t2_1}) ; [ intros H1 | apply term_eq_dec ].
  cut ({t1_2 = t2_2} + {t1_2 <> t2_2}) ; [ intros H2 | apply term_eq_dec ].
  cut ({t1_3 = t2_3} + {t1_3 <> t2_3}) ; [ intros H3 | apply term_eq_dec ].
  clear term_eq_dec. 
  inversion H1 ; subst ; try (right ; congruence) ;
  inversion H2 ; subst ; try (right ; congruence) ;
  inversion H3 ; subst ; try (right ; congruence) ; try (left ; auto).
  (* Pair *) 
  cut ({t1_1 = t2_1} + {t1_1 <> t2_1}) ; [ intros H1 | apply term_eq_dec ].
  cut ({t1_2 = t2_2} + {t1_2 <> t2_2}) ; [ intros H2 | apply term_eq_dec ].
  inversion H1 ; subst ; try (right ; congruence) ;
  inversion H2 ; subst ; try (right ; congruence) ; try (left ; auto).
  (* Split *) 
  cut ({t1_1 = t2_1} + {t1_1 <> t2_1}) ; [ intros H1 | apply term_eq_dec ].
  cut ({t1_2 = t2_2} + {t1_2 <> t2_2}) ; [ intros H2 | apply term_eq_dec ].
  inversion H1 ; subst ; try (right ; congruence) ;
  inversion H2 ; subst ; try (right ; congruence) ; try (left ; auto).
  (* Unit *) 
  left ; auto.
  (* Label *) 
  cut ({t1_1 = t2_1} + {t1_1 <> t2_1}) ; [ intros H1 | apply term_eq_dec ].
  cut ({t1_2 = t2_2} + {t1_2 <> t2_2}) ; [ intros H2 | apply term_eq_dec ].
  clear term_eq_dec. 
  inversion H1 ; subst ; try (right ; congruence) ;
  inversion H2 ; subst ; try (right ; congruence) ; try (left ; auto).
Defined.

Definition FCtx := nat -> Ty.  

Inductive Ctx : Set := 
| ctx : nat -> list Ty -> Ctx.

Inductive Holds : Set := 
| H : Ctx -> Term -> Ty -> Holds. 

Notation "[ n ; l  |= t @ ty ]" := (H (ctx n l) t ty) (at level 0).
Open Scope list_scope.

Fixpoint tyshiftn (n : nat) (d : nat) (ty : Ty) {struct ty} : Ty := 
  match ty with 
    | TV m => if le_lt_dec d m then TV (n+m) else TV m
    | Imp t s => Imp (tyshiftn n d t) (tyshiftn n d s) 
    | All t => All (tyshiftn n (S d) t) 
    | And t s => And (tyshiftn n d t) (tyshiftn n d s)
    | Or t s => Or (tyshiftn n d t) (tyshiftn n d s)
    | Mu t => Mu (tyshiftn n (S d) t) 
    | Nu t => Nu (tyshiftn n (S d) t) 
    | One => One
  end.

Definition tyshift := tyshiftn 1 0.

Definition tysub : forall (ty : Ty) (n : nat) (s : Ty), Ty.  
Proof.
  refine 
    (fix tysub (ty : Ty) (n : nat) (s : Ty) {struct ty} : Ty := 
      match ty with 
        | TV m => match le_lt_dec n m with 
                    | left p => match eq_nat_dec n m with
                                  | left _ => s 
                                  | right p' => 
                                    (match m as m' return (m = m' -> Ty) with 
                                      | 0 => (fun p'' => False_rec _ _)
                                      | S m' => (fun _ => TV m')
                                     end) (refl_equal m)
                                end
                    | right _ => TV m
                  end
        | Imp ty1 ty2 => Imp (tysub ty1 n s) (tysub ty2 n s) 
        | All t => All (tysub t (S n) (tyshift s))
        | Mu t => Mu (tysub t (S n) (tyshift s))
        | Nu t => Nu (tysub t (S n) (tyshift s))
        | One => One
        | And ty1 ty2 => And (tysub ty1 n s) (tysub ty2 n s) 
        | Or ty1 ty2 => Or (tysub ty1 n s) (tysub ty2 n s) 
      end).
  destruct m. apply le_n_O_eq in p. apply p'. auto. inversion p''.
Defined.

Fixpoint tysubt (t : Term) (n : nat) (s : Ty) {struct t} : Term := 
  match t with 
    | F m => F m
    | V m => V m
    | Abs ty t => Abs (tysub ty n s) (tysubt t n s)
    | Lam t => Lam (tysubt t (S n) (tyshift s))
    | App f g => App (tysubt f n s) (tysubt g n s)
    | TApp f ty => TApp (tysubt f n s) (tysub ty n s)
    | Inl t ty => Inl (tysubt t n s) (tysub ty n s)
    | Inr t ty => Inr (tysubt t n s) (tysub ty n s)
    | Case t u v => Case (tysubt t n s) (tysubt u n s) (tysubt v n s)
    | Pair t u => Pair (tysubt t n s) (tysubt u n s)
    | Split t u => Split (tysubt t n s) (tysubt u n s)
    | Fold t ty => Fold (tysubt t n s) (tysub ty n s)
    | Unfold t ty => Unfold (tysubt t n s) (tysub ty n s)
    | Unit => Unit
    | Label t u => Label (tysubt t n s) (tysubt u n s)
  end.

Fixpoint valid (ty : Ty) (n : nat) {struct ty} : Prop := 
  match ty with 
    | TV m => 
      if le_lt_dec n m
        then False
        else True
    | Imp s t => valid s n /\ valid t n
    | Or s t => valid s n /\ valid t n
    | And s t => valid s n /\ valid t n
    | One => True
    | All t => valid t (S n)
    | Nu t => valid t (S n) 
    | Mu t => valid t (S n)       
  end.

Definition valid_dec : forall (ty : Ty) (n : nat), {valid ty n}+{~ valid ty n}.
Proof. 
  induction ty ; intros. 
  (* TV *)
  case_eq (le_lt_dec n0 n). 
  intros. right. simpl. rewrite H0. auto.
  intros. left. simpl. rewrite H0. auto.
  (* One *) 
  firstorder. 
  (* Imp *)
  firstorder.
  (* All *) 
  firstorder.
  (* And *) 
  firstorder.
  (* Or *) 
  firstorder.
  (* Nu *) 
  firstorder.
  (* Mu *) 
  firstorder. 
Defined.

Lemma valid_weaken : forall ty n m, 
  n <= m -> valid ty n -> valid ty m.
Proof.
  induction ty ; simpl ; intros ; numerical || firstorder.
Defined. 

Lemma tyshift_level : forall ty1 n m, 
  valid ty1 n -> valid (tyshiftn 1 m ty1) (S n).
Proof.
  induction ty1 ; simpl ; intros ; numerical ; destruct n ; numerical || firstorder.
Qed.

Lemma tysub_level : forall ty1 ty2 n, 
  valid ty1 (S n) -> valid ty2 n -> valid (tysub ty1 n ty2) n.
Proof.
  induction ty1 ; simpl ; intros ; numerical.
  (* TV *)
  destruct n ; numerical ; firstorder.
  firstorder.
  (* All *) 
  apply IHty1. auto. unfold tyshift.
  apply tyshift_level. auto.
  
  firstorder.
  firstorder.

  (* Mu *) 
  apply IHty1. auto. unfold tyshift.
  apply tyshift_level. auto.
  
  (* Nu *) 
  apply IHty1. auto. unfold tyshift.
  apply tyshift_level. auto.
Qed.

Lemma tysub_level_gen : forall ty1 ty2 m n, 
  m <= n -> valid ty1 (S n) -> valid ty2 n -> valid (tysub ty1 m ty2) n.
Proof.
  induction ty1 ; simpl ; intros ; numerical. 
  (* TV *)
  destruct n ; numerical. 
  firstorder.
  (* All *) 
  apply IHty1. firstorder.  auto.  
  apply tyshift_level. auto.

  firstorder. 
  
  (* Mu *)
  inversion H1 ; split. 
  apply IHty1_1 ; firstorder.
  apply IHty1_2 ; firstorder.

  (* Mu *) 
  apply IHty1. firstorder.  auto.  
  apply tyshift_level. auto.

  (* Nu *) 
  apply IHty1. firstorder.  auto.  
  apply tyshift_level. auto.
Qed.

Lemma tysub_level_Z : forall ty1 ty2 n, 
  valid ty1 (S n) -> valid ty2 n -> valid (tysub ty1 0 ty2) n.
Proof.
  intros; apply tysub_level_gen ; firstorder.
Defined.  

Section Program. 

(* Part of the program assumption *) 
Variable Xi : nat -> Ty.  
Variable ProgTy : forall m, valid (Xi m) 0.

CoInductive Derivation : Holds -> Set := 
| FunIntro : forall n m l, 
  Derivation [n ; l |= F m @ Xi m]
| ImpIntro : forall n l t ty xty,
  valid xty n ->
  Derivation [n ; xty::l |= t @ ty] -> 
  Derivation [n ; l |= (Abs xty t) @ (Imp xty ty)]
| ImpElim : forall n l t f ty xty,
  Derivation [n ; l |= t @ xty] ->
  Derivation [n ; l |= f @ (Imp xty ty)] -> 
  Derivation [n ; l |= (App f t) @ ty]
| AllIntro : forall n l t ty,
  Derivation [S n ; map tyshift l |= t @ ty] -> 
  Derivation [n ; l |= (Lam t) @ All ty]
| AllElim : forall n l t ty xty,
  valid xty n ->
  Derivation [n ; l |= t @ All ty] -> 
  Derivation [n ; l |= TApp t xty @ (tysub ty 0 xty)]
| VarIntro : forall n l ty i,
  valid ty n -> i < length l -> nth i l One = ty ->
  Derivation [n ; l |= V i @ ty]
| AndIntro : forall n l t s A B, 
  Derivation [n ; l |= t @ A] -> 
  Derivation [n ; l |= s @ B] -> 
  Derivation [n ; l |= Pair t s @ And A B]
| AndElim : forall n l t s A B C, 
  Derivation [n ; l |= t @ And A B] ->
  Derivation [n ; A::B::l |= s @ C] -> 
  Derivation [n ; l |= Split t s @ C]
| OrIntroL : forall n l t A B, 
  valid B n -> 
  Derivation [n ; l |= t @ A] -> 
  Derivation [n ; l |= Inl t B @ Or A B]
| OrIntroR : forall n l t A B, 
  valid A n -> 
  Derivation [n ; l |= t @ B] -> 
  Derivation [n ; l |= Inr t A @ Or A B]
| OrElim : forall n l t u v A B C, 
  Derivation [n ; l |= t @ Or A B] ->
  Derivation [n ; A::l |= u @ C] ->
  Derivation [n ; B::l |= v @ C] ->
  Derivation [n ; l |= Case t u v @ C]
| MuIntro : forall n l t A, 
  valid A (S n) ->
  Derivation [n ; l |= t @ tysub A 0 (Mu A) ] -> 
  Derivation [n ; l |= Fold t (Mu A) @ Mu A ]
| MuElim : forall n l t A, 
  valid A (S n) ->
  Derivation [n ; l |= t @ Mu A] -> 
  Derivation [n ; l |= Unfold t (Mu A) @ tysub A 0 (Mu A)]
| NuIntro : forall n l t A, 
  valid A (S n) ->
  Derivation [n ; l |= t @ tysub A 0 (Nu A) ] -> 
  Derivation [n ; l |= Fold t (Nu A) @ Nu A ]
| NuElim : forall n l t A, 
  valid A (S n) ->
  Derivation [n ; l |= t @ Nu A] -> 
  Derivation [n ; l |= Unfold t (Nu A) @ tysub A 0 (Nu A)]
| OneIntro : forall n l, 
  Derivation [n ; l |= Unit @ One]
| Label : forall n l, 
  Derivation [n ; l |= t @ A ] -> t ~> s -> Derivation [n ; l |= label t s @ A ]

(* This is the program assumption - If these hypotheses are met - we can proove weak soundness *) 
Variable Delta : nat -> Term. 
Variable Prog : forall n l m, Derivation [n ; l |= F m @ Xi m] -> Derivation [n ; l |= Delta m @ Xi m]. 

Lemma type_valid_at_n : forall t n l ty, Derivation [n ; l |= t @ ty] -> valid ty n.
Proof.
  induction t.
  (* F *) 
  intros ; inversion H0 ; subst. 
  apply valid_weaken with (n:=0). firstorder. apply ProgTy. 
  (* V *) 
  intros. inversion H0. auto.
  (* App *) 
  intros. inversion H0 ; subst. 
  apply IHt1 in H7. simpl in H7.  inversion H7. auto.  
  (* TApp *) 
  intros. inversion H0. 
  subst. apply IHt in H7. simpl in *. 
  apply tysub_level_Z. auto. auto. 
  (* Abs *) 
  intros. inversion H0 ; subst.
  simpl. split ; auto. apply IHt in H7. auto.
  (* Lam *) 
  intros. inversion H0 ; subst.
  simpl. apply IHt in H2. auto.
  (* Fold *)
  intros. inversion H0 ; subst.
    (* Mu *) 
    simpl. auto.  
    (* Nu *)
    simpl. auto.
  (* Unfold *)
  intros. inversion H0 ; subst.
    (* Mu *) 
    apply tysub_level_gen. firstorder. auto. 
    apply IHt with (l:=l). auto. 
    (* Nu *)
    apply tysub_level_gen. firstorder. auto. 
    apply IHt with (l:=l). auto.
  (* Inl *) 
  intros. inversion H0 ; subst.
  simpl ; split ; auto. apply IHt with (l:=l) ; auto.
  (* Inr *) 
  intros. inversion H0 ; subst.
  simpl ; split ; auto. apply IHt with (l:=l) ; auto.
  (* Case *) 
  intros. inversion H0 ; subst.
  apply IHt3 in H9. auto.
  (* Pair *) 
  intros. inversion H0 ; subst. 
  simpl ; split. 
  apply IHt1 with (l:=l) ; auto.
  apply IHt2 with (l:=l) ; auto.
  (* Split *) 
  intros. inversion H0 ; subst.
  apply IHt2 in H7. auto.
  (* Unit *) 
  intros ; inversion H0 ; subst ; simpl ; auto.
Defined.   

Fixpoint typeof (n : nat) (l : list Ty) (t : Term) {struct t} : option Ty := 
  match t with 
    | F m => Some (Xi m)
    | V n' => 
      if le_lt_dec (length l) n' 
        then None 
        else (fun ty => 
          if valid_dec ty n
            then Some ty 
            else None) (nth n' l One)
    | App r s => 
      (fun mrty msty => 
        match mrty,msty with 
          | Some (Imp xty yty),Some xty' => 
            if ty_eq_dec xty' xty 
              then Some yty
              else None
          | _,_ => None
        end) (typeof n l r) (typeof n l s)
    | TApp r ty => 
      (fun mrty => 
        match mrty with 
          | Some (All ty') =>
            if valid_dec ty n 
              then if valid_dec ty' (S n) 
                then Some (tysub ty' 0 ty)
                else None
              else None
          | _ => None
        end) (typeof n l r)
    | Abs ty r => 
      (fun mrty => 
        match mrty with 
          | Some ty' => 
            if valid_dec ty n
              then Some (Imp ty ty')
              else None
          | _ => None
        end) (typeof n (ty::l) r)
    | Lam r => 
      (fun mrty => 
        match mrty with 
          | Some ty' =>
            if valid_dec ty' (S n) 
              then Some (All ty')
              else None
          | _ => None
        end) (typeof (S n) (map tyshift l) r)
    | Pair r s => 
      (fun mrty msty => 
        match mrty,msty with 
          | Some A,Some B => Some (And A B)
          | _,_ => None
        end) (typeof n l r) (typeof n l s)
    | Split r s => 
      (fun mrty => 
        match mrty with 
          | Some (And A B) => typeof n (A::B::l) s
          | _ => None
        end) (typeof n l r) 
    | Inl t B => 
      (fun mrty => 
        match mrty with 
          | Some A => 
            if valid_dec B n
              then Some (Or A B)
              else None
          | _ => None
        end) (typeof n l t)
    | Inr t A => 
      (fun mrty => 
        match mrty with 
          | Some B => 
            if valid_dec A n
              then Some (Or A B)
              else None
          | _ => None
        end) (typeof n l t)
    | Case t u v => 
      (fun mrty => 
        match mrty with 
          | Some (Or A B) => 
            (fun muty mvty => 
              match muty,mvty with 
                | Some C, Some C' => 
                  if ty_eq_dec C C' 
                    then Some C
                    else None
                | _,_ => None
              end) (typeof n (A::l) u) (typeof n (B::l) v)
          | _ => None
        end) (typeof n l t)
    | Fold s A => 
      (fun mrty => 
        match A,mrty with 
          | Mu A', Some A'' => 
            if valid_dec A' (S n) 
              then if ty_eq_dec A'' (tysub A' 0 (Mu A'))
                then Some (Mu A')
                else None
              else None
          | Nu A', Some A'' => 
            if valid_dec A' (S n)
              then if ty_eq_dec A'' (tysub A' 0 (Nu A'))
                then Some (Nu A')
                else None
              else None                
          | _,_ => None
        end) (typeof n l s) 
    | Unfold s A => 
      (fun mrty => 
        match A, mrty with 
          | Mu A', Some (Mu A'') => 
            if valid_dec A'' (S n) 
              then if ty_eq_dec A' A''
                then Some (tysub A' 0 (Mu A'))
                else None
              else None
          | Nu A', Some (Nu A'') => 
            if valid_dec A'' (S n)
              then if ty_eq_dec A' A''
                then Some (tysub A' 0 (Nu A'))
                else None
              else None
          | _,_ => None
        end) (typeof n l s) 
    | Unit => Some One
  end.

Require Import Sumbool.

Theorem typeof_has_derivation : 
  forall t n l ty, 
    typeof n l t = Some ty -> Derivation [n ; l |= t @ ty].
Proof.
  induction t ; intros.
  (* F *) 
  simpl in H0. inversion H0.  
  apply FunIntro.
  
  (* V *)
  simpl in H0.
  case_eq (le_lt_dec (length l) n) ; 
    intros Ple Hle ; try (rewrite Hle in *) ; try congruence.
  case_eq (valid_dec (nth n l One) n0) ; 
    intros Pval Hval ; try (rewrite Hval in *) ; try congruence.
  apply VarIntro ; auto ; try congruence.

  (* App *)
  simpl in H0.
  case_eq (typeof n l t1) ; intros ; try (rewrite H1 in *) ; try congruence ;
    destruct t ; try congruence.
  case_eq (typeof n l t2) ; intros ; try (rewrite H2 in *) ; try congruence.
  case_eq (ty_eq_dec t t3) ; intros ; try (rewrite H3 in *) ; try congruence.  
  inversion H0.  
  eapply (ImpElim n l t2 t1 ty t3). 
  apply IHt2. rewrite <- e. auto.
  apply IHt1. rewrite <- H5. auto. 
  
  (* TApp *)
  intros. simpl in H0.
  case_eq (typeof n l t). intros. rewrite H1 in H0.
  destruct t1 ; try congruence. 
  case_eq (valid_dec t0 n) ; intros ; try (rewrite H2 in *) ; try congruence.
  case_eq (valid_dec t1 (S n)) ; intros ; try (rewrite H3 in *) ; try congruence.
  inversion H0. subst.
  apply AllElim. auto. auto.
  intros. rewrite H1 in H0. inversion H0.   
  
  (* Abs *) 
  simpl in H0. case_eq (typeof n (t::l) t0) ; intros ; try (rewrite H1 in *) ; try congruence. 
  case_eq (valid_dec t n) ; intros ; try (rewrite H2 in *) ; try congruence.
  inversion H0.
  eapply ImpIntro. auto. apply IHt. auto.

  (* Lam *)
  simpl in H0. case_eq (typeof (S n) (map tyshift l) t) ; intros ; try (rewrite H1 in *) ; try congruence.
  case_eq (valid_dec t0 (S n)). intros. rewrite H2 in H0. inversion H0.
  eapply AllIntro. apply IHt in H1. auto.
  intros. rewrite H2 in H0. inversion H0.

  (* Fold *)
  simpl in H0. destruct t0 ; try congruence.
    (* Nu *)
    case_eq (typeof n l t) ; intros ; try (rewrite H1 in H0 ; simpl) ; try congruence.
    case_eq (valid_dec t0 (S n)) ; intros; try (rewrite H2 in H0 ; simpl) ; try congruence.
    case_eq (ty_eq_dec t1 (tysub t0 0 (Nu t0))) ; intros; try (rewrite H3 in H0 ; simpl) ; try congruence.
    inversion H0. 
    apply NuIntro. auto. apply IHt. rewrite <- e. auto.
   (* Mu *)
    case_eq (typeof n l t) ; intros ; try (rewrite H1 in H0 ; simpl) ; try congruence.
    case_eq (valid_dec t0 (S n)) ; intros; try (rewrite H2 in H0 ; simpl) ; try congruence.
    case_eq (ty_eq_dec t1 (tysub t0 0 (Mu t0))) ; intros; try (rewrite H3 in H0 ; simpl) ; try congruence.
    inversion H0. 
    apply MuIntro. auto. apply IHt. rewrite <- e. auto.
  (* Fold *)
  simpl in H0.
  destruct t0 ; try congruence.
    (* Nu *)
    case_eq (typeof n l t) ; intros ; try (rewrite H1 in H0 ; simpl) ; try congruence.
    destruct t1 ; try congruence.
    case_eq (valid_dec t1 (S n)) ; intros; try (rewrite H2 in H0 ; simpl) ; try congruence.
    case_eq (ty_eq_dec t0 t1) ; intros; try (rewrite H3 in H0 ; simpl) ; try congruence.
    inversion H0. rewrite e.
    apply NuElim ; auto. 
    (* Mu *)
    case_eq (typeof n l t) ; intros ; try (rewrite H1 in H0 ; simpl) ; try congruence.
    destruct t1 ; try congruence.
    case_eq (valid_dec t1 (S n)) ; intros; try (rewrite H2 in H0 ; simpl) ; try congruence.
    case_eq (ty_eq_dec t0 t1) ; intros; try (rewrite H3 in H0 ; simpl) ; try congruence.
    inversion H0. rewrite e.
    apply MuElim ; auto. 
  (* Inl *) 
  simpl in H0. 
  case_eq (typeof n l t) ; intros ; try (rewrite H1 in H0 ; simpl) ; try congruence.
  case_eq (valid_dec t0 n) ; intros ; try (rewrite H2 in H0 ; simpl) ; try congruence.
  inversion H0. subst.
  apply OrIntroL; auto.
  (* Inr *) 
  simpl in H0. 
  case_eq (typeof n l t) ; intros ; try (rewrite H1 in H0 ; simpl) ; try congruence.
  case_eq (valid_dec t0 n) ; intros ; try (rewrite H2 in H0 ; simpl) ; try congruence.
  inversion H0. subst.
  apply OrIntroR; auto.
  (* Case *) 
  simpl in H0.
  case_eq (typeof n l t1) ; intros ; try (rewrite H1 in H0 ; simpl) ; try congruence.
  destruct t ; try congruence.
  case_eq (typeof n (t4::l) t2) ; intros ; try (rewrite H2 in H0 ; simpl) ; try congruence.
  case_eq (typeof n (t5::l) t3) ; intros ; try (rewrite H3 in H0 ; simpl) ; try congruence.
  case_eq (ty_eq_dec t t0) ; intros ; try (rewrite H4 in H0 ; simpl) ; try congruence.
  inversion H0.
  apply OrElim with (A:=t4) (B:=t5); auto. 
  apply IHt2. rewrite H6 in H2. auto. 
  apply IHt3. rewrite <- H6. rewrite <- e in H3. auto.
  (* Pair *) 
  simpl in H0.
  case_eq (typeof n l t1) ; intros ; try (rewrite H1 in H0 ; simpl) ; try congruence.
  case_eq (typeof n l t2) ; intros ; try (rewrite H2 in H0 ; simpl) ; try congruence.
  inversion H0. 
  apply AndIntro. apply IHt1. auto. apply IHt2. auto.
  (* Split *) 
  simpl in H0.
  case_eq (typeof n l t1) ; intros ; try (rewrite H1 in H0 ; simpl) ; try congruence.
  destruct t ; try congruence.
  apply AndElim with (A:=t3) (B:=t4). 
  apply IHt1 ; auto.
  apply IHt2 ; auto.
  (* Unit *) 
  simpl in H0. inversion H0. subst.
  apply OneIntro.
Defined. 
  
Fixpoint shiftn (n : nat) (d : nat) (t : Term) {struct t} : Term := 
  match t with 
    | F m => F m
    | V m => if le_lt_dec d m then V (n+m) else V m
    | App r s => App (shiftn n d r) (shiftn n d s) 
    | Lam r => Lam (shiftn n d r)
    | Abs ty r => Abs ty (shiftn n (1+d) r)
    | TApp r ty => TApp (shiftn n d r) ty
    | Fold r ty => Fold (shiftn n d r) ty
    | Unfold r ty => Unfold (shiftn n d r) ty
    | Pair r s => Pair (shiftn n d r) (shiftn n d s)
    | Split r s => Split (shiftn n d r) (shiftn n (2+d) s)
    | Inl r ty => Inl (shiftn n d r) ty    
    | Inr r ty => Inr (shiftn n d r) ty
    | Case r u v => Case (shiftn n d r) (shiftn n (1+d) u) (shiftn n (1+d) v)
    | Unit => Unit 
  end.

Definition shift := shiftn 1.
Hint Unfold shift. 

Fixpoint tyshift_term (d : nat) (t : Term) {struct t} : Term := 
  match t with 
    | F m => F m 
    | V m => V m 
    | App r s => App (tyshift_term d r) (tyshift_term d s) 
    | Lam r => Lam (tyshift_term (S d) r)
    | Abs ty r => Abs (tyshiftn 1 d ty) (tyshift_term d r)
    | TApp r ty => TApp (tyshift_term d r) (tyshiftn 1 d ty)
    | Fold t ty => Fold (tyshift_term d t) (tyshiftn 1 d ty) 
    | Unfold t ty => Unfold (tyshift_term d t) (tyshiftn 1 d ty) 
    | Inr t ty => Inr (tyshift_term d t) (tyshiftn 1 d ty)
    | Inl t ty => Inl (tyshift_term d t) (tyshiftn 1 d ty)
    | Case t u v => Case (tyshift_term d t) (tyshift_term d u) (tyshift_term d v)
    | Pair t s => Pair (tyshift_term d t) (tyshift_term d s) 
    | Split t s => Split (tyshift_term d t) (tyshift_term d s) 
    | Unit => Unit  
  end.

Definition sub : forall (t : Term) (n : nat) (s : Term), Term.
Proof. 
  refine 
    (fix sub (t : Term) (n : nat) (s : Term) {struct t} : Term := 
      match t with 
        | F m => F m
        | V m => match le_lt_dec n m with 
                   | left p => match eq_nat_dec n m with 
                                 | left p' => s
                                 | right p' => 
                                   (match m as m' return (m = m' -> Term) with 
                                      | 0 => (fun p'' => False_rec _ _)
                                      | S m' => (fun _ => V m')
                                    end) (refl_equal m)
                               end
                   | right p => V m
                 end
        | Abs ty r => Abs ty (sub r (S n) (shift 0 s))
        | Lam r => Lam (sub r n (tyshift_term 0 s))
        | App f g => App (sub f n s) (sub g n s) 
        | TApp r ty => TApp (sub r n s) ty
        | Fold r ty => Fold (sub r n s) ty
        | Unfold r ty => Unfold (sub r n s) ty
        | Pair r u => Pair (sub r n s) (sub u n s) 
        | Split r u => Split (sub r n s) (sub u (S (S n)) (shiftn 2 0 s))
        | Inl r ty => Inl (sub r n s) ty 
        | Inr r ty => Inr (sub r n s) ty 
        | Case r u v => Case (sub r n s) (sub u (S n) (shift 0 s)) (sub v (S n) (shift 0 s))
        | Unit => Unit
      end). destruct m. apply le_n_O_eq in p. apply p'. auto. inversion p''.
Defined.

Lemma nth_sameL : forall A a (l:list A) G d i, 
  i < length G -> 
  nth i (G++(a::l)) d = nth i (G++l) d.
Proof.
  induction G. intros. inversion H0.
  intros. destruct i.
  simpl. auto. simpl. apply IHG. simpl in H0.
  apply lt_S_n. auto.
Defined.
 
Lemma nth_sameR : forall A i a (l:list A) G d, 
  length G < S i -> 
  nth (S i) (G++(a::l)) d = nth i (G++l) d.
Proof.
  refine
    (fix nth_sameR A i a (l G:list A) d (H: length G < S i) {struct G} : nth (S i) (G++(a::l)) d = nth i (G++l) d := 
      (match G as G' return (G = G' -> nth (S i) (G++(a::l)) d = nth i (G++l) d) with 
         | nil => _
         | cons a g => _
       end) (refl_equal G)).
  intros. rewrite H1 in *. simpl. auto.
  intros. rewrite H1 in *. simpl. 
  destruct i. simpl in H0. unfold lt in H0. apply le_S_n in H0.
  apply le_n_O_eq in H0. inversion H0. 
  apply nth_sameR.
  simpl in H0. unfold lt in H0. apply le_S_n in H0.
  unfold lt. auto.
Defined.
 
Lemma one_longer : 
  forall A i (G :list A) xty l, (S i) < S (length (G ++ xty :: l)) -> i < S (length (G++l)).
Proof.
  intros. rewrite app_length in H0. simpl in H0.
  rewrite plus_comm in H0. simpl in H0.
  unfold lt in *. apply le_S_n in H0.
  rewrite app_length. rewrite plus_comm. auto.
Defined.

Lemma strengthenG_gt : forall i n l G xty ty, 
  length G < S i -> 
  Derivation [n ; G ++ xty::l |= V (S i) @ ty] -> 
  Derivation [n ; G ++ l |= V i @ ty].
Proof.
  intros i n l G xty ty Hlength HD.
  inversion HD. 
  rewrite nth_sameR in H6.
  apply VarIntro. auto.  
  induction G. simpl in *.
  firstorder. simpl in *. 
  apply one_longer in H5. auto. auto. auto.
Defined.

Lemma strengthenG_lt : forall i n l G xty ty, 
  i < length G -> 
  Derivation [n ; G ++ xty::l |= V i @ ty] -> 
  Derivation [n ; G ++ l |= V i @ ty].
Proof.
  intros. inversion H1. subst. 
  apply VarIntro ; auto. 
  rewrite app_length. 
  unfold lt in *.
  apply le_plus_trans. auto.
  rewrite nth_sameL. auto. auto.
Defined.

Definition weakenG_lt : forall i G n L ty xty,
  i < length G -> 
  Derivation [n; G ++ L |= V i @ ty] ->
  Derivation [n; G ++ xty :: L |= V i @ ty].
Proof. 
  intros.
  apply VarIntro ; auto. apply type_valid_at_n in H1. auto.
  rewrite app_length.
  apply lt_plus_trans. auto.
  inversion H1; subst. simpl in *.
  apply nth_sameL. auto.
Defined.

Definition weakenG_gt : forall i G n L ty xty,
  length G < (S i) -> 
  Derivation [n; G ++ L |= V i @ ty] ->
  Derivation [n; G ++ xty :: L |= V (S i) @ ty].
Proof. 
  intros.
  inversion H1 ; subst.
  apply VarIntro ; auto. rewrite app_length in *. 
  simpl. rewrite plus_comm. simpl.
  apply lt_n_S. rewrite plus_comm. auto.
  apply nth_sameR. auto.
Defined.

Lemma nth_append : forall G xty l, nth (length G) (G ++ xty :: l) One = xty.
Proof.
  induction G. intros. simpl. auto.
  intros. simpl. apply IHG. 
Defined.

Lemma hole_at_i : forall i j k, 
  shift j (V i) = (V k) -> (~ j = k).
Proof. 
  intros. unfold shift in * ; simpl in *. 
  case_eq (le_lt_dec j i).
  intros. rewrite H1 in H0. clear H1. 
  unfold not. intros.
  rewrite <- H1 in H0. inversion H0.
  rewrite <- H3 in l.
  apply (le_Sn_n i). firstorder.
  intros. rewrite H1 in H0. clear H1.
  inversion H0. rewrite H2 in *.
  unfold not. intro. rewrite H1 in l.
  apply (lt_irrefl k). auto.
Defined.

Lemma shift_var : forall n i G L xty ty, 
  Derivation [n; G ++ L |= V i @ ty] -> 
  Derivation [n; G ++ xty :: L |= shift (length G) (V i) @ ty].
Proof. 
  intros. unfold shift.
  case_eq (shiftn 1 (length G) (V i)) ;   try (intros ;simpl in H1 ; destruct (le_lt_dec (length G) i) ; auto ; inversion H1 ; fail).
 
  (* Var *) 
  intros. 
  cut (shiftn 1 (length G) (V i) = V n0). intros Hdup.
  simpl in H1.                                           
  destruct (le_lt_dec (length G) i) ; auto ; inversion H1.
  apply hole_at_i in Hdup. 
  apply weakenG_gt.
  unfold lt in *. apply le_n_S. auto.
  auto. 
  subst. 
  apply weakenG_lt. auto. auto. 
  auto.
Defined.

Lemma shift_correct : forall n s xty ty G L, 
  Derivation [n; G ++ L |= s @ ty] ->
  Derivation [n; G ++ (xty :: L) |= shift (length G) s @ ty].
Proof.
    refine 
      (fix shift_correct (n : nat) (s : Term) (xty ty : Ty) (G L : list Ty)
        (D : Derivation [n; G ++ L |= s @ ty]) {struct s}:
        Derivation [n; G ++ (xty :: L) |= shift (length G) s @ ty] := 
        (match s as s'
           return (s = s' -> Derivation [n; G ++ (xty :: L) |= shift (length G) s @ ty])
           with 
           | F m => _
           | V i => _
           | Unit => _
           | Abs ty r => _
           | Lam t => _
           | App r s => _
           | TApp r ty' => _
           | Pair r s => _
           | Split u v => _
           | Unfold r ty => _
           | Fold r ty => _ 
           | Inl r ty => _
           | Inr r ty => _ 
           | Case r u v => _
         end) (refl_equal s)) ; intros ; subst.

    (* F *) 
    inversion D. 
    simpl ; subst. 
    apply FunIntro.
  
    (* V *)
    inversion D. 
    apply shift_var. exact D.

    (* App *)
    simpl.
    inversion D ; subst.
    apply ImpElim with (xty:=xty0).
    apply shift_correct ; clear shift_correct ; auto.
    apply shift_correct ; clear shift_correct ; auto.

    (* TApp *)
    simpl. 
    inversion D ; subst.
    apply AllElim. auto. 
    apply shift_correct ; clear shift_correct. auto.  

    (* Abs *)
    simpl.
    inversion D ; subst. unfold shift. 
    apply ImpIntro. auto. fold shiftn.
    simpl.
    cut (length  (ty0 :: G) = (S (length G))).
    intros. rewrite <- H0.
    rewrite app_comm_cons.
    apply shift_correct with (G:=(ty0::G)) (ty:=ty1).
    rewrite <- app_comm_cons.
    auto. simpl. auto.

    (* Lam *) 
    simpl. 
    inversion D ; subst.
    apply AllIntro.
    cut (length G = length (map tyshift G)).
    intros. rewrite H0.
    rewrite map_app. simpl.
    apply shift_correct.
    rewrite <- map_app. auto.
    rewrite map_length. auto.

    (* Fold *) 
    unfold shift. inversion D. 
      (* Mu *) 
      simpl. apply MuIntro. auto. auto.
      (* Nu *) 
      simpl. apply NuIntro. auto. auto.
    
    (* Unfold *) 
    unfold shift. inversion D.
      (* Mu *) 
      simpl. apply MuElim. auto. auto.
      (* Nu *) 
      simpl. apply NuElim. auto. auto.
 
   (* Inl *) 
   unfold shift ; inversion D ; simpl ; apply OrIntroL ; auto.

   (* Inr *) 
   unfold shift ; inversion D ; simpl ; apply OrIntroR ; auto.

   (* Case *) 
   unfold shift ; inversion D ; simpl ; apply OrElim with (A:=A) (B:=B); auto ; subst. 
   cut (S (length G) = length  (A :: G)) ; [ idtac | auto ]. intros.
   cut (A :: G ++ xty :: L = (A :: G) ++ xty :: L) ; [ idtac | auto ]. intros. rewrite H1.
   rewrite H0. fold shift. apply shift_correct ; auto. 
   cut (S (length G) = length  (B :: G)) ; [ idtac | auto ]. intros. 
   cut (B :: G ++ xty :: L = (B :: G) ++ xty :: L) ; [ idtac | auto ]. intros. rewrite H1.
   rewrite H0. fold shift. apply shift_correct ; auto. 

   (* Pair *) 
   unfold shift ; inversion D ; simpl ; apply AndIntro ; auto.
 
   (* Split *) 
   unfold shift ; inversion D ; simpl ; apply AndElim with (A:=A) (B:=B); auto ; subst. 
   cut (S (S (length G)) = length  (A :: B :: G)) ; [ idtac | auto ]. intros.
   cut (A :: B :: G ++ xty :: L = (A :: B :: G) ++ xty :: L) ; [idtac | auto ]. intros. rewrite H1.
   rewrite H0. fold shift ; apply shift_correct ; auto.
 
   inversion D ; simpl ; apply OneIntro.
 
Defined.

Lemma shift_shift_shiftn2 : forall s  m,
 shift m (shift m s) = shiftn 2 m s.
Proof. 
  unfold shift ; induction s ; simpl ; intros ; auto ; numerical ; 
    try (rewrite IHs ; auto ; fail) ; 
      try (rewrite IHs1 ; rewrite IHs2 ; auto ; rewrite IHs3 ; auto ; fail).
Defined.

Theorem tyhole_at_i : forall i j k, 
  tyshiftn 1 j (TV i) = (TV k) -> (~ j = k).
Proof. 
  intros. unfold tyshiftn in *.
  case_eq (le_lt_dec j i). 
  intros. rewrite H1 in H0. inversion H0.
  clear H1.
  apply le_n_S in l. 
  unfold not. intros. rewrite H1 in l.
  apply le_S_n in l. apply (le_Sn_n i). auto.
  intros. rewrite H1 in H0. clear H1.
  inversion H0. unfold not. intros.
  subst. apply (lt_irrefl k). auto.
Qed.

Lemma tyshift_natural : forall G n m, 
  nth n (map (tyshiftn 1 m) G) One = tyshiftn 1 m (nth n G One).
Proof.
  induction G. simpl. intros. destruct n ; auto.
  intros. simpl. destruct n ; auto.
Qed.

Lemma tyshift_comm : forall xty m n,
  m <= n ->
  tyshiftn 1 (S n) (tyshiftn 1 m xty) = tyshiftn 1 m (tyshiftn 1 n xty).
Proof.
  induction xty ; intros ; simpl ; numerical. 

  destruct n; numerical.
  
  rewrite IHxty2. rewrite IHxty1. auto. auto. auto.
  
  rewrite IHxty. auto. firstorder.

  rewrite IHxty1 ; [ idtac | auto ]; rewrite IHxty2 ; [ idtac | auto ] ; auto.

  rewrite IHxty1 ; [ idtac | auto ]; rewrite IHxty2 ; [ idtac | auto ] ; auto.

  rewrite IHxty ; auto. firstorder.

  rewrite IHxty ; auto. firstorder.
Qed.

Lemma tyshift_tyshift_map  : forall m G,
  map (tyshiftn 1 0) (map (tyshiftn 1 m) G) = map (tyshiftn 1 (S m)) (map (tyshiftn 1 0) G).
Proof.
  induction G. simpl. auto. simpl.
  rewrite tyshift_comm. rewrite IHG. auto. 
  apply (le_O_n m). 
Defined.

Lemma tyshift_tysubL : forall ty m n xty,
  m <= n ->
  tyshiftn 1 m (tysub ty n xty) = tysub (tyshiftn 1 m ty) (S n) (tyshiftn 1 m xty).
Proof.
  induction ty ; intros ; simpl ; numerical. 

  destruct n ; unfold tyshift ; simpl ; numerical. 
  destruct n ; unfold tyshift ; simpl ; numerical. 

  rewrite IHty1. rewrite IHty2. auto. auto. auto. 

  rewrite IHty. unfold tyshift.
  rewrite tyshift_comm. auto.  
  firstorder. firstorder.

  rewrite IHty1 ; [ idtac | auto ] ; rewrite IHty2 ; auto.

  rewrite IHty1 ; [ idtac | auto ] ; rewrite IHty2 ; auto.

  rewrite IHty ; [ unfold tyshift ; rewrite tyshift_comm ; auto | auto ] ; firstorder.

  rewrite IHty ; [ unfold tyshift ; rewrite tyshift_comm ; auto | auto ] ; firstorder.
  
Qed.

Lemma tyshift_tysubR : forall ty m n xty,
  n <= m ->xb
  tyshiftn 1 m (tysub ty n xty) = tysub (tyshiftn 1 (S m) ty) n (tyshiftn 1 m xty).
Proof.
  induction ty ; intros ; simpl ; numerical.
  destruct n ; unfold tyshift ; simpl ; numerical. 
  destruct n ; unfold tyshift ; simpl ; numerical. 
  destruct n ; unfold tyshift ; simpl ; numerical.

  rewrite IHty1. rewrite IHty2. auto. auto. auto. 

  rewrite IHty. unfold tyshift.
  rewrite tyshift_comm ; auto ; firstorder. firstorder.

  rewrite IHty1 ; [ idtac | auto ] ; rewrite IHty2 ; auto.

  rewrite IHty1 ; [ idtac | auto ] ; rewrite IHty2 ; auto.

  rewrite IHty ; unfold tyshift ; [ idtac | firstorder ] ; rewrite tyshift_comm ; auto. firstorder.

  rewrite IHty ; unfold tyshift ; [ idtac | firstorder ] ; rewrite tyshift_comm ; auto. firstorder.
Qed.

Lemma tyshiftn_closed_id : forall ty l n m, 
  n <= m -> valid ty n -> tyshiftn l m ty = ty.
Proof.
  induction ty.
  (* TV *) 
  intros; simpl in * ; numerical.

  (* Unit *) 
  intros ; simpl in * ; auto.
 
  (* Imp *) 
  intros. simpl in *.
  inversion H1.
  apply (IHty1 l n m H0) in H2. 
  apply (IHty2 l n m H0) in H3.
  rewrite H2. rewrite H3. auto.

  (* All *) 
  intros. simpl in *.
  apply (IHty l (S n) (S m)) in H1.
  rewrite H1. auto. firstorder.

  (* And *) 
  intros. simpl in *.
  rewrite (IHty1 l n m). 
  rewrite (IHty2 l n m).  auto. auto. firstorder. firstorder. firstorder.

  (* Or *) 
  intros. simpl in *.
  rewrite (IHty1 l n m). 
  rewrite (IHty2 l n m).  auto. auto. firstorder. firstorder. firstorder.

  (* Nu *) 
  intros. simpl in *.
  apply (IHty l (S n) (S m)) in H1. rewrite H1. auto. firstorder.

  (* Mu *) 
  intros. simpl in *.
  apply (IHty l (S n) (S m)) in H1. rewrite H1. auto. firstorder.
Defined.

Lemma tysub_closed_id : forall ty xty n m, 
  n <= m -> valid ty n -> tysub ty m xty = ty.
Proof.
  induction ty.
  (* TV *) 
  intros ; simpl in * ; numerical.

  (* Unit *)
  intros ; auto.
 
  (* Imp *)
  intros ; simpl in *.
  inversion H1.
  apply (IHty1 xty n m H0) in H2. 
  apply (IHty2 xty n m H0) in H3.
  rewrite H2. rewrite H3. auto.

  (* All *) 
  intros. simpl in *.
  apply (IHty (tyshift xty) (S n) (S m)) in H1.
  rewrite H1. auto. firstorder.

  (* And *)
  intros ; simpl in * ; rewrite IHty1 with (n:=n) ; [ idtac | firstorder | firstorder ] ; rewrite IHty2 with (n:=n) ; firstorder.  

  (* Or *)
  intros ; simpl in * ; rewrite IHty1 with (n:=n) ; [ idtac | firstorder | firstorder ] ; rewrite IHty2 with (n:=n) ; firstorder.

  (* Mu *) 
  intros ; simpl in * ; rewrite IHty with (n:=S n) ; firstorder.

  (* Nu *) 
  intros ; simpl in * ; rewrite IHty with (n:=S n) ; firstorder.
Defined.

Lemma tyshift_correct : forall s n m G xty, 
  Derivation [n+m; G |= s @ xty] ->
  Derivation [S (n+m); map (tyshiftn 1 m) G |= tyshift_term m s @ tyshiftn 1 m xty].
Proof.
  induction s ; intros.

  (* F *)
  inversion H0. 
  rewrite tyshiftn_closed_id with (n:=0). simpl. 
  apply FunIntro. firstorder. apply ProgTy.
  
  (* V *) 
  inversion H0. subst. simpl.
  apply VarIntro ; auto.
  apply tyshift_level. auto. 
  rewrite map_length. auto.
  apply tyshift_natural.

  (* App *)
  inversion H0. subst. simpl.
  apply ImpElim with (xty:=tyshiftn 1 m xty0).
  apply IHs2. auto.
  cut (Imp (tyshiftn 1 m xty0) (tyshiftn 1 m xty) = tyshiftn 1 m (Imp xty0 xty)).
  intros. rewrite H1. apply IHs1. auto. simpl. auto.
  
  (* TApp *) 
  simpl.
  inversion H0 ; subst.
  rewrite tyshift_tysubR.
  apply AllElim. 
  apply tyshift_level. auto.
  change (All (tyshiftn 1 (S m) ty)) with (tyshiftn 1 m (All ty)). 
  apply IHs. auto. 
  apply (le_O_n m). 

  (* Abs *) 
  simpl. inversion H0 ; subst.
  simpl. apply ImpIntro. 
  apply tyshift_level. auto.
  change (tyshiftn 1 m t :: map (tyshiftn 1 m) G) with (map (tyshiftn 1 m) (t :: G)).
  apply IHs. auto.
  
  (* Lam *) 
  simpl. inversion H0 ; subst. 
  simpl. apply AllIntro. intros. unfold tyshift.
  rewrite tyshift_tyshift_map.
  intros.
  change (S (S (n + m))) with (S ((S n) + m)).
  rewrite plus_Snm_nSm.  
  apply IHs. auto. 
  rewrite <- plus_Snm_nSm. auto.

  (* Fold *) 
  simpl. inversion H0 ; subst. 
    (* Mu *) 
    apply MuIntro. fold tyshiftn. apply tyshift_level. auto.
    fold tyshiftn. 
    change (Mu (tyshiftn 1 (S m) A)) with (tyshiftn 1 m (Mu A)).
    rewrite <- tyshift_tysubR.
    change (Mu (tyshiftn 1 (S m) A)) with (tyshiftn 1 m (Mu A)).
    apply IHs. auto. firstorder.
    (* Nu *) 
    apply NuIntro. fold tyshiftn. apply tyshift_level. auto.
    fold tyshiftn. 
    change (Nu (tyshiftn 1 (S m) A)) with (tyshiftn 1 m (Nu A)).
    rewrite <- tyshift_tysubR.
    change (Nu (tyshiftn 1 (S m) A)) with (tyshiftn 1 m (Nu A)).
    apply IHs. auto. firstorder.

  (* Unfold *) 
  simpl. inversion H0 ; subst. simpl.  
      (* Mu *) 
      rewrite tyshift_tysubR. simpl. apply MuElim. 
      apply tyshift_level. auto. 
      change (Mu (tyshiftn 1 (S m) A)) with (tyshiftn 1 m (Mu A)).
      apply IHs ; auto.  firstorder.
      (* Mu *) 
      rewrite tyshift_tysubR. simpl. apply NuElim. 
      apply tyshift_level. auto. 
      change (Nu (tyshiftn 1 (S m) A)) with (tyshiftn 1 m (Nu A)).
      apply IHs ; auto.  firstorder.
       
  (* Inl *) 
  simpl ; inversion H0 ; subst ; simpl ; apply OrIntroL. apply tyshift_level ; auto. apply IHs. auto.  

  (* Inr *) 
  simpl ; inversion H0 ; subst ; simpl ; apply OrIntroR. apply tyshift_level ; auto. apply IHs. auto.

  (* Case *) 
  simpl ; inversion H0 ; subst ; simpl ; apply OrElim with (A:=tyshiftn 1 m A) (B:=tyshiftn 1 m B).
  change (Or (tyshiftn 1 m A) (tyshiftn 1 m B)) with (tyshiftn 1 m (Or A B)).
  apply IHs1. auto.
  change (tyshiftn 1 m A :: map (tyshiftn 1 m) G) with (map (tyshiftn 1 m) (A :: G)). 
  apply IHs2. auto. 
  change (tyshiftn 1 m B :: map (tyshiftn 1 m) G) with (map (tyshiftn 1 m) (B :: G)). 
  apply IHs3. auto.

  (* Pair *)  
  simpl ; inversion H0 ; subst ; simpl ; apply AndIntro. 
  apply IHs1. auto. 
  apply IHs2. auto.

  (* Split *) 
  simpl ; inversion H0 ; subst ; simpl ; apply AndElim with (A:=tyshiftn 1 m A) (B:=tyshiftn 1 m B).
  change (And (tyshiftn 1 m A) (tyshiftn 1 m B)) with (tyshiftn 1 m (And A B)).
  apply IHs1. auto. 
  change (tyshiftn 1 m A :: tyshiftn 1 m B :: map (tyshiftn 1 m) G) with (map (tyshiftn 1 m) (A :: (B :: G))).
  apply IHs2. auto. 

  (* Unit *) 
  inversion H0 ; subst. apply OneIntro. 
Qed.

Theorem sub_preservation : forall t s n xty ty G L,
  Derivation [n ; G++xty::L |= t @ ty] -> 
  Derivation [n ; G++L |= s @ xty] -> 
  Derivation [n ; G++L |= sub t (length G) s @ ty].
Proof. 
  induction t.
  (* FunIntro*)
  intros. simpl.
  inversion H0; subst.
  apply FunIntro ; auto.

  (* VarIntro *)
  intros. unfold sub.
  case_eq (le_lt_dec (length G) n) ; intros. 
  case_eq (eq_nat_dec (length G) n). intros. rewrite <- e in H0. 
  inversion H0. 
  rewrite nth_append in H10. rewrite <- H10. auto.
  destruct n. simpl in *.
  intros. elimtype False. clear H2. clear H3.
  apply le_n_O_eq in l. unfold not in n. apply n. auto. 
  intros. 
  
  apply strengthenG_gt with (xty:=xty). clear H2.
  apply le_lt_or_eq in l. inversion l ; auto. clear H3.
  rewrite H2 in n1. unfold not in n1.
  elimtype False. apply n1. auto.

  exact H0.

  apply strengthenG_lt with (xty:=xty). auto. auto. 

  (* ImpElim *)
  intros. simpl.
  inversion H0. subst. 
  apply ImpElim with (xty:=xty0). eapply IHt2. eexact H4.
  exact H1. eapply IHt1. eexact H8. auto.

  (* AllElim *)
  intros. simpl.
  inversion H0. subst.
  apply AllElim. auto. auto. apply IHt with (xty:=xty). auto. auto.
  
  (* ImpIntro *) 
  intros. simpl. 
  inversion H0. subst.
  apply ImpIntro. auto. 
  cut (S (length G) = (length (t::G))).
  intros. rewrite H2. 
  rewrite app_comm_cons.
  apply IHt with (G := (t :: G)) (xty:=xty). auto.
  rewrite <- app_comm_cons. 
  cut (t::G++L = nil++(t::G++L)).
  intros. rewrite H3.
  
  apply shift_correct with (G:=(nil (A:=Ty))). 
  simpl. auto. auto. auto. 

  (* AllIntro *)
  intros. simpl in *.
  inversion H0 ; subst.
  apply AllIntro.
  cut (n+0 = n). intro Hpz. rewrite <- Hpz in H1. 
  apply tyshift_correct in H1. simpl in H1.
  cut (length (map (tyshiftn 1 0) G) = length G). intros.
  rewrite <- H2.
  rewrite map_app. 
  apply IHt with (xty:=tyshiftn 1 0 xty).
  rewrite map_app in H3. simpl in H3. auto. 
  rewrite map_app in H1. 
  rewrite <- Hpz. auto. 
  apply map_length. simpl. auto.

  (* Fold *) 
  intros. inversion H0; subst. 
     (* Mu *) 
     apply MuIntro. auto. fold sub. apply IHt with (xty:=xty). auto. auto.       
     (* Nu *) 
     apply NuIntro. auto. fold sub. apply IHt with (xty:=xty). auto. auto.

  (* Unfold *) 
  intros. inversion H0 ; subst ; simpl. 
     (* Mu *) 
     apply MuElim ; auto. apply IHt with (xty:=xty); auto.   
     (* Nu *) 
     apply NuElim ; auto. apply IHt with (xty:=xty); auto.

  (* Inl *) 
  intros. inversion H0 ; subst ; simpl.
  apply OrIntroL ; auto ; apply IHt with (xty:=xty) ; auto. 

  (* Inr *) 
  intros. inversion H0 ; subst ; simpl.
  apply OrIntroR ; auto ; apply IHt with (xty:=xty) ; auto.

  (* Case *)  
  intros. inversion H0 ; subst ; simpl.
  apply OrElim with (A:=A) (B:=B). 
  apply IHt1 with (xty:=xty). auto. auto. 
  change (A::G ++ L) with ((A::G)++L).
  apply IHt2 with (xty:=xty). simpl. auto. simpl. 
  apply shift_correct with (G:=(nil (A:=Ty))). simpl. auto.
  change (B::G ++ L) with ((B::G)++L).
  apply IHt3 with (xty:=xty). simpl. auto. simpl. 
  apply shift_correct with (G:=(nil (A:=Ty))). simpl. auto.

  (* Pair *) 
  intros ; simpl ; inversion H0 ; subst.  
  apply AndIntro. apply IHt1 with (xty:=xty) ; auto. apply IHt2 with (xty:=xty) ; auto.

  (* Split *) 
  intros ; simpl ; inversion H0 ; subst.
  apply AndElim with (A:=A) (B:=B). 
  apply IHt1 with (xty:=xty). auto. auto.
  change (A::B::G ++ L) with ((A::B::G)++L).
  change (S (S (length G))) with (length (A::B::G)). 
  eapply IHt2 with (xty:=xty). auto.
  rewrite <- shift_shift_shiftn2. 
  simpl. 
  apply shift_correct with (G:=(nil (A:=Ty))). simpl. 
  apply shift_correct with (G:=(nil (A:=Ty))). simpl. 
  auto.

  intros ; simpl. inversion H0. apply OneIntro.

Defined.

Theorem sub_preservation_basic : forall n L t s xty ty, 
  Derivation [n ; xty::L |= t @ ty] -> 
  Derivation [n ; L |= s @ xty] -> 
  Derivation [n ; L |= sub t 0 s @ ty].
Proof.
  intros.
  change L with (nil++L).
  change 0 with (length  (A:=Ty) nil).
  apply sub_preservation with (xty:=xty). simpl. auto. 
  simpl. auto.
Defined.

Theorem type_unique : forall n L t ty1 ty2, 
  Derivation [n ; L |= t @ ty1] -> Derivation [n ; L |= t @ ty2] 
  -> ty1 = ty2. 
Proof.
  refine 
    (fix type_unique n l (t : Term) ty1 ty2 
      (d1 : Derivation [n ; l |= t @ ty1])
      (d2 : Derivation [n ; l |= t @ ty2]) {struct t} 
      : ty1 = ty2 :=
      (match t as t' return (t = t' -> ty1 = ty2)
         with
         | F n => _ 
         | V n => _
         | App f g => _ 
         | Abs ty r => _ 
         | TApp r ty => _
         | Lam r => _
         | Fold r ty => _ 
         | Unfold r ty => _ 
         | Pair r s => _ 
         | Split u v => _ 
         | Inr r ty => _ 
         | Inl r ty => _ 
         | Case r u v => _ 
         | Unit => _
       end) (refl_equal t)) ; intros ; subst ; inversion d1 ; inversion d2 ; subst ; auto.

  (* App *) 
  apply type_unique with (ty1:=xty) (ty2:=xty0) in H2 ; 
    apply type_unique with (ty1:=Imp xty ty1) (ty2:=Imp xty0 ty2) in H6.  
  subst. inversion H6. auto. auto. auto. auto.

  (* TApp *) 
  apply type_unique with (ty1:=All ty0) (ty2:=All ty3) in H6.
  inversion H6. auto. auto.

  (* Abs *) 
  apply type_unique with (ty1:=ty0) (ty2:=ty3) in H6.
  subst ; auto. auto. 

  (* Lam *)
  apply type_unique with (ty1:=ty) (ty2:=ty0) in H6.
  subst ; auto. auto.

  (* Unfold *) 
  apply type_unique with (ty1:=Mu A0) (ty2:=Mu A) in H6.
  subst ; auto. auto. inversion H6 ; auto. auto.  
  inversion H11. inversion H11. 
  apply type_unique with (ty1:=Nu A0) (ty2:=Nu A) in H6.
  subst ; auto. auto. inversion H6 ; auto. auto.

  (* Inl *) 
  apply type_unique with (ty1:=A) (ty2:=A0) in H6.
  subst ; auto. auto.

  (* Inr *)
  apply type_unique with (ty1:=B) (ty2:=B0) in H6.
  subst ; auto. auto.

  (* case *)   
  apply type_unique with (ty1:=Or A B) (ty2:=Or A0 B0) in H3.
  inversion H3 ; subst ; auto. 
  apply type_unique with (ty1:=ty1) (ty2:=ty2) in H7 ; auto.
  auto.

  (* pair *) 
  apply type_unique with (ty1:=A) (ty2:=A0) in H2 ; auto.
  apply type_unique with (ty1:=B) (ty2:=B0) in H6 ; auto.
  subst ; auto.

  (* split *) 
  apply type_unique with (ty1:=And A B) (ty2:=And A0 B0) in H2 ; auto.
  inversion H2 ; subst.
  apply type_unique with (ty1:=ty1) (ty2:=ty2) in H6. auto. auto.  
Defined.

Theorem tysub_tyshift_id : forall a m ty, 
  tysub (tyshiftn 1 m a) m ty = a.
Proof. 
  induction a ; intros ; simpl ; try numerical ; 
    try ( rewrite (IHa1 m ty) ; rewrite (IHa2 m ty) ; auto) ;
      try (unfold tyshift ; rewrite (IHa (S m) (tyshiftn 1 0 ty)) ; auto).
Qed.

Lemma tysub_tyshift_map_id : forall l m ty,  map (fun t => tysub t m ty) (map (tyshiftn 1 m) l) = l.
Proof.
  induction l; intros m ty.
  simpl. auto.
  simpl. rewrite tysub_tyshift_id.
  rewrite IHl. auto.
Defined.

Theorem nth_tysub_tyshift : forall l n m ty ty0,
  nth n (map (tyshiftn 1 m) l) One = ty -> 
  nth n l One = tysub ty m ty0.
Proof.
  induction l.
  intros. simpl in *.
  destruct n ; subst ; simpl ; auto.

  intros.
  destruct n. simpl in H0. 
  simpl. subst.
  rewrite (tysub_tyshift_id a m ty0). auto.

  simpl. apply IHl. simpl in H0. auto.
Defined.

Lemma tyshiftn_z_id : forall ty n, tyshiftn 0 n ty = ty. 
Proof.
  induction ty ; intros ; simpl ; numerical ; 
    try (rewrite IHty ; auto) ; 
      try (rewrite IHty1 ; rewrite IHty2 ; auto).
Defined. 

Lemma tyhole_in : forall n m k ty, 
  tyshiftn (S n) m ty = (TV k) -> k > m+n \/ k < m.
Proof.
  intros ; simpl in H0 ; destruct ty ; simpl in * ; 
    try numerical ; 
      try (inversion H0 ; firstorder).
Defined.

Lemma tysub_into_hole : forall ty n m k ty',
  k <= m+n /\ k >= m ->
  tysub (tyshiftn (S n) m ty) k ty' = tyshiftn n m ty.
Proof.
  induction ty ; intros ; simpl ;
    [ numerical | | | | | | | ] ;  
    auto ;
      try (rewrite IHty ; firstorder) ;
        try (rewrite IHty1 ; firstorder ; rewrite IHty2 ; firstorder). 
Defined.  

Lemma nth_tysub_map : forall l n m ty1, nth n (map (fun ty : Ty => tysub ty m ty1) l) One =
  tysub (nth n l One) m ty1.
Proof.
  induction l ; auto.
  intros. simpl. destruct n ; auto.
  intros. simpl. destruct n. auto. 
  apply IHl. 
Defined. 
  
Lemma commute_tysub_tyshift_maps : forall l tyx m, map tyshift (map (fun ty : Ty => tysub ty m tyx) l)  = 
  map (fun ty => tysub ty (S m) (tyshift tyx)) (map tyshift l).
Proof. 
  induction l ; intros.
  simpl. auto.
  simpl.
  cut (tyshift (tysub a m tyx) = tysub (tyshift a) (S m) (tyshift tyx)).
  intros Heq; rewrite Heq. 
  rewrite IHl. auto. 
  unfold tyshift.
  rewrite tyshift_tysubL. auto. firstorder.
Defined.

Lemma tysub_comm : forall ty0 t0 tyx n m, 
  n <= m -> 
  tysub (tysub ty0 n t0) m tyx =
  tysub (tysub ty0 (S m) (tyshiftn 1 n tyx)) n (tysub t0 m tyx).
Proof.
  induction ty0 ; intros t0 tyx n0 m Hle.
  simpl ; fast_numerical ; destruct n ; simpl; fast_numerical.
  unfold tyshift ; rewrite tysub_into_hole ; try (rewrite tyshiftn_z_id ); firstorder.
  destruct n ; simpl; fast_numerical.
  (* One *) 
  simpl. auto.  
  (* App *) 
  simpl.
  rewrite IHty0_1. rewrite IHty0_2. auto. auto. auto.
  (* All *) 
  simpl.
  unfold tyshift.
  rewrite IHty0.  
  rewrite tyshift_comm.
  rewrite tyshift_tysubL.
  auto. firstorder. firstorder. firstorder.
  (* And *) 
  simpl.
  rewrite IHty0_1. rewrite IHty0_2. auto. auto. auto.
  (* Or *) 
  simpl.
  rewrite IHty0_1. rewrite IHty0_2. auto. auto. auto.
  (* Nu *) 
  simpl.
  unfold tyshift.
  rewrite IHty0.  
  rewrite tyshift_comm.
  rewrite tyshift_tysubL.
  auto. firstorder. firstorder. firstorder.
  (* Mu *) 
  simpl.
  unfold tyshift.
  rewrite IHty0.  
  rewrite tyshift_comm.
  rewrite tyshift_tysubL.
  auto. firstorder. firstorder. firstorder.
Defined. 

Lemma tysub_all : forall t ty tyx n m l,
  valid tyx (n+m) -> 
  Derivation [S (n+m); l |= t @ ty] -> 
  Derivation [(n+m); map (fun ty => tysub ty m tyx) l |= tysubt t m tyx @ tysub ty m tyx].
Proof. 
  induction t; intros ty tyx n0 m l HV HD.
  
  (* F *) 
  inversion HD ; subst. simpl.  
  rewrite tysub_closed_id with (n:=0).
  apply FunIntro. firstorder. apply ProgTy.

  (* V *) 
  inversion HD. subst. 
  apply VarIntro. 
  apply tysub_level_gen. firstorder. auto. auto.
  rewrite map_length. auto. 
  (* change (tysub (nth n l One) m tyx) with ((fun ty => tysub ty m tyx) (nth n l One)). *)
  rewrite <- (map_nth (fun ty : Ty => tysub ty m tyx)). simpl. auto.   

  (* App *) 
  inversion HD. subst. 
  apply ImpElim with (xty := (tysub xty m tyx)). 
  apply IHt2. auto. auto. 
  change (Imp (tysub xty m tyx) (tysub ty m tyx)) with (tysub (Imp xty ty) m tyx).
  apply IHt1. auto. auto.
  (* TApp *) 
  inversion HD ; subst. 
  rewrite tysub_comm. fold tyshift.
  apply AllElim. auto.
  apply tysub_level_gen. firstorder. auto. auto.
  fold tysubt.
  change (All (tysub ty0 (S m) (tyshift tyx))) with (tysub (All ty0) m tyx).
  apply IHt. auto. auto. firstorder. 
  (* Abs *) 
  inversion HD ; subst.
  simpl. 
  apply ImpIntro. 
  apply tysub_level_gen. firstorder. auto. auto. 
  change (tysub t m tyx :: map (fun ty : Ty => tysub ty m tyx) l) with 
    (map (fun ty : Ty => tysub ty m tyx) (t::l)).
  apply IHt. auto. auto.
  (* Lam *)
  inversion HD. subst. 
  simpl. 
  apply AllIntro. 
  rewrite commute_tysub_tyshift_maps.
  change (S (n0 + m)) with (S n0 + m).
  rewrite plus_Snm_nSm.
  apply IHt. fold tyshift.
  rewrite <- plus_Snm_nSm.
  apply tyshift_level. fold plus. auto. 
  rewrite <- plus_Snm_nSm.
  auto.
  (* Fold *)
  inversion HD ; subst. simpl.
    (* Mu *) 
    apply IHt with (tyx:= tyx) in H6.
    apply MuIntro. 
    apply tysub_level_gen. firstorder.  auto.  
    apply tyshift_level. auto.
    rewrite tysub_comm in H6. fold tyshift in H6. 
    change (Mu (tysub A (S m) (tyshift tyx))) with (tysub (Mu A) m tyx). auto.
    firstorder. auto.
    (* Nu *)
    apply IHt with (tyx:= tyx) in H6.
    apply NuIntro. 
    apply tysub_level_gen. firstorder.  auto.  
    apply tyshift_level. auto.
    rewrite tysub_comm in H6. fold tyshift in H6. 
    change (Nu (tysub A (S m) (tyshift tyx))) with (tysub (Nu A) m tyx). auto.
    firstorder. auto.
  (* Unfold *) 
  inversion HD ; subst. simpl.
    (* Mu *) 
    apply IHt with (tyx:= tyx) in H6.
    rewrite tysub_comm. 
    apply MuElim. 
    apply tysub_level_gen. firstorder.  auto.  
    apply tyshift_level. auto.
    change (Mu (tysub A (S m) (tyshift tyx))) with (tysub (Mu A) m tyx). auto.
    firstorder. auto.
    (* Nu *) 
    apply IHt with (tyx:= tyx) in H6.
    rewrite tysub_comm. 
    apply NuElim. 
    apply tysub_level_gen. firstorder.  auto.  
    apply tyshift_level. auto.
    change (Nu (tysub A (S m) (tyshift tyx))) with (tysub (Nu A) m tyx). auto.
    firstorder. auto.
  (* Inl *) 
  inversion HD. subst. 
  apply OrIntroL. fold tysub.
  apply tysub_level_gen. firstorder.  auto.  auto.
  fold tysub. fold tysubt.
  apply IHt. auto. auto. 
  (* Inr *) 
  inversion HD. subst. 
  apply OrIntroR. fold tysub.
  apply tysub_level_gen. firstorder.  auto.  auto.
  fold tysub. fold tysubt.
  apply IHt. auto. auto. 
  (* Case *) 
  inversion HD ;subst. simpl.
  apply OrElim with (A:=tysub A m tyx) (B:=tysub B m tyx). 
  change (Or (tysub A m tyx) (tysub B m tyx)) with (tysub (Or A B) m tyx). 
  apply IHt1. auto. auto.
    (* inl *) 
    change (tysub A m tyx :: map (fun ty : Ty => tysub ty m tyx) l) with 
    (map (fun ty : Ty => tysub ty m tyx) (A::l)).
    apply IHt2. auto. auto. 
    (* inr *) 
    change (tysub B m tyx :: map (fun ty : Ty => tysub ty m tyx) l) with 
    (map (fun ty : Ty => tysub ty m tyx) (B::l)).
    apply IHt3. auto. auto. 
  (* Pair *) 
  simpl ; inversion HD ; subst.
  change (tysub (And A B) m tyx) with (And (tysub A m tyx) (tysub B m tyx)).
  apply AndIntro.
  apply IHt1 ; auto.  
  apply IHt2 ; auto.
  (* Split *) 
  simpl ; inversion HD ; subst.
  apply AndElim with (A:=tysub A m tyx) (B:=tysub B m tyx). 
  change (And (tysub A m tyx) (tysub B m tyx)) with (tysub (And A B) m tyx). 
  apply IHt1 ; auto.
    (* term *)
    change (tysub A m tyx :: tysub B m tyx :: map (fun ty : Ty => tysub ty m tyx) l) with 
    (map (fun ty : Ty => tysub ty m tyx) (A::B::l)).
    apply IHt2. auto. auto.
  (* Unit *) 
  inversion HD; simpl ; auto.  
  apply OneIntro; auto.
Defined.

Lemma tysub_derivation : forall t n m l ty tyx, 
  valid tyx (n+m) -> 
  Derivation [S (n+m); map (tyshiftn 1 m) l |=t @ ty] -> 
  Derivation [(n+m); l |=tysubt t m tyx @ tysub ty m tyx].
Proof. 
  induction t ; intros n0 m l ty tyx HV HD.
  (* F *) 
  inversion HD ; subst ; simpl.
  rewrite tysub_closed_id with (n:=0) ; firstorder. 
  apply FunIntro. 
  
  (* V *) 
  inversion HD ; subst ; simpl. 
  apply VarIntro. 
  apply tysub_level_gen ; firstorder.
  rewrite map_length in H5. auto.
  rewrite <- nth_tysub_map.
  rewrite tysub_tyshift_map_id with (m :=m) (ty:=tyx). auto.

  (* App *) 
  inversion HD ; subst ; simpl.
  apply ImpElim with (xty := tysub xty m tyx).
  apply IHt2 ; auto.
  change (Imp (tysub xty m tyx) (tysub ty m tyx)) with (tysub (Imp xty ty) m tyx).
  apply IHt1 ; auto. 
 
  (* TApp *)
  inversion HD. subst. 
  simpl. 
  rewrite tysub_comm. fold tyshift.
  apply AllElim. 
  apply tysub_level_gen. firstorder. auto. auto. 
  change (All (tysub ty0 (S m) (tyshift tyx))) with (tysub (All ty0) m tyx).
  apply IHt. auto. auto. firstorder. 
  
  (* Abs *) 
  inversion HD ; subst ; simpl.
  apply ImpIntro.
  apply tysub_level_gen ; firstorder.
  cut (l = map (fun t => tysub t m tyx) (map (tyshiftn 1 m) l)).
  intros Heq. rewrite Heq. 
  change (tysub t m tyx :: map (fun t1 : Ty => tysub t1 m tyx) (map (tyshiftn 1 m) l)) with 
    (map (fun t1 : Ty => tysub t1 m tyx) (t::(map (tyshiftn 1 m) l))).
  apply tysub_all. auto. auto.
  rewrite tysub_tyshift_map_id with (m:=m) (ty:=tyx).
  auto.

  (* Lam *)
  inversion HD ; subst ; simpl.
  apply AllIntro.
  change (S (n0+m)) with (S n0 + m).
  rewrite plus_Snm_nSm. 
  apply IHt. 
  rewrite <- plus_Snm_nSm. auto.
  apply tyshift_level. fold plus. auto. 
  cut (map (tyshiftn 1 (S m)) (map tyshift l) = (map tyshift (map (tyshiftn 1 m) l))). 
  intros Heq. rewrite Heq. 
  rewrite <- plus_Snm_nSm. auto.
  rewrite tyshift_tyshift_map. auto.

  (* Fold *)
  inversion HD ; subst ; simpl.
    (* Mu *) 
    apply MuIntro. 
    apply tysub_level_gen. firstorder. auto.
    apply tyshift_level ; auto.
    apply IHt with (tyx:=tyx) in H6.
    rewrite tysub_comm in H6. 
    change (Mu (tysub A (S m) (tyshift tyx))) with (tysub (Mu A) m tyx).
    auto. firstorder. auto.
    (* Nu *) 
    apply NuIntro. 
    apply tysub_level_gen. firstorder. auto.
    apply tyshift_level ; auto.
    apply IHt with (tyx:=tyx) in H6.
    rewrite tysub_comm in H6. 
    change (Nu (tysub A (S m) (tyshift tyx))) with (tysub (Nu A) m tyx).
    auto. firstorder. auto.
  (* Unfold *) 
  inversion HD ; subst ; simpl.
    (* Mu *) 
    rewrite tysub_comm.
    apply MuElim. 
    apply tysub_level_gen. firstorder. auto. 
    apply tyshift_level ; firstorder.
    apply IHt with (tyx:=tyx) in H6.
    change (Mu (tysub A (S m) (tyshiftn 1 0 tyx))) with (tysub (Mu A) m tyx).
    auto. auto. firstorder. 
    (* Nu *) 
    rewrite tysub_comm.
    apply NuElim. 
    apply tysub_level_gen. firstorder. auto. 
    apply tyshift_level ; firstorder.
    apply IHt with (tyx:=tyx) in H6.
    change (Nu (tysub A (S m) (tyshiftn 1 0 tyx))) with (tysub (Nu A) m tyx).
    auto. auto. firstorder. 
  (* Inl *) 
  inversion HD ; subst ; simpl. 
  apply OrIntroL.  
  apply tysub_level_gen. firstorder. auto. auto. 
  apply IHt. auto. auto. 
  (* Inr *) 
  inversion HD ; subst ; simpl. 
  apply OrIntroR.  
  apply tysub_level_gen. firstorder. auto. auto. 
  apply IHt. auto. auto. 
  (* Case *)    
  inversion HD ; subst ; simpl. 
  apply OrElim with (A:=tysub A m tyx) (B:=tysub B m tyx).
  change (Or (tysub A m tyx) (tysub B m tyx)) with (tysub (Or A B) m tyx). 
  apply IHt1. auto. auto.
    (* inl *)  
    cut (l = map (fun t => tysub t m tyx) (map (tyshiftn 1 m) l)).
    intros Heq. rewrite Heq. 
    change (tysub A m tyx :: map (fun t1 : Ty => tysub t1 m tyx) (map (tyshiftn 1 m) l)) with 
      (map (fun t1 : Ty => tysub t1 m tyx) (A::(map (tyshiftn 1 m) l))).
    apply tysub_all. auto. auto.
    rewrite tysub_tyshift_map_id with (m:=m) (ty:=tyx).
    auto.
    (* inr *)  
    cut (l = map (fun t => tysub t m tyx) (map (tyshiftn 1 m) l)).
    intros Heq. rewrite Heq. 
    change (tysub B m tyx :: map (fun t1 : Ty => tysub t1 m tyx) (map (tyshiftn 1 m) l)) with 
      (map (fun t1 : Ty => tysub t1 m tyx) (B::(map (tyshiftn 1 m) l))).
    apply tysub_all. auto. auto.
    rewrite tysub_tyshift_map_id with (m:=m) (ty:=tyx).
    auto.
  (* Pair *) 
  inversion HD ; subst ; simpl. 
  apply AndIntro. 
  apply IHt1 ; auto. apply IHt2 ; auto. 
  (* Split *) 
  inversion HD ; subst ; simpl. 
  apply AndElim with (A:=tysub A m tyx) (B:=tysub B m tyx).
  change (And (tysub A m tyx) (tysub B m tyx)) with (tysub (And A B) m tyx). 
  apply IHt1. auto. auto.
    (* term *)  
    cut (l = map (fun t => tysub t m tyx) (map (tyshiftn 1 m) l)).
    intros Heq. rewrite Heq. 
    change (tysub A m tyx :: tysub B m tyx :: map (fun t1 : Ty => tysub t1 m tyx) (map (tyshiftn 1 m) l)) with 
      (map (fun t1 : Ty => tysub t1 m tyx) (A::B::(map (tyshiftn 1 m) l))).
    apply tysub_all. auto. auto.
    rewrite tysub_tyshift_map_id with (m:=m) (ty:=tyx).
    auto.
  (* Unit *) 
  inversion HD ; subst ; simpl.
  apply OneIntro. 
Defined. 

Lemma tysub_derivation_simple : forall t n l ty tyx, 
  valid tyx n -> 
  Derivation [S n; map tyshift l |=t @ ty] -> 
  Derivation [n; l |=tysubt t 0 tyx @ tysub ty 0 tyx].
Proof.
  intros.
  change n with (0+n).
  rewrite plus_comm.
  apply tysub_derivation ; rewrite <- plus_comm ; firstorder. 
Defined.

End Program. 
