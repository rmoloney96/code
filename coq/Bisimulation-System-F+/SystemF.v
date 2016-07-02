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
| Imp : Ty -> Ty -> Ty 
| All : Ty -> Ty.

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
| Lam : Term -> Term.

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
Defined.

Definition Zero := (All (TV 0)).
Definition One := (Imp Zero Zero).
Definition Unit := Abs Zero (V 0).

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
  end.

Fixpoint valid (ty : Ty) (n : nat) {struct ty} : Prop := 
  match ty with 
    | TV m => 
      if le_lt_dec n m
        then False
        else True
    | Imp s t => valid s n /\ valid t n
    | All t => valid t (S n)
  end.

Definition valid_dec : forall (ty : Ty) (n : nat), {valid ty n}+{~ valid ty n}.
Proof. 
  induction ty ; intros. 
  (* TV *)
  case_eq (le_lt_dec n0 n). 
  intros. right. simpl. rewrite H0. auto.
  intros. left. simpl. rewrite H0. auto.
  (* Imp *)
  firstorder.
  (* All *) 
  firstorder.
Defined.

Lemma valid_weaken : forall ty n m, 
  n <= m -> valid ty n -> valid ty m.
Proof.
  induction ty ; simpl ; intros. 
  numerical.
  inversion H1. 
  split. apply IHty1 with (n:=n). auto. auto. auto.  
  apply IHty2 with (n:=n). auto. auto.
  apply IHty with (n:=S n). firstorder. auto.
Defined. 

Lemma tyshift_level : forall ty1 n m, 
  valid ty1 n -> valid (tyshiftn 1 m ty1) (S n).
Proof.
  induction ty1 ; simpl ; intros ; numerical.
  destruct n ; numerical.
  firstorder.
Qed.

Lemma tysub_level : forall ty1 ty2 n, 
  valid ty1 (S n) -> valid ty2 n -> valid (tysub ty1 n ty2) n.
Proof.
  induction ty1 ; simpl ; intros ; numerical. 
  (* TV *)
  destruct n ; numerical. 
  firstorder.
  firstorder. 

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
 (* apply IHty1_1 ; auto ; firstorder.
  apply IHty1_2 ; auto ; firstorder.*) 
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
  valid ty n -> i < length l -> nth i l Zero = ty ->
  Derivation [n ; l |= V i @ ty].

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
            else None) (nth n' l Zero)
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
  case_eq (valid_dec (nth n l Zero) n0) ; 
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
Defined. 
  
Fixpoint shift (d : nat) (t : Term) {struct t} : Term := 
  match t with 
    | F m => F m
    | V m => if le_lt_dec d m then V (S m) else V m
    | App r s => App (shift d r) (shift d s) 
    | Lam r => Lam (shift d r)
    | Abs ty r => Abs ty (shift (d+1) r)
    | TApp r ty => TApp (shift d r) ty
  end.

Fixpoint tyshift_term (d : nat) (t : Term) {struct t} : Term := 
  match t with 
    | F m => F m 
    | V m => V m 
    | App r s => App (tyshift_term d r) (tyshift_term d s) 
    | Lam r => Lam (tyshift_term (S d) r)
    | Abs ty r => Abs (tyshiftn 1 d ty) (tyshift_term d r)
    | TApp r ty => TApp (tyshift_term d r) (tyshiftn 1 d ty)
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

Lemma nth_append : forall G xty l, nth (length G) (G ++ xty :: l) Zero = xty.
Proof.
  induction G. intros. simpl. auto.
  intros. simpl. apply IHG. 
Defined.

Lemma hole_at_i : forall i j k, 
  shift j (V i) = (V k) -> (~ j = k).
Proof. 
  intros. simpl in *.
  case_eq (le_lt_dec j i).
  intros. rewrite H1 in H0. clear H1. 
  unfold not. intros.
  rewrite <- H1 in H0. inversion H0.
  rewrite <- H3 in l.
  apply (le_Sn_n i). auto.
  intros. rewrite H1 in H0. clear H1.
  inversion H0. rewrite H2 in *.
  unfold not. intro. rewrite H1 in l.
  apply (lt_irrefl k). auto.
Defined.

Lemma shift_var : forall n i G L xty ty, 
  Derivation [n; G ++ L |= V i @ ty] -> 
  Derivation [n; G ++ xty :: L |= shift (length G) (V i) @ ty].
Proof. 
  intros.
  case_eq (shift (length G) (V i)). 
  (* F *) 
  intros. simpl in H1. 
  destruct (le_lt_dec (length G) i) ; auto ; inversion H1.
 
  (* Var *) 
  intros.
  cut (shift (length G) (V i) = V n0). intros Hdup.
  apply hole_at_i in Hdup. 
  simpl in H1. 
  case_eq (le_lt_dec (length G) i). intros. 
  rewrite H2 in H1. inversion H1. 
  apply weakenG_gt. rewrite <- H4 in *.
  unfold lt in *. apply le_n_S. auto.
  auto. 
  intros. rewrite H2 in H1.
  inversion H1. rewrite H4 in *. clear H2. 
  apply weakenG_lt. rewrite <- H4. auto. auto. auto. 

  (* App *) 
  intros. simpl in H1. 
  destruct (le_lt_dec (length G) i) ; auto ; inversion H1.
  
  (* TApp *) 
  intros. simpl in H1. 
  destruct (le_lt_dec (length G) i) ; auto ; inversion H1.
  (* Abs *) 
  intros. simpl in H1. 
  destruct (le_lt_dec (length G) i) ; auto ; inversion H1.
  (* Lam *) 
  intros. simpl in H1. 
  destruct (le_lt_dec (length G) i) ; auto ; inversion H1.
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
           | Abs ty r => _
           | Lam t => _
           | App r s => _
           | TApp r ty' => _
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
    inversion D ; subst. 
    apply ImpIntro. auto.
    rewrite plus_comm. simpl.
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
  nth n (map (tyshiftn 1 m) G) Zero = tyshiftn 1 m (nth n G Zero).
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
Qed.

Lemma tyshift_tysubR : forall ty m n xty,
  n <= m ->
  tyshiftn 1 m (tysub ty n xty) = tysub (tyshiftn 1 (S m) ty) n (tyshiftn 1 m xty).
Proof.
  induction ty ; intros ; simpl ; numerical.
  destruct n ; unfold tyshift ; simpl ; numerical. 
  destruct n ; unfold tyshift ; simpl ; numerical. 
  destruct n ; unfold tyshift ; simpl ; numerical.

  rewrite IHty1. rewrite IHty2. auto. auto. auto. 

  rewrite IHty. unfold tyshift.
  rewrite tyshift_comm ; auto ; firstorder. firstorder.
Qed.

Lemma tyshiftn_closed_id : forall ty l n m, 
  n <= m -> valid ty n -> tyshiftn l m ty = ty.
Proof.
  induction ty.
  (* TV *) 
  intros; simpl in * ; numerical.

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
Defined.

Lemma tysub_closed_id : forall ty xty n m, 
  n <= m -> valid ty n -> tysub ty m xty = ty.
Proof.
  induction ty.
  (* TV *) 
  intros ; simpl in * ; numerical.
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
       end) (refl_equal t)) ; intros ; subst.

  (* F *) 
  intros. inversion d1 ; inversion d2 ; subst ; auto.

  (* V *) 
  intros. inversion d1 ; inversion d2 ; subst ; auto.
  
  (* App *) 
  intros. inversion d1 ; inversion d2 ; subst ; auto.
  apply type_unique with (ty1:=xty) (ty2:=xty0) in H2 ; 
    apply type_unique with (ty1:=Imp xty ty1) (ty2:=Imp xty0 ty2) in H6.  
  subst. inversion H6. auto. auto. auto. auto.

  (* TApp *) 
  intros. inversion d1 ; inversion d2 ; subst ; auto.
  apply type_unique with (ty1:=All ty0) (ty2:=All ty3) in H6.
  inversion H6. auto. auto.

  (* Abs *) 
  intros. inversion d1 ; inversion d2 ; subst ; auto.
  apply type_unique with (ty1:=ty0) (ty2:=ty3) in H6.
  subst ; auto. auto. 

  (* Lam *)
  intros. inversion d1 ; inversion d2 ; subst ; auto.
  apply type_unique with (ty1:=ty) (ty2:=ty0) in H6.
  subst ; auto. auto.
Defined.

Theorem tysub_tyshift_id : forall a m ty, 
  tysub (tyshiftn 1 m a) m ty = a.
Proof. 
  induction a.
  intros. simpl. numerical.

  intros. simpl. 
  rewrite (IHa1 m ty).
  rewrite (IHa2 m ty). auto.

  intros. simpl. unfold tyshift.
  rewrite (IHa (S m) (tyshiftn 1 0 ty)).
  auto.
Qed.

Lemma tysub_tyshift_map_id : forall l m ty,  map (fun t => tysub t m ty) (map (tyshiftn 1 m) l) = l.
Proof.
  induction l; intros m ty.
  simpl. auto.
  simpl. rewrite tysub_tyshift_id.
  rewrite IHl. auto.
Defined.

Theorem nth_tysub_tyshift : forall l n m ty ty0,
  nth n (map (tyshiftn 1 m) l) Zero = ty -> 
  nth n l Zero = tysub ty m ty0.
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
  induction ty.
  intros. simpl. case (le_lt_dec n0 n) ; intros ; auto.

  intros. simpl. rewrite IHty1. rewrite IHty2. auto.
  
  intros. simpl. rewrite IHty. auto.
Defined. 

Lemma tyhole_in : forall n m k ty, 
  tyshiftn (S n) m ty = (TV k) -> k > m+n \/ k < m.
Proof.
  intros. 
  simpl in H0. 
  destruct ty. simpl in *. 
  case_eq (le_lt_dec m n0) ; intros HP  HX ; rewrite HX in H0.
  inversion H0. firstorder.
  inversion H0. firstorder.
  inversion H0. inversion H0.
Defined.

Lemma tysub_into_hole : forall ty n m k ty',
  k <= m+n /\ k >= m ->
  tysub (tyshiftn (S n) m ty) k ty' = tyshiftn n m ty.
Proof.
  induction ty.

  intros. simpl. numerical.

  intros. simpl. intros. rewrite IHty1. rewrite IHty2. auto. auto. auto.
  
  intros. simpl. rewrite IHty. auto.
  firstorder.
Defined.  

Lemma nth_tysub_map : forall l n m ty1, nth n (map (fun ty : Ty => tysub ty m ty1) l) Zero =
  tysub (nth n l Zero) m ty1.
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
  change (tysub (nth n l Zero) m tyx) with ((fun ty => tysub ty m tyx) (nth n l Zero)). 
  rewrite <- map_nth. unfold Zero. simpl. auto.
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