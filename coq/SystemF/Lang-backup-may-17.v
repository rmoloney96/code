
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
    | _ : _ |- context [ False_rec ?x ?y ] => elimtype False
(*  | _ : _ |- context [ False_rec ?x ?y ] => elimtype False ; simpl in * ; omega
    | _ : _ |- ?x = ?y => elimtype False ; simpl in * ; omega *)
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
| V : nat -> Term 
| App : Term -> Term -> Term 
| TApp : Term -> Ty -> Term
| Abs : Ty -> Term -> Term
| Lam : Term -> Term.

Inductive Ctx : Set := 
| G : nat -> list Ty -> Ctx.

Inductive Holds : Set := 
| H : Ctx -> Term -> Ty -> Holds. 

Notation "n ; l |= t @ ty" := (H (G n l) t ty) (at level 60).
Open Scope list_scope.

Fixpoint tyshift (d : nat) (ty : Ty) {struct ty} : Ty := 
  match ty with 
    | TV m => if le_lt_dec d m then TV (S m) else TV m
    | Imp t s => Imp (tyshift d t) (tyshift d s) 
    | All t => All (tyshift (S d) t) 
  end.

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
        | All t => All (tysub t (S n) (tyshift 0 s))
      end).
  destruct m. apply le_n_O_eq in p. apply p'. auto. inversion p''.
Defined.

Fixpoint tysubt (t : Term) (n : nat) (s : Ty) {struct t} : Term := 
  match t with 
    | V m => V m
    | Abs ty t => Abs (tysub ty n s) (tysubt t n s)
    | Lam t => Lam (tysubt t (S n) (tyshift 0 s))
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

Lemma tyshift_level : forall ty1 n m, 
  valid ty1 n -> valid (tyshift m ty1) (S n).
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

  apply IHty1. auto. 
  apply tyshift_level. auto.
Qed.

Definition Zero := (All (TV 0)).
Definition One := (Imp Zero Zero).

Inductive Derivation : Holds -> Set := 
| ImpIntro : forall n l t ty xty,
  valid xty n ->
  Derivation (n ; xty::l |= t @ ty) -> 
  Derivation (n ; l |= (Abs xty t) @ (Imp xty ty))
| ImpElim : forall n l t f ty xty,
  Derivation (n ; l |= t @ xty) ->
  Derivation (n ; l |= f @ (Imp xty ty)) -> 
  Derivation (n ; l |= (App f t) @ ty)
| AllIntro : forall n l t ty,
  Derivation (S n ; map (tyshift 0) l |= t @ ty) -> 
  Derivation (n ; l |= (Lam t) @ All ty)
| AllElim : forall n l t ty xty,
  valid xty n ->
  valid ty (S n) -> 
  Derivation (n ; l |= t @ All ty) -> 
  Derivation (n ; l |= TApp t xty @ (tysub ty 0 xty))
| VarIntro : forall n l ty i,
  i < length l -> nth i l Zero = ty ->
  Derivation (n ; l |= V i @ ty).

Fixpoint typeof (n : nat) (l : list Ty) (t : Term) {struct t} : option Ty := 
  match t with 
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
        end) (typeof (S n) (map (tyshift 0) l) r)
  end.

Require Import Sumbool.

Theorem typeof_has_derivation : 
  forall t n l ty, 
    typeof n l t = Some ty -> Derivation (n ; l |= t @ ty).
Proof.
  induction t ; intros. 
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
  eapply(ImpElim n l t2 t1 ty t3). 
  apply IHt2. rewrite <- e. auto.
  apply IHt1. rewrite <- H5. auto. 
  
  (* TApp *)
  intros. simpl in H0.
  case_eq (typeof n l t). intros. rewrite H1 in H0.
  destruct t1 ; try congruence. 
  case_eq (valid_dec t0 n) ; intros ; try (rewrite H2 in *) ; try congruence.
  case_eq (valid_dec t1 (S n)) ; intros ; try (rewrite H3 in *) ; try congruence.
  inversion H0. subst.
  apply AllElim. auto. auto. apply IHt. auto.  
  intros. rewrite H1 in H0. inversion H0.
  
  (* Abs *) 
  simpl in H0. case_eq (typeof n (t::l) t0) ; intros ; try (rewrite H1 in *) ; try congruence. 
  case_eq (valid_dec t n) ; intros ; try (rewrite H2 in *) ; try congruence.
  inversion H0.
  eapply ImpIntro. auto. apply IHt. auto.

  (* Lam *)
  simpl in H0. case_eq (typeof (S n) (map (tyshift 0) l) t) ; intros ; try (rewrite H1 in *) ; try congruence.
  case_eq (valid_dec t0 (S n)). intros. rewrite H2 in H0. inversion H0.
  eapply AllIntro. apply IHt in H1. auto.
  intros. rewrite H2 in H0. inversion H0.
Defined. 
  
Fixpoint shift (d : nat) (t : Term) {struct t} : Term := 
  match t with 
    | V m => if le_lt_dec d m then V (S m) else V m
    | App r s => App (shift d r) (shift d s) 
    | Lam r => Lam (shift d r)
    | Abs ty r => Abs ty (shift (d+1) r)
    | TApp r ty => TApp (shift d r) ty
  end.

Fixpoint tyshift_term (d : nat) (t : Term) {struct t} : Term := 
  match t with 
    | V m => V m 
    | App r s => App (tyshift_term d r) (tyshift_term d s) 
    | Lam r => Lam (tyshift_term (S d) r)
    | Abs ty r => Abs (tyshift d ty) (tyshift_term d r)
    | TApp r ty => TApp (tyshift_term d r) (tyshift d ty)
  end.

Definition sub : forall (t : Term) (n : nat) (s : Term), Term.
Proof. 
  refine 
    (fix sub (t : Term) (n : nat) (s : Term) {struct t} : Term := 
      match t with 
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

Lemma nth_sameL : forall A a (l:list A) F d i, 
  i < length F -> 
  nth i (F++(a::l)) d = nth i (F++l) d.
Proof.
  induction F. intros. inversion H0.
  intros. destruct i.
  simpl. auto. simpl. apply IHF. simpl in H0.
  apply lt_S_n. auto.
Defined.
 
Lemma nth_sameR : forall A i a (l:list A) F d, 
  length F < S i -> 
  nth (S i) (F++(a::l)) d = nth i (F++l) d.
Proof.
  refine
    (fix nth_sameR A i a (l F:list A) d (H: length F < S i) {struct F} : nth (S i) (F++(a::l)) d = nth i (F++l) d := 
      (match F as F' return (F = F' -> nth (S i) (F++(a::l)) d = nth i (F++l) d) with 
         | nil => _
         | cons a g => _
       end) (refl_equal F)).
  intros. rewrite H1 in *. simpl. auto.
  intros. rewrite H1 in *. simpl. 
  destruct i. simpl in H0. unfold lt in H0. apply le_S_n in H0.
  apply le_n_O_eq in H0. inversion H0. 
  apply nth_sameR.
  simpl in H0. unfold lt in H0. apply le_S_n in H0.
  unfold lt. auto.
Defined.
 
Lemma one_longer : 
  forall A i (F :list A) xty l, (S i) < S (length (F ++ xty :: l)) -> i < S (length (F++l)).
Proof.
  intros. rewrite app_length in H0. simpl in H0.
  rewrite plus_comm in H0. simpl in H0.
  unfold lt in *. apply le_S_n in H0.
  rewrite app_length. rewrite plus_comm. auto.
Defined.

Lemma strengthenF_gt : forall i n l F xty ty, 
  length F < S i -> 
  Derivation (n ; F ++ xty::l |= V (S i) @ ty) -> 
  Derivation (n ; F ++ l |= V i @ ty).
Proof.
  intros.
  inversion H1. 
  rewrite nth_sameR in H7.
  apply VarIntro. 
  induction F. simpl in *. 
  unfold lt in *. apply le_S_n in H4. auto.
  simpl in *. 
  apply one_longer in H4. auto. auto. auto.
Defined.

Lemma strengthenF_lt : forall i n l F xty ty, 
  i < length F -> 
  Derivation (n ; F ++ xty::l |= V i @ ty) -> 
  Derivation (n ; F ++ l |= V i @ ty).
Proof.
  intros. inversion H1. subst. 
  apply VarIntro. 
  rewrite app_length. 
  unfold lt in *.
  apply le_plus_trans. auto.
  rewrite nth_sameL. auto. auto.
Defined.

Definition weakenF_lt : forall i F n L ty xty,
  i < length F -> 
  Derivation (n; F ++ L |= V i @ ty) ->
  Derivation (n; F ++ xty :: L |= V i @ ty).
Proof. 
  intros.
  apply VarIntro. rewrite app_length.
  apply lt_plus_trans. auto.
  inversion H1; subst. simpl in *.
  apply nth_sameL. auto.
Defined.

Definition weakenF_gt : forall i F n L ty xty,
  length F < (S i) -> 
  Derivation (n; F ++ L |= V i @ ty) ->
  Derivation (n; F ++ xty :: L |= V (S i) @ ty).
Proof. 
  intros.
  inversion H1 ; subst.
  apply VarIntro. rewrite app_length in *. 
  simpl. rewrite plus_comm. simpl.
  apply lt_n_S. rewrite plus_comm. auto.
  apply nth_sameR. auto.
Defined.

Lemma nth_append : forall F xty l, nth (length F) (F ++ xty :: l) Zero = xty.
Proof.
  induction F. intros. simpl. auto.
  intros. simpl. apply IHF. 
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

Lemma shift_var : forall n i F L xty ty, 
  Derivation (n; F ++ L |= V i @ ty) -> 
  Derivation (n; F ++ xty :: L |= shift (length F) (V i) @ ty).
Proof. 
  intros.
  case_eq (shift (length F) (V i)). 

  (* Var *) 
  intros.
  cut (shift (length F) (V i) = V n0). intros Hdup.
  apply hole_at_i in Hdup. 
  simpl in H1. 
  case_eq (le_lt_dec (length F) i). intros. 
  rewrite H2 in H1. inversion H1. 
  apply weakenF_gt. rewrite <- H4 in *.
  unfold lt in *. apply le_n_S. auto.
  auto. 
  intros. rewrite H2 in H1.
  inversion H1. rewrite H4 in *. clear H2. 
  apply weakenF_lt. rewrite <- H4. auto. auto. auto. 

  (* App *) 
  intros. simpl in H1. 
  destruct (le_lt_dec (length F) i) ; auto ; inversion H1.
  
  (* TApp *) 
  intros. simpl in H1. 
  destruct (le_lt_dec (length F) i) ; auto ; inversion H1.
  (* Abs *) 
  intros. simpl in H1. 
  destruct (le_lt_dec (length F) i) ; auto ; inversion H1.
  (* Lam *) 
  intros. simpl in H1. 
  destruct (le_lt_dec (length F) i) ; auto ; inversion H1.
Defined.

Lemma shift_correct : forall n s xty ty F L, 
  Derivation (n; F ++ L |= s @ ty) ->
  Derivation (n; F ++ (xty :: L) |= shift (length F) s @ ty).
Proof.
    refine 
      (fix shift_correct (n : nat) (s : Term) (xty ty : Ty) (F L : list Ty)
        (d : Derivation (n; F ++ L |= s @ ty)) {struct s}:
        Derivation (n; F ++ (xty :: L) |= shift (length F) s @ ty) := 
        (match s as s'
           return (s = s' -> Derivation (n; F ++ (xty :: L) |= shift (length F) s @ ty))
           with 
           | V i => _
           | Abs ty r => _
           | Lam t => _
           | App r s => _
           | TApp r ty' => _
         end) (refl_equal s)) ; intros ; subst.
  
    (* V *)
    inversion d. 
    apply shift_var. exact d.

    (* App *)
    simpl.
    inversion d. subst.
    apply ImpElim with (xty:=xty0).
    apply shift_correct. auto.
    apply shift_correct. auto.

    (* TApp *)
    simpl. 
    inversion d ; subst.
    apply AllElim. auto. auto.
    apply shift_correct. auto.

    (* Abs *)
    simpl.
    inversion d ; subst. 
    apply ImpIntro. auto.
    rewrite plus_comm. simpl.
    cut (length  (ty0 :: F) = (S (length F))).
    intros. rewrite <- H0.
    rewrite app_comm_cons.
    apply shift_correct with (F:=(ty0::F)) (ty:=ty1).
    rewrite <- app_comm_cons.
    auto. simpl. auto.

    (* Lam *) 
    simpl. 
    inversion d ; subst.
    apply AllIntro.
    cut (length F = length (map (tyshift 0) F)).
    intros. rewrite H0.
    rewrite map_app. simpl.
    apply shift_correct.
    rewrite <- map_app. auto.
    rewrite map_length. auto.
Defined.

Theorem tyhole_at_i : forall i j k, 
  tyshift j (TV i) = (TV k) -> (~ j = k).
Proof. 
  intros. unfold tyshift in *.
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

Lemma tyshift_natural : forall F n m, 
  nth n (map (tyshift m) F) Zero = tyshift m (nth n F Zero).
Proof.
  induction F. simpl. intros. destruct n ; auto.
  intros. simpl. destruct n ; auto.
Qed.

Lemma tyshift_comm : forall xty m n,
  m <= n ->
  tyshift (S n) (tyshift m xty) = tyshift m (tyshift n xty).
Proof.
  induction xty ; intros ; simpl ; numerical. 

  destruct n; numerical.
  
  rewrite IHxty2. rewrite IHxty1. auto. auto. auto.
  
  rewrite IHxty. auto. firstorder.
Qed.

Lemma tyshift_tyshift_map  : forall m F,
  map (tyshift 0) (map (tyshift m) F) = map (tyshift (S m)) (map (tyshift 0) F).
Proof.
  induction F. simpl. auto. simpl.
  rewrite tyshift_comm. rewrite IHF. auto. 
  apply (le_O_n m). 
Defined.

Lemma tyshift_tysubL : forall ty m n xty,
  m <= n ->
  tyshift m (tysub ty n xty) = tysub (tyshift m ty) (S n) (tyshift m xty).
Proof.
  induction ty ; intros ; simpl ; numerical. 

  destruct n ; unfold tyshift ; simpl ; numerical. 
  destruct n ; unfold tyshift ; simpl ; numerical. 

  rewrite IHty1. rewrite IHty2. auto. auto. auto. 

  rewrite IHty.
  rewrite tyshift_comm. auto.  
  firstorder. firstorder.
Qed.

Lemma tyshift_tysubR : forall ty m n xty,
  n <= m ->
  tyshift m (tysub ty n xty) = tysub (tyshift (S m) ty) n (tyshift m xty).
Proof.
  induction ty ; intros ; simpl ; numerical.
  destruct n ; unfold tyshift ; simpl ; numerical. 
  destruct n ; unfold tyshift ; simpl ; numerical. 
  destruct n ; unfold tyshift ; simpl ; numerical.

  rewrite IHty1. rewrite IHty2. auto. auto. auto. 

  rewrite IHty.
  rewrite tyshift_comm ; auto ; firstorder. firstorder.
Qed.

Lemma tyshift_correct : forall s m n F xty, 
  Derivation (m+n; F |= s @ xty) ->
  Derivation (S(m+n); map (tyshift m) F |= tyshift_term m s @ tyshift m xty).
Proof.
  induction s ; intros.
  
  (* V *) 
  inversion H0. subst. simpl.
  apply VarIntro. rewrite map_length. auto.
  apply tyshift_natural.

  (* App *)
  inversion H0. subst. simpl.
  apply ImpElim with (xty:=tyshift m xty0).
  apply IHs2. auto.
  cut (Imp (tyshift m xty0) (tyshift m xty) = tyshift m (Imp xty0 xty)).
  intros. rewrite H1. apply IHs1. auto. simpl. auto.
  
  (* TApp *) 
  simpl.
  inversion H0 ; subst.

  rewrite tyshift_tysubR. 
  apply AllElim. 
  apply tyshift_level. auto. 
  apply tyshift_level. auto.
  change (All (tyshift (S m) ty)) with (tyshift m (All ty)).
  apply IHs. auto. 
  apply (le_O_n m). 

  (* Abs *) 
  simpl. inversion H0 ; subst.
  simpl. apply ImpIntro. 
  apply tyshift_level. auto.
  change (tyshift m t :: map (tyshift m) F) with (map (tyshift m) (t :: F)).
  apply IHs. auto.
  
  (* Lam *) 
  simpl. inversion H0 ; subst. 
  simpl. apply AllIntro. intros.
  rewrite tyshift_tyshift_map.
  intros.
  change (S (S (m + n))) with (S ((S m) + n)).

  apply IHs. auto.
Qed.

Theorem sub_preservation : forall t s n xty ty F L,
  Derivation (n ; F++xty::L |= t @ ty) -> 
  Derivation (n ; F++L |= s @ xty) -> 
  Derivation (n ; F++L |= sub t (length F) s @ ty).
Proof. 
  induction t. 
  (* VarIntro *)
  intros. unfold sub.
  case_eq (le_lt_dec (length F) n) ; intros. 
  case_eq (eq_nat_dec (length F) n). intros. rewrite <- e in H0. 
  inversion H0. simpl in H9.
  rewrite nth_append in H9. rewrite <- H9. auto.
  destruct n. simpl in *.
  intros. elimtype False. clear H2. clear H3.
  apply le_n_O_eq in l. unfold not in n. apply n. auto. 
  intros. 
  
  apply strengthenF_gt with (xty:=xty). clear H2.
  apply le_lt_or_eq in l. inversion l ; auto. clear H3.
  rewrite H2 in n1. unfold not in n1.
  elimtype False. apply n1. auto.

  exact H0.

  apply strengthenF_lt with (xty:=xty). auto. auto. 

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
  cut (S (length F) = (length (t::F))).
  intros. rewrite H2. 
  rewrite app_comm_cons.
  apply IHt with (F := (t :: F)) (xty:=xty). auto.
  rewrite <- app_comm_cons. 
  cut (t::F++L = nil++(t::F++L)).
  intros. rewrite H3.
  
  apply shift_correct with (F:=(nil (A:=Ty))). 
  simpl. auto. auto. auto. 

  (* AllIntro *)
  intros. simpl in *.
  inversion H0 ; subst.
  apply AllIntro.
  cut (0+n = n). intro Hpz. rewrite <- Hpz in H1.
  apply tyshift_correct in H1. simpl in H1.
  cut (length (map (tyshift 0) F) = length F). intros.
  rewrite <- H2.
  rewrite map_app. 
  apply IHt with (xty:=tyshift 0 xty).
  rewrite map_app in H3. simpl in H3. auto. 
  rewrite map_app in H1. auto. 
  apply map_length. simpl. auto.
Defined.

Theorem sub_preservation_basic : forall n L t s xty ty, 
  Derivation (n ; xty::L |= t @ ty) -> 
  Derivation (n ; L |= s @ xty) -> 
  Derivation (n ; L |= sub t 0 s @ ty).
Proof.
  intros.
  change L with (nil++L).
  change 0 with (length  (A:=Ty) nil).
  apply sub_preservation with (xty:=xty). simpl. auto. 
  simpl. auto.
Defined.

Theorem type_unique : forall n L t ty1 ty2, 
  Derivation (n ; L |= t @ ty1) -> Derivation (n ; L |= t @ ty2) 
  -> ty1 = ty2. 
Proof.
  refine 
    (fix type_unique n l (t : Term) ty1 ty2 
      (d1 : Derivation (n ; l |= t @ ty1))
      (d2 : Derivation (n ; l |= t @ ty2)) {struct t} 
      : ty1 = ty2 :=
      (match t as t' return (t = t' -> ty1 = ty2)
         with
         | V n => _
         | App f g => _ 
         | Abs ty r => _ 
         | TApp r ty => _
         | Lam r => _
       end) (refl_equal t)) ; intros ; subst.

  (* V *) 
  intros. inversion d1 ; inversion d2 ; subst ; auto.
  
  (* App *) 
  intros. inversion d1 ; inversion d2 ; subst ; auto.
  apply type_unique with (ty1:=xty) (ty2:=xty0) in H2 ; 
    apply type_unique with (ty1:=Imp xty ty1) (ty2:=Imp xty0 ty2) in H6.  
  subst. inversion H6. auto. auto. auto. auto.

  (* TApp *) 
  intros. inversion d1 ; inversion d2 ; subst ; auto.
  apply type_unique with (ty1:=All ty0) (ty2:=All ty3) in H7.
  inversion H7. auto. auto.

  (* Abs *) 
  intros. inversion d1 ; inversion d2 ; subst ; auto.
  apply type_unique with (ty1:=ty0) (ty2:=ty3) in H6.
  subst ; auto. auto. 

  (* Lam *)
  intros. inversion d1 ; inversion d2 ; subst ; auto.
  apply type_unique with (ty1:=ty) (ty2:=ty0) in H1.
  subst ; auto. auto.
Defined.

Theorem tysub_tyshift_id : forall a m ty, 
  a = tysub (tyshift m a) m ty.
Proof. 
  induction a.
  intros. simpl. numerical.

  intros. simpl. 
  rewrite <- (IHa1 m ty).
  rewrite <- (IHa2 m ty). auto.

  intros. simpl.
  rewrite <- (IHa (S m) (tyshift 0 ty)).
  auto.
Qed.

Theorem nth_tysub_tyshift : forall l n m ty ty0,
  nth n (map (tyshift m) l) Zero = ty -> 
  nth n l Zero = tysub ty m ty0.
Proof.
  induction l.
  intros. simpl in *.
  destruct n ; subst ; simpl ; auto.

  intros.
  destruct n. simpl in H0. 
  simpl. subst.
  rewrite <- (tysub_tyshift_id a m ty0). auto.

  simpl. apply IHl. simpl in H0. auto.
Defined.

(*
Definition ty := Imp (TV 0) (TV 1).
Definition ty0 := TV 1.
Definition ty1 := Imp (TV 1) (TV 0).
Definition m := 0. 
Eval compute in tysub (tysub ty (S m) (tyshift 0 ty1)) 0 (tysub ty0 m ty1).
Eval compute in tysub (tysub ty 0 ty0) m ty1.
*)

Fixpoint tyshiftn (n:nat) (m:nat) (ty:Ty) {struct n} : Ty := 
  match n with 
    | 0 => ty 
    | S n' => tyshiftn n' m (tyshift m ty)
  end.

Lemma tysub_reorder : forall ty ty0 ty1 m n, 
  tysub (tysub ty (S (m+n)) (tyshiftn (S n) 0 ty1)) n (tysub ty0 m ty1) = 
  tysub (tysub ty n (tyshiftn n 0 ty0)) (m+n) (tyshiftn n 0 ty1).
Proof. 
  induction ty ; try (simpl; numerical ; auto ; fail).

  (* V *)
  intros. simpl.
  destruct n. simpl. auto.
  numerical. subst. simpl. rewrite plus_comm. simpl. auto.
  simpl. numerical. subst.
  rewrite shifted_sub_irrelevant. auto.
  destruct n. elimtype False. firstorder. auto.
  
  (* Imp *)
  intros. simpl. 
  rewrite IHty1. rewrite IHty2. auto. auto. auto.
  
  (* All *)
  intros. 
  simpl.
  rewrite IHty. 
  rewrite <- tyshift_tysubR.
intros.
  rewrite IHty.

  
Theorem tysub_preservation : forall t m n l ty xty, 
  Derivation (S(m+n); map (tyshift m) l |= t @ ty) -> 
  Derivation (m+n; l |= tysubt t m xty @ tysub ty m xty).
Proof.
  induction t ; intros.
  
  (* V *) 
  inversion H0 ; subst.
  simpl. 
  apply VarIntro. rewrite map_length in H3. auto. 
  apply nth_tysub_tyshift. auto.

  (* App *) 
  inversion H0. subst.
  simpl.
  apply ImpElim with (xty:=tysub xty0 m xty). 
  apply IHt2. auto.
  change (Imp (tysub xty0 m xty) (tysub ty m xty)) with (tysub (Imp xty0 ty) m xty).
  apply IHt1. auto. 

  (* TApp *) 
  inversion H0. subst. simpl.


  apply IHt with (xty:=xty) in H8.
  simpl in H8.
  apply AllElim with (xty:=tysub t0 m xty) in H8.
  
  Check AllElim.
  intros. rewrite <- H1.
  auto. auto.

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



Extract 