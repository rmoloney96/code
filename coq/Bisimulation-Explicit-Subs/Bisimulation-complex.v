
Inductive Ty : Set := 
| TV : nat -> Ty
| Imp : Ty -> Ty -> Ty 
| Or : Ty -> Ty -> Ty 
| And : Ty -> Ty -> Ty 
| Unit : Ty
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
| Cas : Term -> Term -> Term -> Term
| Split  Term -> Term -> Term
| Lam : Term -> Term.

Inductive Ctx : Set := 
| G : nat -> list Ty -> Ctx.

Definition Delta := nat -> Term.

Inductive Holds : Set := 
| H : Delta -> Ctx -> Term -> Ty -> Holds. 

Notation "d ; n ; l |= t @ ty" := (H d (G n l) t ty) (at level 60).
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
    | V m => V m
    | Abs ty t => Abs (tysub ty n s) (tysubt t n s)
    | Lam t => Lam (tysubt t (S n) (tyshift s))
    | App f g => App (tysubt f n s) (tysubt g n s)
    | TApp f ty => TApp (tysubt f n s) (tysub ty n s)
  end.

Eval compute in tysubt (tysubt (Lam (TApp (V 0) (TV 2))) 0 (TV 0)) 0 (TV 3). 

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
  Derivation (S n ; map tyshift l |= t @ ty) -> 
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
        end) (typeof (S n) (map tyshift l) r)
  end.
