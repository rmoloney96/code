
Require Import Arith.
Require Import List. 

(*
Require Import Peano.
Require Import Peano_dec.
*) 

Inductive Ty : Set := 
| Imp : Ty -> Ty -> Ty 
| TV : nat -> Ty
| Nu : Ty -> Ty
| One : Ty 
| And : Ty -> Ty -> Ty
| Or : Ty -> Ty -> Ty.

Inductive Term : Set := 
| V : nat -> Term
| Unit : Term
| Pair : Term -> Term -> Term
| Inl : Ty -> Term -> Term
| Inr : Ty -> Term -> Term
| Cas : Term -> Term -> Term -> Term
| Spl : Term -> Term -> Term
| Rec : nat -> Term -> Term
| App : Term -> Term -> Term
| Abs : Ty -> Term -> Term
| I : Ty -> Term -> Term
| O : Ty -> Term -> Term.

Lemma ty_eq_dec : forall (ty1 ty2 : Ty), {ty1 = ty2} + {ty1 <> ty2}.
Proof. 
  decide equality. decide equality. 
Defined.

Inductive Ctx : Set := 
| G : nat -> list Ty -> Ctx.

Inductive Holds : Set := 
| H : Ctx -> Term -> Ty -> Holds. 

Notation "n ; l |= t @ ty" := (H (G n l) t ty) (at level 60).
Open Scope list_scope.

Fixpoint tyshift (ty : Ty) (d : nat) {struct ty} : Ty := 
  match ty with 
    | One => One
    | Imp ty0 ty1 => Imp (tyshift ty0 d) (tyshift ty1 d)
    | TV m => if le_lt_dec d m then TV (S m) else TV m
    | Nu ty0 => Nu (tyshift ty0 (S d))
    | And ty0 ty1 => And (tyshift ty0 d) (tyshift ty1 d)
    | Or ty0 ty1 => Or (tyshift ty0 d) (tyshift ty1 d)
  end.

Require Import Omega. 
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
        | One => One
        | And ty0 ty1 => And (tysub ty0 n s) (tysub ty1 n s)
        | Or ty0 ty1 => Or (tysub ty0 n s) (tysub ty1 n s)
        | Nu t => Nu (tysub t (S n) (tyshift s n))
      end).
  destruct m. apply le_n_O_eq in p. apply p'. auto. inversion p''.
Defined.

Fixpoint valid (ty : Ty) (n : nat) {struct ty} : Prop := 
  match ty with 
    | TV m => 
      if le_lt_dec n m
        then False
        else True
    | Imp s t => valid s n /\ valid t n
    | One => True
    | And s t => valid s n /\ valid t n
    | Or s t => valid s n /\ valid t n
    | Nu t => valid t (S n)
  end.

Definition valid_dec : forall (ty : Ty) (n : nat), {valid ty n}+{~ valid ty n}.
Proof. 
  induction ty ; intros ; simpl ; auto ; firstorder. 

  (* TV *) intros. 
  case_eq (le_lt_dec n0 n). intros. right. simpl. auto. 
  intros. left. simpl. auto.
Defined.

Lemma tyshift_level : forall ty1 n, 
  valid ty1 n -> valid (tyshift ty1 n) (S n).
Proof.
  induction ty1 ; intros ; simpl ; firstorder.
  (* TV *) 
  case_eq (le_lt_dec n0 n). simpl. intros. rewrite H1. 
  simpl in H0. rewrite H1 in H0. inversion H0.
  intros. simpl. destruct n. auto.
  case_eq (le_lt_dec n0 n). intros. simpl. omega. simpl. intros. auto.
Defined.

Lemma tysub_level : forall ty1 ty2 n, 
  valid ty1 (S n) -> valid ty2 n -> valid (tysub ty1 n ty2) n.
Proof.
   induction ty1 ; intros ; simpl ; firstorder.
   (* TV *)
   simpl.
   case_eq (le_lt_dec n0 n); case_eq (eq_nat_dec n0 n) ; intros ; auto.
   destruct n. absurd (n0 <> 0). omega. omega. 
   simpl in H0. case_eq (le_lt_dec n0 n). intros. rewrite H4 in H0. simpl in H0. inversion H0.
   intros. clear H0.  absurd (n0 <> S n). intros. omega. omega. 
   absurd (n0 = n). omega. omega. simpl. rewrite H3. auto.
   (* Nu *)
   intros. simpl in H0. simpl. 
   apply IHty1. auto. 
   (* need tyshift lemma *)
   apply tyshift_level. auto.
 Defined.

Inductive Derivation : Holds -> Set := 
| ImpIntro : forall n l t ty xty,
  valid xty n ->
  Derivation (n ; l |= t @ ty) -> 
  Derivation (n ; xty::l |= (Abs xty t) @ (Imp xty ty))
| ImpElim : forall n l t f ty xty,
  Derivation (n ; l |= t @ xty) ->
  Derivation (n ; l |= f @ (Imp xty ty)) -> 
  Derivation (n ; l |= (App f t) @ ty)
| OneIntro : forall n l, 
  Derivation (n ; l |= Unit @ One)
| PairIntro : forall n l r s rty sty, 
  Derivation (n ; l |= r @ rty) -> 
  Derivation (n ; l |= s @ sty) -> 
  Derivation (n ; l |= Pair r s @ And rty sty)
| PairElim : forall n l r s aty bty cty, 
  Derivation (n ; l |= r @ And aty bty) -> 
  Derivation (n ; aty::bty::l |= s @ cty) -> 
  Derivation (n ; l |= Spl r s @ cty)
| OrIntroL : forall n l t lty rty, 
  valid rty n ->
  Derivation (n ; l |= t @ lty) -> 
  Derivation (n ; l |= Inl (Or lty rty) t @ Or lty rty)
| OrIntroR : forall n l t lty rty, 
  valid lty n ->
  Derivation (n ; l |= t @ rty) -> 
  Derivation (n ; l |= Inr (Or lty rty) t @ Or lty rty)
| OrElim : forall n l r s t lty rty cty, 
  Derivation (n ; l |= r @ Or lty rty) -> 
  Derivation (n ; lty::l |= s @ cty) -> 
  Derivation (n ; rty::l |= t @ cty) -> 
  Derivation (n ; l |= Cas r s t @ cty)
| NuIntro : forall n l r ty, 
  Derivation (S n ; l |= r @ tysub ty 0 (Nu ty)) -> 
  Derivation (n ; l |= I (Nu ty) r @ Nu ty)
| NuElim : forall n l r ty, 
  Derivation (n ; l |= r @ Nu ty) -> 
  Derivation (S n ; l |= O (Nu ty) r @ tysub ty 0 (Nu ty))
| VarIntro : forall n l ty i,
  i < length l -> nth i l One = ty ->
  Derivation (n ; l |= V i @ ty).

Fixpoint typeof (n : nat) (l : list Ty) (t : Term) {struct t} : option Ty := 
  match t with
    | Unit => Some One 
    | V n' => 
      if le_lt_dec (length l) n' 
        then None 
        else Some (nth n' l One)
    | Pair r s => 
      (fun mrty msty => 
        match mrty,msty with 
          | Some aty,Some bty => Some (And aty bty)
          | _,_ => None
        end) (typeof n l r) (typeof n l s)
    | Inl ty s => 
      match ty with 
        | Or lty rty => 
          (fun mlty => 
            match mlty with 
              | Some lty' => 
                if ty_eq_dec lty' lty 
                  then if valid_dec rty n
                    then Some (Or lty rty)
                    else None
                  else None
              | _ => None
            end) (typeof n l s)
        | _ => None
      end
    | Inr ty s => 
      match ty with 
        | Or lty rty => 
          (fun mrty => 
            match mrty with 
              | Some rty' => 
                if ty_eq_dec rty' rty 
                  then if valid_dec lty n
                    then Some (Or lty rty)
                    else None
                  else None
              | _ => None
            end) (typeof n l s)
        | _ => None
      end
    | Cas r s t => 
      (fun mrty => 
        match mrty with
          | Some (Or lty rty) => 
            (fun msty mtty => 
              match msty,mtty with 
                | Some cty, Some cty' => 
                  if ty_eq_dec cty cty' 
                    then Some cty 
                    else None
                | _,_ => None
              end) (typeof n (lty::l) s) (typeof n (rty::l) t)
          | _ => None
        end) (typeof n l r)
    | Spl r s => 
      (fun mrty => 
        match mrty with 
          | Some (And lty rty) => typeof n (lty::rty::l) s
          | _ => None
        end) (typeof n l r)
    | App r s => 
      (fun mrty msty => 
        match mrty,msty with 
          | Some (Imp xty yty),Some xty' => 
            if ty_eq_dec xty' xty 
              then Some yty
              else None
          | _,_ => None
        end) (typeof n l r) (typeof n l s)
    | Abs ty r => 
      (fun mrty => 
        match mrty with 
          | Some ty' => Some (Imp ty ty')
          | _ => None
        end) (typeof n (ty::l) r)
    | I ty r => 
      (fun mrty => 
        match mrty with 
          | Some ty' => Some (Nu ty')
          | _ => None
        end) (typeof (S n) l r)
    | O ty r => 
      (fun mrty => 
        match mrty with 
          | Some ty' => Some (Nu ty')
          | _ => None
        end) (typeof (S n) l r)
    | Rec n t => 
      (fun mrty => 
        match mrty with 
          | Some ty => Some ty 
          | _ => None
        end) (typeof n l t)
  end.
      
Eval compute in typeof 0 nil (Abs One Unit).

Definition check : forall n l t ty, option (Derivation (n ; l |= t @ ty)).
Proof. 
  refine 
    (fix check (n : nat) (l : list Ty) (t : Term) (ty : Ty) {struct t} : option (Derivation (n ; l |= t @ ty)) :=
      (match t as t' return t = t' -> option (Derivation (n ; l |= t @ ty)) with 
         | V n' => match le_lt_dec (length l) n' with 
                     | left p => (fun _ => None (A:=Derivation (n; l |= t @ ty)))
                     | right p => 
                       match ty_eq_dec (nth n' l Zero) ty with 
                         | left p' => _
                         | right p' => (fun _ => None (A:=Derivation (n; l |= t @ ty)))
                       end
                   end
         | App r s => (fun r' s' => _) (check n l r (Imp tyx ty)) (check n l s tyx)
         | Abs ty' s => _
         | TApp r ty' => _
         | Lam s => _
       end) (refl_equal t)).
  (* V -- using firstorder as a stand-in for failure *)
  intros. apply Some. apply (VarIntro n l ty) in p.  rewrite <- H0 in p. auto. auto. intros. 
  (* App *) 
  apply (check n l r

Defined.
Print check.


  



