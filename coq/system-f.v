
Require Import Arith.
Require Import List. 

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

Fixpoint tyshift (ty : Ty) (d : nat) {struct ty} : Ty := 
  match ty with 
    | TV m => if le_lt_dec d m then TV (S m) else TV m
    | Imp t s => Imp (tyshift t d) (tyshift s d) 
    | All t => All (tyshift t (S d)) 
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
        | All t => All (tysub t (S n) (tyshift s n))
      end).
  destruct m. apply le_n_O_eq in p. apply p'. auto. inversion p''.
Defined.

Print tysub.

Fixpoint tysubt (t : Term) (n : nat) (s : Ty) {struct t} : Term := 
  match t with 
    | V m => V m
    | Abs ty t => Abs (tysub ty n s) (tysubt t n s)
    | Lam t => Lam (tysubt t (S n) s)
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
  case_eq (le_lt_dec n0 n). intros. right. simpl. rewrite H0. auto.
  intros. left. simpl. rewrite H0. auto.
  (* Imp *)
  simpl. 
  (* All *) 
  firstorder.
Defined.

Print valid_dec.

 Lemma tyshift_level : forall ty1 n, 
   valid ty1 n -> valid (tyshift ty1 n) (S n).
 Proof.
   induction ty1.
   (* TV *) 
   intros. simpl.
   case_eq (le_lt_dec n0 n). simpl. intros. rewrite H1. 
   simpl in H0. rewrite H1 in H0. inversion H0.
   intros. simpl. destruct n. auto.
   case_eq (le_lt_dec n0 n). intros. simpl. omega. simpl. intros. auto.
   (* Imp *)
   intros. simpl in H0.  inversion H0. 
   simpl. auto.
   (* All *) 
   intros. simpl in H0. simpl. apply IHty1. auto.
 Defined.

 Lemma tysub_level : forall ty1 ty2 n, 
   valid ty1 (S n) -> valid ty2 n -> valid (tysub ty1 n ty2) n.
 Proof.
   induction ty1. intros. 
   (* TV *)
   simpl.
   case_eq (le_lt_dec n0 n); case_eq (eq_nat_dec n0 n) ; intros ; auto.
   destruct n. absurd (n0 <> 0). omega. omega. 
   simpl in H0. case_eq (le_lt_dec n0 n). intros. rewrite H4 in H0. simpl in H0. inversion H0.
   intros. clear H0.  absurd (n0 <> S n). intros. omega. omega. 
   absurd (n0 = n). omega. omega. simpl. rewrite H3. auto.
   (* Imp *)
   intros. simpl in H0. inversion H0. simpl. split. auto. auto.
   (* All *)
   intros. simpl in H0. simpl. 
   apply IHty1. auto. 
   (* need tyshift lemma *)
   apply tyshift_level. auto.
 Defined.

 Definition Zero := (All (TV 0)).
 Definition One := (Imp Zero Zero).

 Inductive Derivation : Holds -> Set := 
 | ImpIntro : forall n l t ty xty,
   valid xty n ->
   Derivation (n ; l |= t @ ty) -> 
   Derivation (n ; xty::l |= (Abs xty t) @ (Imp xty ty))
 | ImpElim : forall n l t f ty xty,
   Derivation (n ; l |= t @ xty) ->
   Derivation (n ; l |= f @ (Imp xty ty)) -> 
   Derivation (n ; l |= (App f t) @ ty)
 | AllIntro : forall n l t ty,
   Derivation (S n ; l |= t @ ty) -> 
   Derivation (n ; l |= (Lam t) @ All ty)
 | AllElim : forall n l t ty xty,
   Derivation (n ; l |= (TApp t xty) @ ty) -> 
   Derivation (S n ; l |= t @ (tysub ty n xty))
 | VarIntro : forall n l ty i,
   i < length l -> nth i l Zero = ty ->
   Derivation (n ; l |= V i @ ty)
 | Weaken : forall n l t ty ty',
   valid ty' n ->
   Derivation (n ; l |= t @ ty) -> 
   Derivation (n ; (l++(ty'::nil)) |= t @ ty)
 | WeakenTy : forall n l t ty, 
   Derivation (n ; l |= t @ ty) -> 
   Derivation (S n ; l |= t @ ty).

 Fixpoint typeof (n : nat) (l : list Ty) (t : Term) {struct t} : option Ty := 
   match t with 
     | V n' => 
       if le_lt_dec (length l) n' 
         then None 
         else Some (nth n' l Zero)
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
           | Some (All ty') => Some (tysub ty' n ty)
           | _ => None
         end) (typeof n l r)
     | Abs ty r => 
       (fun mrty => 
         match mrty with 
           | Some ty' => Some (Imp ty ty')
           | _ => None
         end) (typeof n (ty::l) r)
     | Lam r => 
       (fun mrty => 
         match mrty with 
           | Some ty' => Some (All ty')
           | _ => None
         end) (typeof (S n) l r)
  end.
      
Eval compute in typeof 0 nil (Lam (Abs (TV 3) (V 0))).

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


  



