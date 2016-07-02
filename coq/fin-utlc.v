Inductive Fin : nat -> Set :=
| fz : forall {n}, Fin (S n)
| fs : forall {n}, Fin (S n) -> Fin (S (S n)).

Definition fs' {n} (f : Fin n) : Fin (S n) :=
  match f with
    | fz _ => fs fz
    | fs _ i => fs (fs i)
  end.

Inductive L : nat -> Set :=
| var : forall {n}, Fin n -> L n
| lam : forall {n}, L (S n) -> L n
| app : forall {n}, L n -> L n -> L n.

Definition thick {n} (f g : Fin (S n)) : unit + Fin n.
Proof. 
  intros.
refine (
  (fix thick {n} (f g : Fin (S n)) : unit + Fin n :=
  match f in Fin n' return S n = n' -> unit + Fin n with
    | fz _ => fun e1 =>
      match g in Fin n'' return S n = n'' -> unit + Fin n with
        | fz _ => fun e2 => inl _ tt
        | fs _ g' => fun e2 => inr _ (@eq_rect _ _ Fin g' _ _)
      end
      (refl_equal _)
    | fs n' f' => fun e1 =>
      @eq_rect _ _ (fun n => (unit + Fin n)%type)
      (match g in Fin n'' return S n = n'' -> unit + Fin (S n') with
         | fz _ => fun e2 => inr _ fz
         | fs n'' g' => fun e2 => match thick _ f' _ (* g' *) return unit + Fin (S n') with
                                    | inl tt => inl _ tt
                                    | inr x => inr _ (fs' x)
                                  end
       end (refl_equal _))
      _ _
  end
  (refl_equal _))
  n f g
).

congruence.

injection e1; intro; subst.
injection e2; intro; subst.
refine (
  g'
).

congruence.
Defined.

Definition thin {n} : Fin n -> Fin (S n) -> Fin (S n).
Proof.
 intros n.
 refine (
   (fix thin {n} (f : Fin n) (g : Fin (S n)) : Fin (S n) :=
     match g in Fin n' return S n = n' -> Fin (S n) with
       | fz _ => fun e1 => fs' f
       | fs _ g' => fun e1 =>
         match f in Fin n'' return n = n'' -> Fin (S n) with
           | fz _ => fun e2 => fz
           | fs _ f' => fun e2 => @eq_rect _ _ Fin (fs (thin _ f' (@eq_rect _ _ Fin g' _ _))) _ _
         end (refl_equal _)
     end
     (refl_equal _)) n
 );congruence.
Defined.

Lemma thick_of_thin {n} i (f : Fin n) :
  thick i (thin f i) = inr _ f.
Admitted.

Definition thin' {n} : L n -> Fin (S n) -> L (S n).
Proof. 
  intros n. 
refine (
  (fix thin' {n} (t : L n) (i : Fin (S n)) : L (S n) :=
    match t in L n' return n = n' -> L (S n') with
      | var _ v => fun e1 => var (thin v (@eq_rect _ _ Fin i _ _))
      | lam _ b => fun e1 => lam (thin' _ b (@eq_rect _ _ Fin (fs' i) _ _))
      | app _ a b => fun e1 => app (thin' _ a (@eq_rect _ _ Fin i _ _))
                                   (thin' _ b (@eq_rect _ _ Fin i _ _))
    end (refl_equal _)) n
); congruence.
Defined.

Definition substitute {n} (term : L (S n)) (x : L n) (v : Fin (S n)) : L n.
Proof. 
intros.
refine (
  (fix substitute {n} (term : L (S n)) (x : L n) (v : Fin (S n)) : L n :=
    match term in L n' return S n = n' -> L n with
      | var n'' i => fun e1 =>
        match thick v (@eq_rect _ _ Fin i _ _) with
          | inl tt => x
          | inr i' => var i'
        end
    | app n'' a b => fun e1 =>
      @eq_rect _ _ L
      (app (substitute n (@eq_rect _ _ L a _ _) x v)
           (substitute n (@eq_rect _ _ L b _ _) x v))
      _ _
    | lam _ b => fun e1 =>
      lam (@eq_rect _ _ L
            (substitute _ b (@eq_rect _ _ L (thin' x v) _ _)
                            (@eq_rect _ _ Fin (fs' v) _ _))
            _ _)
  end
  (refl_equal _))
  n term x v
);congruence.
Defined.

Section test.
  Hypothesis a : L (S O).
  
  Eval compute in substitute (var fz) a fz.
  Eval compute in substitute (app (var fz) (var fz)) a fz.
  Eval compute in substitute (lam (app (var (fs fz)) (var fz))) (@var (S (S (S (S (S O))))) (fs (fs (fs (fs fz))))) fz.
  Eval compute in substitute (lam (app (var (fs fz)) (var fz))) a fz.
  (* because of wrapping and unwrapping (i.e. using (induction O S) instead of id, substitute (and hence everything based on it..) does not compute nicely with hypotheticals *)
  
End test.

Inductive Beta : forall n, L n -> L n -> Prop :=

| redex : forall n b x,
  Beta n (app (lam b) x) (substitute b x fz)

| congruence_app_left : forall n a a' b,
  Beta n a a' ->
  Beta n (app a b) (app a' b)
| congruence_app_right : forall n a b b',
  Beta n b b' ->
  Beta n (app a b) (app a b')
| congruence_lam : forall n b b',
  Beta (S n) b b' ->
  Beta n (lam b) (lam b').

Inductive Beta_star : forall n, L n -> L n -> Prop :=
| transitive_identity : forall n t,
  Beta_star n t t
| transitive_step : forall n t t' t'',
  Beta n t t' ->
  Beta_star n t' t'' ->
  Beta_star n t t''.

Inductive Beta_equiv : forall n, L n -> L n -> Prop :=
| Beta_reduce : forall n t t',
  Beta n t t' ->
  Beta_equiv n t t'

| Beta_equiv_refl : forall n t,
  Beta_equiv n t t
| Beta_equiv_symm : forall n t t',
  Beta_equiv n t t' ->
  Beta_equiv n t' t
| Beta_equiv_trans : forall n t t' t'',
  Beta_equiv n t t' ->
  Beta_equiv n t' t'' ->
  Beta_equiv n t t''

| Beta_equiv_cong_app_left : forall n a a' b,
  Beta_equiv n a a' ->
  Beta_equiv n (app a b) (app a' b)
| Beta_equiv_cong_app_right : forall n a b b',
  Beta_equiv n b b' ->
  Beta_equiv n (app a b) (app a b')
| Beta_equiv_cong_lam : forall n b b',
  Beta_equiv (S n) b b' ->
  Beta_equiv n (lam b) (lam b').

Section Combinator.
  Definition S := lam (lam (lam
    (let x := var (fs (fs (@fz O))) in
      (let y := var (fs (@fz (S O))) in
        (let z := var (@fz (S (S O))) in
          (app (app x z) (app y z))))))).
  Definition K := lam (lam (var (fs (@fz O)))).
  Definition I := lam (var (@fz O)).
  
  Lemma I_character {x} : Beta_equiv _ (app I x) x.
  Proof. 
    intros. 
    unfold I. 
    eapply Beta_equiv_trans.
    apply Beta_reduce.
    apply redex.
    simpl.
    apply Beta_equiv_refl.
  Defined.
  
  Lemma K_character {x y} : Beta_equiv _ (app (app K x) y) x.
  Proof.
    intros.
    unfold K.
    eapply Beta_equiv_trans.
    apply Beta_reduce.
    apply congruence_app_left.
    apply redex.
    simpl.
    eapply Beta_equiv_trans.
    apply Beta_reduce.
    apply redex.
    simpl. 
    unfold substitute. 
    
    Lemma substitution_lemma {n} x y i :
      Beta_equiv n (substitute (thin' x i) y i) x.
      induction x; simpl.
      
      rewrite (thick_of_thin i f).
      apply Beta_equiv_refl.
      
      eapply Beta_equiv_cong_lam.
      apply IHx.
      
      eapply Beta_equiv_trans.
      apply Beta_equiv_cong_app_left.
      apply IHx1.
      apply Beta_equiv_cong_app_right.
      apply IHx2.
    Defined.
    
    apply substitution_lemma.
  Defined.
  
  Lemma S_character {x y z} : Beta_equiv _ (app (app (app S x) y) z) (app (app x z) (app y z)).
    unfold S.
