Require Import MyUtils. 
Require Import Atom. 
Require Import List. 
Require Import Metatheory.

(* Infix "==" := eq_atom_dec (at level 90). *)

(* Instead of notation, we can use a type-class with the following file *)
(* However, we should probably stick all decidable equalities into the class *)
(* and get something like MLs eq types. *) 
(* Require Import EqAtomDec. *) 

(* Define preterms *)
Inductive term : Set := 
| bvar : nat -> term
| fvar : atom -> term
| abs : term -> term
| func : atom -> term
| app : term -> term -> term
| letrec : atom -> term -> term -> term
| con : atom -> list term -> term
| cas : term -> list (atom * nat * term) -> term.
Coercion bvar : nat >-> term.
Coercion fvar : atom >-> term.

(* Because of Coq stupidity, we end up with a bad inductive principle, we need to make our own and prove it *)
Reset term_rect.

Require Import Peano_dec.

Definition term_eq_dec : forall (t0 t1:term), {t0 = t1} + {t0 <> t1}.
  refine 
    (fix term_eq_dec (t':term) (t'':term) {struct t'} : {t' = t''} + {t' <> t''} := 
      match t', t'' return {t' = t''} + {t' <> t''} with 
        | bvar n, bvar n' => match eq_nat_dec n n' with | left _ => _ | right _ => _ end
        | fvar s, fvar s' => match s == s' with | left _ => _ | right _ => _ end
        | abs t0, abs t1 => match term_eq_dec t0 t1 with | left _ => _ | right _ => _ end
        | func s, func s' => match s == s' with | left _ => _ | right _ => _ end
        | app M N, app M' N' => match term_eq_dec M M' with 
                                  | left _ => match term_eq_dec N N' with | left _ => _ | right _ => _ end
                                  | right _ => _ 
                                end 
        | letrec s e1 e2, letrec s' e1' e2' => match s == s' with 
                                                 | left _ => match term_eq_dec e1 e1' with 
                                                               | left _ => match term_eq_dec e2 e2' with 
                                                                             | left _ => _ 
                                                                             | right _ => _ 
                                                                           end
                                                               | right _ => _ 
                                                             end
                                                 | right _ => _
                                               end
        | con c lt0, con c' lt1 => match c == c' return {con c lt0 = con c' lt1} + {con c lt0 <> con c' lt1} with 
                                     | left _ => _ | right _ => _ 
                                   end
        | cas t0 trip, cas t1 trip' => match term_eq_dec t0 t1 with
                                         | left _ => _
                                         | right _ => _ 
                                       end
        | _,_ => right _ _
      end) ; try (right ; congruence) ; try (congruence) ; try (subst ; left ; clear term_eq_dec ; auto; fail).
  (* constructors *)
  subst. generalize dependent lt1 ; generalize dependent lt0 ; induction lt0.
  destruct lt1. left ; clear term_eq_dec ; auto. right ; congruence.
  induction lt1. right ; congruence. case (term_eq_dec a a0). intros. subst.
  case (IHlt0 lt1). intros. inversion e. rewrite <- H0. left. reflexivity. 
  intros. right. congruence.
  intros. right. congruence.
  (* case *)
  subst. generalize dependent trip' ; generalize dependent trip ; induction trip as [|a1].
  destruct trip'. left. clear term_eq_dec ; auto. right ; congruence.
  induction trip' as [|a2]. right ; congruence. 
  generalize dependent a2. generalize dependent a1. destruct a1 as [pa1 ta1]. destruct a2 as [pa2 ta2].
  case (term_eq_dec ta1 ta2). intros. subst.
  case ((pair_eq_dec eq_atom_dec eq_nat_dec) pa1 pa2).
  intros. subst. case (IHtrip trip'). intros. inversion e. subst. left. reflexivity.
  intros. right. congruence. intros. right. congruence. intros. right. congruence.
Defined. 

Definition snt_dec := (pair_eq_dec (pair_eq_dec eq_atom_dec eq_nat_dec) term_eq_dec).  
Definition st_dec := (pair_eq_dec eq_atom_dec term_eq_dec). 

Definition term_rect :  
  forall P : term -> Type,
    (forall n : nat, P (bvar n)) ->
    (forall s : atom, P (fvar s)) ->
    (forall t : term, P t -> P (abs t)) ->
    (forall s : atom, P (func s)) ->
    (forall t0 : term, P t0 -> forall t : term, P t -> P (app t0 t)) ->
    (forall (s : atom) (t1 t2:term), P t1 -> P t2 -> P (letrec s t1 t2)) ->
    (forall (s : atom) (l : list term), (forall t, Member term_eq_dec t l -> P t) -> P (con s l)) ->
    (forall t0 : term, P t0 -> 
      forall l : list (atom * nat * term), 
        (forall triple, Member snt_dec triple l -> P (snd triple)) -> P (cas t0 l)) -> 
    forall t : term, P t. 
Proof.
  intros P Hbv Hfv Habs Hfunc Happ Hlr Hcon Hcas.
  refine (fix IH (t:term) {struct t} := _).
  case t.
  (* bound vars  *) apply Hbv. (* free vars *) apply Hfv.
  (* abs *) 
  intros ; apply Habs ; apply IH.
  (* func *) apply Hfunc.  
  (* app *)
  intros ; apply Happ ; apply IH.
  (* letrec *) 
  intros ; apply Hlr ; apply IH.
  (* constructors *)
  intros. apply Hcon. 
    induction l. intros t' Hin. inversion Hin.  
    intros t' Hin. simpl in Hin. destruct (term_eq_dec t' a0).
    subst t'. apply IH.  
    apply IHl. exact Hin.
  (* case *) 
  intros. apply Hcas. apply IH. 
    induction l. intros triple Hin. inversion Hin.
    intros triple Hin. simpl in Hin. destruct (snt_dec triple a).
    subst triple. apply IH.
    apply IHl. exact Hin.
Defined.

Definition term_rec :  
  forall P : term -> Set,
    (forall n : nat, P (bvar n)) ->
    (forall s : atom, P (fvar s)) ->
    (forall t : term, P t -> P (abs t)) ->
    (forall s : atom, P (func s)) ->
    (forall t0 : term, P t0 -> forall t : term, P t -> P (app t0 t)) ->
    (forall (s : atom) (t1 t2:term), P t1 -> P t2 -> P (letrec s t1 t2)) ->
    (forall (s : atom) (l : list term), (forall t, Member term_eq_dec t l -> P t) -> P (con s l)) ->
    (forall t0 : term, P t0 -> 
      forall l : list (atom * nat * term), 
        (forall triple, Member snt_dec triple l -> P (snd triple)) -> P (cas t0 l)) -> 
    forall t : term, P t. 
Proof.
  intros P Hbv Hfv Habs Hfunc Happ Hlr Hcon Hcas ; apply term_rect ; auto.
Defined.

(* For Prop, we use the `In' predicate since proofs are less involved. *)
Definition term_ind :  
  forall P : term -> Prop,
    (forall n : nat, P (bvar n)) ->
    (forall s : atom, P (fvar s)) ->
    (forall t : term, P t -> P (abs t)) ->
    (forall s : atom, P (func s)) ->
    (forall t0 : term, P t0 -> forall t : term, P t -> P (app t0 t)) ->
    (forall (s : atom) (t1 t2:term), P t1 -> P t2 -> P (letrec s t1 t2)) ->
    (forall (s : atom) (l : list term), (forall t, In t l -> P t) -> P (con s l)) ->
    (forall t0 : term, P t0 -> 
      forall l : list (atom * nat * term), 
        (forall triple, In triple l -> P (snd triple)) -> P (cas t0 l)) -> 
    forall t : term, P t. 
Proof.
  intros P Hbv Hfv Habs Hfunc Happ Hlr Hcon Hcas. apply term_rect ; auto using in_imp_member.
Defined.

(* Substitute term 'e' for a free variable *)
Fixpoint subst (z : atom) (u : term) (e : term) {struct e} : term :=
  match e with
    | bvar i => bvar i
    | fvar v => if v == z then u else (fvar v)
    | abs e1 => abs (subst z u e1)
    | func f => func f
    | app e1 e2 => app (subst z u e1) (subst z u e2)
    | letrec v e1 e2 => 
      if v == z 
        then (letrec v e1 e2) 
        else (letrec v (subst z u e1) (subst z u e2))
    | con c l => con c (List.map (subst z u) l)
    | cas e l => 
      cas (subst z u e)
      (List.map 
        (fun pv => 
          match pv with 
            | ((c,vars),exp) => ((c,vars),subst z u exp)
          end) l)
  end.
 
Notation "[ z ~> u ] e" := (subst z u e) (at level 68).

Fixpoint open_rec (k : nat) (u : term) (e : term) {struct e} : term :=
  match e with
    | bvar i => if k === i then u else (bvar i)
    | fvar x => fvar x
    | func f => func f
    | abs e1 => abs (open_rec (S k) u e1)
    | app e1 e2 => app (open_rec k u e1) (open_rec k u e2)
    | letrec v e1 e2 => (letrec v (open_rec k u e1) (open_rec k u e2))
    | con c l => con c (List.map (open_rec k u) l)
    | cas e l => 
      cas (open_rec k u e)
      (List.map 
        (fun pv => 
          match pv with 
            | (c,d,exp) => (c,d,open_rec (k+d) u exp)
          end) l)
  end.

Notation "{ k ~> u } t" := (open_rec k u t) (at level 67).

(* opening that just replaces an outermost abstraction *)
Definition open e u := open_rec 0 u e.
 
Definition open_times n e u := 
  match n with 
    | 0 => e
    | S n' => open_rec n' u e
  end.

(* Convert a free variable b to a bound index i in a term *)
Fixpoint abstract (i:nat) (b:atom) (e:term) := 
  match e with
    | bvar j => bvar j
    | fvar v => if v == b then (bvar i) else (fvar v)
    | letrec v e1 e2 => letrec v (abstract (i+1) b e1) (abstract (i+1) b e1)
    | abs e1 => abs (abstract (i+1) b e1)
    | con c l => con c (List.map (abstract i b) l)
    | app e1 e2 => app (abstract i b e1) (abstract i b e2)
    | func f => func f
    | cas e l => 
      cas (abstract i b e) 
      (List.map (fun pv => 
        match pv with 
          | (c,step,exp) => (c,step, abstract (i+step) b exp)
        end) l)
  end.

Require Import Compare_dec. (* needed for le_lt_dec  {a =< b} + {a > b} *)

Fixpoint shift (i:nat) (d:nat) (u:term) : term := 
  match i with 
    | 0 => u 
    | S i' => 
      match u with 
        | bvar j => if le_lt_dec d j then bvar (j+1) else bvar j
        | fvar v => fvar v
        | letrec v e1 e2 => letrec v (shift i (d+1) e1) (shift i (d+1) e2)
        | abs e1 => abs (shift i (d+1) e1)
        | con c l => con c (List.map (shift i d) l)
        | app e1 e2 => app (shift i d e1) (shift i d e2)
        | func f => func f
        | cas e l => 
          cas (shift i d e) 
          (List.map (fun pv => 
            match pv with 
              | (c,step,exp) => (c,step, shift i (d+step) exp)
            end) l)
      end
  end.

(* This is totally wrong, use fsets *)
Notation env := (list (atom*term)).

(* replace free variables with terms from the environment 

!! is, 'not' 'not' which converts sigmas to booleans *) 
Fixpoint inst (env:env) (e:term) : term := 
  match e with 
    | bvar j => bvar j
    | fvar v => match assoc (fun x => !! (x==v)) env with
                  | None => fvar v
                  | Some a => a
                end
    | letrec v e1 e2 => letrec v (inst env e1) (inst env e2)
    | abs e1 => abs (inst env e1)
    | con c l => con c (List.map (inst env) l)
    | app e1 e2 => app (inst env e1) (inst env e2)
    | func f => func f
    | cas e l => 
      cas (inst env e) 
      (List.map (fun pv => 
        match pv with 
          | (c,step,exp) => (c,step, inst env exp)
        end) l)
  end.

Fixpoint replace (t:term) (u:term) (e:term) {struct e} : term := 
  match e with 
    | abs t' => if term_eq_dec t (abs t') then u else abs (replace (shift 1 0 t) u t')
    | letrec v t1 t2 =>  if term_eq_dec t (letrec v t1 t2) then u else letrec v (replace t u t1) (replace (shift 1 0 t) u t2)
    | con c ts => if term_eq_dec t (con c ts) then u else con c (List.map (replace t u) ts)
    | app t1 t2 => if term_eq_dec t (app t1 t2) then u else app (replace t u t1) (replace t u t2)
    | cas t' bs => 
      if term_eq_dec t (cas t' bs) 
        then u 
        else cas (replace t u t') (List.map (fun x => match x with 
                                                   | (c,step,e) => (c,step,(replace (shift step 0 t) u e)) 
                                                 end) bs)
    | t' => if term_eq_dec t t' then u else t'
  end.

Fixpoint freevars (t : term) := 
  match t with 
    | bvar j => {}
    | fvar v => singleton v
    | letrec v e1 e2 => (freevars e2) `union` (freevars e1)
    | abs e1 => freevars e1
    | con c ts => fold_right (fun t' vs' => (freevars t') `union` vs') {} ts
    | app e1 e2 => (freevars e2) `union` (freevars e1)
    | func f => {}
    | cas e cs => fold_right (fun tr vs' => match tr with (c,n,t') => (freevars t') `union` vs' end) (freevars e) cs
  end.

Tactic Notation "subst" "++" :=
  repeat (
    match goal with
      | x : _ |- _ => subst x
    end);
  cbv zeta beta in *.

(* Prove the correctness of substitution *) 
Lemma subst_fresh : forall (x : atom) e u,
  x `notin` (freevars e) -> [x ~> u] e = e.
Proof.
  induction e ; intros ; simpl in * ; auto.
  (* fvar *) 
  case_eq (s == x) ; intros ; subst++ ; simpl in * ; auto ; try notin_solve.
  (* abs *)
  cut ([x ~> u]e = e). intros. rewrite H0. auto. apply IHe. auto. 
  (* app *)
  cut ([x ~> u]e1 = e1 /\ [x ~> u]e2 = e2). intros. destruct H0 as [He1 He2]. rewrite He1 ; rewrite He2 ; auto.
  split. apply IHe1. auto. apply IHe2. auto.
  (* letrec *) 
  case_eq (s == x) ; intros ; subst++ ; simpl in * ; auto ; try notin_solve.
  cut ([x ~> u]e1 = e1 /\ [x ~> u]e2 = e2). intros. destruct H1 as [He1 He2]. rewrite He1 ; rewrite He2 ; auto.
  split. apply IHe1. auto. apply IHe2. auto.
  (* con *) 
  induction l. auto. simpl.
  cut ([x ~> u]a = a). intros H1. rewrite H1. 
  cut (con s (List.map (subst x u) l) = con s l). intros H2. inversion H2 as [H4]. rewrite H4. rewrite H4. auto.
  apply IHl. intros. apply H. simpl. right. auto. auto. simpl in H0. auto. apply H. simpl. left. auto.
  simpl in H0. notin_solve.
  (* cas *) 
  induction l. simpl. f_equal. apply IHe. simpl in H0. auto.
  cut (cas ([x ~> u]e)
          (List.map
             (fun pv : atom * nat * term =>
              let (y, exp) := pv in
              let (c, vars) := y in (c, vars, [x ~> u]exp)) l) = 
        cas e l).
  intros Heq. inversion Heq as [Heeq]. rewrite Heeq. simpl.
  induction a. induction a. f_equal. auto. f_equal. 
  f_equal. change b with (snd (a,b0,b)). apply H. simpl. left. auto. 
  simpl in H0. simpl. notin_solve.
  rewrite H1. rewrite H1. auto. 
  (* finally! application of the inductive hypothesis.  there has to be an easier way... *)
  apply IHl. intros.  apply H. simpl. right. auto. auto.
  simpl in H0. destruct a. destruct p. notin_solve.
Defined.

Require Import Arith.
(* Local Closure so we can move from talking about pre-terms to terms *) 
Inductive lc : term -> Prop :=
| lc_fvar : forall x,
  lc (fvar x)
| lc_abs : forall L e,
  (forall x:atom, x `notin` L -> lc (open e (fvar x))) ->
  lc (abs e)
| lc_app : forall e1 e2,
  lc e1 ->
  lc e2 ->
  lc (app e1 e2)
| lc_letrec : forall e1 e2, 
  lc e1 -> 
  lc e2 -> 
  forall x, lc (letrec x e1 e2)
| lc_con : forall x l, 
  (forall t, In t l -> lc t) ->
  lc (con x l)
| lc_cas : forall L e1 l, 
  lc e1 ->
  (forall x:atom, x `notin` L -> 
    forall trip, In trip l -> 
      lc (open_times (snd (fst trip)) (snd trip) (fvar x))) -> 
  lc (cas e1 l).
Hint Constructors lc.   


(* These tests motivate the notation that lc correctly captures local closure *) 
Lemma lc_test1 : forall x y z, lc (letrec x (fvar y) (fvar z)).
Proof.
  intros. auto.
Defined.

Notation "#<>#" := nil.
Notation "#< a >#" := (cons a nil).
Notation "#< a , .. , b >#" := (cons a .. (cons b nil) ..).

(* need to gather atoms from letrec, or this is bogus *)
Ltac gather_atoms :=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  constr:(A `union` B).

Tactic Notation "pick" "fresh" ident(x) :=
  let L := gather_atoms in
  (pick fresh x for L).

Tactic Notation
      "pick" "fresh" ident(atom_name) "and" "apply" constr(lemma) :=
  let L := gather_atoms in
  pick fresh atom_name excluding L and apply lemma.

Lemma lc_test2 : lc (abs (bvar 0)). 
Proof.
  pick fresh y and apply lc_abs. compute. auto.
Defined.

Lemma lc_test3 : forall x Z S, lc (cas (fvar x) #< (Z,0,(fvar Z)) , (S,1,(bvar 1)) ># ) -> False.
Proof. 
  intros. inversion H. subst.
  pick fresh y for L. 
  apply H3 with (trip:=(S, 1%nat, bvar 1)) in Fr. simpl in Fr. inversion Fr.
  simpl. auto. 
Defined.  

Lemma lc_test4 : forall x Z S, lc (cas (fvar x) #< (Z,0,(fvar Z)) , (S,1,(bvar 0)) ># ).
Proof. 
  intros. 
  pick fresh y and apply lc_cas. auto.
  intros. destruct H. subst. simpl. auto.
  intros. destruct H. subst. simpl. compute. auto. inversion H. 
Defined.

(* Probably not needed.  We should use opening instead. 
Definition boundvars t := 
  (fix boundvars' (d:nat) (t : term) (bs : NatSet.t) {struct t} := 
    match t with 
      | bvar i => if (le_lt_dec d i) then NatSet.add i bs else bs
      | fvar v => bs
      | letrec v e1 e2 => boundvars' (d+1) e2 (boundvars' (d+1) e1 bs)
      | abs e1 => boundvars' (d+1) e1 bs
      | con c ts => fold_right (fun t' bs' => boundvars' d t' bs') bs ts
      | app e1 e2 => boundvars' d e2 (boundvars' d e1 bs)
      | func f => bs
      | cas e cs => fold_right (fun tr bs' => match tr with (c,n,t') => boundvars' (d+n) t' bs' end) bs cs
    end) 0 t NatSet.empty.
*)

Lemma open_lc_diff : forall e j v i u,
  i <> j ->
  {j ~> v} e = {i ~> u} ({j ~> v} e) ->
  e = {i ~> u} e.
Proof.
  induction e ; intros j v i u Hdiff.
  (* bvar *) 
  simpl in *. case (j === n) ; case (i === n) ; intros ; auto with arith ; try congruence. subst. simpl in H. 
  case_eq (n===n). intros. rewrite H0 in H. auto. intros. congruence.
  (* fvar *) 
  simpl in *. intros ; auto.
  (* abs *) 
  intros. simpl in *. f_equal. apply (IHe (S j) v (S i) u). omega. inversion H. auto.
  (* func *)
  intros. simpl. auto.
  (* app *)
  intros. simpl in *. inversion H. f_equal. apply (IHe1 j v i u) ; auto. apply (IHe2 j v i u) ; auto.
  (* letrec *) 
  intros. simpl in *. inversion H. f_equal. apply (IHe1 j v i u) ; auto. apply (IHe2 j v i u) ; auto.
  (* con *)
  intros. simpl in *. inversion H0. f_equal.
  induction l. simpl. auto. simpl. f_equal. eapply (H a) with (i:=i) (j:=j) (v:=v). simpl. auto. eexact Hdiff. 
  inversion H0. auto. apply IHl. intros ; auto. eapply (H t) with (i:=i0) (u:=u0) (j:=j0) (v:=v0); auto. simpl. right. auto. 
  simpl in H0. inversion H0. f_equal. simpl in H2. inversion H2. auto.
  (* cas *) 
  intros. simpl in *. inversion H0. clear H0. f_equal.    
  eapply IHe ; eauto.
  induction l. simpl. auto. simpl in *. f_equal. 
  inversion H3. clear H3. simpl in *. destruct a ; destruct p. inversion H1. clear H1.
  cut (snd (a,n,t) = {i+n ~> u} (snd (a,n,t))). intros. simpl in H0. rewrite <- H0. auto. 
  eapply H with (i:=i+n) (j:=j+n) (v:=v). auto. omega. auto.
  eapply IHl. intros. eapply H with (i:=i0) (j:=j0) (v:=v0). auto. auto. auto.
  inversion H3. clear H3. inversion H1. clear H1.  
  f_equal.
Defined.

Lemma open_lc : forall k u e, lc e -> e = {k ~> u} e.
Proof.
  intros.  generalize dependent k.
  induction H ; simpl ; try (intros ; f_equal ; intuition).
  (* abs *)
  simpl in *. intros. f_equal. 
  pick fresh x for L. intros.
  apply open_lc_diff with (i := S k) (j := 0) (u := u) (v := (fvar x)). auto. 
  unfold open in H0. apply H0. auto. 
  (* con *)
  induction l. simpl. auto. simpl. f_equal. apply H0. intuition. apply IHl. intros. apply H. right. auto.  
  intros. apply H0. right. auto.
  (* case *)   
  induction l. simpl. auto. simpl. f_equal. destruct a ; destruct p. 
  set (trip:=  (a, n, t)).
  pick fresh x for L.
  cut (open_times (snd (fst trip)) (snd trip) (fvar x) =
    {k ~> u}open_times (snd (fst trip)) (snd trip) (fvar x)). 
  change trip with (a,n,t). f_equal. 
  intros. destruct n. simpl in H1. rewrite plus_0_r. f_equal. auto. f_equal.
  eapply open_lc_diff with (i := k + S n) (j := n) (v := (fvar x)) (u:=u). omega. simpl in H2.
  unfold not in Fr.
  eapply H1 with (trip := trip) (k:=k+(S n)) in Fr. simpl in Fr. auto. simpl. left. auto. simpl.
  change (open_times n t (fvar x)) with (open_times (snd (fst trip)) (snd trip) (fvar x)). 
  eapply H1. auto. simpl. left. auto. 
  (* And finally the inductive hypothesis for lists *) 
  apply IHl. intros. apply H0. auto. simpl. right. auto. intros.
  simpl. apply H1. auto. intuition.
Defined.

Lemma subst_open_rec : forall e1 e2 u x k,
  lc u ->[x ~> u] ({k ~> e2} e1) = {k ~> [x ~> u] e2} ([x ~> u] e1).
Proof.
  induction e1; intros e2 u x k Hlc; try (simpl in *; f_equal; auto ; fail).
  (* bvar *)
  simpl ; case (k === n) ; intros ; auto.
  (* fvar *)
  simpl ; case (s == x) ; intros ; eapply open_lc ; auto.
  (* letrec *) 
  simpl ; case (s == x) ; intros ; subst. simpl. f_equal.
  cut ([x ~> u]{k ~> e2}e1_1 = {k ~> [x ~> u]e2}([x ~> u]e1_1)). intros. 
  

  
  eapply open_lc in Hlc.
  
eapply open_lc.
  generalize dependent ([x ~> u]e2). intros. eapply open_lc.
 
Defined.

Lemma subst_lc_invariant : forall (x : atom) u e, lc e -> lc u -> lc ([x ~> u] e).
Proof.
  intros x u e He Hu. 
  induction He ; try (simpl ; auto).
  (* fvar *)
  case (x0 == x) ; auto.
  (* abs *) 
  pick fresh y and apply lc_abs.
  cut (lc ([x ~> u]open e (fvar y))). intros. induction e ; auto. 
  apply H0.

Defined.

(* 
Fixpoint unfold fenv (t:term) : option term := 
  match t with 
    | cas e cs => res <- unfold fenv e ;; cas res cs
    | app (abs e1) e2 => ret (open e2 e1)
    | app e1 e2 => res <- unfold fenv e1 ;; unfold fenv (app res e2)
    | func f => (get f fenv)
    | t => ret t
  end.

Fixpoint redex (t:term) : term := 
  match t with 
    | app e1 e2 => redex e1 
    | cas t l => redex t 
    | _ => t
  end.
*)