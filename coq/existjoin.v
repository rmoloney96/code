

CoInductive Sierp : Set := 
| T : Sierp
| DS : Sierp -> Sierp.

CoInductive CoEq : Sierp -> Sierp -> Prop := 
| coeq_base : CoEq T T
| coeq_next : forall x y, CoEq x y -> CoEq (DS x) (DS y).


CoFixpoint join (x : Sierp) (y : Sierp) : Sierp := 
  match x with 
    | T => T
    | DS x' => match y with 
                 | T => T
                 | DS y' => DS (join x' y')
               end
  end.

Require Import Streams.

Section Exists.

  Variable A : Set.
  
  CoFixpoint existsfun (f : Sierp -> Sierp) (xs : Stream A) (P : A -> Sierp) : Sierp := 
    match xs with 
      | Cons x' xs' => match (P x') with 
                         | T => T
                         | DS y => match (f y) with 
                                     | T => T 
                                     | DS y' => DS (existsfun (join y') xs' P)
                                   end
                       end
    end.

  CoFixpoint existsone (x : Sierp) (xs : Stream A) (P : A -> Sierp) : Sierp :=
    match xs with 
      | Cons x' xs' => match x with 
                         | T => T
                         | DS y' => match (P x') with 
                                      | T => T 
                                      | DS x'' => DS (existsone (join x'' y') xs' P)
                                    end
                       end
    end.

  Definition exist (xs : Stream A) (P : A -> Sierp) : Sierp := 
    match xs with 
      | Cons x' xs' => match (P x') with 
                         | T => T 
                         | DS y' => existsfun (join y') xs' P 
                       end
    end.

  Definition exist' (xs : Stream A) (P : A -> Sierp) : Sierp := 
    match xs with 
      | Cons x' xs' => match (P x') with 
                         | T => T 
                         | DS y' => existsone y' xs' P 
                       end
    end.


  Definition decomp (x : Sierp) : Sierp := 
    match x with 
      | T => T
      | DS x' => DS x'
    end.

  Lemma decomp_eql : forall x, x = decomp x.
    intro x. case x. simpl. auto.
    intros. simpl. auto.
  Defined.
  
  Lemma ex_same : forall xs P, CoEq (exist' xs P) (exist xs P).
  Proof.
    intros. rewrite (decomp_eql (exist' xs P)). 
    rewrite (decomp_eql (exist xs P)). 
    case_eq xs. intros.
  simpl. 
  case_eq (P a). 
  intros. simpl. apply coeq_base.
  intros.
  generalize s0 s.
  cofix.
  intros.
  case_eq s1.
  intros.
  case_eq s2. 
  intros. simpl. 
  case_eq (P a0). intros. apply coeq_base.
  intros. apply coeq_base.
  intros. 
  case_eq s2.
  intros. simpl.
  case_eq (P a0). intros. apply coeq_base.
  intros. 
  case_eq s5. intros. simpl.
End Exists.
