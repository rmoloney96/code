
Require Import List.
Parameter A : Set.
Parameter B : Set.
Definition assoc_list := list (A * B)%type.
Parameter eq_dec : forall (x:A) (y:A),{x=y}+{x<>y}.

Lemma assoc : forall (x:A) (l: assoc_list),
  {y | In (x,y) l} + {forall (y:B), ~In (x,y) l}.
Proof. 
  intros x l. induction l.
    (* nil *)
    right. auto.
    (* cons *)
    case (eq_dec x (fst a)).
      (* x = fst p *)
      intros eq.
      left. exists (snd a). rewrite eq.
      case a. firstorder.
      (* x <> fst a *)
      intros neq.
      case IHl.
        (* subcase left *)
        intro leftcase.
        left. inversion leftcase. exists x0.
        apply or_intror. auto.
        (* subcase right *)
        intro rightcase.
        right.
        intros y NotIn.
        apply (rightcase y).
        inversion NotIn ; auto.
        rewrite H in neq.
        contradiction neq. auto.
Defined. 

Extraction assoc.
Print assoc.