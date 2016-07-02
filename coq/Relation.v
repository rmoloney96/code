

Variable Term : Prop. 
Variable R : Term -> Term -> Prop. 
Variable succ : Term -> Term.
Variable alt : Term -> Term -> Term.  

Axiom rel1 : forall c d e, R (alt c (succ d)) (alt (succ c) e).
Axiom rel2 : forall c d e, R (alt (succ c) d) (alt c (succ d)).

Axiom relanti : forall c d, R c d -> R d c -> False.
Axiom reltrans : forall c d e, R c d -> R d e -> R c e. 

Theorem relbot : forall a b : Term, False.
Proof.
  intros.
  apply (relanti (alt (succ a) b) (alt a (succ b))). 
  eapply rel2.
  eapply rel1.
Defined. 
