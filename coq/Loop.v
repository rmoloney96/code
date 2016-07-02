
CoInductive cotrue : Set := 
| d : cotrue -> cotrue.

Axiom loop : cotrue -> cotrue -> cotrue.

Lemma test : cotrue.
Proof.
  refine (cofix x (a : cotrue) : cotrue := (d (loop (d (x a)) (d (x a))))).
Defined. 