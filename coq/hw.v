
Parameter (C:Type). 
Lemma test : False -> C.

intros. inversion H.
Proof.   

Parameter (A:Set) (P Q: A -> Prop).

Lemma lm3 : (exists x, forall R : A -> Prop, R x) -> 2 = 3.
intros. 
inversion H. 
apply (H0 (fun _ => 2 = 3)).
Defined.

Print lm3.