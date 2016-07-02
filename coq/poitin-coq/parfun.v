
Require Import Logic_Type.

Definition pf (A : Set) (B : Set) (D : A -> Prop) := {y : A & D y -> B}.

Lemma comp_domain_predicate : 
  forall A B C P1 P2 (f : pf A B P1) (g : pf B C P2),
    pf A C (fun (x : A) => match f with 
                             | existT x h => 
                               match (h P1 y)) with 
                                 | existT z i => exist x i
                               end 
                           end).
                             

    (fun (x : A) :  forall (A : x), D x -> C (f x) -> 
    
Proof. 
  intros.

Stuff like currying, uncurrying, dependent partial functions, theorems  
about partial functions...



{x : A | P x}