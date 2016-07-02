Class EqDec (Eq : Type -> Type) :=
  A : Type ;
  eq_dec : forall (x y:A), {x = y} + {x <> y}. 

Hint Resolve @eq_dec : eq_dec.

Notation "A == B" := (eq_dec A B) (at level 90).