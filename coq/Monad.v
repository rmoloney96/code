Class Monad (M : Type -> Type) :=
  unit : forall `A`, A -> M A ; 
  bind : forall `A B`, M A -> (A -> M B) -> M B ;

  bind_unit_left : forall A B (x : A) (f : A -> M B),
    bind (unit x) f = f x ;

  bind_unit_right : forall A (x : M A), bind x unit = x ;

  bind_assoc : forall A B C (x : M A) (f : A -> M B) (g : B -> M C),
    bind x (fun a : A => bind (f a) g) = bind (bind x f) g.

Hint Resolve @bind_unit_left @bind_unit_right @bind_assoc : monad.

Notation "T >>= U" := (bind T U) (at level 55).
Notation "T >> U" := (bind T (fun _ => U)) (at level 55).
Notation "x <- T ;; E" := (bind T (fun x : _ => E)) (at level 30, right associativity).