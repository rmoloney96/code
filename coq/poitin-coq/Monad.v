Class Monad (M : Type -> Type) :=
  ret : forall `A`, A -> M A ; 
  bind : forall `A B`, M A -> (A -> M B) -> M B ;

  bind_ret_left : forall A B (x : A) (f : A -> M B),
    bind (ret x) f = f x ;

  bind_ret_right : forall A (x : M A), bind x ret = x ;

  bind_assoc : forall A B C (x : M A) (f : A -> M B) (g : B -> M C),
    bind x (fun a : A => bind (f a) g) = bind (bind x f) g.

Hint Resolve @bind_ret_left @bind_ret_right @bind_assoc : monad.

Notation "T >>= U" := (bind T U) (at level 55).
Notation "T >> U" := (bind T (fun _ => U)) (at level 55).
Notation "x <- T ;; E" := (bind T (fun x : _ => E)) (at level 30, right associativity).