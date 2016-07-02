
Definition plus_z : forall n, n + O = n := (fun n => refl_equal n).

Close Scope nat_scope.

Inductive nat : Set := 
| O : nat 
| S : nat -> nat.

Fixpoint plus (n m : nat) : nat := 
  match m with 
    | O => n 
    | S m' => S (n + m') 
  end 
where "n + m" := (plus n m).


Definition plus_z : forall n, n + O = n := (fun n => refl_equal n).
