
Require Import List. 

Fixpoint rev (x : list nat) (y : list nat) {struct x} : list nat := 
  match x with 
    | nil => y 
    | cons xh xt => rev xt (cons xh y)
  end.

Eval compute in (rev (cons 1 (cons 2 (cons 3 nil)))) nil.