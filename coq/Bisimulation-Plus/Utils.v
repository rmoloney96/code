Require Import List. 

Section UtilsList. 
  
  Variable A : Type. 
  Hypothesis eq_dec : forall (x y : A), {x = y}+{x <> y}.


  Fixpoint mem (x : A) (l : list A) : bool := 
    match l with 
      | nil => false 
      | cons y l' => match eq_dec x y with 
                       | left P => true 
                       | right P => mem x l' 
                     end
    end.

End UtilsList.