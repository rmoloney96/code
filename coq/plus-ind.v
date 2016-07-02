
Theorem plus_assoc : 
  forall x y z, (x+y)+z = x+(y+z).
Proof.
  refine 
    (fix plus_assoc (x y z : nat) {struct x} : (x+y)+z = x+(y+z) := 
      (match x as x' return (x = x' -> (x+y)+z = x+(y+z)) with
         | 0 => _
         | S n => _
       end) (refl_equal x)) ; intros ; subst.
  simpl. auto.
  change (S n + y + z) with (S (n + y + z)).
  change (S n + (y + z)) with (S (n + (y + z))).
  cut (n + y + z = n + (y + z)).
  intros. rewrite H. auto.
  apply plus_assoc.
Defined.

Print plus_assoc.

x + (y + z) = 

match x with 
  | 0 => y + z
  | S x' => S (x' + (y + z))
end
  
(x + y) + z =

match (x + y) with 
  | 0 => z 
  | S n' => S (n' + z)
end

match (match x with 
         | 0 => y 
         | S n' => 