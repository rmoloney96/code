
Fixpoint fact (x:nat) := 
  match x with 
    | 0 => 1 
    | S x' => x * fact x'
  end.

fact _|_ => 

match _|_ with 
  | 0 => 1 
  | S x' => x * fact x' 
end