module vec where 

data Nat : Set where 
  zero : Nat 
  succ : Nat → Nat

data Vec (A : Set) : Nat → Set where 
  [] : Vec A zero 
  _::_ : A → Vec A n → Vec A (succ n)

one = succ zero
two = succ one
three = succ two

_++_