module Sumlen where 

open import Coinduction

-- infixl 40 _::_  

data Colist (A : Set) : Set where 
  [] : Colist A
  _::_ : (x : A) (xs : ∞ (Colist A)) -> Colist A

data Conat : Set where 
  z : Conat 
  s : (∞ Conat) -> Conat

plus : Conat -> Conat -> Conat 
plus z y = y 
plus (s x) y = s (♯ (plus (♭ x) y))

sumlen : Colist Conat -> Conat
sumlen [] = z 
sumlen (x :: xs) = s (♯ (plus x (sumlen (♭ xs))))

sumlen' : Colist Conat -> Conat
sumlen' [] = z
sumlen' (x :: xs) = plus x (s (♯ (sumlen (♭ xs))))