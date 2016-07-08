module Typecheck where 

data Nat : Set where 
  zero : Nat 
  succ : Nat → Nat

data Vec (A : Set) : Nat → Set where 
  [] : Vec A zero 
  _::_ : {n : Nat} → A → Vec A n → Vec A (succ n)

_+_ : Nat → Nat → Nat 
zero + m = m
(succ n) + m = succ (n + m)

_++_ : {A : Set} {n m : Nat} → Vec A n → Vec A m → Vec A (n + m)
[] ++ ys = ys
(x :: xs) ++ w = x :: (xs ++ w)

_+'_ : Nat → Nat → Nat 
n +' zero = n
n +' (succ m) = succ (n +' m)

data _==_ {A : Set} : A → A → Set where 
  refl : (a : A) → a == a

subst : {A : Set} → {C : A → Set} → (a a' : A) → a == a' → C a → C a'
subst .a .a (refl a) p = p

natrec : {C : Nat → Set} → (C zero) → ((m : Nat) → (C m) → (C (succ m))) → (n : Nat) → C n
natrec p1 p2 zero = p1 
natrec p1 p2 (succ n) = p2 n (natrec p1 p2 n)

eq-succ : {n m : Nat} → n == m -> (succ n) == (succ m)
eq-succ {.n} {.n} (refl n) = refl (succ n) 

eq-sym : {A : Set} {n m : A} → n == m → m == n 
eq-sym (refl a) = refl a 

+'-zero : (m : Nat) → (zero +' m) == m 
+'-zero m = natrec {λ m → (zero +' m) == m } (refl zero) (λ m' ih → eq-succ ih) m

+'-succ : (n m : Nat) → (succ n +' m) == (succ (n +' m))
+'-succ n m = natrec {λ m → (succ n +' m) == (succ (n +' m))} (eq-succ (refl n)) (λ m ih → eq-succ ih) m

testit : (n m : Nat) → (succ (n +' m)) == (succ n +' m)
testit n m = eq-sym (+'-succ n m) -- {!!}

+'-assoc : (n m : Nat) → (n +' m) == (m +' n)
+'-assoc (zero) m = +'-zero m
+'-assoc (succ n) m = subst {Nat} {λ r → r == succ (m +' n)} 
                      (succ (n +' m)) (succ n +' m) 
                      (eq-sym (+'-succ n m)) 
                      (eq-succ (+'-assoc n m))

_++'_ : {A : Set} {n m : Nat} → Vec A n → Vec A m → Vec A (n +' m)
_++'_ {A} {zero} {m} [] ys = subst {_} {λ r → Vec A r} _ _ (eq-sym (+'-zero m)) 
                             ys
_++'_ {A} {succ n} {m} (x :: xs)  ys = subst {_} {λ r → Vec A r} _ _ (eq-sym (+'-succ n m)) 
                                       (x :: (xs ++' ys))
