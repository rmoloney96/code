module Filter where 

codata CoNat : Set where 
  czero : CoNat
  csucc : CoNat -> CoNat

codata CoList (A : Set) : Set where 
  [] : CoList A
  _::_ : A -> CoList A -> CoList A

infixr 40 _+_
_+_ : CoNat -> CoNat -> CoNat
czero     + y = y 
(csucc x) + y = csucc (x + y)

sumlen : CoList CoNat -> CoNat
sumlen []        = czero 
sumlen (x :: xs) = csucc (x + (sumlen xs))

data Bool : Set where 
  true : Bool 
  false : Bool 

data List (A : Set) : Set where 
  [] : List A
  _::_ : A -> List A -> List A

data Nat : Set where 
  zero : Nat 
  succ : Nat -> Nat

if_then_else_ : { A : Set } -> Bool -> A -> A -> A
if true then x else y = x
if false then x else y = y

infix 5 if_then_else_

infixr 40 _::_
codata Stream (A : Set) : Set where 
  _::_ : A -> Stream A -> Stream A

le : Nat -> Nat -> Bool 
le zero _ = true 
le _ zero = false 
le (succ x) (succ y) = le x y

pred : Nat -> Nat
pred zero = zero 
pred (succ x) = x

f : Stream Nat -> Stream Nat
f (x :: y :: xs) = if (le x y)
                   then (x :: (f (y :: xs)))
                   else (f ((pred x) :: y :: xs))

mutual 
  p : Stream Nat -> Stream Nat 
  p (zero   :: y      :: xs) = zero :: (p (y :: xs))
  p (succ x :: zero   :: xs) = g x xs
  p (succ x :: succ y :: xs) with le x y 
  ...                        | true  = (succ x) :: (p ((succ y) :: xs))
  ...                        | false = h x y xs

  g : Nat -> Stream Nat -> Stream Nat
  g zero xs = zero :: (p (zero :: xs))
  g (succ x) xs = g x xs

  h : Nat -> Nat -> Stream Nat -> Stream Nat
  h zero     y xs = zero :: (p ((succ y) :: xs))
  h (succ x) y xs with le x y
  ...             | true  = (succ x)::(p ((succ y) :: xs))
  ...             | false = h x y xs

join : CoNat -> CoNat -> CoNat
join czero x = czero
join x czero = czero
join (csucc x) (csucc y) = csucc (join x y)

ex : { A : Set } -> (A -> CoNat) -> Stream A -> CoNat
ex p (x :: xs) = join (p x) (ex p xs)

