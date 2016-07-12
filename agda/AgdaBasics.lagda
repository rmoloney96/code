\begin{code}

module AgdaBasics where

data Bool : Set where 
  true : Bool 
  false : Bool

myFun : Bool → Bool
myFun true = false
myFun false = false

not : Bool -> Bool 
not true = false 
not false = true

data Nat : Set where 
  zero : Nat 
  succ : Nat -> Nat

_+_ : Nat -> Nat -> Nat
zero + m = m 
succ n + m = succ (n + m)

\end{code}

This is not code.

I can say anything I want here...

\begin{code}
-- This is code...

\end{code}
