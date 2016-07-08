
module Mu where

  open import Data.Vec
  open import Data.Nat
  open import Relation.Binary.HeterogeneousEquality

  postulate
    A : Set
    P : ∀ {m} -> Vec A m -> Set
    Q : ∀ {m} -> Vec A m -> Set
    red : ∀ {x m} -> {xs : Vec A m} -> P (x ∷ xs) -> P xs

    eq1 : ∀ {k} {a : Set k} {m n} (xs : Vec a m) (x : a) (ys : Vec a n) →
                  (xs ++ [ x ]) ++ ys ≅ xs ++ (x ∷ ys)

  thm' : ∀ {m n} (xs : Vec A m) → (zs : Vec A n) → P xs → Q (zs ++ xs)
  thm' [] _ _ = {!!}
  thm' (x ∷ xs) zs pxs with thm' xs (zs ++ [ x ]) (red pxs) --(red pxs) 
  thm' (x ∷ xs) zs pxs | p = {!!} 
{-
  thm' : ∀ {m n} (xs : Vec A m) → (zs : Vec A n) →
           P xs → Q (zs ++ xs)
  thm' [] _ _ = {!...!}
  thm' {suc m} {n} (x ∷ xs) zs pxs with (n + suc m) | zs ++ x ∷ xs |
sym (eq1 zs x xs)
  thm' {suc m} {n} (_∷_  x xs) zs pxs | ._ | ._ | refl  = thm' xs (zs
++ [ x ]) (red pxs)-}

  rev : ∀ {a m n} {A : Set a} → Vec A m → Vec A n → Vec A (m + n)
  rev [] ys = ys
  rev (x ∷ xs) ys = rev xs (x ∷ ys)     -- (**)
