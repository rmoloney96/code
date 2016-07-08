
open import Data.Vec
open import Data.Nat
--open import Relation.Binary.PropositionalEquality as PropEq
--  using (_≡_; refl; sym; subst; trans; cong; cong₂)
open import Relation.Binary.HeterogeneousEquality as HetEq
  using (_≅_; refl; sym; subst; trans; cong; cong₂)

module Vector where 

dapp : ∀ {a m n k} {A : Set a} → Vec A m → Vec A n → Vec A k → Vec A (m + n + k)
dapp [] v w = v ++ w
dapp (x ∷ xs) v w = x ∷ (dapp xs v w)

test : Vec ℕ 0
test = dapp [] [] []

{-
rev : ∀ {a m n} → Vec a m → Vec a n → Vec a (m + n)
rev [] ys = ys
rev (x ∷ xs) ys = rev xs (x ∷ ys)     -- (**) 
-}

eq1 : ∀ {a m n} {A : Set a} (xs : Vec A m) (x : A) (ys : Vec A n) → (xs ++ [ x ]) ++ ys ≅ xs ++ (x ∷ ys)
eq1 [] x [] = refl
eq1 [] x (x' ∷ xs) = refl
eq1 (x ∷ xs) x' ys = {!!} 

-- map g Γ ++ g α ∷ map g Γ' ≡ map g (Γ ++ α ∷ Γ')


{-
map-++-commute : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) xs ys →
                 map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++-commute f []       ys = refl
map-++-commute f (x ∷ xs) ys =
  P.cong (_∷_ (f x)) (map-++-commute f xs ys)

sum-++-commute : ∀ xs ys → sum (xs ++ ys) ≡ sum xs + sum ys
sum-++-commute []       ys = refl
sum-++-commute (x ∷ xs) ys = begin
  x + sum (xs ++ ys)
                         ≡⟨ P.cong (_+_ x) (sum-++-commute xs ys) ⟩
  x + (sum xs + sum ys)
                         ≡⟨ P.sym $ +-assoc x _ _ ⟩
  (x + sum xs) + sum ys
 -}