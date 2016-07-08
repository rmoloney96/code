module Logic where 

open import Level
open import Data.Bool
open import Relation.Binary.PropositionalEquality as PropEq -- using (_≡_; refl; cong; cong₂; sym ) renaming (subst to sub≣) 

data Con : Set where
  CBase : Bool → Con
  CNext : Con → Con → Con

data Dis : Set where 
  DBase : Bool → Dis
  DNext : Dis → Dis → Dis

_↓_ : Bool → Bool → Bool 
false ↓ false = true 
false ↓ true = false 
true ↓ false = false 
true ↓ true = false

infixr 4 _↓_

⟦_⟧Con : Con → Bool 
⟦ CBase x ⟧Con = not x
⟦ CNext x n ⟧Con = ⟦ x ⟧Con ∧ ⟦ n ⟧Con

⟦_⟧Dis : Dis → Bool 
⟦ DBase x ⟧Dis = x
⟦ DNext n m ⟧Dis = ⟦ n ⟧Dis ↓ ⟦ m ⟧Dis

inj : Con → Dis 
inj (CBase x) = DNext (DBase x) (DBase x)
inj (CNext n m) = DNext (DNext (inj n) (inj n)) (DNext (inj m) (inj m))

true↓ : ∀ x → false ≡ (true ↓ x)
true↓ true = refl
true↓ false = refl

theorem : ∀ x → ⟦ x ⟧Con ≡ ⟦ inj x ⟧Dis
theorem (CBase true) = refl
theorem (CBase false) = refl
theorem (CNext x y) with theorem x
theorem (CNext x y) | p with theorem y
theorem (CNext x y) | p | q = conjecture ⟦ x ⟧Con ⟦ y ⟧Con ⟦ inj x ⟧Dis ⟦ inj y ⟧Dis p q
  where conjecture : ∀ x y a b → x ≡ a → y ≡ b → x ∧ y ≡ (a ↓ a) ↓ (b ↓ b)
        conjecture true true .true .true refl refl = refl
        conjecture true false .true .false refl refl = refl
        conjecture false true .false .true refl refl = refl
        conjecture false false .false .false refl refl = refl