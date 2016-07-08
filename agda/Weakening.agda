module Weakening where 

open import Level

data ⊥ {ℓ} : Set ℓ where 
  
data ⊤ {ℓ} : Set ℓ where 
  tt : ⊤

data ℕ : Set where 
  z : ℕ 
  s : ℕ → ℕ

one = (s z) 
two = (s one) 
three = (s two)

_+_ : ℕ → ℕ → ℕ 
z + y = y
s x + y = s (x + y) 

data 𝔹 : Set where 
  true : 𝔹 
  false : 𝔹 

_≡ℕ_ : ℕ → ℕ → 𝔹
z ≡ℕ z = true
z ≡ℕ s y = false
s x ≡ℕ z = false
s x ≡ℕ s y = x ≡ℕ y

Eq : {A : Set} → (x : A) → (x : A) → Set
Eq x y = 


record Σ {ℓ} (A : Set ℓ) (B : A → Set ℓ) : Set ℓ where 
  constructor 
    _,_
  field 
    π₁ : A
    π₂ : B π₁

_×_ : Set → Set → Set 
A × B = Σ A (λ _ -> B)

data List (A : Set) : Set where 
  ε : List A 
  _∷_ : A → List A → List A
  
_++_ : ∀ {A} → List A → List A → List A 
ε ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys) 

if_then_else_ : ∀ {ℓ} {C : Set ℓ} → 𝔹 → C → C → C 
if true then c else d = c
if false then c else d = d

_∈_ : ∀ x xs → Set 
x ∈ ε = ⊥ 
x ∈ (y ∷ xs) = if x ≡ℕ y then ⊤ else (x ∈ xs)


weakening : ∀ {a} (as bs cs : List ℕ) → 
    (a ∈ (as ++ cs)) → (a ∈ (as ++ (bs ++ cs)))
weakening ε ε cs init = init
weakening {a} ε (x ∷ bs) cs init with a ≡ℕ x
weakening ε (x ∷ bs) cs init | true = tt
weakening ε (x ∷ bs) cs init | false = weakening ε bs cs init
weakening {a} (x ∷ as) bs cs init with a ≡ℕ x
weakening (x ∷ as) bs cs init | true = tt
weakening (x ∷ as) bs cs init | false = weakening as bs cs init 


weaken2 : ∀ {a} (as bs cs ds : List ℕ) →
     (a ∈ (as ++ (bs ++ ds))) → (a ∈ (as ++ (bs ++ (cs ++ ds))))
weaken2 {a} as bs cs ds init with weakening (as ++ bs) cs ds {!init!}
weaken2 {a} as bs cs ds init | res = {!!} 