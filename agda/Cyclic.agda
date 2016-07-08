
module Cyclic where 

data Nat : Set where 
  Z : Nat 
  S : Nat → Nat

infixr 40 _⊗_ 
infixl 50 _⇒_
data Type : Set where 
  U : Type 
  τ : Nat → Type
  _⇒_ : Type → Type → Type 
  _⊗_ : Type → Type → Type
  _⊕_ : Type → Type → Type
  μ : Type → Type

data Term : Set where
  u : Term
  ̌ : Nat → Term
  _⋆_ : Term → Term → Term
  π₁ : Term → Term 
  π₂ : Term → Term
  inl : Type → Term → Term 
  inr : Type → Term → Term
  _⨆_ : Term → Term → Term
  _∘_ : Term → Term → Term 
  ƛ : Type → Term → Term
  rec : Term → Term
  inμ : Term → Term 
  outμ : Term → Term 

infixr 40 _,_
data Ctx : Set where 
  · : Ctx 
  _,_ : Ctx → Type → Ctx

size : Ctx → Nat 
size · = Z
size (Γ , _) = S (size Γ)

data False : Set where
record True : Set where

_∈_ : Nat → Ctx → Set
_     ∈ ·       = False
Z     ∈ (Γ , A) = A
(S x) ∈ (Γ , A) = x ∈ Γ

infix 5 _∙_⊢_◂_
data _∙_⊢_◂_ : Ctx → Term → Set where 
  holds : Nat → Ctx → Term → Type

[_:=_]_ : Nat → Type → Type → Type 
[ X := T ] (A ⇒ B) = ([ X := T ] A) ⇒ ([ X := T ] B)
[ X := T ] (A ⊕ B) = ([ X := T ] A) ⊕ ([ X := T ] B)
[ X := T ] (A ⊗ B) = ([ X := T ] A) ⊗ ([ X := T ] B)
[ X := T ] (μ A) = μ ([ S X := T ] A)
[ X := T ] (τ n) where n == X
..               | true = 

codata PreProof : Set where 
  UnitIntro : ∀ {Δ Γ} (Δ ∙ Γ ⊢ u ◂ U)
  VarIntro : ∀ {Δ Γ n r s A B} (p : n ∈ Γ) → (Δ ∙ Γ ⊢ ̌ n ◂ (p n Γ))
  ImpIntro : ∀ {Δ Γ r s A B} → (Δ ∙ Γ , A ⊢ r ◂ B) → (Δ ∙ Γ ⊢ (ƛ A r) ◂ A ⇒ B) 
  ImpElim : ∀ {Δ Γ r s A B} → (Δ ∙ Γ ⊢ r ◂ A ⇒ B) → (Δ ∙ Γ ⊢ s ◂ A)  → (Δ ∙ Γ ⊢ r ∘ s ◂ B)
  PairIntro : ∀ {Δ Γ r s A B} → (Δ ∙ Γ , A ⊢ r ◂ A) → (Δ ∙ Γ ⊢ s ◂ B) → (Δ ∙ Γ ⊢ s ◂ A ⊗ B) 
  PairElim1 : ∀ {Δ Γ r A B} → (Δ ∙ Γ ⊢ r ◂ A ⊗ B) → (Δ ∙ Γ ⊢ π₁ r ◂ A)
  PairElim2 : ∀ {Δ Γ r A B} → (Δ ∙ Γ ⊢ r ◂ A ⊗ B) → (Δ ∙ Γ ⊢ π₂ r ◂ B)
  SumIntro1 : ∀ {Δ Γ r A B} → (Δ ∙ Γ ⊢ r ◂ A) → (Δ ∙ Γ ⊢ inl B r ◂ A ⊕ B)
  SumIntro2 : ∀ {Δ Γ r A B} → (Δ ∙ Γ ⊢ r ◂ B) → (Δ ∙ Γ ⊢ inr A r ◂ A ⊕ B)
  SumElim : ∀ {Δ Γ f g A B C} → (Δ ∙ Γ ⊢ f ◂ A ⇒ C) → (Δ ∙ Γ ⊢ g ◂ B ⇒ C) → (Δ ∙ Γ ⊢ (f ⨆ g) ◂ (A ⊕ B ⇒ C))
  MuElim : ∀ {Δ Γ r A} → (Δ ∙ Γ ⊢ r ◂ μ A) → (Δ ∙ Γ ⊢ r ◂ [ Z := μ A ] A) 
  MuIntro : ∀ {Δ Γ r A} → (Δ ∙ Γ ⊢ r ◂ [ Z := μ A ] A ) → (Δ ∙ Γ ⊢ r ◂ μ A)
  
