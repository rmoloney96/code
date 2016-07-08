module Topological where

open import Level

data ⊥ : Set where

¬ : ∀ {ℓ} → Set ℓ → Set ℓ
¬ P = P → ⊥ 

record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where 
  constructor 
    _,_
  field 
    π₁ : A
    π₂ : B π₁

syntax Σ A (λ x → B) = ∃[ x ∶ A ] B

_×_ : ∀ {a b} (A : Set a) (B : Set b) → Set (a ⊔ b)
A × B = ∃[ x ∶ A ] B

data _≡_ {ℓ} {A : Set ℓ} : A → A → Set ℓ where 
  refl : {x : A} → x ≡ x

data [_] {ℓ} (A : Set ℓ) : Set ℓ where 
  ε : [ A ] 
  _∷_ : A → [ A ] → [ A ]  

data Dec {ℓ} (P : Set ℓ) : Set ℓ where 
  yes : (p : P) → Dec P
  no : (¬p : ¬ P) → Dec P

_++_ : ∀ {ℓ} {A : Set ℓ} → [ A ] → [ A ] → [ A ] 
ε ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

data Forall {ℓ m} {A : Set ℓ} (R : A → Set m) : [ A ] → Set (ℓ ⊔ m) where 
  Forallε : Forall R ε 
  Forall∷ : ∀ {a l} → Forall R l → R a → Forall R (a ∷ l)

record PO {ℓ} (A : Set ℓ) : Set (suc ℓ) where 
  constructor 
    makePO 
  field 
    _≤A_ : A → A → Set ℓ
    refl≤ : ∀ x → x ≤A x
    anti≤ : ∀ {x y} → x ≤A y → y ≤A x → x ≡ y
    trans≤ : ∀ {x y z} → x ≤A y → y ≤A z → x ≤A z
    _≤Adec_ : ∀ x y → Dec (x ≤A y)

_∘_ : ∀ {ℓ m n} → {A : Set ℓ} {B : Set m} {C : Set n} → (f : B → C) → (g : A → B) → (A → C)
f ∘ g = λ x → f (g x)

record TopologicalSort {ℓ} : Set (suc ℓ) where 
  constructor 
    makeTopologicalSort 
  field 
    A : Set ℓ
    po : PO A

  open PO po

  all : (x : A) → (l : [ A ]) → Dec (Forall (_≤A_ x) l)
  all x ε = yes Forallε
  all x (x₁ ∷ xs) with x ≤Adec x₁ 
  all x (x₁ ∷ xs) | yes p  with all x xs
  all x (x₁ ∷ xs) | yes p₁ | yes p = yes (Forall∷ p p₁) 
  all x (x₁ ∷ xs) | yes p  | no ¬p = no (¬p ∘ fnextinv)
    where fnextinv : ∀ {x x₁} → Forall (_≤A_ x) (x₁ ∷ xs) → Forall (_≤A_ x) xs
          fnextinv (Forall∷ f x₄) = f 
  all x (x₁ ∷ xs) | no ¬p = no (¬p ∘ finv)
    where finv : ∀ {x x₁} → Forall (_≤A_ x) (x₁ ∷ xs) → x ≤A x₁
          finv (Forall∷ f x₄) = x₄ 

--  topoOrdered : (xs : [ [ A ] ]) → Forall (λ xs → (Forall (_≤_ x) 

{-

L ← Empty list that will contain the sorted nodes
S ← Set of all nodes with no incoming edges
for each node n in S do
    visit(n) 
function visit(node n)
    if n has not been visited yet then
        mark n as visited
        for each node m with an edge from n to m do
            visit(m)
        add n to L
-}
  
  findBaseOne : (x : A) → (l : [ A ]) → Dec (Forall (λ y → ¬ (x ≤A y)) l)
  findBaseOne x ε = yes Forallε
  findBaseOne x (x₁ ∷ l) with x ≤Adec x₁
  findBaseOne x (x₁ ∷ l) | yes p = no forallisbot
    where forallisbot : ∀ (p : Forall (λ y → x ≤A y → ⊥) (x₁ ∷ l)) → ⊥
          forallisbot (Forall∷ p₁ x₂) = x₂ p 
  findBaseOne x (x₁ ∷ l) | no ¬p with findBaseOne x l
  findBaseOne x (x₁ ∷ l) | no ¬p  | yes p = yes (Forall∷ p ¬p)
  findBaseOne x (x₁ ∷ l) | no ¬p₁ | no ¬p = no (¬p ∘ forallinv) 
    where forallinv : ∀ (f : Forall (λ y → x ≤A y → ⊥) (x₁ ∷ l)) → Forall (λ y → x ≤A y → ⊥) l
          forallinv (Forall∷ f x₂) = f 

  findBaseAux : (checking : [ A ]) → (all : [ A ]) → (found : ∃[ l ∶ [ A ] ] Forall (λ y → (Forall (λ x → ¬ (x ≤A y)) l)) all) 
                → Forall (λ y → (Forall (λ x → ¬ (x ≤A y)) all)) all
  findBaseAux ε all found = {!!}
  findBaseAux (x ∷ checking) all found with findBaseOne x all
  findBaseAux (x ∷ checking) all found | yes p = {!!} --findBaseAux checking all (x ∷ found) 
  findBaseAux (x ∷ checking) all found | no ¬p = {!!} --findBaseAux checking all found

  findBase : [ A ] → [ A ] 
  findBase xs = {!!} 

  topoSort : [ A ] → [ A ] 
  topoSort = {!!} 