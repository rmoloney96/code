module IntroModule where 

open import Level

data ⊥ : Set where 
  
¬ : ∀ {ℓ} → Set ℓ → Set ℓ
¬ A = A → ⊥ 

data ⊤ : Set where 
  tt : ⊤ 

notnottrue : ¬ (¬ ⊤)
notnottrue = λ x → x tt 

notfalse : ¬ ⊥ 
notfalse p = p

record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where 
  constructor 
    _,_
  field 
    π₁ : A
    π₂ : B π₁

syntax Σ A (λ x → B) = ∃[ x ∶ A ] B

_×_ : ∀ {a b} (A : Set a) (B : Set b) → Set (a ⊔ b)
A × B = ∃[ x ∶ A ] B

data _⊎_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  inl : (x : A) → A ⊎ B
  inr : (y : B) → A ⊎ B
 
data ℕ : Set where 
  ∅ : ℕ
  1+ : ℕ → ℕ

one = 1+ ∅ 
two = 1+ one
three = 1+ two

data _≤ℕ_ : ℕ → ℕ → Set where 
  ∅≤ : ∀ x → ∅ ≤ℕ x
  1+≤ : ∀ x y → x ≤ℕ y → (1+ x) ≤ℕ (1+ y)

_∘_ : ∀ {ℓ} {A B C : Set ℓ} → (B → C) → (A → B) → A → C
f ∘ g = λ x → f (g x)

_≤ℕdec_ : ∀ x y → (x ≤ℕ y) ⊎ (y ≤ℕ x)
∅ ≤ℕdec y = inl (∅≤ y)
1+ x ≤ℕdec ∅ = inr (∅≤ (1+ x))
1+ x ≤ℕdec 1+ y with x ≤ℕdec y 
1+ x ≤ℕdec 1+ y | inl x₁ = inl (1+≤ x y x₁)
1+ x ≤ℕdec 1+ y | inr y₁ = inr (1+≤ y x y₁) 

{-
∅ ≤ℕdec y = yes (∅≤ y)
(1+ x) ≤ℕdec ∅ = no f
  where f : _ → ⊥
        f ()
(1+ x) ≤ℕdec (1+ y) with x ≤ℕdec y
(1+ x) ≤ℕdec (1+ y) | yes p = yes (1+≤ x y p) 
(1+ x) ≤ℕdec (1+ y) | no p = no (p ∘ invlemma)
  where invlemma : ∀ {x y} → (1+ x) ≤ℕ (1+ y) → x ≤ℕ y
        invlemma {x₁} {y₁} (1+≤ .x₁ .y₁ p₁) = p₁ 
-}

data 𝔹 : Set where 
  true : 𝔹
  false : 𝔹

_≤_ : ℕ → ℕ → 𝔹 
∅ ≤ y = true
1+ x ≤ ∅ = false
1+ x ≤ 1+ y = x ≤ y 

∥_∥ : 𝔹 → Set 
∥ true ∥ = ⊤ 
∥ false ∥ = ⊥

≤⇒≤ℕ : ∀ x y → ∥ (x ≤ y) ∥ → (x ≤ℕ y)
≤⇒≤ℕ ∅ y p = ∅≤ y
≤⇒≤ℕ (1+ x) ∅ ()
≤⇒≤ℕ (1+ x) (1+ y) p = 1+≤ x y (≤⇒≤ℕ x y p)

≤ℕ⇒≤ : ∀ x y → (x ≤ℕ y) → ∥ (x ≤ y) ∥ 
≤ℕ⇒≤ .∅ y (∅≤ .y) = tt
≤ℕ⇒≤ .(1+ x) .(1+ y) (1+≤ x y p) = ≤ℕ⇒≤ x y p 

_≤dec_ : ℕ → ℕ → 𝔹
x ≤dec y with (x ≤ℕdec y)
x ≤dec y | inl p = true
x ≤dec y | inr q = false 

data _≡_ {ℓ} {A : Set ℓ} : A → A → Set ℓ where 
  refl : ∀ {x} → x ≡ x

cong : ∀ {ℓ} {A B : Set ℓ} {x y : A} → (C : A → B) → x ≡ y → C x ≡ C y
cong c refl = refl 

1+≡ : ∀ {x y} → x ≡ y → (1+ x) ≡ (1+ y)
1+≡ refl = refl 

data ⟦_⟧ (A : Set) : Set where 
  ε : ⟦ A ⟧
  _∷_ : A → ⟦ A ⟧ → ⟦ A ⟧ 

[_] : ∀ {A : Set} → A  → ⟦ A ⟧
[ x ] = x ∷ ε

_++_ : ∀ {A : Set} → ⟦ A ⟧ → ⟦ A ⟧ → ⟦ A ⟧
ε ++ l₂ = l₂
(x ∷ l₁) ++ l₂ = x ∷ (l₁ ++ l₂)

example : ⟦ ℕ ⟧
example = one ∷ (two ∷ ε)

example2 : ⟦ ℕ ⟧ 
example2 = example ++ example

record PO (A : Set) : Set₁ where 
  constructor 
    makePO 
  field 
    _≤A_ : A → A → Set
    refl≤ : ∀ x → x ≤A x
    anti≤ : ∀ {x y} → x ≤A y → y ≤A x → x ≡ y
    trans≤ : ∀ {x y z} → x ≤A y → y ≤A z → x ≤A z
    _≤Adec_ : ∀ x y → (x ≤A y) ⊎ (y ≤A x)

ℕSorts : PO ℕ
ℕSorts = record { _≤A_ = _≤ℕ_; refl≤ = refl≤ℕ; anti≤ = anti≤ℕ; trans≤ = trans≤ℕ; _≤Adec_ = _≤ℕdec_ } 
  where refl≤ℕ : ∀ (x : ℕ) → x ≤ℕ x
        refl≤ℕ ∅ = ∅≤ ∅
        refl≤ℕ (1+ x) = 1+≤ x x (refl≤ℕ x) 
        anti≤ℕ : ∀ {x y} → x ≤ℕ y → y ≤ℕ x → x ≡ y 
        anti≤ℕ (∅≤ .∅) (∅≤ .∅) = refl
        anti≤ℕ (1+≤ x y p) (1+≤ .y .x q) with anti≤ℕ p
        anti≤ℕ (1+≤ x y p) (1+≤ .y .x q) | r = (1+≡ ∘ r) q
        trans≤ℕ : ∀ {x y z : ℕ} → x ≤ℕ y → y ≤ℕ z → x ≤ℕ z
        trans≤ℕ (∅≤ .∅) (∅≤ z) = ∅≤ z
        trans≤ℕ (∅≤ .(1+ x)) (1+≤ x y q) = ∅≤ (1+ y)
        trans≤ℕ (1+≤ x y p) (1+≤ .y z q) with trans≤ℕ p q 
        trans≤ℕ (1+≤ x y p) (1+≤ .y z q) | r = 1+≤ℕ x z r
          where 1+≤ℕ : (x y : ℕ) → x ≤ℕ y → (1+ x) ≤ℕ (1+ y)
                1+≤ℕ x y p = 1+≤ x y p

data ! : {A : Set} → ⟦ A ⟧ → ⟦ A ⟧ → Set₁ where 
  !empty : ∀ {A : Set} → ! {A} ε ε
  !skip : ∀ {A : Set} {x : A} {l₁ l₂} → ! l₁ l₂ → ! (x ∷ l₁) (x ∷ l₂) 
  !swap : ∀ {A : Set} {x y : A} {l} → ! (x ∷ (y ∷ l)) (y ∷ (x ∷ l))
  !trans : ∀ {A : Set} {l₁ l₂ l₃ : ⟦ A ⟧ } → ! l₁ l₂ → ! l₂ l₃ → ! l₁ l₃

!refl : ∀ {A : Set} → {l : ⟦ A ⟧} → ! l l
!refl {A} {ε} = !empty
!refl {A} {x ∷ l} = !skip !refl 

!sym : ∀ {A : Set} → {l l' : ⟦ A ⟧} → ! l l' → ! l' l
!sym !empty = !empty
!sym (!skip p) = !skip (!sym p)
!sym !swap = !swap
!sym (!trans p p₁) = !trans (!sym p₁) (!sym p) 

!ε : ∀ {A : Set} → {l : ⟦ A ⟧} → ! ε l → ε ≡ l 
!ε {A} {ε} p = refl
!ε {A} {x ∷ l} (!trans p p₁) with !ε p
!ε {A} {x ∷ l} (!trans p p₁) | refl = !ε p₁ 

¬!ε∷ : ∀ {A : Set} → {x : A} → {l : ⟦ A ⟧} → ¬ (! ε (x ∷ l))
¬!ε∷ (!trans p p₁) with !ε p
¬!ε∷ (!trans p p₁) | refl with !ε p₁
¬!ε∷ (!trans p p₁) | refl | ()

!moveone : ∀ {A} → (x : A) → (l₁ l₂ : ⟦ A ⟧) → ! ([ x ] ++ (l₁ ++ l₂)) (l₁ ++ ([ x ] ++ l₂))
!moveone x ε l₂ = !refl
!moveone x (x₁ ∷ l₁) l₂ with !moveone x l₁ l₂
!moveone x (x₁ ∷ l₁) l₂ | res = !trans !swap (!skip res) 

!insert : ∀ {A} (x : A) (l l₁ l₂ : ⟦ A ⟧)  → ! l (l₁ ++ l₂) → ! (x ∷ l) (l₁ ++ ([ x ] ++ l₂))
!insert x l l₁ l₂ p = !trans (!skip p) (!moveone x l₁ l₂)

data Forall  {A : Set} (R : A → Set) : ⟦ A ⟧ → Set where 
  Forallε : Forall R ε 
  Forall∷ : ∀ {a l} → Forall R l → R a → Forall R (a ∷ l)

record Sorting : Set₂ where 
  field 
    A : Set
    po : PO A
  
  open PO po

  data Sorted : ⟦ A ⟧ → Set where 
    Sortedε : Sorted ε
    Sorted∷ : ∀ {l} {a} → Sorted l → Forall (λ x → a ≤A x) l → Sorted (a ∷ l)

  insert : A → ⟦ A ⟧ → ⟦ A ⟧
  insert x ε = [ x ]
  insert x (y ∷ l) with x ≤Adec y
  insert x (y ∷ l) | inl x₁ = x ∷ (y ∷ l)
  insert x (y ∷ l) | inr y₁ = y ∷ insert x l

  insertionSort : ⟦ A ⟧ → ⟦ A ⟧
  insertionSort ε = ε
  insertionSort (x ∷ l) = insert x (insertionSort l)

  forallSortTrans : ∀ {x a : A} → (l : ⟦ A ⟧) → (x ≤A a) → Sorted (a ∷ l) → Forall (_≤A_ x) l
  forallSortTrans .ε le (Sorted∷ s Forallε) = Forallε
  forallSortTrans .(a₁ ∷ l) le (Sorted∷ s (Forall∷ {a₁} {l} x₁ x₂)) with trans≤ le x₂ 
  forallSortTrans .(a₁ ∷ l) le (Sorted∷ s (Forall∷ {a₁} {l} x₁ x₂)) | res = Forall∷ (forallSortTrans l res s) res 

  safeOnTop : ∀ {x a} l₁ l₂ → (a ≤A x) → Forall (_≤A_ a) (l₁ ++ l₂) → Sorted (l₁ ++ (x ∷ l₂)) → Sorted (a ∷ (l₁ ++ (x ∷ l₂)))
  safeOnTop {x} {a} ε l₂ nle f (Sorted∷ s x₁) = Sorted∷ (Sorted∷ s x₁) (Forall∷ f nle)
  safeOnTop {x} {a} (x₁ ∷ l₁) l₂ nle (Forall∷ f x₂) s with forallSortTrans (l₁ ++ ([ x ] ++ l₂)) x₂ s
  safeOnTop {x} {a} (x₁ ∷ l₁) l₂ nle (Forall∷ f x₂) s | res = Sorted∷ s (Forall∷ res x₂)
    
  split : (l₁ : ⟦ A ⟧) → (x : A) → Sorted l₁ → 
    ∃[ l₂ ∶ ⟦ A ⟧ ] ∃[ l₃ ∶ ⟦ A ⟧ ] ((l₁ ≡ (l₂ ++ l₃)) × Sorted (l₂ ++ ([ x ] ++ l₃)))
  split .ε x Sortedε = ε , (ε , (refl , Sorted∷ Sortedε Forallε))
  split (a ∷ l) x s             with x ≤Adec a 
  split (a ∷ l) x s              | inl p = ε , ((a ∷ l) , (refl , Sorted∷ s (Forall∷ (forallSortTrans l p s) p)))
  split (a ∷ l) x (Sorted∷ s x₁) | inr q with split l x s
  split (a ∷ .(l₁ ++ l₂)) x (Sorted∷ s x₁) | inr q | l₁ , (l₂ , (refl , s')) = (a ∷ l₁) , (l₂ , (refl , safeOnTop l₁ l₂ q x₁ s')) 

  insertionSortStrong : (l₁ : ⟦ A ⟧) → ∃[ l₂ ∶ ⟦ A ⟧ ] (Sorted l₂ × ! l₁ l₂)
  insertionSortStrong ε = ε , (Sortedε , !empty)
  insertionSortStrong (x ∷ l) with insertionSortStrong l
  insertionSortStrong (x ∷ l) | l₁ , (s , p) with split l₁ x s
  insertionSortStrong (x ∷ l) | .(π₁ ++ π₂) , (s , p) | π₁ , (π₂ , (refl , π₄)) = (π₁ ++ ([ x ] ++ π₂)) , (π₄ , !insert x l π₁ π₂ p) 

