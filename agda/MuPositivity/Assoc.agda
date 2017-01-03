
open import Utils
open import Relation.Binary hiding (_⇒_)
open import Relation.Nullary.Decidable
open import Level

module Assoc
  (C : Set)
  (Atom : Set)
  (default : C)
  (_≼_ : Rel Atom zero)
  (tdoe : DecTotalOrderEq Atom _≼_)
  where

open import FinSet
open import Data.List
open import Data.Product
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding (inspect ; [_])
open import Data.Unit hiding (_≟_)
open import Data.Empty
open import Relation.Nullary.Negation using () renaming (contradiction to _↯_)


_≼?_ : ∀ x y → Dec (x ≼ y)
_≼?_ = DecTotalOrderEq._≼?_ tdoe

_≟_ : ∀ x y → Dec (x ≡ y)
_≟_ = DecTotalOrderEq._≟_ tdoe

tri : Trichotomous _≡_ _≼_ 
tri = DecTotalOrderEq.tri tdoe

tran : Transitive _≼_ 
tran = DecTotalOrderEq.tran tdoe

x≼y : ∀ {x y} → x ≼ y → Σ[ a ∈ x ≼ y ] Σ[ b ∈ ¬ x ≡ y ] Σ[ c ∈ ¬ y ≼ x ] tri x y ≡ tri< a b c
x≼y {x} {y} p with tri x y
x≼y p | tri< a ¬b ¬c = a , ¬b , ¬c , refl
x≼y p | tri≈ ¬a b ¬c = p ↯ ¬a
x≼y p | tri> ¬a ¬b c = p ↯ ¬a

x≡y : ∀ {x y} → x ≡ y → Σ[ a ∈ ¬ x ≼ y ] Σ[ b ∈ x ≡ y ] Σ[ c ∈ ¬ y ≼ x ] tri x y ≡ tri≈ a b c
x≡y {x} {y} p with tri x y
x≡y p | tri< a ¬b ¬c = p ↯ ¬b
x≡y p | tri≈ ¬a b ¬c = ¬a , b , ¬c , refl
x≡y p | tri> ¬a ¬b c = p ↯ ¬b

y≼x : ∀ {x y} → y ≼ x → Σ[ a ∈ ¬ x ≼ y ] Σ[ b ∈ ¬ x ≡ y ] Σ[ c ∈ y ≼ x ] tri x y ≡ tri> a b c
y≼x {x} {y} p with tri x y
y≼x p | tri< a ¬b ¬c = p ↯ ¬c
y≼x p | tri≈ ¬a b ¬c = p ↯ ¬c
y≼x p | tri> ¬a ¬b c = ¬a , ¬b , c , refl

x≡x : ∀ x → Σ[ a ∈ ¬ x ≼ x ] Σ[ b ∈ x ≡ x ] Σ[ c ∈ ¬ x ≼ x ] tri x x ≡ tri≈ a b c
x≡x x with tri x x
x≡x x | tri< a ¬b ¬c = refl ↯ ¬b
x≡x x | tri≈ ¬a b ¬c = ¬a , b , ¬c , refl
x≡x x | tri> ¬a ¬b c = refl ↯ ¬b

open import Data.Sum

Assoc : Set
Assoc = List (Atom × C)

data _≼*_ : Atom → Assoc → Set where
  [] : ∀ {x} → x ≼* []
  _∷_ : ∀ {x y c l} → x ≼ y → x ≼* l → x ≼* ((y , c)∷ l)

x≼y∧y≼*l⇒x≼*l : ∀ {x y l} → x ≼ y → y ≼* l → x ≼* l
x≼y∧y≼*l⇒x≼*l x≼y [] = []
x≼y∧y≼*l⇒x≼*l x≼y (y≼y' ∷ y≼*l) = tran x≼y y≼y' ∷ (x≼y∧y≼*l⇒x≼*l x≼y y≼*l)

data OrderedKeys : Assoc → Set where
  [] : OrderedKeys []
  ⟨_↦_⟩∷_ : ∀ {x l} → x ≼* l → (c : C) → OrderedKeys l → OrderedKeys ((x , c) ∷ l)

_[_≔_] : Assoc → Atom → C → Assoc
[] [ x ≔ X ] = (x , X) ∷ []
((x , c) ∷ i) [ x₁ ≔ X ] with tri x₁ x
((x , c) ∷ i) [ x₁ ≔ X ] | tri< a ¬b ¬c = (x₁ , X) ∷ (x , c) ∷ i
((x , c) ∷ i) [ x₁ ≔ X ] | tri≈ ¬a b ¬c = (x₁ , X) ∷ i
((x , c₁) ∷ i) [ x₁ ≔ X ] | tri> ¬a ¬b c =  (x , c₁) ∷ (i [ x₁ ≔ X ]) 

y≼x∧y≼*l⇒y≼*l[x≔X] : ∀ {x y l X} → y ≼ x → y ≼* l → y ≼* (l [ x ≔ X ])
y≼x∧y≼*l⇒y≼*l[x≔X] p [] = p ∷ []
y≼x∧y≼*l⇒y≼*l[x≔X] {x} {y} p (_∷_ {_} {y'} x₁ q) with tri x y'
y≼x∧y≼*l⇒y≼*l[x≔X] p (x₁ ∷ q) | tri< a ¬b ¬c = p ∷ (x₁ ∷ q)
y≼x∧y≼*l⇒y≼*l[x≔X] p (x₁ ∷ q) | tri≈ ¬a b ¬c = p ∷ q
y≼x∧y≼*l⇒y≼*l[x≔X] {X = X} p (x₁ ∷ q) | tri> ¬a ¬b c₁ = x₁ ∷ (y≼x∧y≼*l⇒y≼*l[x≔X] {X = X} p q)

_⟨_⟩ : Assoc → Atom → C  
[] ⟨ x ⟩ = default
((x , X) ∷ i) ⟨ x₁ ⟩ with x ≟ x₁
((x , X) ∷ i) ⟨ x₁ ⟩ | yes p = X
((x , X) ∷ i) ⟨ x₁ ⟩ | no ¬p = i ⟨ x₁ ⟩ 

InsertOrdered : ∀ {i} x X → OrderedKeys i → OrderedKeys (i [ x ≔ X ])
InsertOrdered x X [] =  ⟨ [] ↦ X ⟩∷ []
InsertOrdered x X (⟨_↦_⟩∷_ {y} yle Y l) with tri x y
InsertOrdered x X (⟨ yle ↦ Y ⟩∷ l) | tri< a ¬b ¬c = ⟨ (a ∷ (x≼y∧y≼*l⇒x≼*l a yle)) ↦ X ⟩∷ (⟨ yle ↦ Y ⟩∷ l) 
InsertOrdered x X (⟨ yle ↦ Y ⟩∷ l) | tri≈ ¬a refl ¬c = ⟨ yle ↦ X ⟩∷ l 
InsertOrdered x X (⟨ yle ↦ Y ⟩∷ l) | tri> ¬a ¬b c = ⟨ y≼x∧y≼*l⇒y≼*l[x≔X] c yle ↦ Y ⟩∷ InsertOrdered x X l

Same : ∀ {x a X} i → x ≡ a → (i [ a ≔ X ]) ⟨ x ⟩ ≡ X
Same {x} {a} [] p with a ≟ x
Same [] p₁ | yes p = refl
Same [] p | no ¬p = sym p ↯ ¬p
Same {x} ((y , Y) ∷ i) refl with tri x y | x≡x x
Same {x} ((y , Y) ∷ i) refl | tri< a ¬b ¬c | (_ , _ , _ , eq) rewrite eq = refl
Same {x} ((y , Y) ∷ i) refl | tri≈ ¬a b ¬c | (_ , _ , _ , eq) rewrite eq = refl
Same {x} ((y , Y) ∷ i) refl | tri> ¬a ¬b c | res with y ≟ x
Same ((x , Y) ∷ i) refl | tri> ¬a ¬b c | res | yes refl = refl ↯ ¬b
Same ((y , Y) ∷ i) refl | tri> ¬a ¬b c | res | no ¬p = Same i refl 

Ignore : ∀ {x a X} i → x ≢ a → (i [ a ≔ X ]) ⟨ x ⟩ ≡ i ⟨ x ⟩
Ignore {x} {a} [] ¬p with a ≟ x
Ignore [] ¬p | yes p = sym p ↯ ¬p
Ignore [] ¬p₁ | no ¬p = refl
Ignore {x} {a} ((y , Y) ∷ i) ¬p with tri a y | y ≟ x 
Ignore {.y} {a} ((y , Y) ∷ i) ¬p₁ | tri< a₁ ¬b ¬c | yes refl with a ≟ y
Ignore ((y , Y) ∷ i) ¬p₁ | tri< a₁ ¬b ¬c | yes refl | yes refl = refl ↯ ¬p₁
Ignore ((y , Y) ∷ i) ¬p₁ | tri< a₁ ¬b ¬c | yes refl | no ¬p with y ≟ y
Ignore ((y , Y) ∷ i) ¬p₁ | tri< a₁ ¬b ¬c | yes refl | no ¬p | yes refl = refl
Ignore ((y , Y) ∷ i) ¬p₂ | tri< a₁ ¬b ¬c | yes refl | no ¬p₁ | no ¬p = refl ↯ ¬p
Ignore {x} {a} ((y , Y) ∷ i) ¬p₁ | tri< a₁ ¬b ¬c | no ¬p with x ≟ a
Ignore {.x} {x} ((y , Y) ∷ i) ¬p₁ | tri< a₁ ¬b ¬c | no ¬p | yes refl = refl ↯ ¬p₁
Ignore {x} {a} ((y , Y) ∷ i) ¬p₂ | tri< a₁ ¬b ¬c | no ¬p₁ | no ¬p with x ≟ a
Ignore ((y , Y) ∷ i) ¬p₂ | tri< a₁ ¬b ¬c | no ¬p₁ | no ¬p | yes refl = refl ↯ ¬p₂
Ignore {x} {a} ((y , Y) ∷ i) ¬p₃ | tri< a₁ ¬b ¬c | no ¬p₂ | no ¬p₁ | no ¬p with tri a x
Ignore {x} ((y , Y) ∷ i) ¬p₃ | tri< a₂ ¬b₁ ¬c₁ | no ¬p₂ | no ¬p₁ | no ¬p | tri< a₁ ¬b ¬c with y ≟ x
Ignore ((y , Y) ∷ i) ¬p₃ | tri< a₂ ¬b₁ ¬c₁ | no ¬p₂ | no ¬p₁ | no ¬p | tri< a₁ ¬b ¬c | yes p = p ↯ ¬p₂
Ignore ((y , Y) ∷ i) ¬p₄ | tri< a₂ ¬b₁ ¬c₁ | no ¬p₃ | no ¬p₂ | no ¬p₁ | tri< a₁ ¬b ¬c | no ¬p = refl
Ignore ((y , Y) ∷ i) ¬p₃ | tri< a₁ ¬b ¬c₁ | no ¬p₂ | no ¬p₁ | no ¬p | tri≈ ¬a refl ¬c = refl ↯ ¬p₃
Ignore {x} {a} ((y , Y) ∷ i) ¬p₃ | tri< a₁ ¬b₁ ¬c | no ¬p₂ | no ¬p₁ | no ¬p | tri> ¬a ¬b c with y ≟ x
Ignore ((x , Y) ∷ i) ¬p₃ | tri< a₁ ¬b₁ ¬c | no ¬p₂ | no ¬p₁ | no ¬p | tri> ¬a ¬b c | yes refl = refl ↯ ¬p₂
Ignore ((y , Y) ∷ i) ¬p₄ | tri< a₁ ¬b₁ ¬c | no ¬p₃ | no ¬p₂ | no ¬p₁ | tri> ¬a ¬b c | no ¬p = refl
Ignore ((y , Y) ∷ i) ¬p | tri≈ ¬a refl ¬c | yes refl = refl ↯ ¬p
Ignore {x} {.y} ((y , Y) ∷ i) ¬p₁ | tri≈ ¬a refl ¬c | no ¬p with y ≟ x
Ignore ((y , Y) ∷ i) ¬p₁ | tri≈ ¬a refl ¬c | no ¬p | yes p = p ↯ ¬p
Ignore ((y , Y) ∷ i) ¬p₂ | tri≈ ¬a refl ¬c | no ¬p₁ | no ¬p = refl
Ignore ((y , Y) ∷ i) ¬p | tri> ¬a ¬b c | yes refl with y ≟ y
Ignore ((y , Y) ∷ i) ¬p | tri> ¬a ¬b c | yes refl | yes p = refl
Ignore ((y , Y) ∷ i) ¬p₁ | tri> ¬a ¬b c | yes refl | no ¬p = refl ↯ ¬p 
Ignore {x} {a} ((y , Y) ∷ i) ¬p₁ | tri> ¬a ¬b c | no ¬p with y ≟ a
Ignore ((a , Y) ∷ i) ¬p₁ | tri> ¬a ¬b c | no ¬p | yes refl = refl ↯ ¬b
Ignore {x} {a} ((y , Y) ∷ i) ¬p₂ | tri> ¬a ¬b c | no ¬p₁ | no ¬p with tri y x
Ignore ((y , Y) ∷ i) ¬p₂ | tri> ¬a ¬b₁ c | no ¬p₁ | no ¬p | tri< a₁ ¬b ¬c = Ignore i ¬p₂
Ignore ((y , Y) ∷ i) ¬p₂ | tri> ¬a₁ ¬b c | no ¬p₁ | no ¬p | tri≈ ¬a refl ¬c = refl ↯ ¬p₁ 
Ignore ((y , Y) ∷ i) ¬p₂ | tri> ¬a₁ ¬b₁ c₁ | no ¬p₁ | no ¬p | tri> ¬a ¬b c = Ignore i ¬p₂

Overwrite : ∀ {x X Y} i → i [ x ≔ X ] [ x ≔ Y ] ≡ i [ x ≔ Y ]
Overwrite {x} [] with tri x x
Overwrite [] | tri< a ¬b ¬c = a ↯ ¬c
Overwrite [] | tri≈ ¬a refl ¬c = refl
Overwrite [] | tri> ¬a ¬b c = c ↯ ¬a
Overwrite {x} ((y , c) ∷ i) with tri x y
Overwrite {x} ((y , c) ∷ i) | tri< a ¬b ¬c with tri x x
Overwrite ((y , c) ∷ i) | tri< a₁ ¬b₁ ¬c₁ | tri< a ¬b ¬c = refl ↯ ¬b
Overwrite ((y , c) ∷ i) | tri< a ¬b ¬c₁ | tri≈ ¬a b ¬c = refl
Overwrite ((y , c₁) ∷ i) | tri< a ¬b₁ ¬c | tri> ¬a ¬b c = refl ↯ ¬b
Overwrite {x} ((y , c) ∷ i) | tri≈ ¬a b ¬c with tri x x
Overwrite ((y , c) ∷ i) | tri≈ ¬a b ¬c₁ | tri< a ¬b ¬c = refl ↯ ¬b
Overwrite ((y , c) ∷ i) | tri≈ ¬a₁ b₁ ¬c₁ | tri≈ ¬a b ¬c = refl
Overwrite ((y , c₁) ∷ i) | tri≈ ¬a₁ b ¬c | tri> ¬a ¬b c = refl ↯ ¬b
Overwrite ((y , c₁) ∷ i) | tri> ¬a ¬b c with y≼x c
Overwrite {x} {X} {Y} ((y , c₁) ∷ i) | tri> ¬a ¬b c | (_ , _ , _ , eq) rewrite eq with Overwrite {x} {X} {Y} i 
Overwrite {x} {X} {Y} ((y , c₁) ∷ i) | tri> ¬a ¬b c | (_ , _ , _ , eq) | overeq rewrite overeq = refl

Swap : ∀ {x y X Y i} → OrderedKeys i → x ≢ y → i [ x ≔ X ] [ y ≔ Y ] ≡ i [ y ≔ Y ] [ x ≔ X ]
Swap {x} {y} [] p with tri x y
Swap {x} {y} [] p | tri< a ¬b ¬c with y≼x a
Swap [] p | tri< a ¬b ¬c | (_ , _ , _ , eq) rewrite eq = refl
Swap [] p | tri≈ ¬a b ¬c = b ↯ p
Swap {x} {y} [] p | tri> ¬a ¬b c with x≼y c
Swap [] p | tri> ¬a ¬b c | (_ , _ , _ , eq) rewrite eq = refl
Swap {x} {y} (⟨_↦_⟩∷_ {x₁} p₁ c j) p with tri x x₁ | tri y x₁ 
Swap {x} {y} (⟨_↦_⟩∷_ {x₁} p₁ c j) p | tri< a ¬b ¬c | tri< a₁ ¬b₁ ¬c₁ with tri y x
Swap (⟨ p₁ ↦ c ⟩∷ j) p | tri< a₁ ¬b₁ ¬c₁ | tri< a₂ ¬b₂ ¬c₂ | tri< a ¬b ¬c
  with y≼x a | x≼y a₁
Swap (⟨ p₁ ↦ c ⟩∷ j) p | tri< a₁ ¬b₁ ¬c₁ | tri< a₂ ¬b₂ ¬c₂ | tri< a ¬b ¬c
  | (_ , _ , _ , eq) | (_ , _ , _ , eq₁) rewrite eq | eq₁ = refl
Swap (⟨ p₁ ↦ c ⟩∷ j) p | tri< a ¬b ¬c₁ | tri< a₁ ¬b₁ ¬c₂ | tri≈ ¬a b ¬c = sym b ↯ p
Swap (⟨ p₁ ↦ c₁ ⟩∷ j) p | tri< a ¬b₁ ¬c | tri< a₁ ¬b₂ ¬c₁ | tri> ¬a ¬b c
  with x≼y a₁ | x≼y c
Swap (⟨ p₁ ↦ c₁ ⟩∷ j) p | tri< a ¬b₁ ¬c | tri< a₁ ¬b₂ ¬c₁ | tri> ¬a ¬b c
  | (_ , _ , _ , eq) | (_ , _ , _ , eq₁) rewrite eq | eq₁ = refl
Swap {x} {y} (⟨ p₁ ↦ c ⟩∷ j) p | tri< a ¬b ¬c | tri≈ ¬a refl ¬c₁
  with x≼y a | y≼x a | x≡x y
Swap (⟨ p₁ ↦ c ⟩∷ j) p | tri< a ¬b ¬c | tri≈ ¬a refl ¬c₁
  | (_ , _ , _ , eq) | (_ , _ , _ , eq₁) | (_ , _ , _ , eq₂) rewrite eq | eq₁ | eq₂ = refl
Swap {x} {y} (⟨ p₁ ↦ c₁ ⟩∷ j) p | tri< a ¬b ¬c | tri> ¬a ¬b₁ c with tri y x
Swap (⟨ p₁ ↦ c₁ ⟩∷ j) p | tri< a₁ ¬b₁ ¬c₁ | tri> ¬a ¬b₂ c | tri< a ¬b ¬c = tran c a ↯ ¬c₁ 
Swap (⟨ p₁ ↦ c₁ ⟩∷ j) p | tri< a ¬b ¬c₁ | tri> ¬a₁ ¬b₁ c | tri≈ ¬a refl ¬c = refl ↯ p
Swap (⟨ p₁ ↦ c₂ ⟩∷ j) p | tri< a ¬b₁ ¬c | tri> ¬a₁ ¬b₂ c₁ | tri> ¬a ¬b c
  with x≼y a | y≼x c₁
Swap (⟨ p₁ ↦ c₂ ⟩∷ j) p | tri< a ¬b₁ ¬c | tri> ¬a₁ ¬b₂ c₁ | tri> ¬a ¬b c
  | (_ , _ , _ , eq) | (_ , _ , _ , eq₁ ) rewrite eq | eq₁ = refl
Swap {x} (⟨_↦_⟩∷_ x₁ c j) p | tri≈ ¬a refl ¬c | tri< a ¬b ¬c₁ with x≼y a | y≼x a | x≡x x
Swap (⟨ x₁ ↦ c ⟩∷ j) p | tri≈ ¬a refl ¬c | tri< a ¬b ¬c₁
  | (_ , _ , _ , eq) | (_ , _ , _ , eq₁) | (_ , _ , _ , eq₂) rewrite eq | eq₁ | eq₂ = refl
Swap (⟨ x₁ ↦ c ⟩∷ j) p | tri≈ ¬a refl ¬c | tri≈ ¬a₁ b ¬c₁ = sym b ↯ p
Swap {x} (⟨ x₁ ↦ c₁ ⟩∷ j) p | tri≈ ¬a refl ¬c | tri> ¬a₁ ¬b c
  with y≼x c | x≡x x
Swap (⟨ x₁ ↦ c₁ ⟩∷ j) p | tri≈ ¬a refl ¬c | tri> ¬a₁ ¬b c
  | (_ , _ , _ , eq) | (_ , _ , _ , eq₁) rewrite eq | eq₁ = refl
Swap (⟨ x₂ ↦ c₁ ⟩∷ j) p | tri> ¬a ¬b c | tri< a ¬b₁ ¬c
  with x≼y a | y≼x (tran a c) | y≼x c
Swap (⟨ x₂ ↦ c₁ ⟩∷ j) p | tri> ¬a ¬b c | tri< a ¬b₁ ¬c
  | (_ , _ , _ , eq) | (_ , _ , _ , eq₁) | (_ , _ , _ , eq₂) rewrite eq | eq₁ | eq₂ = refl 
Swap {x} {y} (⟨ x₂ ↦ c₁ ⟩∷ j) p | tri> ¬a ¬b c | tri≈ ¬a₁ refl ¬c
  with x≡x x | y≼x c | x≡x y
Swap (⟨ x₂ ↦ c₁ ⟩∷ j) p | tri> ¬a ¬b c | tri≈ ¬a₁ refl ¬c
  | (_ , _ , _ , eq) | (_ , _ , _ , eq₁) | (_ , _ , _ , eq₂) rewrite eq | eq₁ | eq₂ = refl
Swap (⟨ x₂ ↦ c₂ ⟩∷ j) p | tri> ¬a ¬b c | tri> ¬a₁ ¬b₁ c₁
  with y≼x c₁ | y≼x c 
Swap {x} {y} {X} {Y} (⟨ x₂ ↦ c₂ ⟩∷ j) p | tri> ¬a ¬b c | tri> ¬a₁ ¬b₁ c₁
  | (_ , _ , _ , eq) | (_ , _ , _ , eq₁) rewrite eq | eq₁ with Swap {x} {y} {X} {Y} j p 
Swap (⟨ x₂ ↦ c₂ ⟩∷ j) p | tri> ¬a ¬b c | tri> ¬a₁ ¬b₁ c₁
  | (_ , _ , _ , eq) | (_ , _ , _ , eq₁) | q = cong₂ _∷_ refl q 
