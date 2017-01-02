
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
  _∷_ : ∀ {l} x c → x ≼* l → OrderedKeys l → OrderedKeys ((x , c) ∷ l)

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
InsertOrdered x X [] = (x ∷ X) [] []
InsertOrdered x X ((y ∷ Y) x₂ l₁) with tri x y
InsertOrdered x X ((y ∷ Y) x₂ l₁) | tri< a ¬b ¬c = (x ∷ X) (a ∷ x≼y∧y≼*l⇒x≼*l a x₂) ((y ∷ Y) x₂ l₁)
InsertOrdered y X ((.y ∷ Y) x₂ l₁) | tri≈ ¬a refl ¬c = (y ∷ X) x₂ l₁
InsertOrdered x X ((y ∷ Y) x₂ l₁) | tri> ¬a ¬b c with InsertOrdered x X l₁
InsertOrdered x X ((y ∷ Y) x₂ l₁) | tri> ¬a ¬b c | res = (y ∷ Y) {!!} res 

Overwrite : ∀ {x X Y i} → i [ x ≔ X ] [ x ≔ Y ] ≡ i [ x ≔ Y ]
Overwrite = {!!}


{-
Swap : ∀ {x y X Y i} → OrderedKeys i → x ≢ y → i [ x ≔ X ] [ y ≔ Y ] ≡ i [ y ≔ Y ] [ x ≔ X ]
Swap {x} {y} base np with tri x y 
Swap base np | tri< a ¬b ¬c with y≼x a
Swap base np | tri< a ¬b ¬c | p₁ , p₂ , p₃ , eq rewrite eq = refl
Swap base np | tri≈ ¬a b ¬c = b ↯ np
Swap base np | tri> ¬a ¬b c with x≼y c
Swap base np | tri> ¬a ¬b c | p₁ , p₂ , p₃ , eq rewrite eq = refl
Swap {x} {y} (one z) np with tri x z | tri y z | tri x y 
Swap (one z) np | tri< a ¬b ¬c | tri< a₁ ¬b₁ ¬c₁ | tri< a₂ ¬b₂ ¬c₂ = {!!}
Swap (one z) np | tri< a ¬b ¬c | tri< a₁ ¬b₁ ¬c₁ | tri≈ ¬a b ¬c₂ = {!!}
Swap (one z) np | tri< a ¬b ¬c | tri< a₁ ¬b₁ ¬c₁ | tri> ¬a ¬b₂ c = {!!}
Swap (one z) np | tri< a ¬b ¬c | tri≈ ¬a b ¬c₁ | tri< a₁ ¬b₁ ¬c₂ = {!!}
Swap (one z) np | tri< a ¬b ¬c | tri≈ ¬a b ¬c₁ | tri≈ ¬a₁ b₁ ¬c₂ = {!!}
Swap (one z) np | tri< a ¬b ¬c | tri≈ ¬a b ¬c₁ | tri> ¬a₁ ¬b₁ c = {!!}
Swap (one z) np | tri< a ¬b ¬c | tri> ¬a ¬b₁ c | tri< a₁ ¬b₂ ¬c₁ = {!!}
Swap (one z) np | tri< a ¬b ¬c | tri> ¬a ¬b₁ c | tri≈ ¬a₁ b ¬c₁ = {!!}
Swap (one z) np | tri< a ¬b ¬c | tri> ¬a ¬b₁ c | tri> ¬a₁ ¬b₂ c₁ = {!!}
Swap (one z) np | tri≈ ¬a b ¬c | res₁ | res = {!!}
Swap (one z) np | tri> ¬a ¬b c | res₁ | res = {!!}
Swap {x} {y} (next z x₂ ok) np with tri x y 
Swap (next z x₂ ok) np | res = {!!}
-}



