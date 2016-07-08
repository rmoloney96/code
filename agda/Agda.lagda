\documentclass{scrartcl}

% current annoyance: this will be fixed
% by the next update of agda.fmt
\def\textmu{}

%include agda.fmt

\begin{document}

We start with the module header:
\begin{code}
module Agda where


open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Data.Function using (_∘_)
\end{code}

This is the identity function:
\begin{code}
id : {A : Set} -> A -> A
id {A} x = x
\end{code}

Natural numbers (Peano style), addition and predecessor:
\begin{code}
data ℕ : Set where
  zero  :  ℕ
  suc   :  ℕ -> ℕ

_+_ : ℕ -> ℕ -> ℕ
zero   +  n  =  n
suc m  +  n  =  suc (m + n)

pred : ℕ -> ℕ
pred zero     =  zero
pred (suc n)  =  n
\end{code}

Vectors:
\begin{code}
data Vec (A : Set) : ℕ -> Set where
  []   :  Vec A zero
  _∷_  :  forall {n} -> A -> Vec A n -> Vec A (suc n)
\end{code}

The empty type |⊥| and its eliminator:
\begin{code}
data ⊥ : Set where

⊥-elim : {whatever : Set} -> ⊥ -> whatever
⊥-elim ()
\end{code}

Decidable propositions and relations:
\begin{code}
Rel : Set -> Set1
Rel a = a -> a -> Set

infix 3 ¬_

¬_ : Set -> Set
¬ P = P -> ⊥

data Dec (P : Set) : Set where
  yes  :  ( p :   P) -> Dec P
  no   :  (¬p : ¬ P) -> Dec P

Decidable : {a : Set} -> Rel a -> Set
Decidable _∼_ = forall x y -> Dec (x ∼ y)
\end{code}

Decidable equality on natural numbers:
\begin{code}
zero≢suc : forall {n} -> ¬ zero ≡ suc n
zero≢suc ()

_≟_ : Decidable {ℕ} _≡_
zero   ≟  zero                   =  yes ≡-refl
suc m  ≟  suc n   with m ≟ n
suc m  ≟  suc .m  |  yes ≡-refl  =  yes ≡-refl
suc m  ≟  suc n   |  no prf      =  no (prf ∘ ≡-cong pred)
zero   ≟  suc n                  =  no (⊥-elim ∘ zero≢suc)
suc m  ≟  zero                   =  no (⊥-elim ∘ zero≢suc ∘ ≡-sym)
\end{code}

Associative and commutative operations:
\begin{code}
Op₂ : Set
Op₂ = ℕ -> ℕ -> ℕ

Associative : Op₂ -> Set
Associative _∙_ = forall x y z -> ((x ∙ y) ∙ z) ≡ (x ∙ (y ∙ z))

Commutative : Op₂ -> Set
Commutative _∙_ = forall x y -> (x ∙ y) ≡ (y ∙ x)
\end{code}

Commutativity of addition:
%format begin = "\Keyword{begin}"
\begin{code}
m+1+n≡1+m+n  : forall m n -> m + suc n ≡ suc (m + n)
m+1+n≡1+m+n  zero     n  =  byDef
m+1+n≡1+m+n  (suc m)  n  =  ≡-cong suc (m+1+n≡1+m+n m n)

n+0≡n : forall n -> n + zero ≡ n
n+0≡n  zero     =  byDef
n+0≡n  (suc n)  =  ≡-cong suc (n+0≡n n)

+-comm : Commutative _+_
+-comm  zero     n  = ≡-sym (n+0≡n n)
+-comm  (suc m)  n  =
   begin
     suc m + n
   ≡⟨ byDef ⟩
     suc (m + n)
   ≡⟨ ≡-cong suc (+-comm m n) ⟩
     suc (n + m)
   ≡⟨ ≡-sym (m+1+n≡1+m+n n m) ⟩
     n + suc m
   ∎
\end{code}

\end{document}
