{-# OPTIONS --type-in-type #-}

import Algebra.Definitions
open import Relation.Binary.Structures
import Algebra.Structures

module rings
    {A : Set}
    {_≈_ : A → A → Set}
    (≈-equiv : IsEquivalence _≈_)
    (open Algebra.Definitions  _≈_)
    {0# : A}
    {1# : A}
    {_⊕_ : A → A → A}
    {_⊗_ : A → A → A}
    (let infixr 5 _⊕_; _⊕_ = _⊕_)
    (let infixr 6 _⊗_; _⊗_ = _⊗_)
    (open Algebra.Structures _≈_)
    (⊕-monoid : IsMonoid _⊕_ 0#)
    (⊗-monoid : IsMonoid _⊗_ 1#)
    (⊗-⊕-distrib : _⊗_ DistributesOver _⊕_)
  where

open import Data.Nat renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Nat.Properties



open import Data.Vec

rtimes : ℕ → A → A
rtimes zero a = 0#
rtimes (suc zero) a = a
rtimes (suc x) a = a ⊗ rtimes x a

record  Normal (n : ℕ) : Set where
  constructor norm
  field
    coefficients : Vec A n
    constant : A


data Poly : ℕ →  Set where
  K : A → Poly 0
  X : Poly 1
  _+_ : {m n : ℕ} → Poly m → Poly n → Poly (m ⊔ n)
  _*_ : {m n : ℕ} → Poly m → Poly n → Poly (m +ℕ n)

construct : {n : ℕ} → Poly n → A → A
construct (K x) v = x
construct X v = v
construct (x + y) v = construct x v ⊕ construct y v
construct (x * y) v = construct x v ⊗ construct y v

open import Data.Sum

padLeft' : ∀ {A} → (m k : ℕ) → A → Vec A m → Vec A (suc (m +ℕ k))
padLeft' m zero pad v rewrite +-identityʳ m = pad ∷ v
padLeft' m (suc k) pad v rewrite +-suc m k = pad ∷ padLeft' m k pad v

padLeft : ∀ {A : Set} {m n : ℕ} → (m ≤ n) → A → Vec A m → Vec A n
padLeft {m = m} {n} m≤n pad v with compare m n
... | less .m k = padLeft' m k pad v
... | equal .m = v
... | greater .n k = ?

+-combine : ∀ {m} {n} → (m≤n : m ≤ n) (a : Normal m) (b : Normal n) → Normal n
+-combine m≤n (norm ac ax) (norm bc bx) = norm (zipWith _⊕_ (padLeft m≤n 0# ac) bc) (ax ⊕ bx)

+-norm : {m n : ℕ} → Normal m → Normal n → Normal (m ⊔ n)
+-norm {m} {n} a b with ≤-total m n
... | inj₁ m≤n rewrite m≤n⇒m⊔n≡n m≤n = +-combine m≤n a b
... | inj₂ n≤m rewrite m≥n⇒m⊔n≡m n≤m = +-combine n≤m b a

*-norm : {m n : ℕ} → Normal m → Normal n → Normal (m +ℕ n)
*-norm = ?

normalize : {n : ℕ} → Poly n → Normal n
normalize (K x) = norm [] x
normalize X = norm [ 1# ] 0#
normalize (x + y) = +-norm (normalize x) (normalize y)
normalize (x * y) = *-norm (normalize x) (normalize y)

evaluate : {n : ℕ} → Normal n → A → A
evaluate (norm [] x) a = x
evaluate {n = n} (norm (x₁ ∷ cs) x) a
  = rtimes n a ⊕ evaluate (norm cs x) a


open IsEquivalence ≈-equiv

construct-is-normal : {n : ℕ} → (x : Poly n) → (a : A) → construct x a ≈ evaluate (normalize x) a
construct-is-normal (K x) a = refl
construct-is-normal X a = sym (IsMonoid.identityʳ ⊕-monoid a)
construct-is-normal (x + y) a = {! !}
construct-is-normal (x * y) a = {! !}



