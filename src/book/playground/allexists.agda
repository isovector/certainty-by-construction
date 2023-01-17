module playground.allexists {A : Set} (P : A → Set) where

open import Function using (id)
open import Relation.Nullary
open import Relation.Nullary.Decidable hiding (map)
open import Relation.Unary
open import Data.Product
open import Data.Empty
open import Data.Unit hiding (_≟_)
open import Data.Sum hiding (map₁; map)

open import Data.Nat
open import Data.Nat.Properties
open import 8-iso
open import Data.Fin hiding (_≤_; _<_; _≟_)
open import Agda.Primitive

open import Relation.Binary.PropositionalEquality using (refl; cong; subst; _≡_)

record IsFinite (l : Level) (A : Set) : Set (lsuc l) where
  field
    card : ℕ
    {{ A-equiv }} : Equivalent l A
    {{ fin-equiv }} : Equivalent l (Fin card)
    is-finite : A ↔ Fin card

not-∀ : ¬ ((a : A) → P a) → ∃[ a ] ¬ P a
not-∀ x = {! !}


bonk-∀P
  : {n : ℕ}
  → (P : Fin (suc n) → Set)
  → P zero
  → ¬ (∀ i → P i)
  → ¬ (∀ i → P (suc i))
bonk-∀P P P0 ¬∀P ∀Psuc = ¬∀P λ
  { zero → P0
  ; (suc i) → ∀Psuc i
  }


search
  : {n : ℕ}
  → (P : Fin n → Set)
  → (∀ i → Dec (P i))
  → ¬ (∀ i → P i)
  → ∃[ i ] ¬ P i
search {zero} P P? ¬∀P = ⊥-elim (¬∀P λ ())
search {suc n} P P? ¬∀P with P? zero
... | no ¬P0 = zero , ¬P0
... | yes P0 with search (λ i → P (suc i)) (λ i → P? (suc i) ) (bonk-∀P P P0 ¬∀P)
... | i , Pi = suc i , Pi


not-∀-fin : {ℓ : Level} → IsFinite ℓ A → Decidable P → ¬ ((a : A) → P a) → ∃[ a ] ¬ P a
not-∀-fin {ℓ} a-fin dec-P ¬∀P = map from id (search P' P'Dec ¬∀P')
  where
    open IsFinite a-fin
    open _↔_ is-finite

    P' : Fin card → Set
    P' i = P (from i)

    P'Dec : (n : Fin card) → Dec (P' n)
    P'Dec i = dec-P (from i)

    postulate
      ≈-to-≡ : ∀ {_≈_ : A → A → Set ℓ} {a b : A} → a ≈ b → a ≡ b

    ¬∀P' : ¬ ((n : Fin card) → P' n)
    ¬∀P' x = ¬∀P λ { a → subst P (≈-to-≡ {A-equiv ._≋_} (left-inv-of a)) (x (to a)) }

    p-from : (n : Fin card) → Set
    p-from n = P (from n)

