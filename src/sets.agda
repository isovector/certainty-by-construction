module sets where

open import Function.Inverse
open import Data.Sum renaming (_⊎_ to infixr 80 _⊎_)
open import Data.Nat
open import Data.Fin using (Fin)
open import Function.Equality using (_⟨$⟩_)
open import Relation.Binary.PropositionalEquality

record IsFinite (A : Set) : Set where
  field
    card : ℕ
    is-finite : A ↔ Fin card

open IsFinite

#∣_∣ : {A : Set} → IsFinite A → ℕ
#∣_∣ = IsFinite.card

open Inverse

bijection-sum : {A B A' B' : Set} → A ↔ B → A' ↔ B' → A ⊎ A' ↔ B ⊎ B'
bijection-sum ab a'b' =
  inverse
    (Data.Sum.map (ab .to ._⟨$⟩_)   (a'b' .to ._⟨$⟩_))
    (Data.Sum.map (ab .from ._⟨$⟩_) (a'b' .from ._⟨$⟩_))
    (λ { (inj₁ x) → cong inj₁ (ab .left-inverse-of x)
       ; (inj₂ y) → cong inj₂ (a'b' .left-inverse-of y)
       })
    (λ { (inj₁ x) → cong inj₁ (ab .right-inverse-of x)
       ; (inj₂ y) → cong inj₂ (a'b' .right-inverse-of y)
       })

fin-sum : {m n : ℕ} → Fin m ⊎ Fin n ↔ Fin (m + n)
fin-sum = ?

finite-sum : {A B : Set} → IsFinite A → IsFinite B → IsFinite (A ⊎ B)
IsFinite.card (finite-sum a b) = #∣ a ∣ + #∣ b ∣
IsFinite.is-finite (finite-sum a b) = ?


-- data A : Set where

-- a : A ↔ A
-- a = inverse {! !} {! !} {! !} {! !}
