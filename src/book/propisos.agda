module propisos where

open import Agda.Primitive
open import Relation.Binary.PropositionalEquality
open import Function using (id; _∘_)
open import Relation.Binary using (Setoid; _Preserves_⟶_)

private variable
  c₁ c₂ ℓ₁ ℓ₂ : Level

record _↔_
      (s₁ : Setoid c₁ ℓ₁)
      (s₂ : Setoid c₂ ℓ₂)
      : Set (c₁ ⊔ c₂ ⊔ ℓ₁ ⊔ ℓ₂) where
  open Setoid s₁ using () renaming (Carrier to A; _≈_ to _≈₁_) public
  open Setoid s₂ using () renaming (Carrier to B; _≈_ to _≈₂_) public


  field
    to   : A → B
    from : B → A
    left-inv-of  : (x : A) → from (to x) ≈₁ x
    right-inv-of : (x : B) → to (from x) ≈₂ x
    to-cong   : to Preserves _≈₁_ ⟶ _≈₂_
    from-cong : from Preserves _≈₂_ ⟶ _≈₁_

-- private variable
--   c₃ : Level

--   A : Set c₁
--   B : Set c₂
--   C : Set c₃


-- ↔-refl : A ↔ A
-- ↔-refl = inverse id id (λ x → refl) (λ x → refl)


-- ↔-sym : A ↔ B → B ↔ A
-- ↔-sym (inverse to from left-inv-of right-inv-of) =
--   inverse from to right-inv-of left-inv-of


-- ↔-trans : A ↔ B
--         → B ↔ C
--         → A ↔ C
-- ↔-trans (inverse to₁ from₁ left-inv-of₁ right-inv-of₁)
--         (inverse to₂ from₂ left-inv-of₂ right-inv-of₂) =
--   inverse
--     (to₂ ∘ to₁)
--     (from₁ ∘ from₂)
--     (λ x → begin
--       from₁ (from₂ (to₂ (to₁ x)))  ≡⟨ cong from₁ (left-inv-of₂ (to₁ x)) ⟩
--       from₁ (to₁ x)                ≡⟨ left-inv-of₁ x ⟩
--       x                            ∎
--     )
--     (λ x → begin
--       to₂ (to₁ (from₁ (from₂ x)))  ≡⟨ cong to₂ (right-inv-of₁ (from₂ x)) ⟩
--       to₂ (from₂ x)                ≡⟨ right-inv-of₂ x ⟩
--       x                            ∎
--     )
--   where open ≡-Reasoning

