open import Relation.Binary using (Setoid)

module iso where

open import Relation.Binary.Structures public
open import Relation.Binary.PropositionalEquality

open import Function using (_∘_; id)
open import Agda.Primitive

private variable
  ℓ₁ ℓ₂ c₁ c₂ : Level

open Setoid using (Carrier)

record _↔_
      (s₁ : Setoid ℓ₁ c₁)
      (s₂ : Setoid ℓ₂ c₂) : Set (ℓ₁ ⊔ ℓ₂ ⊔ c₁ ⊔  c₂) where
  constructor inverse

  open Setoid s₁ renaming (Carrier to A; _≈_ to _≈₁_)
  open Setoid s₂ renaming (Carrier to B; _≈_ to _≈₂_)

  field
    to   : A → B
    from : B → A
    left-inverse-of  : (x : A) → from (to x) ≈₁ x
    right-inverse-of : (x : B) → to (from x) ≈₂ x

open _↔_


-- ↔-equiv : IsEquivalence (_↔_ {ℓ₁})
-- IsEquivalence.refl ↔-equiv = inverse id id (λ { x → refl }) (λ { x → refl })
-- IsEquivalence.sym ↔-equiv (inverse to from left-inverse-of right-inverse-of) =
--   inverse from to right-inverse-of left-inverse-of
-- IsEquivalence.trans ↔-equiv a b =
--   inverse
--     (b .to ∘ a .to)
--     (a .from ∘ b .from)
--     (λ { x → trans (cong (a .from) (b .left-inverse-of  (a .to x)))   (a .left-inverse-of x) })
--     (λ { x → trans (cong (b .to)   (a .right-inverse-of (b .from x))) (b .right-inverse-of x) })

-- ↔-refl : {x : Set ℓ₁} → x ↔ x
-- ↔-refl = ↔-equiv .IsEquivalence.refl

-- ↔-sym : {x y : Set ℓ₁} → x ↔ y → y ↔ x
-- ↔-sym = ↔-equiv .IsEquivalence.sym

-- ↔-trans : {i j k : Set ℓ₁} → i ↔ j → j ↔ k → i ↔ k
-- ↔-trans = ↔-equiv .IsEquivalence.trans

