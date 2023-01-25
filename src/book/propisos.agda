module propisos where

open import Agda.Primitive
open import Relation.Binary.PropositionalEquality
open import Function using (id; _∘_)

record _↔_
      {c₁ c₂ : Level}
      (A : Set c₁)
      (B : Set c₂)
      : Set (c₁ ⊔ c₂) where
  constructor inverse
  field
    to   : A → B
    from : B → A
    left-inv-of  : (x : A) → from (to x) ≡ x
    right-inv-of : (x : B) → to (from x) ≡ x

private variable
  c₁ c₂ c₃ : Level

  A : Set c₁
  B : Set c₂
  C : Set c₃


↔-refl : A ↔ A
↔-refl = inverse id id (λ x → refl) (λ x → refl)


↔-sym : A ↔ B → B ↔ A
↔-sym (inverse to from left-inv-of right-inv-of) =
  inverse from to right-inv-of left-inv-of


↔-trans : A ↔ B
        → B ↔ C
        → A ↔ C
↔-trans (inverse to₁ from₁ left-inv-of₁ right-inv-of₁)
        (inverse to₂ from₂ left-inv-of₂ right-inv-of₂) =
  inverse
    (to₂ ∘ to₁)
    (from₁ ∘ from₂)
    (λ x → begin
      from₁ (from₂ (to₂ (to₁ x)))  ≡⟨ cong from₁ (left-inv-of₂ (to₁ x)) ⟩
      from₁ (to₁ x)                ≡⟨ left-inv-of₁ x ⟩
      x                            ∎
    )
    (λ x → begin
      to₂ (to₁ (from₁ (from₂ x)))  ≡⟨ cong to₂ (right-inv-of₁ (from₂ x)) ⟩
      to₂ (from₂ x)                ≡⟨ right-inv-of₂ x ⟩
      x                            ∎
    )
  where open ≡-Reasoning

