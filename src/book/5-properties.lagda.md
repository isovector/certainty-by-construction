## Common Properties

```agda
module 5-properties where

open import Level

private variable
  a b c ℓ ℓ₁ ℓ₂ ℓ₃ : Level
  A : Set a
  B : Set b
  C : Set c

REL : Set a → Set b → (ℓ : Level) → Set (a ⊔ b ⊔ suc ℓ)
REL A B ℓ = A → B → Set ℓ

Rel : Set a → (ℓ : Level) → Set (a ⊔ suc ℓ)
Rel A ℓ = REL A A ℓ

Reflexive : Rel A ℓ → Set _
Reflexive _≈_ = ∀ {x} → x ≈ x

_Preserves_⟶_ : (f : A → B) → Rel A ℓ₁ → Rel B ℓ₂ → Set _
_Preserves_⟶_  f P Q = ∀ {x y} → P x y → Q (f x) (f y)

```


