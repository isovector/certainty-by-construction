open import Algebra.Bundles

open import Agda.Primitive

module homomorphism (monoid→ : Monoid lzero lzero) (→monoid : Monoid lzero lzero) where

open Monoid monoid→ using () renaming (Carrier to Carrier₁; _∙_ to _∙₁_; ε to ε₁; _≈_ to _≈₁_)
open Monoid →monoid using () renaming (Carrier to Carrier₂; _∙_ to _∙₂_; ε to ε₂; _≈_ to _≈₂_)

record MonoidHomomorphism (f : Carrier₁ → Carrier₂) : Set where
  field
    ∙-commute : ∀ a b → f (a ∙₁ b) ≈₂ f a ∙₂ f b
    ε-commute : f ε₁ ≈₂ ε₂



