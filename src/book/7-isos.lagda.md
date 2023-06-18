# Isomorphism

```agda
open import Relation.Binary using (Setoid; _Preserves_⟶_)
open import Level
open import Algebra using (LeftInverse; RightInverse)

private variable
  a b c₁ c₂ ℓ₁ ℓ₂ : Level

record Iso
      (s₁ : Setoid c₁ ℓ₁)
      (s₂ : Setoid c₂ ℓ₂)
      : Set (c₁ ⊔ c₂ ⊔ ℓ₁ ⊔ ℓ₂) where
  open Setoid s₁ using ()
      renaming (Carrier to A; _≈_ to _≈₁_)
      public
  open Setoid s₂ using ()
      renaming (Carrier to B; _≈_ to _≈₂_)
      public

  field
    to   : A → B
    from : B → A
    from∘to≈id  : (x : A) → from (to x) ≈₁ x
    to∘from≈id  : (x : B) → to (from x) ≈₂ x
    to-cong    : to    Preserves _≈₁_ ⟶ _≈₂_
    from-cong  : from  Preserves _≈₂_ ⟶ _≈₁_

  module A-Reasoning where
    open import Relation.Binary.Reasoning.Setoid s₁
      public
  module B-Reasoning where
    open import Relation.Binary.Reasoning.Setoid s₂
      public

_↔_ = Iso

open import Function using (id)

module _ {s : Setoid c₁ ℓ₁} where
  open Setoid s

  ↔-refl : s ↔ s
  Iso.to          ↔-refl    = id
  Iso.from        ↔-refl    = id
  Iso.from∘to≈id  ↔-refl x  = refl
  Iso.to∘from≈id  ↔-refl x  = refl
  Iso.to-cong     ↔-refl    = id
  Iso.from-cong   ↔-refl    = id

open import Data.Unit
  using (⊤; tt)

open import Relation.Binary.PropositionalEquality
  using (setoid)

import 6-structures
open 6-structures.Sandbox-Monoids
  using (≗-setoid)

open Iso
open Setoid

_¹ : (s : Setoid c₁ ℓ₁) → s ↔ ≗-setoid ⊤ s
to          (s ¹) x _   = x
from        (s ¹) f     = f tt
from∘to≈id  (s ¹) x     = refl s
to∘from≈id  (s ¹) x tt  = refl s
to-cong     (s ¹) x tt  = x
from-cong   (s ¹) f     = f tt

open import Data.Product using (_×_; _,_)

private variable
  X : Set a
  Y : Set b

hmm
  : (s : Setoid c₁ ℓ₁)
  → ≗-setoid (X × Y) s ↔ ≗-setoid X (≗-setoid Y s)
to          (hmm s) f x y      = f (x , y)
from        (hmm s) f (x , y)  = f x y
from∘to≈id  (hmm s) f xy       = refl s
to∘from≈id  (hmm s) f x y      = refl s
to-cong     (hmm s) f x y      = f (x , y)
from-cong   (hmm s) f (x , y)  = f x y

open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Data.Product.Relation.Binary.Pointwise.NonDependent
  using (×-setoid)

hmm2
  : (s : Setoid c₁ ℓ₁)
  → ≗-setoid (X ⊎ Y) s
      ↔ ×-setoid (≗-setoid X s) (≗-setoid Y s)
to    (hmm2 s) f  = (λ x → f (inj₁ x) )
                  , (λ y → f (inj₂ y))
from  (hmm2 s) (fx , fy) (inj₁ x) = fx x
from  (hmm2 s) (fx , fy) (inj₂ y) = fy y
from∘to≈id  (hmm2 s) f (inj₁ x) = refl s
from∘to≈id  (hmm2 s) f (inj₂ y) = refl s
to∘from≈id  (hmm2 s) fxfy  = (λ x → refl s)
                           , (λ y → refl s)
to-cong     (hmm2 s) f = (λ x → f (inj₁ x))
                       , (λ y → f (inj₂ y))
from-cong   (hmm2 s) (fx , fy) (inj₁ x) = fx x
from-cong   (hmm2 s) (fx , fy) (inj₂ y) = fy y

```
