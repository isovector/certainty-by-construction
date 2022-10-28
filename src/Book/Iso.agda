module Book.Iso where

open import Relation.Binary.Structures public
open import Relation.Binary.PropositionalEquality

open import Function using (_∘_; id)

record _↔_ (A B : Set) : Set where
  constructor inverse
  field
    to   : A → B
    from : B → A
    left-inverse-of  : (x : A) → from (to x) ≡ x
    right-inverse-of : (x : B) → to (from x) ≡ x

open _↔_

↔-equiv : IsEquivalence _↔_
IsEquivalence.refl ↔-equiv = inverse id id (λ { x → refl }) (λ { x → refl })
IsEquivalence.sym ↔-equiv (inverse to from left-inverse-of right-inverse-of) =
  inverse from to right-inverse-of left-inverse-of
IsEquivalence.trans ↔-equiv a b =
  inverse
    (b .to ∘ a .to)
    (a .from ∘ b .from)
    (λ { x → trans (cong (a .from) (b .left-inverse-of  (a .to x)))   (a .left-inverse-of x) })
    (λ { x → trans (cong (b .to)   (a .right-inverse-of (b .from x))) (b .right-inverse-of x) })

↔-refl : {x : Set} → x ↔ x
↔-refl = ↔-equiv .IsEquivalence.refl

↔-sym : {x y : Set} → x ↔ y → y ↔ x
↔-sym = ↔-equiv .IsEquivalence.sym

↔-trans : {i j k : Set} → i ↔ j → j ↔ k → i ↔ k
↔-trans = ↔-equiv .IsEquivalence.trans

