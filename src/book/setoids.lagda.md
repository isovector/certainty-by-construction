```agda
module setoids where

private variable
  A : Set
  a b c : A

record IsEquivalence (_≈_ : A → A → Set) : Set where
  field
    refl : a ≈ a
    sym : a ≈ b → b ≈ a
    trans : a ≈ b → b ≈ c → a ≈ c
open IsEquivalence

record Setoid : Set₁ where
  infix 4 _≈_
  field
    Carrier : Set
    _≈_ : Carrier → Carrier → Set
    isEquivalence : IsEquivalence _≈_
open Setoid

module _ where
  import Relation.Binary.PropositionalEquality as P

  setoid : Set → Setoid
  Carrier (setoid A) = A
  _≈_ (setoid A) = P._≡_
  refl (isEquivalence (setoid A)) = P.refl
  sym (isEquivalence (setoid A)) = P.sym
  trans (isEquivalence (setoid A)) = P.trans

module _ where
  open import Data.Nat
  import Relation.Binary.PropositionalEquality as P

  data Modular (n : ℕ) : ℕ → ℕ → Set where
    ≈-mod : {a b : ℕ} → (x y : ℕ) → (a + x * n P.≡ b + y * n) → Modular n a b

  _≈_⟨mod_⟩ : ℕ → ℕ → ℕ → Set
  _≈_⟨mod_⟩ a b n = Modular n a b


  mod-setoid : ℕ → Setoid
  Carrier (mod-setoid n) = ℕ
  _≈_ (mod-setoid n) = Modular n
  refl (isEquivalence (mod-setoid n)) = ≈-mod 0 0 P.refl
  sym (isEquivalence (mod-setoid n)) (≈-mod x y p) = ≈-mod y x (P.sym p)
  trans (isEquivalence (mod-setoid n)) {a} {b} {c}
      (≈-mod x y pxy)
      (≈-mod x' y' pxy') = ≈-mod (x * y') (y * x')
      (
      begin
        a + x * y' * n
      ≡⟨ ? ⟩
        c + y * x' * n
      ∎
      )
    where open P.≡-Reasoning

  test : 5 ≈ 3 ⟨mod 2 ⟩
  test = ≈-mod 0 1 P.refl

```
