```agda
open import np-complete1
open import Data.Product
open import Relation.Nullary using (¬_)
open import Relation.Unary using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_)

-- turing-machines
module np-complete2
  (Γ Q : Set)
  (δ : Q × Γ → Q × Γ × MoveDirection → Set)
  (H : Q × Γ → Set)
  (halted : {qi : Q × Γ} → H qi → (qir : Q × Γ × MoveDirection) → ¬ δ qi qir)
  (b : Γ)
  (b-dec : Decidable (_≡ b))
  where

open Tapes Γ b b-dec public

moveWrite : MoveDirection → Γ → Tape → Tape
moveWrite d i t = move d (write i t)


open import Data.Nat using (ℕ; _+_)

data _-⟨_⟩→_ : Q × Tape → ℕ → Q × Tape → Set where
  refl
      : {qt : Q × Tape}
      → qt -⟨ 0 ⟩→ qt
  trans
      : {qt₁ qt₂ qt₃ : Q × Tape}
        {n₁ n₂ : ℕ }
      → qt₁ -⟨ n₁ ⟩→ qt₂
      → qt₂ -⟨ n₂ ⟩→ qt₃
      → qt₁ -⟨ n₂ + n₁ ⟩→ qt₃
  step
      : {i : Γ} {d : MoveDirection} {q₁ q₂ : Q} {t : Tape}
      → δ (q₁ , Tape.head t) (q₂ , i , d)
      → (q₁ , t) -⟨ 1 ⟩→ (q₂ , moveWrite d i t)
open _-⟨_⟩→_

_⟶_ : Q × Tape → Q × Tape → Set
_⟶_ qt₁ qt₂ = ∀ {n : ℕ} → qt₁ -⟨ n ⟩→ qt₂


open import Relation.Binary.PropositionalEquality using (_≡_; refl)

⟶-subst
    : {qt₁ qt₁' qt₂ qt₂' : Q × Tape}
    → qt₁ ≡ qt₁'
    → qt₂ ≡ qt₂'
    → qt₁ ⟶ qt₂
    → qt₁' ⟶ qt₂'
⟶-subst refl refl x = x

data HaltsWith (qt : Q × Tape) (q : Q) : Set where
  halts-with
      : {t : Tape} {n : ℕ}
      → qt -⟨ n ⟩→ (q , t)
      → H (q , Tape.head t)
      → HaltsWith qt q

data HaltsIn (qt : Q × Tape) (q : Q) (n : ℕ) : Set where
  halts-in
      : {t : Tape}
      → qt -⟨ n ⟩→ (q , t)
      → H (q , Tape.head t)
      → HaltsIn qt q n

halts-glue
  : {qt₁ qt₂ : Q × Tape} {q : Q} {n : ℕ}
  → qt₁ -⟨ n ⟩→ qt₂
  → HaltsWith qt₂ q
  → HaltsWith qt₁ q
halts-glue x₁ (halts-with x₂ h) =
  halts-with (_-⟨_⟩→_.trans x₁ x₂) h

subst-halts
  : {qt qt' : Q × Tape} {q q' : Q}
  → qt ≡ qt'
  → q ≡ q'
  → HaltsWith qt q
  → HaltsWith qt' q'
subst-halts refl refl x = x

module ⟶-Reasoning where
  begin_ : ∀ {qt₁ qt₂ n}
         → qt₁ -⟨ n ⟩→ qt₂
         → qt₁ -⟨ n ⟩→ qt₂
  begin_ x = x

  _≈⟨_⟩_ : ∀ {qt₂ qt₃ n₁ n₂}
         → (qt₁ : _)
         → qt₁ -⟨ n₁ ⟩→ qt₂
         → qt₂ -⟨ n₂ ⟩→ qt₃
         → qt₁ -⟨ n₂ + n₁ ⟩→ qt₃
  _≈⟨_⟩_ _ r a = trans r a

  _≡⟨_⟩_ : ∀ {qt₂ qt₃ n}
         → (qt₁ : _)
         → qt₁ ≡ qt₂
         → qt₂ -⟨ n ⟩→ qt₃
         → qt₁ -⟨ n ⟩→ qt₃
  _≡⟨_⟩_ _ refl a = a

  _≡ᵀ⟨_⟩_ : ∀ {qt₂ n₁ n₂}
         → (qt₁ : _)
         → n₁ ≡ n₂
         → qt₁ -⟨ n₁ ⟩→ qt₂
         → qt₁ -⟨ n₂ ⟩→ qt₂
  _≡ᵀ⟨_⟩_ _ refl a = a

  _≡⟨⟩_ : ∀ {qt₂ n}
         → (qt₁ : _)
         → qt₁ -⟨ n ⟩→ qt₂
         → qt₁ -⟨ n ⟩→ qt₂
  _≡⟨⟩_ _ a = a

  _∎ : ∀ qt
     → qt -⟨ 0 ⟩→ qt
  _∎ _ = refl

  infix  1 begin_
  infixr 2 _≈⟨_⟩_ _≡⟨⟩_ _≡⟨_⟩_ _≡ᵀ⟨_⟩_
  infix  3 _∎




  -- open import Relation.Binary.Reasoning.Base.Single _⟶_
  --     (λ {z} → refl {z})
  --     ?
  --     as Base public
  --   hiding (step-∼)

  -- infixr 2 step-≈

  -- step-≈ = Base.step-∼
  -- syntax step-≈ x y≈z x≈y = x ≈⟨ x≈y ⟩ y≈z
```


