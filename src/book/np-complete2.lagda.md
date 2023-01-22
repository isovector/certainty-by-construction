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


data _⟶_ : Q × Tape → Q × Tape → Set where
  refl
      : {qt : Q × Tape}
      → qt ⟶ qt
  trans
      : {qt₁ qt₂ qt₃ : Q × Tape}
      → qt₁ ⟶ qt₂
      → qt₂ ⟶ qt₃
      → qt₁ ⟶ qt₃
  step
      : {i : Γ} {d : MoveDirection} {q₁ q₂ : Q} {t : Tape}
      → δ (q₁ , Tape.head t)
          (q₂ , i , d)
      → (q₁ , t) ⟶ (q₂ , moveWrite d i t)

open import Data.Nat using (ℕ; _+_)

data _-⟨_⟩→_ : Q × Tape → ℕ → Q × Tape → Set where
  n→refl
      : {qt : Q × Tape}
      → qt -⟨ 0 ⟩→ qt
  n→trans
      : {qt₁ qt₂ qt₃ : Q × Tape}
        {n₁ n₂ : ℕ }
      → qt₁ -⟨ n₁ ⟩→ qt₂
      → qt₂ -⟨ n₂ ⟩→ qt₃
      → qt₁ -⟨ n₁ + n₂ ⟩→ qt₃
  n→step
      : {i : Γ} {d : MoveDirection} {q₁ q₂ : Q} {t : Tape}
      → (q₁ , t) -⟨ 1 ⟩→ (q₂ , moveWrite d i t)
open _-⟨_⟩→_

count : {qt₁ qt₂ : Q × Tape} → qt₁ ⟶ qt₂ → ∃[ n ] qt₁ -⟨ n ⟩→ qt₂
count refl = 0 , n→refl
count (trans x y) with count x | count y
... | nx , ax | ny , ay = nx + ny , n→trans ax ay
count (step x) = 1 , n→step

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
      : {t : Tape}
      → qt ⟶ (q , t)
      → H (q , Tape.head t)
      → HaltsWith qt q

data HaltsIn (qt : Q × Tape) (q : Q) (n : ℕ) : Set where
  halts-in
      : {t : Tape}
      → qt -⟨ n ⟩→ (q , t)
      → H (q , Tape.head t)
      → HaltsIn qt q n

halts-glue
  : {qt₁ qt₂ : Q × Tape} {q : Q}
  → qt₁ ⟶ qt₂
  → HaltsWith qt₂ q
  → HaltsWith qt₁ q
halts-glue x₁ (halts-with x₂ h) =
  halts-with (_⟶_.trans x₁ x₂) h

subst-halts
  : {qt qt' : Q × Tape} {q q' : Q}
  → qt ≡ qt'
  → q ≡ q'
  → HaltsWith qt q
  → HaltsWith qt' q'
subst-halts refl refl x = x

module ⟶-Reasoning where
  open import Relation.Binary.Reasoning.Base.Single _⟶_ refl trans as Base public
    hiding (step-∼)

  infixr 2 step-≈

  step-≈ = Base.step-∼
  syntax step-≈ x y≈z x≈y = x ≈⟨ x≈y ⟩ y≈z
```


