```agda
open import np-complete1
open import Data.Product
open import Relation.Nullary using (¬_)

-- turing-machines
module np-complete2
  (Γ Q : Set)
  (δ : Q × Γ → Q × Γ × MoveDirection → Set)
  (H : Q × Γ → Set)
  (halted : {qi : Q × Γ} → H qi → (qir : Q × Γ × MoveDirection) → ¬ δ qi qir)
  (b : Γ)
  where

moveWrite : MoveDirection → Γ → Tape Γ → Tape Γ
moveWrite d i t = move b d (write i t)


data _⟶_ : Q × Tape Γ → Q × Tape Γ → Set where
  refl
      : {qt : Q × Tape Γ}
      → qt ⟶ qt
  trans
      : {qt₁ qt₂ qt₃ : Q × Tape Γ}
      → qt₁ ⟶ qt₂
      → qt₂ ⟶ qt₃
      → qt₁ ⟶ qt₃
  step
      : {i : Γ} {d : MoveDirection} {q₁ q₂ : Q} {t : Tape Γ}
      → δ (q₁ , Tape.head t)
          (q₂ , i , d)
      → (q₁ , t) ⟶ (q₂ , moveWrite d i t)


data HaltsWith (qt : Q × Tape Γ) (q : Q) : Set where
  halts-with
      : {t : Tape Γ}
      → qt ⟶ (q , t)
      → H (q , Tape.head t)
      → HaltsWith qt q


module ⟶-Reasoning where
  open import Relation.Binary.Reasoning.Base.Single _⟶_ refl trans as Base public
    hiding (step-∼)

  infixr 2 step-≈

  step-≈ = Base.step-∼
  syntax step-≈ x y≈z x≈y = x ≈⟨ x≈y ⟩ y≈z
```


