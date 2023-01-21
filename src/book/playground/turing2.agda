open import playground.turing using (MoveDirection; L; R; Tape; tape; write)
open import Data.Product
open import Relation.Nullary using (¬_)

module playground.turing2
  (Γ Q : Set)
  (δ : Q × Γ → Q × Γ × MoveDirection → Set)
  (H : Q × Γ → Set)
  (_ : {qi : Q × Γ} → H qi → (qir : Q × Γ × MoveDirection) → ¬ δ qi qir)
  (b : Γ)
  where

open import Data.List using ([]; _∷_)

move : MoveDirection → Tape Γ → Tape Γ
move L (tape [] h r)
  = tape [] b (h ∷ r)
move L (tape (x ∷ l) h r)
  = tape l x (h ∷ r)
move R (tape l h [])
  = tape (h ∷ l) b []
move R (tape l h (x ∷ r))
  = tape (h ∷ l) x r


moveWrite : MoveDirection → Γ → Tape Γ → Tape Γ
moveWrite dir sym t = move dir (write sym t)


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
  halts-with : {t : Tape Γ} → qt ⟶ (q , t) → H (q , Tape.head t) → HaltsWith qt q


module ⟶-Reasoning where
  open import Relation.Binary.Reasoning.Base.Single _⟶_ refl trans as Base public
    hiding (step-∼)

  infixr 2 step-≈

  step-≈ = Base.step-∼
  syntax step-≈ x y≈z x≈y = x ≈⟨ x≈y ⟩ y≈z

