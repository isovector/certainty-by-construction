```agda
module np-complete0 where

open import Data.Nat
  using (ℕ)
open import Data.Fin
  using (Fin; zero; suc)
open import Data.Vec
  using (Vec; lookup; _∷_; [])
open import Data.Bool
open import Data.List using (List)


module _ (n : ℕ) where
  data Lit  : Set where
    ↪ : Fin n → Lit
    ! : Fin n → Lit

  data Instr : Set where
    pop : Instr
    val : Lit → Instr
    nop : Instr

  Clause : Set
  Clause = List Lit

  CNF : Set
  CNF = List Clause

private variable
  n : ℕ

_↓ˡ_ : Lit n → Vec Bool n → Bool
_↓ˡ_ (↪ x) bs = lookup bs x
_↓ˡ_ (! x) bs = not (lookup bs x)

open import Data.List using (List; _∷_; []; foldr)

_↓ᶜ_ : List (Lit n) → Vec Bool n → Bool
_↓ᶜ_ cl bs = foldr (λ l lo → (l ↓ˡ bs) ∨ lo) false cl

_↓_ : List (List (Lit n)) → Vec Bool n → Bool
_↓_ cnf bs = foldr (λ cl hi → (cl ↓ᶜ bs) ∧ hi) true cnf


module Example where
  x₁ x₂ x₃ : Fin 3
  x₁ = zero
  x₂ = suc zero
  x₃ = suc (suc zero)

  test : CNF 3
  test = (↪ x₁ ∷ ! x₂ ∷ [])
      ∷ (! x₁ ∷ ↪ x₂ ∷ ↪ x₃ ∷ [])
      ∷ (! x₁ ∷ [])
      ∷ []

  open import Relation.Binary.PropositionalEquality

  _ : test ↓ (false ∷ false ∷ true ∷ []) ≡ true
  _ = refl
```
