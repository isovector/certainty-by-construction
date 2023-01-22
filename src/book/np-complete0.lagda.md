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

evaluateLit : Vec Bool n → Lit n → Bool
evaluateLit bs (↪ x) = lookup bs x
evaluateLit bs (! x) = not (lookup bs x)

open import Data.List using (List; _∷_; []; foldr)

evaluateClause : Vec Bool n → List (Lit n) → Bool
evaluateClause bs = foldr (λ l lo → evaluateLit bs l ∨ lo) false

evaluate : Vec Bool n → List (List (Lit n)) → Bool
evaluate bs = foldr (λ cl hi → evaluateClause bs cl ∧ hi) true


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

  _ : evaluate (false ∷ false ∷ true ∷ []) test ≡ true
  _ = refl
```
