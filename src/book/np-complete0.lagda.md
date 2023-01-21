```agda
module np-complete0 where

open import Data.Nat
  using (ℕ)
open import Data.Fin
  using (Fin; zero; suc)
open import Data.Vec
  using (Vec; lookup; _∷_; [])
open import Data.Bool
  renaming (_∨_ to or; _∧_ to and)


module _ (n : ℕ) where
  data Lit  : Set where
    ↪ : Fin n → Lit
    ! : Fin n → Lit

  data Clause  : Set where
    last : Lit → Clause
    _∨_ : Lit → Clause → Clause


  data CNF : Set where
    last : Clause → CNF
    _∧_ : Clause → CNF → CNF

  infixr 3 _∧_
  infixr 4 _∨_

  data Instr : Set where
    pop : Instr
    val : Lit → Instr
    halt : Instr

private variable
  n : ℕ

evaluateLit : Vec Bool n → Lit n → Bool
evaluateLit bs (↪ x) = lookup bs x
evaluateLit bs (! x) = not (lookup bs x)

evaluateClause : Vec Bool n → Clause n → Bool
evaluateClause bs (last x) = evaluateLit bs x
evaluateClause bs (x ∨ y) = or (evaluateLit bs x) (evaluateClause bs y)

evaluate : Vec Bool n → CNF n → Bool
evaluate bs (last x) = evaluateClause bs x
evaluate bs (x ∧ y) = and (evaluateClause bs x) (evaluate bs y)


module Example where
  x₁ x₂ x₃ : Fin 3
  x₁ = zero
  x₂ = suc zero
  x₃ = suc (suc zero)

  test : CNF 3
  test = (↪ x₁ ∨ last (! x₂))
      ∧ (! x₁ ∨ ↪ x₂ ∨ last (↪ x₃))
      ∧ last (last (! x₁))

  open import Relation.Binary.PropositionalEquality

  _ : evaluate (false ∷ false ∷ true ∷ []) test ≡ true
  _ = refl
```
