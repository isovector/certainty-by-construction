module playground.NP-complete where

open import Data.Bool renaming (_∨_ to or; _∧_ to and) hiding (_≤_; _<_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using (Vec; _∷_; []; lookup)
open import Data.Nat
open import Data.List hiding (last; head; lookup; or; and)
open import Data.Maybe
open import Data.Sum hiding (map₂)
import Data.Sum as ⊎
open import Data.Product
import Data.Product as ×
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Function
open import Data.Empty

data Lit (n : ℕ) : Set where
  ↪ : Fin n → Lit n
  ¬ : Fin n → Lit n

data Clause (n : ℕ) : Set where
  last : Lit n → Clause n
  _∨_ : Lit n → Clause n → Clause n


data CNF (n : ℕ) : Set where
  last : Clause n → CNF n
  _∧_ : Clause n → CNF n → CNF n

private variable
  n : ℕ

evaluateLit : Vec Bool n → Lit n → Bool
evaluateLit bs (↪ x) = lookup bs x
evaluateLit bs (¬ x) = not (lookup bs x)

evaluateClause : Vec Bool n → Clause n → Bool
evaluateClause bs (last x) = evaluateLit bs x
evaluateClause bs (x ∨ y) = or (evaluateLit bs x) (evaluateClause bs y)

evaluate : Vec Bool n → CNF n → Bool
evaluate bs (last x) = evaluateClause bs x
evaluate bs (x ∧ y) = and (evaluateClause bs x) (evaluate bs y)

infixr 3 _∧_
infixr 4 _∨_

x₁ x₂ x₃ : Fin 3
x₁ = zero
x₂ = suc zero
x₃ = suc (suc zero)

test : CNF 3
test = (↪ x₁ ∨ last (¬ x₂))
     ∧ (¬ x₁ ∨ ↪ x₂ ∨ last (↪ x₃))
     ∧ last (last (¬ x₁))

assignments : Vec Bool 3
assignments = false ∷ false ∷ true ∷ []

test2 : Bool
test2 = evaluate assignments test

open import playground.turing
open TuringMachine

data State : Set where
  done : Bool → Bool → State
  have : Bool → Bool → State

data Final : State → Set where
  done : {lo hi : Bool} → Final (done lo hi)


data Instr (n : ℕ) : Set where
  pop halt : Instr n
  val : Lit n → Instr n


compileClause : Clause n → List (Instr n)
compileClause (last x) = [ val x ]
compileClause (x ∨ cnf) = val x ∷ compileClause cnf

compile : CNF n → List (Instr n)
compile (last x) = (compileClause x ++ [ pop ])
compile (x ∧ cnf) = (compileClause x ++ (pop ∷ compile cnf))

