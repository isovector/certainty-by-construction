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

sizeClause : Clause n → ℕ
sizeClause (last x) = 1
sizeClause (x ∨ xs) = 1 + sizeClause xs

size : CNF n → ℕ
size (last x) = sizeClause x
size (x ∧ xs) = sizeClause x + size xs

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

-- compile : Vec Bool n → CNF n → TuringMachine (StackInstr ⊎ Bool) (Bool × Bool) Bool × List (StackInstr ⊎ Bool)



compileClause : Clause n → List (Instr n)
compileClause (last x) = [ val x ]
compileClause (x ∨ cnf) = val x ∷ compileClause cnf

compile : CNF n → List (Instr n)
compile (last x) = (compileClause x ++ [ pop ])
compile (x ∧ cnf) = (compileClause x ++ (pop ∷ compile cnf))

open import Relation.Nullary

module _ (bs : Vec Bool n) where

  satTM : TuringMachine (Instr n) Final
  blank satTM = halt
  F-dec satTM (done lo hi) = yes done
  F-dec satTM (have _ _) = no λ ()
  initial-state satTM = have true false
  transition satTM (done lo hi) i = done lo hi , i , R
  transition satTM (have lo hi) pop = have (and lo hi) false , halt , R
  transition satTM (have lo hi) halt = done lo hi , halt , R
  transition satTM (have lo hi) (val x) = have lo (or hi (evaluateLit bs x)) , halt , R

  open Stepping satTM

  postulate
    always-r : ∀ q h → proj₂ (proj₂ (transition satTM q h)) ≡ R
    always-halt : ∀ q h → proj₁ (proj₂ (transition satTM q h)) ≡ halt

  open import Data.Product.Properties

  {-# TERMINATING #-}
  yo : (q : State) → (t : Tape (Instr n)) → HaltsIn (q , t) (finite-sizeʳ t)
  yo q t@(tape _ h []) = Stepping.halts ? (moveWrite satTM R halt t) done {! !}
  yo q t@(tape l h (x ∷ r)) with step satTM q t in eq
  yo q t@(tape l h (x ∷ r)) | z = ?
  -- ... | h = glue₁ {! Stepping.step-via !} h
  -- ... | Stepping.halts q₁ t x₄ x₅
  --     rewrite always-r q h
  --     rewrite always-halt q h
  --     = Stepping.halts q₁ t x₄ (Stepping.step-trans (Stepping.step-via (
  --       begin
  --         step satTM q (tape l h (x ∷ r))
  --       ≡⟨⟩
  --         proj₁ (transition satTM q h) , move satTM (proj₂ (proj₂ (transition satTM q h))) (tape l (proj₁ (proj₂ (transition satTM q h))) (x ∷ r))
  --       ≡⟨ ? ⟩
  --         proj₁ (transition satTM q h) , move satTM R (tape l (proj₁ (proj₂ (transition satTM q h))) (x ∷ r))
  --       ≡⟨ ? ⟩
  --         proj₁ (transition satTM q h) , move satTM R (tape l halt (x ∷ r))
  --       ≡⟨⟩
  --         proj₁ (transition satTM q h) , tape (halt ∷ l) x r
  --       ≡⟨ ? ⟩
  --         q , tape (halt ∷ l) x r
  --       ∎
  --     )) x₅)
      where open ≡-Reasoning


Q : Set
Q = Bool × Bool




--   step : Q → Tape Γ → F ⊎ (Q × Tape Γ)


testTM : _
testTM = run (satTM assignments) 100 (compile test)

compiled-size : CNF n → ℕ
compiled-size cnf = length (compile cnf)

remaining-size : Tape (Instr n) → ℕ
remaining-size (tape _ _ r) = suc (length r)

postulate
  impossible : {A : Set} → A
