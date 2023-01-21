open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; lookup)
open import Data.Bool
  using (Bool; true; false; not)
  renaming (_∧_ to and; _∨_ to or)


module playground.SAT2 {n : ℕ} (bs : Vec Bool n) where

open import Data.Fin using (Fin)

data Lit : Set where
  ↪ : Fin n → Lit
  ! : Fin n → Lit

data Instr : Set where
  pop : Instr
  val : Lit → Instr
  halt : Instr

open import Data.Product

State : Set
State = Bool × Bool

evaluateLit : Lit → Bool
evaluateLit (↪ x) = lookup bs x
evaluateLit (! x) = not (lookup bs x)

open import playground.turing using (MoveDirection; L; R)

data δ : State × Instr → State × Instr × MoveDirection → Set where
  ⟶pop : {lo hi : Bool} → δ ((lo , hi) , pop) ((and lo hi , false) , pop , R)
  ⟶val : {x : Lit} → {lo hi : Bool} → δ ((lo , hi), val x) ((lo , or hi (evaluateLit x)) , val x , R)

data Halted : State × Instr → Set where
  halted : {q : State} → Halted (q , halt)

open import Relation.Nullary using (¬_)

is-halted : ∀ {qi} → Halted qi → ∀ qir → ¬ δ qi qir
is-halted halted _ ()


open import playground.turing2 Instr State δ Halted is-halted halt public



