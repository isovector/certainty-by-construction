```agda
open import sets

module np-complete0 (Name : Set) (name-fin : IsFinite Name) where

open import Data.Nat
  using (ℕ; _*_; _+_; zero; suc)
open import Data.Fin
  using (Fin; zero; suc)
open import Data.Vec
  using (Vec; lookup; _∷_; []; foldr′)
open import Data.Bool
open import Data.List using (List; _++_)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable
open import Relation.Binary.Definitions using (DecidableEquality)
open import propisos
open import case-bash

open IsFinite

data Lit : Set where
  ↪ : Name → Lit
  ! : Name → Lit

open import Data.Sum
open _↔_

lit-iso : Lit ↔ (Name ⊎ Name)
to lit-iso (↪ x) = inj₁ x
to lit-iso (! x) = inj₂ x
from lit-iso (inj₁ x) = ↪ x
from lit-iso (inj₂ x) = ! x
left-inv-of lit-iso (↪ x) = refl
left-inv-of lit-iso (! x) = refl
right-inv-of lit-iso (inj₁ x) = refl
right-inv-of lit-iso (inj₂ y) = refl

lit-fin : IsFinite Lit
card lit-fin = card name-fin + card name-fin
is-fin lit-fin = ↔-trans lit-iso (is-fin (finite-sum name-fin name-fin))

data Instr : Set where
  pop : Instr
  val : Lit → Instr
  nop : Instr

instr-iso : Instr ↔ (Bool ⊎ Lit)
to instr-iso pop = inj₁ false
to instr-iso (val x) = inj₂ x
to instr-iso nop = inj₁ true
from instr-iso (inj₁ false) = pop
from instr-iso (inj₁ true) = nop
from instr-iso (inj₂ y) = val y
left-inv-of instr-iso = case-bash!
right-inv-of instr-iso (inj₁ false) = refl
right-inv-of instr-iso (inj₁ true) = refl
right-inv-of instr-iso (inj₂ y) = refl

instr-fin : IsFinite Instr
card instr-fin = 2 + card lit-fin
is-fin instr-fin = ↔-trans instr-iso (is-fin (finite-sum bool-fin lit-fin))


Clause : ℕ → Set
Clause = Vec Lit

data CNF : ℕ → Set where
  [] : CNF zero
  _∷_ : {n m : ℕ} → Clause n → CNF m → CNF (suc (m + n))

_↓ˡ_ : Lit → (Name → Bool) → Bool
_↓ˡ_ (↪ x) bs = bs x
_↓ˡ_ (! x) bs = not (bs x)

open import Data.List using (List; _∷_; [])

_↓ᶜ_ : {n : ℕ} → Vec Lit n → (Name → Bool) → Bool
_↓ᶜ_ cl bs = foldr′ (λ l lo → (l ↓ˡ bs) ∨ lo) false cl

_↓_ : {n : ℕ} → CNF n → (Name → Bool) → Bool
[] ↓ bs = true
(cl ∷ cnf) ↓ bs = (cl ↓ᶜ bs) ∧ (cnf ↓ bs)

-- foldr (λ cl hi → (cl ↓ᶜ bs) ∧ hi) true cnf


data Expr : Set where
  lit : Lit → Expr
  _∨ᵇ_ : Expr → Expr → Expr
  _∧ᵇ_ : Expr → Expr → Expr

¬ᵇ : Expr → Expr
¬ᵇ (lit (↪ x)) = lit (! x)
¬ᵇ (lit (! x)) = lit (↪ x)
¬ᵇ (x ∨ᵇ y) = ¬ᵇ x ∧ᵇ ¬ᵇ y
¬ᵇ (x ∧ᵇ y) = ¬ᵇ x ∨ᵇ ¬ᵇ y

_⇒ᵇ_ : Expr → Expr → Expr
x ⇒ᵇ y = ¬ᵇ x ∨ᵇ y

_↓ᵇ_ : Expr → (Name → Bool) → Bool
lit x ↓ᵇ bs = x ↓ˡ bs
(x ∨ᵇ y) ↓ᵇ bs = (x ↓ᵇ bs) ∨ (y ↓ᵇ bs)
(x ∧ᵇ y) ↓ᵇ bs = (x ↓ᵇ bs) ∧ (y ↓ᵇ bs)



-- module Example where
--   x₁ x₂ x₃ : Fin 3
--   x₁ = zero
--   x₂ = suc zero
--   x₃ = suc (suc zero)

--   test : CNF (Fin 3)
--   test = (↪ x₁ ∷ ! x₂ ∷ [])
--       ∷ (! x₁ ∷ ↪ x₂ ∷ ↪ x₃ ∷ [])
--       ∷ (! x₁ ∷ [])
--       ∷ []

--   open import Relation.Binary.PropositionalEquality

--   _ : test ↓ (lookup (false ∷ false ∷ true ∷ [])) ≡ true
--   _ = refl
```
