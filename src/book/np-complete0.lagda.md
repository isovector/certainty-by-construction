```agda
open import Relation.Binary.Definitions using (DecidableEquality)

module np-complete0 (Name : Set) (_≟N_ : DecidableEquality Name) where

open import Data.Nat
  using (ℕ)
open import Data.Fin
  using (Fin; zero; suc)
open import Data.Vec
  using (Vec; lookup; _∷_; [])
open import Data.Bool
open import Data.List using (List)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable


data Lit : Set where
  ↪ : Name → Lit
  ! : Name → Lit


↪-injective : ∀ {x y} → ↪ x ≡ ↪ y → x ≡ y
↪-injective refl = refl

!-injective : ∀ {x y} → ! x ≡ ! y → x ≡ y
!-injective refl = refl

_≟L_ : DecidableEquality Lit
↪ x ≟L ↪ y = map′ (cong ↪) ↪-injective (x ≟N y)
↪ x ≟L ! y = no λ ()
! x ≟L ↪ y = no λ ()
! x ≟L ! y = map′ (cong !) !-injective (x ≟N y)

data Instr : Set where
  pop : Instr
  val : Lit → Instr
  nop : Instr

val-injective : ∀ {x y} → val x ≡ val y → x ≡ y
val-injective refl = refl

_≟I_ : DecidableEquality Instr
pop ≟I pop = yes refl
pop ≟I val x = no λ ()
pop ≟I nop = no λ ()
val x ≟I pop = no λ ()
val x ≟I val y = map′ (cong val) val-injective (x ≟L y)
val x ≟I nop = no λ ()
nop ≟I pop = no λ ()
nop ≟I val x = no λ ()
nop ≟I nop = yes refl


Clause : Set
Clause = List Lit

CNF : Set
CNF = List Clause

_↓ˡ_ : Lit → (Name → Bool) → Bool
_↓ˡ_ (↪ x) bs = bs x
_↓ˡ_ (! x) bs = not (bs x)

open import Data.List using (List; _∷_; []; foldr)

_↓ᶜ_ : List Lit → (Name → Bool) → Bool
_↓ᶜ_ cl bs = foldr (λ l lo → (l ↓ˡ bs) ∨ lo) false cl

_↓_ : List (List Lit) → (Name → Bool) → Bool
_↓_ cnf bs = foldr (λ cl hi → (cl ↓ᶜ bs) ∧ hi) true cnf


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
