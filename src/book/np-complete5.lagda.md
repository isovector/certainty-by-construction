```agda
-- NP / NP-completeness
module np-complete5 where

open import np-complete1
open import Data.Nat hiding (_⊔_)
open import Data.Product
import np-complete2
open import Relation.Binary.PropositionalEquality
open import Agda.Primitive using (Level; lsuc; _⊔_)
open import propisos

data Poly (sz : ℕ) : ℕ → Set where
  zero : Poly sz 0
  _n^_+_ : {c : ℕ} → (k exp : ℕ) → Poly sz c → Poly sz (k * sz ^ exp + c)

open import Data.Nat.Properties

poly-refl : {sz : ℕ} → Poly sz sz
poly-refl {sz} = subst (Poly sz) (trans (+-comm _ 0) (*-identityʳ sz)) (sz n^ 0 + zero)

postulate
  poly-trans : {a b c : ℕ} → Poly a b → Poly b c → Poly a c

infixr 10 _n^_+_

postulate
  x : ℕ

o³ : Poly x (5 * (x ^ 1) + (3 * (x ^ 2) + 0))
o³ = 5 n^ 1 + 3 n^ 2 + zero

record ProblemClass {ℓ₁ ℓ₂ ℓ₃ : Level} : Set (lsuc (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)) where
  field
    Problem : Set ℓ₁
    Candidate : Problem → Set ℓ₂
    Solution : {p : Problem} → Candidate p → Set ℓ₃


record InNP {ℓ₁ ℓ₂ ℓ₃ : Level} (PC : ProblemClass {ℓ₁} {ℓ₂} {ℓ₃}) : Set (lsuc (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)) where
  open ProblemClass PC

  field
    Γ Q : Set
    runtime : Problem → ℕ
    -- runtime-poly : Poly sz runtime
    tm : TuringMachine Γ Q

  open TuringMachine tm
  open np-complete2 tm

  field
    compile : {ins : Problem} → (soln : Candidate ins) → Q × Tape
    verify : {ins : Problem} (soln : Candidate ins) → (∃[ q ] AcceptsWith (compile soln) q (runtime ins)) ↔ Solution soln



open import propisos

-- record _≤ₚ_ {C C' : ℕ → Set} (C-in-NP : InNP C) (C'-in-NP : InNP C') : Set₁ where
--   open TuringMachine
--   open InNP

--   field
--     size : ℕ → ℕ
--     size-poly : (sz : ℕ) → Poly sz (size sz)
--     reduce : {sz : ℕ} → C sz → C' (size sz)
--     equiv
--       : {sz : ℕ}
--       → (ins : C sz)
--       → (∃[ qc ]  HaltsWith (tm C-in-NP ins)  (compile C-in-NP ins)           qc  (runtime C-in-NP sz))
--       ↔ (∃[ qc' ] HaltsWith (tm C'-in-NP) (compile C'-in-NP (reduce ins)) qc' (runtime C'-in-NP (size sz)))

-- open _≤ₚ_

-- ≤ₚ-refl : {C : ℕ → Set} → {in-np : InNP C} → in-np ≤ₚ in-np
-- size ≤ₚ-refl sz = sz
-- size-poly ≤ₚ-refl sz = subst (Poly sz) (trans (+-comm _ 0) (*-identityʳ sz)) (sz n^ 0 + zero)
-- reduce ≤ₚ-refl ins = ins
-- _↔_.to (equiv ≤ₚ-refl ins)   h = h
-- _↔_.from (equiv ≤ₚ-refl ins) h = h
-- _↔_.left-inv-of (equiv ≤ₚ-refl ins) x = refl
-- _↔_.right-inv-of (equiv ≤ₚ-refl ins) x = refl

-- ≤ₚ-trans
--   : {A B C : ℕ → Set}
--   → {A-in-np : InNP A}
--   → {B-in-np : InNP B}
--   → {C-in-np : InNP C}
--   → A-in-np ≤ₚ B-in-np
--   → B-in-np ≤ₚ C-in-np
--   → A-in-np ≤ₚ C-in-np
-- size (≤ₚ-trans x₁ x₂) sz = size x₂ (size x₁ sz)
-- size-poly (≤ₚ-trans x₁ x₂) sz = poly-trans (size-poly x₁ sz) (size-poly x₂ (size x₁ sz))
-- reduce (≤ₚ-trans x₁ x₂) x₃ = reduce x₂ (reduce x₁ x₃)
-- equiv (≤ₚ-trans x₁ x₂) ins = ↔-trans (equiv x₁ ins) (equiv x₂ (reduce x₁ ins))

-- record InNP-Complete {C : ℕ → Set} (is-NP : InNP C) : Set₁ where
--   field
--     is-complete
--       : {sz : ℕ} {C' : ℕ → Set}
--       → (C'-in-np : InNP C')
--       → C'-in-np ≤ₚ is-NP

```