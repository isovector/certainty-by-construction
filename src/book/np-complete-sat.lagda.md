```agda

module np-complete-sat where

open import Data.Nat
open import Data.Bool
open import sets
import np-complete0
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Product
import Data.Integer as ℤ
open import propisos

record SAT-Problem (n : ℕ) : Set₁ where
  field
    Name : Set
    Name-finite : IsFinite Name

  open np-complete0 Name Name-finite public

  field
    cnf : CNF n

open import np-complete5

SAT : ℕ → ProblemClass
ProblemClass.Problem (SAT sz) = SAT-Problem sz
ProblemClass.Candidate (SAT _) p = SAT-Problem.Name p → Bool
ProblemClass.Solution (SAT sz) {p = p} bs = cnf ↓ bs ≡ true
  where open SAT-Problem p

open import np-complete2
import np-complete3

SAT-in-NP : (sz : ℕ) → InNP (SAT sz)
InNP.Γ (SAT-in-NP sz) = ?
InNP.Q (SAT-in-NP sz) = Bool × Bool
InNP.runtime (SAT-in-NP sz) = {! !}
InNP.tm (SAT-in-NP sz) = {! !}
InNP.compile (SAT-in-NP sz) = {! !}
InNP.verify (SAT-in-NP sz) = {! !}

-- InNP.Γ (SAT-in-NP _) = SAT-Problem.Instr
-- InNP.Q (SAT-in-NP _) _ = Bool × Bool
-- InNP.runtime (SAT-in-NP sz) = sz
-- InNP.runtime-poly (SAT-in-NP sz) = poly-refl
-- InNP.tm (SAT-in-NP sz) {ins} soln = sat
--   where open np-complete3 (SAT-Problem.Name-finite ins) soln
-- InNP.compile (SAT-in-NP sz) {ins} soln = (true , false) , mkTape ℤ.0ℤ ⌊ SAT-Problem.cnf ins ⌋
--   where open np-complete3 (SAT-Problem.Name-finite ins) soln
-- _↔_.to
--   (InNP.verify (SAT-in-NP sz) {ins} soln)
--     ((.true , hi) , halts-with (tape index left-of .np-complete0.nop right-of) arr np-complete3.accept)
--       = {! !}
-- _↔_.from (InNP.verify (SAT-in-NP sz) {ins} soln) x
--   rewrite x
--   with np-complete3.DONE _ soln (SAT-Problem.cnf ins)
-- ... | halts-with final-tape arr is-halted = (true , false) , halts-with final-tape {! arr !} {! accept !}
-- _↔_.left-inv-of (InNP.verify (SAT-in-NP sz) {ins} soln) (fst , snd) = {! !}
-- _↔_.right-inv-of (InNP.verify (SAT-in-NP sz) {ins} soln) x₁ = {! !}

-- InNP.Γ SAT-in-NP x = SAT-Problem.Instr x
-- InNP.Q SAT-in-NP _ = Bool × Bool
-- InNP.runtime SAT-in-NP n = n
-- InNP.runtime-poly SAT-in-NP n = poly-refl
-- InNP.tm SAT-in-NP ins soln = sat
--   where open import np-complete3 (SAT-Problem.Name-finite ins) soln
-- InNP.compile SAT-in-NP ins soln = (true , false) , mkTape ℤ.0ℤ ⌊ SAT-Problem.cnf ins ⌋
--   where open import np-complete3 (SAT-Problem.Name-finite ins) soln
-- _↔_.to (InNP.verify SAT-in-NP ins soln) (q' , np-complete2.halts-with final-tape arr is-halted) = {! !}
-- _↔_.from (InNP.verify SAT-in-NP ins soln) = {! !}
-- _↔_.left-inv-of (InNP.verify SAT-in-NP ins soln) = {! !}
-- _↔_.right-inv-of (InNP.verify SAT-in-NP ins soln) = {! !}
--   where open import np-complete3 (SAT-Problem.Name-finite ins) soln


```
