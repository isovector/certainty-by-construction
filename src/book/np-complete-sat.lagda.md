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

SAT : ProblemClass
ProblemClass.Problem SAT = SAT-Problem
ProblemClass.Candidate SAT p = SAT-Problem.Name p → Bool
ProblemClass.Solution SAT p bs = cnf ↓ bs ≡ true
  where open SAT-Problem p

import np-complete2

SAT-in-NP : InNP SAT
InNP.Γ SAT-in-NP x = SAT-Problem.Instr x
InNP.Q SAT-in-NP _ = Bool × Bool
InNP.runtime SAT-in-NP n = n
InNP.runtime-poly SAT-in-NP n = poly-refl
InNP.tm SAT-in-NP ins soln = sat
  where open import np-complete3 (SAT-Problem.Name-finite ins) soln
InNP.compile SAT-in-NP ins soln = (true , false) , mkTape ℤ.0ℤ ⌊ SAT-Problem.cnf ins ⌋
  where open import np-complete3 (SAT-Problem.Name-finite ins) soln
_↔_.to (InNP.verify SAT-in-NP ins soln) (q' , np-complete2.halts-with final-tape arr is-halted) = {! !}
_↔_.from (InNP.verify SAT-in-NP ins soln) = {! !}
_↔_.left-inv-of (InNP.verify SAT-in-NP ins soln) = {! !}
_↔_.right-inv-of (InNP.verify SAT-in-NP ins soln) = {! !}
  where open import np-complete3 (SAT-Problem.Name-finite ins) soln


```
