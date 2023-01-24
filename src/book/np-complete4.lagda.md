```agda
-- compile to SAT
module np-complete4 where

open import np-complete1
open import Data.Product
open import Relation.Nullary using (¬_)
open import Relation.Unary using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import sets
open import 8-iso using (Equivalent)
open import Agda.Primitive using (Level; lzero; lsuc)
open import Data.Nat

module TmToSat {Γ Q : Set} (tm : TuringMachine Γ Q) where
  open TuringMachine tm
  open import np-complete2 Γ Q δ H halted b b-dec
  open import Data.Fin

  module _ {qt : Q × Tape} {q : Q} {n : ℕ} (hw : HaltsWith qt q n) where

    arr : qt -⟨ n ⟩→ (q , HaltsWith.final-tape hw)
    arr = HaltsWith.arr hw

    TapeCell : Set
    TapeCell = Fin (2 * n)

    TimeCell : Set
    TimeCell = Fin n

    data SLit : Set where
      tape-contents : TapeCell → Γ → TimeCell → SLit
      tape-position : TapeCell → TimeCell → SLit
      state-at-time : TimeCell → Q → SLit

    open import Relation.Binary using (Setoid)
    open import Relation.Binary.PropositionalEquality

    instance
      slit-equiv : Equivalent lzero SLit
      Equivalent._≋_ slit-equiv = _≡_
      Equivalent.equiv slit-equiv = Setoid.isEquivalence (setoid SLit)


    postulate
      slit-finite : IsFinite SLit

    open import np-complete3 SLit


```
