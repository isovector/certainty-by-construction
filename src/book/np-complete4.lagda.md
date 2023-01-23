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

record TuringMachine (Γ Q : Set) : Set₁ where
  field
    δ : Q × Γ → Q × Γ × MoveDirection → Set
    H : Q × Γ → Set
    halted : {qi : Q × Γ} → H qi → (qir : Q × Γ × MoveDirection) → ¬ δ qi qir
    b : Γ
    b-dec : Decidable (_≡ b)
    {{q-equiv}} : Equivalent lzero Q
    q-finite : IsFinite Q

module TmToSat {Γ Q : Set} (tm : TuringMachine Γ Q) where
  open TuringMachine tm
  open import np-complete2 Γ Q δ H halted b b-dec

  module _ {qt : Q × Tape} {q : Q} {n : ℕ} (hw : HaltsWith qt q n) where

    arr : qt -⟨ n ⟩→ (q , HaltsWith.final-tape hw)
    arr = HaltsWith.arr hw

    TapeCell : Set
    TapeCell = ℕ

    TimeCell : Set
    TimeCell = ℕ

    data SLit : Set where
      tape-contents : TapeCell → Γ → TimeCell → SLit
      tape-position : TapeCell → TimeCell → SLit
      state-at-time : TimeCell → Q → SLit

    open import np-complete3 SLit


```
