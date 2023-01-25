```agda
-- compile to SAT
module np-complete4 where

open import np-complete1
open import Data.Product
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Unary using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import sets
open import 8-iso using (Equivalent)
open import Agda.Primitive using (Level; lzero; lsuc)
open import Data.Nat

module TmToSat {Γ Q : Set} (tm : TuringMachine Γ Q) where
  open TuringMachine tm
  open import np-complete2 tm
  open import Data.Fin

  module _ {qt : Q × Tape} {q : Q} {n : ℕ} (hw : HaltsWith qt q n) where

    arr : qt -⟨ n ⟩→ (q , HaltsWith.final-tape hw)
    arr = HaltsWith.arr hw

    TapeCell : Set
    TapeCell = Fin (2 * n)

    TimeCell : Set
    TimeCell = Fin n

    get-time : TimeCell → ℕ
    get-time = toℕ

    open import Data.Integer using (ℤ; +_; -[1+_])
    open import Data.Sum

    get-pos : TapeCell → ℤ
    get-pos tc with splitAt n tc
    ... | inj₁ x = + (toℕ x)
    ... | inj₂ y = -[1+ toℕ y ]

    data SLit : Set where
      tape-contents : (tc : TapeCell) → (i : Γ) → (m : TimeCell) → SLit
      tape-position : (tc : TapeCell) → (m : TimeCell) → SLit
      state-at-time : (m : TimeCell) → (q : Q) → SLit

    open import Relation.Binary.Definitions using (DecidableEquality)

    postulate
      _≟SL_ : DecidableEquality SLit
    -- tape-contents tc i m ≟SL tape-contents tc₁ i₁ m₁ = {! !}
    -- tape-contents _ _ _ ≟SL tape-position _ _ = no λ ()
    -- tape-contents _ _ _ ≟SL state-at-time _ _ = no λ ()
    -- tape-position _ _ ≟SL tape-contents _ _ _ = no λ ()
    -- tape-position tc m ≟SL tape-position tc₁ m₁ = {! !}
    -- tape-position _ _ ≟SL state-at-time _ _ = no λ ()
    -- state-at-time _ _ ≟SL tape-contents _ _ _ = no λ ()
    -- state-at-time _ _ ≟SL tape-position _ _ = no λ ()
    -- state-at-time m q ≟SL state-at-time m₁ q₁ = {! !}

    open import Data.Bool
    open Properties

    ↓ : SLit → Bool
    ↓ (tape-contents tc i m) = cell-at-t-is qt (get-time m) (get-pos tc) i
    ↓ (tape-position tc m) = pos-at-t-is qt (get-time m) (get-pos tc)
    ↓ (state-at-time m q) = q-at-t-is qt (get-time m) q

    open import Relation.Binary using (Setoid)
    open import Relation.Binary.PropositionalEquality

    instance
      slit-equiv : Equivalent lzero SLit
      Equivalent._≋_ slit-equiv = _≡_
      Equivalent.equiv slit-equiv = Setoid.isEquivalence (setoid SLit)


    postulate
      slit-finite : IsFinite SLit

    open import np-complete3 SLit (dec-finite _ slit-finite) ↓


```
