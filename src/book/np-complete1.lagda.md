## NP-Completeness

```agda
open import Relation.Unary
open import Relation.Binary.PropositionalEquality

module np-complete1 where

open import Relation.Nullary
open import Data.List
  using (List; _∷_; [])

data MoveDirection : Set where
  L R : MoveDirection

module Tapes (Γ : Set) (b : Γ) (is-blank : Decidable (_≡ b)) where

  record Tape : Set where
    constructor tape
    field
      left-of : List Γ
      head : Γ
      right-of : List Γ

  push : Γ → List Γ → List Γ
  push x [] with is-blank x
  ... | yes _ = []
  ... | no  _ = x ∷ []
  push x (y ∷ l) = x ∷ y ∷ l

  move : MoveDirection → Tape → Tape
  move L (tape [] h r) = tape [] b (push h r)
  move L (tape (x ∷ l) h r) = tape l x (push h r)
  move R (tape l h []) = tape (push h l) b []
  move R (tape l h (x ∷ r)) = tape (push h l) x r

  write : Γ → Tape → Tape
  write a (tape l _ r) = tape l a r
```
