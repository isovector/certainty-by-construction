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

  -- module _ (arr :

  open import np-complete3


```
