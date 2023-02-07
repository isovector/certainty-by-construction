## NP-Completeness

```agda
open import Relation.Unary
open import Relation.Binary.PropositionalEquality

module np-complete1 where

open import Relation.Nullary
open import Data.List
  using (List; _∷_; []; drop)

data MoveDirection : Set where
  L R : MoveDirection

open import 8-iso using (Equivalent)
open import Data.Product using (_×_; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Agda.Primitive using (Level; lzero; lsuc)
open import sets using (IsFinite; IsNonemptyFinite)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Data.Empty
open import propisos

record TuringMachine (Γ Q : Set) : Set₁ where
  field
    δ : Q × Γ → Q × Γ × MoveDirection → Set
    δ-dec : (qi : Q × Γ) → (qid : Q × Γ × MoveDirection) → Dec (δ qi qid)
    δ-finite : IsFinite (∃[ qi ] ∃[ qid ] δ qi qid)
    δ-deterministic
      : (qt : Q × Γ)
      → {o₁ o₂ : Q × Γ × MoveDirection}
      → δ qt o₁ → δ qt o₂
      → o₁ ≡ o₂
    Accept : Q × Γ → Set
    Reject : Q × Γ → Set

  H : Q × Γ → Set
  H qi = Accept qi ⊎ Reject qi

  field
    H-dec : Decidable H
    step-or-halt : (qi : Q × Γ) → ∃ (δ qi) ⊎ H qi
    not-both : {qi : Q × Γ} → Accept qi → Reject qi → ⊥
    -- step-or-halt₁
    --   : (qi : Q × Γ) {qid : Q × Γ × MoveDirection}
    --   → δ qi qid
    --   → ¬ H qi
    -- step-or-halt₂
    --   : (qi : Q × Γ)
    --   → H qi
    --   → ¬ ∃ (δ qi)
    b : Γ
    Q-ne-finite : IsNonemptyFinite Q
    Γ-ne-finite : IsNonemptyFinite Γ

  Q-finite : IsFinite Q
  Q-finite = IsNonemptyFinite.finite Q-ne-finite

  Γ-finite : IsFinite Γ
  Γ-finite = IsNonemptyFinite.finite Γ-ne-finite

  _≟Γ_ : DecidableEquality Γ
  _≟Γ_ = IsFinite.dec-finite Γ-finite

  _≟Q_ : DecidableEquality Q
  _≟Q_ = IsFinite.dec-finite Q-finite


module _ {Γ Q : Set} (tm : TuringMachine Γ Q) where
  open TuringMachine tm
  Accept-dec : Decidable Accept
  Accept-dec qi with H-dec qi
  ... | yes (_⊎_.inj₁ x) = yes x
  ... | yes (_⊎_.inj₂ y) = no λ x → ⊥-elim (not-both x y)
  ... | no z = no λ x → z (_⊎_.inj₁ x)

  Reject-dec : Decidable Reject
  Reject-dec qi with H-dec qi
  ... | yes (_⊎_.inj₂ x) = yes x
  ... | yes (_⊎_.inj₁ y) = no λ x → ⊥-elim (not-both y x)
  ... | no z = no λ x → z (_⊎_.inj₂ x)

--   step-or-halt : (qi : Q × Γ) → ∃ (δ qi) ⊎ H qi
--   step-or-halt qi with H-dec qi
--   ... | yes x = inj₂ x
--   ... | no x = todo
--     where postulate
--       todo : {A : Set} → A


module Tapes {Γ : Set} (b : Γ) (_≟Γ_ : DecidableEquality Γ) where

  open import Data.Integer using (ℤ; _+_; suc; pred)

  record Tape : Set where
    constructor tape
    field
      index : ℤ
      left-of : List Γ
      head : Γ
      right-of : List Γ

  push : Γ → List Γ → List Γ
  push x [] with x ≟Γ b
  ... | yes _ = []
  ... | no  _ = x ∷ []
  push x (y ∷ l) = x ∷ y ∷ l

  move : MoveDirection → Tape → Tape
  move L (tape n [] h r)      = tape (pred n) [] b (push h r)
  move L (tape n (x ∷ l) h r) = tape (pred n) l x (push h r)
  move R (tape n l h [])      = tape (suc n) (push h l) b []
  move R (tape n l h (x ∷ r)) = tape (suc n) (push h l) x r

  write : Γ → Tape → Tape
  write a (tape n l _ r) = tape n l a r

  open import Data.Integer
  open import Data.Integer.Properties
  open import Relation.Binary
  open import Data.Maybe using (fromMaybe)

  read : ℤ → Tape → Γ
  read m (tape n ls i rs) with <-cmp n m
  ... | tri< n<m _ _ = fromMaybe b (Data.List.head (drop ∣ m - n ∣ rs))
  ... | tri≈ _ n=m _ = i
  ... | tri> _ _ n>m = fromMaybe b (Data.List.head (drop ∣ m - n ∣ ls))
```
