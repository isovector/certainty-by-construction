module playground.decidability where

open import Data.Nat
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Data.Sum
open import Data.Empty
open import Relation.Nullary

yo : (ℕ → Bool) → ℕ
yo f with f 1000000
... | false = 0
... | true = 1

prove : (f g : (ℕ → Bool) → ℕ) → f ≡ g ⊎ ¬ (f ≡ g)
prove f g = {! !}
