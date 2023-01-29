```agda
-- NP / NP-completeness
module np-complete5 where

open import np-complete1
open import Data.Nat
open import Data.Product
open import np-complete2 using (HaltsWith)

data Poly (sz : ℕ) : ℕ → Set where

record InNP (C : ℕ → Set) : Set₁ where
  field
    Γ Q : Set
    tm : TuringMachine Γ Q

  open Tapes (TuringMachine.b tm) (TuringMachine._≟Γ_ tm)

  field
    compile : {sz : ℕ} → C sz → Q × Tape
    verify : {sz : ℕ} → (ins : C sz) → ∃[ q ] ∃[ n ] (Poly sz n × HaltsWith tm (compile ins) q n)

record InNP-Complete (C : ℕ → Set) : Set₁ where
  field
    in-NP : InNP C
    reduce : {sz : ℕ} → (C' : ℕ → Set) → InNP C' → ∃[ n ] (Poly sz n × (C' sz → C n))



```
