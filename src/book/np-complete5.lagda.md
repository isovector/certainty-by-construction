```agda
-- NP / NP-completeness
module np-complete5 where

open import np-complete1
open import Data.Nat
open import Data.Product
open import np-complete2 using (HaltsWith)

data Poly (sz : ℕ) : ℕ → Set where
  zero : Poly sz 0
  _n^_+_ : {c : ℕ} → (k exp : ℕ) → Poly sz c → Poly sz (k * sz ^ exp + c)

infixr 10 _n^_+_

postulate
  x : ℕ

o³ : Poly x (5 * (x ^ 1) + (3 * (x ^ 2) + 0))
o³ = 5 n^ 1 + 3 n^ 2 + zero

record InNP (C : ℕ → Set) : Set₁ where
  field
    Γ Q : Set
    tm : TuringMachine Γ Q

  open Tapes (TuringMachine.b tm) (TuringMachine._≟Γ_ tm)

  field
    compile : {sz : ℕ} → C sz → Q × Tape
    verify : {sz : ℕ} → (ins : C sz) → ∃[ q ] ∃[ n ] (Poly sz n × HaltsWith tm (compile ins) q n)

open import propisos

record PolyReduction (C C' : ℕ → Set) : Set₁ where
  open TuringMachine
  open InNP

  field
    C-in-NP : InNP C
    C'-in-NP : InNP C'
    reduce : {sz n : ℕ} → Poly sz n → C sz → C' n
    equiv
      : {sz n : ℕ}
      → (p : Poly sz n)
      → (ins : C sz)
      → (∃[ qc ]  ∃[ sz' ] Σ (Poly sz sz') λ _ → HaltsWith (tm C-in-NP)  (compile C-in-NP ins) qc sz')
      ↔ (∃[ qc' ] ∃[ n' ]  Σ (Poly n n') λ p₂  → HaltsWith (tm C'-in-NP) (compile C'-in-NP (reduce p ins)) qc' n')

record InNP-Complete (C : ℕ → Set) : Set₁ where
  field
    in-NP : InNP C
    is-complete
      : {sz : ℕ} {C' : ℕ → Set}
      → PolyReduction C' C

```
