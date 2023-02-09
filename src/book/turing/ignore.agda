open import np-complete1

module turing.ignore {Γ₁ Q : Set} (tm : TuringMachine Γ₁ Q) (Γ₂ : Set) where

open TuringMachine tm

record Q' : Set where
  constructor mkQ'
  field
    q : Q
    last-dir : MoveDirection

open import Data.Sum
open import Data.Product
open import Relation.Nullary

private variable
  i : Γ₁ ⊎ Γ₂
  i₁ i₁' : Γ₁
  i₂ i₂' : Γ₂

  q q₁ q₂ : Q
  q' q₁' q₂' : Q'

  d d₁ d₂ : MoveDirection

data δ' : Q' × (Γ₁ ⊎ Γ₂)
        → Q' × (Γ₁ ⊎ Γ₂) × MoveDirection
        → Set where
  lift : δ (q₁ , i₁)
           (q₂ , i₁' , d)
       → δ' (mkQ' q₁ d₁ , inj₁ i₁)
            (mkQ' q₂ d  , inj₁ i₁' , d)
  skip : δ' (mkQ' q d , inj₂ i₂)
            (mkQ' q d , inj₂ i₂ , d)

data Wrap (X : Q × Γ₁ → Set) : (Q' × (Γ₁ ⊎ Γ₂)) → Set where
  wrap : X (q , i₁) → Wrap X (mkQ' q d , inj₁ i₁)


postulate
  exercise-to-reader : {A : Set} → A

ignore : TuringMachine (Γ₁ ⊎ Γ₂) Q'
TuringMachine.δ ignore = δ'
TuringMachine.δ-dec ignore = exercise-to-reader
TuringMachine.δ-finite ignore = exercise-to-reader
TuringMachine.δ-deterministic ignore = exercise-to-reader
TuringMachine.Accept ignore = Wrap Accept
TuringMachine.Reject ignore = Wrap Reject
TuringMachine.H-dec ignore (mkQ' q last-dir , inj₁ x) with H-dec (q , x)
... | yes (inj₁ x₁) = yes (inj₁ (wrap x₁))
... | yes (inj₂ y) = yes (inj₂ (wrap y))
... | no z = no λ { (inj₁ (wrap x)) → z (inj₁ x)
                  ; (inj₂ (wrap y)) → z (inj₂ y) }
TuringMachine.H-dec ignore (mkQ' q last-dir , inj₂ y) = no λ { (inj₁ ()) ; (inj₂ ()) }
TuringMachine.step-or-halt ignore (mkQ' q d , inj₁ i) with step-or-halt (q , i)
... | inj₁ ((q , i , md) , tr) = inj₁ ((mkQ' q md , inj₁ i , md) , lift tr)
... | inj₂ (inj₁ x) = inj₂ (inj₁ (wrap x))
... | inj₂ (inj₂ y) = inj₂ (inj₂ (wrap y))
TuringMachine.step-or-halt ignore (mkQ' q d , inj₂ y)
  = inj₁ ((mkQ' q d , inj₂ y , d) , skip)
TuringMachine.not-both ignore (wrap x) (wrap x₁) = not-both x x₁
TuringMachine.b ignore = inj₁ b
TuringMachine.Q-ne-finite ignore = exercise-to-reader
TuringMachine.Γ-ne-finite ignore = exercise-to-reader

