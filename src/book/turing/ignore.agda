open import np-complete1 renaming (TuringMachine to TM)

module turing.ignore {Γ₁ Q : Set} (tm : TM Γ₁ Q) (Γ₂ : Set) where

open TM tm

record Q' : Set where
  constructor mkQ'
  field
    q : Q
    last-dir : MoveDirection

open import Function using (_∘_)
open import Data.Sum as ⊎
open import Data.Product as ×
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality

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

unwrap : ∀ {X q} → Wrap X (mkQ' q d , inj₁ i₁) → X (q , i₁)
unwrap (wrap x) = x


postulate
  exercise-to-reader : {A : Set} → A

hoist : Q × Γ₁ × MoveDirection → Q' × (Γ₁ ⊎ Γ₂) × MoveDirection
hoist (q , i , md) = mkQ' q md , inj₁ i , md

ignore : TM (Γ₁ ⊎ Γ₂) Q'
TM.δ ignore = δ'
TM.δ-dec ignore = exercise-to-reader
TM.δ-finite ignore = exercise-to-reader
TM.δ-deterministic ignore (mkQ' q d , inj₁ i) (lift x) (lift x₁) =
  cong hoist (δ-deterministic (q , i) x x₁)
TM.δ-deterministic ignore (mkQ' q _ , inj₂ _) skip skip = refl
TM.Accept ignore = Wrap Accept
TM.Reject ignore = Wrap Reject
TM.H-dec ignore (mkQ' q last-dir , inj₁ x) =
  map′ (⊎.map wrap wrap) (⊎.map unwrap unwrap) (H-dec (q , x))
TM.H-dec ignore (mkQ' q last-dir , inj₂ y) =
  no λ { (inj₁ ()) ; (inj₂ ()) }
TM.step-or-halt ignore (mkQ' q d , inj₁ i) =
  ⊎.map
    (×.map hoist lift)
    (⊎.map wrap wrap)
    (step-or-halt (q , i))
TM.step-or-halt ignore (mkQ' q d , inj₂ y)
  = inj₁ ((mkQ' q d , inj₂ y , d) , skip)
TM.not-both ignore (wrap x) (wrap x₁) = not-both x x₁
TM.b ignore = inj₁ b
TM.Q-ne-finite ignore = exercise-to-reader
TM.Γ-ne-finite ignore = exercise-to-reader

