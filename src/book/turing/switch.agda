open import np-complete1 renaming (TuringMachine to TM)
open import Data.Bool
open import Data.Product as ×
open import Relation.Binary.PropositionalEquality hiding ([_])

open TM

module
  turing.switch
    {Γ Q₁ Q₂ : Set}
    (tm₁ : TM Γ Q₁)
    (tm₂ : TM Γ (Bool × Q₁ × Q₂))
    (same-b : b tm₁ ≡ b tm₂) where

open import Function using (_∘_; id)
open import Data.Sum as ⊎
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Data.Maybe

Q2 : Set
Q2 = Bool × Q₁ × Q₂

Q' : Set
Q' = Q₁ ⊎ Q2

Tr : Set
Tr = Q' × Γ

Trd : Set
Trd = Q' × Γ × MoveDirection


private variable
  i i' i₁ i₁' : Γ
  i₂ i₂' : Γ

  q : Q₁ × Q2
  q₁ q₁' : Q₁
  q₂ q₂' : Q2

  d : MoveDirection

q₀2 : Q₂
q₀2 = proj₂ (proj₂ (q₀ tm₂))

data δ' : Tr → Trd → Set where
  lift₁ : δ tm₁ (q₁ , i) (q₁' , i' , d) → δ' (inj₁ q₁ , i) (inj₁ q₁' , i' , d)
  switch+ : (Accept tm₁ (q₁' , i')) → δ' (inj₁ q₁ , i) (inj₂ (true , q₁' , q₀2) , i' , R)
  switch- : (Reject tm₁ (q₁' , i')) → δ' (inj₁ q₁ , i) (inj₂ (false , q₁' , q₀2) , i' , R)
  lift₂ : δ tm₂ (q₂ , i) (q₂' , i' , d) → δ' (inj₂ q₂ , i) (inj₂ q₂' , i' , d)



postulate
  exercise-to-reader : {A : Set} → A

hoist₁ : Q₁ × Γ × MoveDirection → Q' × Γ × MoveDirection
hoist₁ (q , i , md) = inj₁ q , i , md

hoist₂ : Q2 × Γ × MoveDirection → Q' × Γ × MoveDirection
hoist₂ (q , i , md) = inj₂ q , i , md


data Wrap (X : Q2 × Γ → Set) : (Q' × Γ) → Set where
  wrap : X (q₂ , i) → Wrap X (inj₂ q₂ , i)

unwrap : ∀ {X} → Wrap X (inj₂ q₂ , i) → X (q₂ , i)
unwrap (wrap x) = x

switch : TM Γ Q'
q₀ switch = inj₁ (q₀ tm₁)
δ switch = δ'
δ-dec switch = exercise-to-reader
δ-finite switch = exercise-to-reader
δ-deterministic switch = exercise-to-reader
Accept switch = Wrap (Accept tm₂)
Reject switch = Wrap (Reject tm₂)
H-dec switch (inj₁ x , i) = no λ { (inj₁ ()) ; (inj₂ ()) }
H-dec switch (inj₂ y , i) =
  map′
    (⊎.map wrap wrap)
    (⊎.map unwrap unwrap)
    (H-dec tm₂ (y , i))
step-or-halt switch (inj₁ x , i) =
  [ inj₁ ∘ ×.map hoist₁ lift₁
  , inj₁ ∘ [ (λ x₁ → _ , switch+ x₁ )
           , (λ x₁ → _ , switch- x₁ )
           ]
  ]′ (step-or-halt tm₁ (x , i))
step-or-halt switch (inj₂ y , i) =
  ⊎.map
    (×.map hoist₂ lift₂)
    (⊎.map wrap wrap)
    (step-or-halt tm₂ (y , i))
not-both switch (wrap x) (wrap x₁) = not-both tm₂ x x₁
b switch = b tm₁
Q-ne-finite switch = exercise-to-reader
Γ-ne-finite switch = exercise-to-reader

-- ignore : TM (Γ₁ ⊎ Γ₂) Q'
-- TM.δ ignore = δ'
-- TM.δ-dec ignore = exercise-to-reader
-- TM.δ-finite ignore = exercise-to-reader
-- TM.δ-deterministic ignore (mkQ' q d , inj₁ i) (lift x) (lift x₁) =
--   cong hoist (δ-deterministic (q , i) x x₁)
-- TM.δ-deterministic ignore (mkQ' q _ , inj₂ _) skip skip = refl
-- TM.Accept ignore = Wrap Accept
-- TM.Reject ignore = Wrap Reject
-- TM.H-dec ignore (mkQ' q last-dir , inj₁ x) =
--   map′ (⊎.map wrap wrap) (⊎.map unwrap unwrap) (H-dec (q , x))
-- TM.H-dec ignore (mkQ' q last-dir , inj₂ y) =
--   no λ { (inj₁ ()) ; (inj₂ ()) }
-- TM.step-or-halt ignore (mkQ' q d , inj₁ i) =
--   ⊎.map
--     (×.map hoist lift)
--     (⊎.map wrap wrap)
--     (step-or-halt (q , i))
-- TM.step-or-halt ignore (mkQ' q d , inj₂ y)
--   = inj₁ ((mkQ' q d , inj₂ y , d) , skip)
-- TM.not-both ignore (wrap x) (wrap x₁) = not-both x x₁
-- TM.b ignore = inj₁ b
-- TM.Q-ne-finite ignore = exercise-to-reader
-- TM.Γ-ne-finite ignore = exercise-to-reader


