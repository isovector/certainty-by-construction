module playground.turing where

open import Data.Nat hiding (_⊔_)
open import Data.List hiding (last; head; lookup; or; and)
open import Data.Maybe
open import Data.Sum hiding (map₁; map₂)
import Data.Sum as ⊎
open import Data.Product
import Data.Product as ×
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Function using (const; _∘_)

data MoveDirection : Set where
  L R : MoveDirection

open import Relation.Nullary
open import Relation.Unary


record TuringMachine (Γ : Set) (Q : Set) (F : Set) : Set where
  field
    blank : Γ
    initial-state : Q
    transition : Q → Γ → F ⊎ (Q × Γ × MoveDirection)

record Tape (B : Set) : Set where
  constructor tape
  field
    left-of : List B
    head : B
    right-of : List B
open Tape

finite-sizeʳ : {C : Set} → Tape C → ℕ
finite-sizeʳ = suc ∘ length ∘ right-of

buildTape : {D : Set} → D → List D → Tape D
buildTape blank [] = tape [] blank []
buildTape _ (x ∷ xs) = tape [] x xs

write : {E : Set} → E → Tape E → Tape E
write a (tape l _ r) = tape l a r

open import Agda.Primitive

ExactlyOne : {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} → (P Q : A → Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
ExactlyOne P Q = ∀ x → (P x × ¬ Q x) ⊎ (¬ P x × Q x)


module _ {Γ : Set} {Q : Set} {F : Set} where

  module _ (tm : TuringMachine Γ Q F) where
    open TuringMachine tm

    move : MoveDirection → Tape Γ → Tape Γ
    move L (tape [] h r)
      = tape [] blank (h ∷ r)
    move L (tape (x ∷ l) h r)
      = tape l x (h ∷ r)
    move R (tape l h [])
      = tape (h ∷ l) blank []
    move R (tape l h (x ∷ r))
      = tape (h ∷ l) x r

    moveWrite : MoveDirection → Γ → Tape Γ → Tape Γ
    moveWrite dir sym t = move dir (write sym t)

    step : Q → Tape Γ → F ⊎ (Q × Tape Γ)
    step q t =
      ⊎.map₂
        (×.map₂′ (λ { (sym , dir) → moveWrite dir sym t }))
        (transition q (head t))


    runHelper : ℕ → Q → Tape Γ → F ⊎ (Q × Tape Γ)
    runHelper zero q t = inj₂ (q , t)
    runHelper (suc gas) q t =
      [ inj₁ , uncurry (runHelper gas) ]′
        (step q t)

    run : ℕ → List Γ → Maybe F
    run gas t
      = [ just , const nothing ]′
          (runHelper gas initial-state (buildTape blank t))



module BusyBeaver where
  open TuringMachine

  data State : Set where
    A B C : State

  data Final : Set where
    HALT : Final

  open import Data.Bool

  busy-beaver : TuringMachine Bool State Final
  blank busy-beaver = false
  initial-state busy-beaver = A
  transition busy-beaver A false = inj₂ (B , true , R)
  transition busy-beaver B false = inj₂ (A , true , L)
  transition busy-beaver C false = inj₂ (B , true , L)
  transition busy-beaver A true  = inj₂ (C , true , L)
  transition busy-beaver B true  = inj₂ (B , true , R)
  transition busy-beaver C true  = inj₁ HALT

