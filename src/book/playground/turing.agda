module playground.turing where

open import Data.Nat
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


record TuringMachine {Q : Set} (Γ : Set) (F : Q → Set) : Set where
  field
    F-dec : Decidable F
    blank : Γ
    initial-state : Q
    transition : Q → Γ → Q × Γ × MoveDirection

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

module _ {Γ : Set} {Q : Set} {F : Q → Set} where

  module _ (tm : TuringMachine Γ F) where
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

    step : Q → Tape Γ → Q × Tape Γ
    step q t =
      (×.map₂′ λ { (sym , dir) → moveWrite dir sym t })
          (transition q (head t))


    runHelper : ℕ → Q → Tape Γ → Σ Q F ⊎ (Q × Tape Γ)
    runHelper zero q t = inj₂ (q , t)
    runHelper (suc gas) q t with step q t
    runHelper (suc gas) q t | q' , t' with F-dec q'
    ... | yes f = inj₁ (q' , f)
    ... | no _ = runHelper gas q' t'

    run : ℕ → List Γ → Maybe (Σ Q F)
    run gas t
      = [ just , const nothing ]′
          (runHelper gas initial-state (buildTape blank t))

  module Stepping (tm : TuringMachine Γ F) where
    open TuringMachine tm

    private variable
     q q₁ q₂ q₃ : Q
     t t₁ t₂ t₃ : Tape Γ
     n n₁ n₂ n₃ : ℕ
     qt₁ qt₂ : Q × Tape Γ

    data _-⟨_⟩→_ : Q × Tape Γ → ℕ → Q × Tape Γ → Set where
      step-refl : (q , t) -⟨ 0 ⟩→ (q , t)
      step-trans : (q₁ , t₁) -⟨ n₁ ⟩→ (q₂ , t₂)
                 → (q₂ , t₂) -⟨ n₂ ⟩→ (q₃ , t₃)
                 → (q₁ , t₁) -⟨ n₁ + n₂ ⟩→ (q₃ , t₃)
      step-via : (q , t) -⟨ 1 ⟩→ step tm q t

    data HaltsIn : Q × Tape Γ → ℕ → Set where
      halts
          : (q : Q)
          → (t : Tape Γ)
          → F q
          → qt₁ -⟨ n ⟩→ (q , t)
          → HaltsIn qt₁ n

    glue : qt₁ -⟨ n₁ ⟩→ qt₂ → HaltsIn qt₂ n₂ → HaltsIn qt₁ (n₁ + n₂)
    glue x (halts q t f arr) = halts q t f (step-trans x arr)

    glue₁ : qt₁ -⟨ 1 ⟩→ qt₂ → HaltsIn qt₂ n₂ → HaltsIn qt₁ (suc n₂)
    glue₁ = glue

--     module ⟶-Reasoning where
--       open import Relation.Binary.Reasoning.Base.Single _-⟨_⟩→_ step-refl step-trans public




module BusyBeaver where
  open TuringMachine

  data State : Set where
    A B C HALT : State

  data HaltState : State → Set where
    halt : HaltState HALT

  open import Data.Bool

  busy-beaver : TuringMachine Bool HaltState
  F-dec busy-beaver A = no λ ()
  F-dec busy-beaver B = no λ ()
  F-dec busy-beaver C = no λ ()
  F-dec busy-beaver HALT = yes halt
  blank busy-beaver = false
  initial-state busy-beaver = A
  transition busy-beaver A false = B , true , R
  transition busy-beaver B false = A , true , L
  transition busy-beaver C false = B , true , L
  transition busy-beaver A true  = C , true , L
  transition busy-beaver B true  = B , true , R
  transition busy-beaver C true  = HALT , true , R
  transition busy-beaver HALT x  = HALT , x , R

  open Stepping busy-beaver
  _ : (A , tape [] false []) -⟨ 3 ⟩→ (C , tape [] false (true ∷ true ∷ [])) -- (A , tape [] true [ true ])
  _ = step-trans step-via (step-trans step-via step-via)

