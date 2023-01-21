open import Data.Vec using (_∷_; [])
open import Data.List using (_∷_; [])
open import Data.Bool using (true; false)
open import Data.Fin using (Fin; zero; suc)

module playground.SAT2-ex where

open import playground.SAT2 (true ∷ false ∷ [])

open import playground.turing using (Tape; tape; R; L; buildTape)

open ⟶-Reasoning

mkTape = buildTape halt

x₁ x₂ : Fin 2
x₁ = zero
x₂ = suc zero

t : Tape Instr
t = mkTape ( val (↪ x₁)
           ∷ val (! x₂)
           ∷ pop
           ∷ val (! x₁)
           ∷ val (↪ x₂)
           ∷ pop
           ∷ halt
           ∷ []
           )

open import Data.Product
open import Data.Nat using (ℕ; zero; suc)

moveR : ℕ → Tape Instr → Tape Instr
moveR zero t = t
moveR (suc n) t = move R (moveR n t)

ex : ((true , false) , t) ⟶ ((false , false) , moveR 6 t)
ex = begin
  (true , false)  , moveR 0 t  ≈⟨ step ⟶val ⟩
  (true , true)   , moveR 1 t  ≈⟨ step ⟶val ⟩
  (true , true)   , moveR 2 t  ≈⟨ step ⟶pop ⟩
  (true , false)  , moveR 3 t  ≈⟨ step ⟶val ⟩
  (true , false)  , moveR 4 t  ≈⟨ step ⟶val ⟩
  (true , false)  , moveR 5 t  ≈⟨ step ⟶pop ⟩
  (false , false) , moveR 6 t  ∎

ex-halts : HaltsWith ((true , false) , t) (false , false)
ex-halts = halts-with ex halted

