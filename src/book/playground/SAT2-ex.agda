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

ex : ((true , false) , t) ⟶ ((false , false) , _)
ex = begin
  (true , false)  , _  ≈⟨ step ⟶val ⟩
  (true , true)   , _  ≈⟨ step ⟶val ⟩
  (true , true)   , _  ≈⟨ step ⟶pop ⟩
  (true , false)  , _  ≈⟨ step ⟶val ⟩
  (true , false)  , _  ≈⟨ step ⟶val ⟩
  (true , false)  , _  ≈⟨ step ⟶pop ⟩
  (false , false) , _  ∎

ex-halts : HaltsWith ((true , false) , t) (false , false)
ex-halts = halts-with ex halted

