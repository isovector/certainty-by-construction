```agda
open import Data.Bool
  using (Bool; true; false; not)
  renaming (_∧_ to and; _∨_ to or)
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; lookup)
open import Data.List
  using (List; _∷_; []; _++_; [_]; reverse; _∷ʳ_)

-- SAT
module np-complete3 {n : ℕ} (bs : Vec Bool n) where

open import np-complete0
open import Data.Fin using (Fin)

open import Data.Product using (_×_; _,_)

State : Set
State = Bool × Bool

open import np-complete1 using (MoveDirection; L; R; Tape; tape; move)

data δ : State × Instr n → State × Instr n × MoveDirection → Set where
  ⟶pop
      : {lo hi : Bool}
      → δ ((lo , hi)           , pop)
          ((and lo hi , false) , pop , R)
  ⟶val
      : {x : Lit n} {lo hi : Bool}
      → δ ((lo , hi)                       , val x)
          ((lo , or hi (evaluateLit bs x)) , val x , R)

data Halted : State × Instr n → Set where
  halted : {q : State} → Halted (q , halt)

compileClause : Clause n → List (Instr n)
compileClause (last x) = val x ∷ pop ∷ []
compileClause (x ∨ cnf) = val x ∷ compileClause cnf

compile : CNF n → List (Instr n)
compile (last x) = compileClause x
compile (x ∧ cnf) = compileClause x ++ compile cnf


open import Relation.Nullary using (¬_)

is-halted : ∀ {qi} → Halted qi → ∀ qir → ¬ δ qi qir
is-halted halted _ ()

open import np-complete2 (Instr n) State δ Halted is-halted halt public


mkTape : List (Instr n) → List (Instr n) → Tape (Instr n)
mkTape ls [] = tape ls halt []
mkTape ls (r ∷ rs)  = tape ls r rs


open import Relation.Binary.PropositionalEquality
open import Data.Bool.Properties
open import Data.Bool.Properties


postulate
  lemma₁ : ∀ ls x cl → move halt R (tape ls (val x) (compileClause cl)) ≡ mkTape (val x ∷ ls) (compileClause cl)
  lemma : ∀ cl x ls → reverse (compileClause cl) ++ val x ∷ ls ≡ reverse (val x ∷ compileClause cl) ++ ls

equivClause
    : (lo hi : Bool)
    → (ls : List (Instr n))
    → (cl : Clause n)
    → ((lo , hi) , mkTape ls (compileClause cl)) ⟶
      ((and lo (or hi (evaluateClause bs cl)) , false) , mkTape (reverse (compileClause cl) ++ ls) [])
equivClause lo hi ls (last x) =
  begin
    (lo , hi) , tape _ (val x) (pop ∷ [])
  ≈⟨ step ⟶val ⟩
    (lo , or hi (evaluateLit bs x)) , tape _ pop []
  ≈⟨ step ⟶pop ⟩
    (and lo (or hi (evaluateLit bs x)) , false) , tape _ halt []
  ∎
  where open ⟶-Reasoning
equivClause lo hi ls (x ∨ cl) =
  begin
    (lo , hi) , _
  ≈⟨ step ⟶val ⟩
    (lo , or hi (evaluateLit bs x)) , move halt R (tape ls (val x) (compileClause cl))
  ≡⟨ cong (λ φ → (lo , or hi (evaluateLit bs x)) , φ) (lemma₁ ls x cl) ⟩
    (lo , or hi (evaluateLit bs x)) , mkTape (val x ∷ ls) (compileClause cl)
  ≈⟨ equivClause lo (or hi (evaluateLit bs x)) (val x ∷ ls) cl ⟩
    let rev = mkTape (reverse (compileClause cl) ++ val x ∷ ls) [] in
    (and lo (or (or hi (evaluateLit bs x)) (evaluateClause bs cl)) , false) , rev
  ≡⟨ cong (_, rev) (cong (_, false) (cong (and lo) (∨-assoc hi (evaluateLit bs x) (evaluateClause bs cl))))  ⟩
    let q = (and lo (or hi (or (evaluateLit bs x) (evaluateClause bs cl))) , false) in
    q , mkTape (reverse (compileClause cl) ++ val x ∷ ls) []
  ≡⟨ cong (q ,_) (cong (λ φ → mkTape φ []) (lemma cl x ls)) ⟩
    q , mkTape (reverse (compileClause (x ∨ cl)) ++ ls) []
  ∎
  where open ⟶-Reasoning

equiv
    : (ls : List (Instr n))
    → (cnf : CNF n)
    → HaltsWith ((true , false) , mkTape ls (compile cnf))
                (evaluate bs cnf , false)
equiv ls (last x) = halts-with {! !} {! !}
equiv ls (x ∧ cnf) = {! !}

```

