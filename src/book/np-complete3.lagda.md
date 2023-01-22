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

open import Data.Product using (_×_; _,_; Σ)

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
open import Data.List.Properties
open import Data.Bool.Properties

cc-ne : ∀ x → Σ (Instr n) λ i → Σ (List (Instr n)) λ is → compileClause x ≡ i ∷ is
cc-ne (last x) = val x , pop ∷ [] , refl
cc-ne (x ∨ x₁) = val x , compileClause x₁ , refl

lemma₁ : ∀ ls x cl rs → move halt R (tape ls (val x) (compileClause cl ++ rs)) ≡ mkTape (val x ∷ ls) (compileClause cl ++ rs)
lemma₁ ls x cl rs with cc-ne cl
... | i , is , proof = begin
  move halt R (tape ls (val x) (compileClause cl ++ rs)) ≡⟨ cong (λ φ → move halt R (tape ls (val x) (φ ++ rs))) proof ⟩
  move halt R (tape ls (val x) (i ∷ is ++ rs))  ≡⟨⟩
  tape (val x ∷ ls) i (is ++ rs)                  ≡⟨⟩
  mkTape (val x ∷ ls) (i ∷ is ++ rs)            ≡⟨ cong (λ φ → mkTape (val x ∷ ls) (φ ++ rs)) (sym proof) ⟩
  mkTape (val x ∷ ls) (compileClause cl ++ rs)  ∎
  where open ≡-Reasoning

lemma : {A : Set} → ∀ cl (x : A) ls → reverse cl ++ x ∷ ls ≡ reverse (x ∷ cl) ++ ls
lemma [] x ls = refl
lemma (x₁ ∷ cl) x ls = begin
  reverse (x₁ ∷ cl) ++ x ∷ ls   ≡⟨ sym (∷ʳ-++ (reverse (x₁ ∷ cl)) x ls)  ⟩
  reverse (x₁ ∷ cl) ∷ʳ x ++ ls  ≡⟨ cong (_++ ls) (sym (unfold-reverse x (x₁ ∷ cl))) ⟩
  reverse (x ∷ x₁ ∷ cl) ++ ls   ∎
  where open ≡-Reasoning

lemma₂ : ∀ x ls rs → move halt R (tape (val x ∷ ls) pop rs) ≡ mkTape (pop ∷ val x ∷ ls) rs
lemma₂ x ls [] = refl
lemma₂ x ls (x₁ ∷ rs) = refl

equivClause
    : (lo hi : Bool)
    → (ls : List (Instr n))
    → (rs : List (Instr n))
    → (cl : Clause n)
    → ((lo , hi) , mkTape ls (compileClause cl ++ rs)) ⟶
      ( (and lo (or hi (evaluateClause bs cl)) , false)
      , mkTape (reverse (compileClause cl) ++ ls) rs
      )
equivClause lo hi ls rs (last x) =
  begin
    (lo , hi) , tape _ (val x) (pop ∷ rs)
  ≈⟨ step ⟶val ⟩
    let t' = tape _ pop rs in
    (lo , or hi (evaluateLit bs x)) , t'
  ≈⟨ step ⟶pop ⟩
    (and lo (or hi (evaluateLit bs x)) , false)
      , move halt R t'
  ≡⟨ cong (λ φ → (and lo (or hi (evaluateLit bs x)) , false) , φ) (lemma₂ x ls rs) ⟩
    (and lo (or hi (evaluateLit bs x)) , false)
      , mkTape (pop ∷ val x ∷ ls) rs
  ∎
  where open ⟶-Reasoning
equivClause lo hi ls rs (x ∨ cl) =
  begin
    (lo , hi) , tape ls (val x) (compileClause cl ++ rs)
  ≈⟨ step ⟶val ⟩
    (lo , or hi (evaluateLit bs x)) , move halt R (tape ls (val x) (compileClause cl ++ rs))
  ≡⟨ cong (λ φ → (lo , or hi (evaluateLit bs x)) , φ) (lemma₁ ls x cl rs) ⟩
    (lo , or hi (evaluateLit bs x)) , mkTape (val x ∷ ls) (compileClause cl ++ rs)
  ≈⟨ equivClause lo (or hi (evaluateLit bs x)) (val x ∷ ls) rs cl ⟩
    let t = mkTape (reverse (compileClause cl) ++ val x ∷ ls) rs in
    (and lo (or (or hi (evaluateLit bs x)) (evaluateClause bs cl)) , false)
      , mkTape (reverse (compileClause cl) ++ val x ∷ ls) rs
  ≡⟨ cong (λ φ → (and lo φ , false) , t) (∨-assoc hi (evaluateLit bs x) (evaluateClause bs cl)) ⟩
    let q = (and lo (or hi (evaluateClause bs (x ∨ cl))) , false) in
    q
      , mkTape (reverse (compileClause cl) ++ val x ∷ ls) rs
  ≡⟨ cong (λ φ → q , mkTape φ rs) (lemma (compileClause cl) (val x) ls) ⟩
    q
      , mkTape (reverse (compileClause (x ∨ cl)) ++ ls) rs
  ∎
  where open ⟶-Reasoning


equiv
    : (lo : Bool)
    → (ls : List (Instr n))
    → (cnf : CNF n)
    → HaltsWith ((lo , false) , mkTape ls (compile cnf))
                (and lo (evaluate bs cnf ), false)
equiv lo ls (last x) = halts-with (
  begin
    _ , mkTape ls (compileClause x)
  ≡⟨ cong (λ φ → _ , mkTape ls φ) (sym (++-identityʳ (compileClause x))) ⟩
    _ , mkTape ls (compileClause x ++ [])
  ≈⟨ equivClause lo false ls [] x ⟩
    (and lo (or false (evaluateClause bs x)) , false) , mkTape (reverse (compileClause x) ++ ls) []
  ∎
  ) halted
  where open ⟶-Reasoning
equiv lo ls (x ∧ cnf) = halts-glue
  (
    begin
      (lo , false) , mkTape ls (compile (x ∧ cnf))
    ≡⟨⟩
      (lo , false) , mkTape ls (compileClause x ++ compile cnf)
    ≈⟨ equivClause lo false ls (compile cnf) x ⟩
      (and lo (evaluateClause bs x) , false) , mkTape (reverse (compileClause x) ++ ls) (compile cnf)
    ∎
  ) (subst-halts refl (cong (_, false)
      (∧-assoc lo (evaluateClause bs x) (evaluate bs cnf)))
      (equiv (and lo (evaluateClause bs x)) (reverse (compileClause x) ++ ls) cnf)
      )
  where open ⟶-Reasoning

DONE : (cnf : CNF n)
     → HaltsWith ((true , false) , mkTape [] (compile cnf))
                 (evaluate bs cnf , false)
DONE = equiv true []

```

