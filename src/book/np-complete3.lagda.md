```agda
open import Data.Bool
  using (Bool; true; false; not)
  renaming (_∧_ to and; _∨_ to or)
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; lookup)
open import Data.List
  using (List; _∷_; []; _++_; [_]; reverse; _∷ʳ_; map; concatMap; length)
open import Relation.Unary using (Decidable)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- SAT
module np-complete3 (n : ℕ) (bs : Vec Bool n) where

open import np-complete0
open import Data.Fin using (Fin)

open import Data.Product using (_×_; _,_; Σ)

State : Set
State = Bool × Bool

open import np-complete1 using (MoveDirection; L; R) -- ; Tape; tape; move)

data δ : State × Instr n → State × Instr n × MoveDirection → Set where
  ⟶pop
      : {lo hi : Bool}
      → δ ((lo , hi)           , pop)
          ((and lo hi , false) , nop , R)
  ⟶val
      : {x : Lit n} {lo hi : Bool}
      → δ ((lo , hi)                       , val x)
          ((lo , or hi (evaluateLit bs x)) , nop , R)

data Halted : State × Instr n → Set where
  halted : {q : State} → Halted (q , nop)

compileClause : Clause n → List (Instr n)
compileClause (last x) = val x ∷ pop ∷ []
compileClause (x ∨ cnf) = val x ∷ compileClause cnf

compile : CNF n → List (Instr n)
compile (last x) = compileClause x
compile (x ∧ cnf) = compileClause x ++ compile cnf

compileClause' : List (Lit n) → List (Instr n)
compileClause' ls = map val ls ∷ʳ pop

compile' : List (List (Lit n)) → List (Instr n)
compile' = concatMap compileClause'


open import Relation.Nullary using (¬_)

is-halted : ∀ {qi} → Halted qi → ∀ qir → ¬ δ qi qir
is-halted halted _ ()

b-dec : Decidable (_≡ nop {n = n})
b-dec pop = no λ ()
b-dec (val x) = no λ ()
b-dec nop = yes refl

open import np-complete2 (Instr n) State δ Halted is-halted nop b-dec public


mkTape : List (Instr n) → Tape
mkTape [] = tape [] nop []
mkTape (r ∷ rs)  = tape [] r rs


open import Relation.Binary.PropositionalEquality
open import Data.List.Properties
open import Data.Bool.Properties

cc-ne : ∀ x → Σ (Instr n) λ i → Σ (List (Instr n)) λ is → compileClause x ≡ i ∷ is
cc-ne (last x) = val x , pop ∷ [] , refl
cc-ne (x ∨ x₁) = val x , compileClause x₁ , refl

lemma : (i : Instr n) → (rs : List (Instr n)) → moveWrite R nop (tape [] i rs) ≡ mkTape rs
lemma i [] = refl
lemma i (x ∷ rs) = refl

equivClause
    : (lo hi : Bool)
    → (rs : List (Instr n))
    → (cl : Clause n)
    → ((lo , hi) , mkTape (compileClause cl ++ rs)) ⟶
      ( (and lo (or hi (evaluateClause bs cl)) , false)
      , mkTape rs
      )
equivClause lo hi rs (last x) =
  begin
    (lo , hi) , _
  ≈⟨ step ⟶val ⟩
    (lo , or hi (evaluateLit bs x)) , _
  ≈⟨ step ⟶pop ⟩
    _ , moveWrite R nop (tape [] pop rs)
  ≡⟨ cong (_ ,_) (lemma pop rs) ⟩
    _ , mkTape rs
  ∎
  where open ⟶-Reasoning
equivClause lo hi rs (x ∨ cl) =
  begin
    (lo , hi) , _
  ≈⟨ step ⟶val ⟩
    (lo , or hi (evaluateLit bs x)) , _
  ≡⟨⟩
    _ , moveWrite R nop (tape [] (val x) (compileClause cl ++ rs))
  ≡⟨ cong (_ ,_) (lemma (val x) (compileClause cl ++ rs)) ⟩
    _ , mkTape (compileClause cl ++ rs)
  ≈⟨ equivClause lo (or hi (evaluateLit bs x)) rs cl ⟩
    (and lo (or (or hi (evaluateLit bs x)) (evaluateClause bs cl)) , false)
      , mkTape rs
  ≡⟨ cong (λ φ → (and lo φ , false) , _)
          (∨-assoc hi (evaluateLit bs x) (evaluateClause bs cl)) ⟩
    (and lo (or hi (evaluateClause bs (x ∨ cl))) , false)
      , _
  ∎
  where open ⟶-Reasoning


equiv
    : (lo : Bool)
    → (cnf : CNF n)
    → HaltsWith ((lo , false) , mkTape (compile cnf))
                (and lo (evaluate bs cnf ), false)
equiv lo (last x) = halts-with (
  begin
    _ , mkTape (compileClause x)
  ≡⟨ cong (λ φ → _ , mkTape φ) (sym (++-identityʳ (compileClause x))) ⟩
    _ , mkTape (compileClause x ++ [])
  ≈⟨ equivClause lo false [] x ⟩
    (and lo (or false (evaluateClause bs x)) , false) , mkTape []
  ∎
  ) halted
  where open ⟶-Reasoning
equiv lo (x ∧ cnf) = halts-glue
  (
    begin
      (lo , false) , mkTape (compileClause x ++ compile cnf)
    ≈⟨ equivClause lo false (compile cnf) x ⟩
      (and lo (evaluateClause bs x) , false) , mkTape (compile cnf)
    ∎
  ) (subst-halts refl (cong (_, false)
      (∧-assoc lo (evaluateClause bs x) (evaluate bs cnf)))
      (equiv (and lo (evaluateClause bs x)) cnf)
      )
  where open ⟶-Reasoning

DONE : (cnf : CNF n)
     → HaltsWith ((true , false) , mkTape (compile cnf))
                 (evaluate bs cnf , false)
DONE = equiv true

```

