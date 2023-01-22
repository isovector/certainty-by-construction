```agda
open import Data.Bool
  using (Bool; true; false; not; _∨_; _∧_)
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec)

-- SAT
module np-complete3 (n : ℕ) (bs : Vec Bool n) where

open import np-complete0
open import Data.Fin using (Fin)

open import Data.List
  using (List; _∷_; []; _++_; [_]; reverse; _∷ʳ_; map; concatMap; length)
open import Relation.Unary using (Decidable)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Data.Product using (_×_; _,_; Σ)

State : Set
State = Bool × Bool

open import np-complete1 using (MoveDirection; L; R) -- ; Tape; tape; move)

data δ : State × Instr n → State × Instr n × MoveDirection → Set where
  ⟶pop
      : {lo hi : Bool}
      → δ ((lo , hi)           , pop)
          ((lo ∧ hi , false) , nop , R)
  ⟶val
      : {x : Lit n} {lo hi : Bool}
      → δ ((lo , hi)                       , val x)
          ((lo , hi ∨ evaluateLit bs x) , nop , R)

data Halted : State × Instr n → Set where
  halted : {q : State} → Halted (q , nop)

compileClause : Clause n → List (Instr n)
compileClause ls = map val ls ∷ʳ pop

compile : CNF n → List (Instr n)
compile = concatMap compileClause


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


open import Relation.Binary.PropositionalEquality using (cong; sym)
open import Data.Bool.Properties using (∨-assoc; ∧-assoc; ∨-identityʳ; ∧-identityʳ)

lemma₁ : (rs : List (Instr n)) → move R (tape [] nop rs) ≡ mkTape rs
lemma₁ [] = refl
lemma₁ (x ∷ rs) = refl

equivClause
    : (lo hi : Bool)
    → (rs : List (Instr n))
    → (cl : Clause n)
    → ((lo , hi) , mkTape (compileClause cl ++ rs)) ⟶
      ( (lo ∧ (hi ∨ evaluateClause bs cl) , false)
      , mkTape rs
      )
equivClause lo hi rs [] =
  begin
    (lo , hi) , mkTape (pop ∷ rs)
  ≈⟨ step ⟶pop ⟩
    (lo ∧ hi , false) , move R (tape [] nop rs)
  ≡⟨ cong (_ ,_) (lemma₁ rs) ⟩
    (lo ∧ hi , false) , mkTape rs
  ≡⟨ cong (λ φ → (lo ∧ φ , false) , _) (sym (∨-identityʳ hi)) ⟩
    (lo ∧ (hi ∨ false) , false) , _
  ∎
  where open ⟶-Reasoning
equivClause lo hi rs (x ∷ xs) =
  begin
    (lo , hi) , mkTape (compileClause (x ∷ xs) ++ rs)
  ≡⟨⟩
    (lo , hi) , tape [] (val x) ((map val xs ++ (pop ∷ [])) ++ rs)
  ≈⟨ step ⟶val ⟩
    (lo , hi ∨ evaluateLit bs x) , move R (tape [] nop (compileClause xs ++ rs))
  ≡⟨ cong (_ ,_) (lemma₁ (compileClause xs ++ rs)) ⟩
    (lo , hi ∨ evaluateLit bs x) , mkTape (compileClause xs ++ rs)
  ≈⟨ equivClause lo (hi ∨ evaluateLit bs x) rs xs ⟩
    (lo ∧ ((hi ∨ evaluateLit bs x) ∨ evaluateClause bs xs) , false) , mkTape rs
  ≡⟨ cong (λ φ → (lo ∧ φ , false) , mkTape rs) (∨-assoc hi (evaluateLit bs x) (evaluateClause bs xs)) ⟩
    (lo ∧ (hi ∨ evaluateClause bs (x ∷ xs)) , false) , mkTape rs
  ∎
  where open ⟶-Reasoning

open import Function using (flip; _$_)

equiv
    : (lo : Bool)
    → (cnf : CNF n)
    → HaltsWith ((lo , false) , mkTape (compile cnf))
                ((lo ∧ evaluate bs cnf) , false)
equiv lo [] = flip halts-with halted $
  begin
    (lo , false) , mkTape (compile [])
  ≡⟨ cong (λ φ → (φ , _) , _) (sym (∧-identityʳ lo)) ⟩
    (lo ∧ true , false) , mkTape (compile [])
  ∎
  where open ⟶-Reasoning
equiv lo (x ∷ cnf) =
  halts-glue
    ( begin
        (lo , false) , mkTape (compile (x ∷ cnf))
      ≡⟨⟩
        (lo , false) , mkTape (compileClause x ++ compile cnf)
      ≈⟨ equivClause lo false (compile cnf) x ⟩
        (lo ∧ evaluateClause bs x , false) , mkTape (compile cnf)
      ∎
    )
    (subst-halts refl (cong (_, false)
      (∧-assoc lo (evaluateClause bs x) (evaluate bs cnf)))
      (equiv (lo ∧ evaluateClause bs x) cnf)
    )
  where open ⟶-Reasoning

DONE : (cnf : CNF n)
     → HaltsWith ((true , false) , mkTape (compile cnf))
                 (evaluate bs cnf , false)
DONE = equiv true

```

