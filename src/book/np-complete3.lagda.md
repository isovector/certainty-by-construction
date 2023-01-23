```agda
open import Data.Bool
  using (Bool; true; false; not; _∨_; _∧_)
open import Data.Nat using (ℕ; _+_; suc)
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
          ((lo , hi ∨ (x ↓ˡ bs)) , nop , R)

data Halted : State × Instr n → Set where
  halted : {q : State} → Halted (q , nop)

⌊_⌋ᶜ : Clause n → List (Instr n)
⌊_⌋ᶜ ls = map val ls ∷ʳ pop

⌊_⌋ : CNF n → List (Instr n)
⌊_⌋ = concatMap ⌊_⌋ᶜ


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

open import Data.Nat.Properties
open import Data.List.Properties
import Relation.Binary.PropositionalEquality as PropEq

equivClause
    : (lo hi : Bool)
    → (rs : List (Instr n))
    → (cl : Clause n)
    → ((lo , hi) , mkTape (⌊ cl ⌋ᶜ ++ rs)) -⟨ length ⌊ cl ⌋ᶜ ⟩→
      ( (lo ∧ (hi ∨ (cl ↓ᶜ bs)) , false)
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
    (lo , hi) , mkTape (⌊ x ∷ xs ⌋ᶜ ++ rs)
  ≡⟨⟩
    (lo , hi) , tape [] (val x) ((map val xs ++ (pop ∷ [])) ++ rs)
  ≡ᵀ⟨ +-comm (length ⌊ xs ⌋ᶜ) 1 ⟩
    _
  ≈⟨ step ⟶val ⟩
    (lo , hi ∨ (x ↓ˡ bs)) , move R (tape [] nop (⌊ xs ⌋ᶜ ++ rs))
  ≡⟨ cong (_ ,_) (lemma₁ (⌊ xs ⌋ᶜ ++ rs)) ⟩
    (lo , hi ∨ (x ↓ˡ bs)) , mkTape (⌊ xs ⌋ᶜ ++ rs)
  ≈⟨ equivClause lo (hi ∨ (x ↓ˡ bs)) rs xs ⟩
    (lo ∧ ((hi ∨ (x ↓ˡ bs)) ∨ (xs ↓ᶜ bs)) , false) , mkTape rs
  ≡⟨ cong (λ φ → (lo ∧ φ , false) , mkTape rs) (∨-assoc hi (x ↓ˡ bs) (xs ↓ᶜ bs)) ⟩
    (lo ∧ (hi ∨ ((x ∷ xs) ↓ᶜ bs)) , false) , mkTape rs
  ∎
  where open ⟶-Reasoning

open import Function using (flip; _$_; _∘_)

equiv
    : (lo : Bool)
    → (cnf : CNF n)
    → HaltsWith ((lo , false) , mkTape ⌊ cnf ⌋)
                ((lo ∧ (cnf ↓ bs)) , false)
equiv lo [] = flip halts-with halted $
  begin
    (lo , false) , mkTape ⌊ [] ⌋
  ≡⟨ cong (λ φ → (φ , _) , _) (sym (∧-identityʳ lo)) ⟩
    (lo ∧ true , false) , mkTape ⌊ [] ⌋
  ∎
  where open ⟶-Reasoning
equiv lo (x ∷ cnf) =
  halts-glue
    ( begin
        (lo , false) , mkTape ⌊ x ∷ cnf ⌋
      ≡⟨⟩
        (lo , false) , mkTape (⌊ x ⌋ᶜ ++ ⌊ cnf ⌋)
      ≈⟨ equivClause lo false ⌊ cnf ⌋ x ⟩
        (lo ∧ (x ↓ᶜ bs) , false) , mkTape ⌊ cnf ⌋
      ∎
    )
    (subst-halts refl (cong (_, false)
      (∧-assoc lo ((x ↓ᶜ bs)) ((cnf ↓ bs))))
      (equiv (lo ∧ (x ↓ᶜ bs)) cnf)
    )
  where open ⟶-Reasoning

DONE : (cnf : CNF n)
     → HaltsWith ((true , false) , mkTape ⌊ cnf ⌋)
                 ((cnf ↓ bs) , false)
DONE = equiv true

open import Relation.Binary.PropositionalEquality as PropEq
open import Data.List.Relation.Unary.All using (All)
open import Data.Empty


linear-time
  : {q₁ q₂ : State}
    {m : ℕ}
  → (l₁ l₂ : List (Instr n))
  → All (_≢ nop) l₁
  → All (_≢ nop) l₂
  → (q₁ , mkTape l₁) -⟨ m ⟩→ (q₂ , mkTape l₂)
  → m + length l₂ ≡ length l₁
linear-time [] [] _ _ refl = refl
linear-time [] (_ ∷ .[]) _ (nop≠nop All.∷ _) refl = ⊥-elim (nop≠nop refl)
linear-time _ [] (nop≠nop All.∷ _) _ refl = ⊥-elim (nop≠nop refl)
linear-time (_ ∷ l₁) [] (_ All.∷ nop∌l₁) _ (step-with ⟶pop x₄)
  = cong suc (linear-time l₁ [] nop∌l₁ All.[] (⟶-subst (cong (_ ,_) (lemma₁ l₁)) refl refl x₄))
linear-time (_ ∷ l₁) [] (_ All.∷ nop∌l₁) _ (step-with ⟶val x₄)
  = cong suc (linear-time l₁ [] nop∌l₁ All.[] (⟶-subst (cong (_ ,_) (lemma₁ l₁)) refl refl x₄))
linear-time (x₃ ∷ l₁) (.x₃ ∷ .l₁) _ _ refl = refl
linear-time (_ ∷ l₁) l₂@(_ ∷ _) (_ All.∷ nop∌l₁) nops (step-with ⟶pop x₅) =
  begin
    suc _ + length l₂
  ≡⟨ cong suc (linear-time l₁ l₂ nop∌l₁ nops (⟶-subst (cong (_ ,_) (lemma₁ l₁)) refl refl x₅)) ⟩
    length (pop ∷ l₁)
  ∎
  where open ≡-Reasoning
linear-time (_ ∷ l₁) l₂@(_ ∷ _) (_ All.∷ nop∌l₁) nops (step-with (⟶val {x = x}) x₅) =
  begin
    suc _ + length l₂
  ≡⟨ cong suc (linear-time l₁ l₂ nop∌l₁ nops (⟶-subst (cong (_ ,_) (lemma₁ l₁)) refl refl x₅)) ⟩
    length (val x ∷ l₁)
  ∎
  where open ≡-Reasoning


```

