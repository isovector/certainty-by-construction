```agda
open import Data.Bool
  using (Bool; true; false; not; _∨_; _∧_)
open import Data.Nat using (ℕ; _+_; suc)
open import Data.Vec using (Vec)

-- SAT
module np-complete3 (Name : Set) (bs : Name → Bool) where

open import np-complete0
open import Data.Fin using (Fin)

open import Data.List
  using (List; _∷_; []; _++_; [_]; reverse; _∷ʳ_; map; concatMap; length)
open import Relation.Unary using (Decidable)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Empty using (⊥-elim)

open import Data.Product using (_×_; _,_; ∃)
open import Data.Sum using (_⊎_; inj₁; inj₂)

State : Set
State = Bool × Bool

⌊_⌋ᶜ : Clause Name → List (Instr Name)
⌊_⌋ᶜ ls = map val ls ∷ʳ pop

⌊_⌋ : CNF Name → List (Instr Name)
⌊_⌋ = concatMap ⌊_⌋ᶜ

open import np-complete1 using (MoveDirection; L; R)

data δ : State × Instr Name → State × Instr Name × MoveDirection → Set where
  ⟶pop
      : {lo hi : Bool}
      → δ ((lo , hi)         , pop)
          ((lo ∧ hi , false) , nop , R)
  ⟶val
      : {x : Lit Name} {lo hi : Bool}
      → δ ((lo , hi)             , val x)
          ((lo , hi ∨ (x ↓ˡ bs)) , nop , R)

no-nops : ∀ q o → ¬ δ (q , nop) o
no-nops q o ()

δ-deterministic
    : (qt : State × Instr Name)
    → {o₁ o₂ : State × Instr Name × MoveDirection}
    → δ qt o₁ → δ qt o₂
    → o₁ ≡ o₂
δ-deterministic (_ , pop) ⟶pop ⟶pop = refl
δ-deterministic (_ , val _) ⟶val ⟶val = refl

data Halted : State × Instr Name → Set where
  halted : {q : State} → Halted (q , nop)

Halted-dec : Decidable Halted
Halted-dec (_ , pop) = no λ ()
Halted-dec (_ , val x) = no λ ()
Halted-dec (_ , nop) = yes halted


open import Relation.Nullary using (¬_)

step-or-halt : (qi : State × Instr Name) →  ∃ (δ qi) ⊎ Halted qi
step-or-halt (q , pop) = inj₁ (_ , ⟶pop)
step-or-halt (q , val x) = inj₁ (_ , ⟶val)
step-or-halt (q , nop) = inj₂ halted

is-halted : ∀ {qi} → Halted qi → ∀ qir → ¬ δ qi qir
is-halted halted _ ()

nop-dec : Decidable (_≡ nop {Name = Name})
nop-dec pop = no λ ()
nop-dec (val x) = no λ ()
nop-dec nop = yes refl

open import np-complete2
    (Instr Name)
    State
    δ δ-deterministic
    Halted Halted-dec
    step-or-halt
    nop nop-dec
  public


mkTape : List (Instr Name) → Tape
mkTape [] = tape [] nop []
mkTape (r ∷ rs)  = tape [] r rs


open import Relation.Binary.PropositionalEquality using (cong; sym)
open import Data.Bool.Properties using (∨-assoc; ∧-assoc; ∨-identityʳ; ∧-identityʳ)

lemma₁ : (rs : List (Instr Name)) → move R (tape [] nop rs) ≡ mkTape rs
lemma₁ [] = refl
lemma₁ (x ∷ rs) = refl

open import Data.Nat.Properties
open import Data.List.Properties

equivClause
    : (lo hi : Bool)
    → (rs : List (Instr Name))
    → (cl : Clause Name)
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
    → (cnf : CNF Name)
    → HaltsWith ((lo , false) , mkTape ⌊ cnf ⌋)
                ((lo ∧ (cnf ↓ bs)) , false)
                (length ⌊ cnf ⌋)
equiv lo [] = flip (halts-with _) halted $
  begin
    (lo , false) , mkTape ⌊ [] ⌋
  ≡⟨ cong (λ φ → (φ , _) , _) (sym (∧-identityʳ lo)) ⟩
    (lo ∧ true , false) , mkTape ⌊ [] ⌋
  ∎
  where open ⟶-Reasoning
equiv lo (x ∷ cnf)
  = subst-halts refl refl (sym (length-++ ⌊ x ⌋ᶜ))
  $ halts-glue
      ( begin
          (lo , false) , mkTape ⌊ x ∷ cnf ⌋
        ≡⟨⟩
          (lo , false) , mkTape (⌊ x ⌋ᶜ ++ ⌊ cnf ⌋)
        ≈⟨ equivClause lo false ⌊ cnf ⌋ x ⟩
          (lo ∧ (x ↓ᶜ bs) , false) , mkTape ⌊ cnf ⌋
        ∎
      )
  $ subst-halts
      refl
      (cong (_, false) (∧-assoc lo ((x ↓ᶜ bs)) ((cnf ↓ bs))))
      refl
      (equiv (lo ∧ (x ↓ᶜ bs)) cnf)
  where open ⟶-Reasoning

DONE : (cnf : CNF Name)
     → HaltsWith ((true , false) , mkTape ⌊ cnf ⌋)
                 ((cnf ↓ bs)     , false)
                 (length ⌊ cnf ⌋)
DONE = equiv true

open import Relation.Binary.PropositionalEquality
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Empty


linear-time
  : {q₁ q₂ : State}
    {m : ℕ}
  → (l₁ l₂ : List (Instr Name))
  → All (_≢ nop) l₁
  → All (_≢ nop) l₂
  → (q₁ , mkTape l₁) -⟨ m ⟩→ (q₂ , mkTape l₂)
  → m + length l₂ ≡ length l₁
linear-time [] [] _ _ refl = refl
linear-time [] (_ ∷ .[]) _ (nop≠nop ∷ _) refl = ⊥-elim (nop≠nop refl)
linear-time _ [] (nop≠nop ∷ _) _ refl = ⊥-elim (nop≠nop refl)
linear-time (_ ∷ l₁) [] (_ ∷ nop∌l₁) _ (step-with ⟶pop x₄)
  = cong suc
  $ linear-time l₁ [] nop∌l₁ []
  $ ⟶-subst (cong (_ ,_) (lemma₁ l₁)) refl refl x₄
linear-time (_ ∷ l₁) [] (_ ∷ nop∌l₁) _ (step-with ⟶val x₄)
  = cong suc
  $ linear-time l₁ [] nop∌l₁ []
  $ ⟶-subst (cong (_ ,_) (lemma₁ l₁)) refl refl x₄
linear-time (x₃ ∷ l₁) (.x₃ ∷ .l₁) _ _ refl = refl
linear-time (_ ∷ l₁) l₂@(_ ∷ _) (_ ∷ nop∌l₁) nops (step-with ⟶pop x₅) =
  begin
    suc _ + length l₂
  ≡⟨ cong suc $ linear-time l₁ l₂ nop∌l₁ nops
              $ ⟶-subst (cong (_ ,_) (lemma₁ l₁)) refl refl x₅ ⟩
    length (pop ∷ l₁)
  ∎
  where open ≡-Reasoning
linear-time (_ ∷ l₁) l₂@(_ ∷ _) (_ ∷ nop∌l₁) nops (step-with (⟶val {x = x}) x₅) =
  begin
    suc _ + length l₂
  ≡⟨ cong suc $ linear-time l₁ l₂ nop∌l₁ nops
              $ ⟶-subst (cong (_ ,_) (lemma₁ l₁)) refl refl x₅ ⟩
    length (val x ∷ l₁)
  ∎
  where open ≡-Reasoning

nop∌⌊⌋ᶜ : ∀ x → All (_≢ nop) ⌊ x ⌋ᶜ
nop∌⌊⌋ᶜ [] = (λ ()) ∷ []
nop∌⌊⌋ᶜ (x ∷ x₁) = (λ ()) ∷ nop∌⌊⌋ᶜ x₁

All++
    : {l₁ l₂ : List (Instr Name)}
    → All (_≢ nop) l₁
    → All (_≢ nop) l₂
    → All (_≢ nop) (l₁ ++ l₂)
All++ [] x₁ = x₁
All++ (px ∷ x) x₁ = px ∷ All++ x x₁

nop∌⌊⌋ : ∀ x → All (_≢ nop) ⌊ x ⌋
nop∌⌊⌋ [] = []
nop∌⌊⌋ (x ∷ x₁) = All++ (nop∌⌊⌋ᶜ x) (nop∌⌊⌋ x₁)


```

