```agda
open import Data.Bool
  using (Bool; true; false; not; _∨_; _∧_; _≟_)
open import Data.Nat using (ℕ; _+_; suc)
open import Data.Nat.Properties using (+-comm)
open import Data.Vec using (Vec; toList; _∷_; [])

open import Relation.Binary.Definitions using (DecidableEquality)
open import sets

-- SAT
module np-complete3 {Name : Set} (name-fin : IsFinite Name) (bs : Name → Bool) where

open import np-complete0 Name name-fin public
open import Data.Fin using (Fin; zero; suc)

open import Data.List
  using (List; _∷_; []; _++_; [_]; reverse; _∷ʳ_; map; concatMap; length)
open import Relation.Unary using (Decidable)
open import Relation.Nullary using (yes; no; ¬_; Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; module ≡-Reasoning; cong)
open import Data.Empty using (⊥-elim)

open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Agda.Primitive using (Level)

State : Set
State = Bool × Bool

⌊_⌋ᶜ : {m : ℕ} → Clause m → List Instr
⌊_⌋ᶜ ls = map val (toList ls) ∷ʳ pop

⌊⌋ᶜ-length : {m : ℕ} → (ins : Clause m) → length ⌊ ins ⌋ᶜ ≡ suc m
⌊⌋ᶜ-length [] = refl
⌊⌋ᶜ-length (x ∷ ins) rewrite ⌊⌋ᶜ-length ins = refl

⌊_⌋ : {m : ℕ} → CNF m → List Instr
⌊ [] ⌋ = []
⌊ x ∷ x₁ ⌋ = ⌊ x ⌋ᶜ ++ ⌊ x₁ ⌋

open import Data.List.Properties using (length-++)

⌊⌋-length : {sz : ℕ} → (ins : CNF sz) → length ⌊ ins ⌋ ≡ sz
⌊⌋-length [] = refl
⌊⌋-length (_∷_ {m} {n} x ins) = begin
  length ⌊ x ∷ ins ⌋              ≡⟨⟩
  length (⌊ x ⌋ᶜ ++ ⌊ ins ⌋)      ≡⟨ length-++ ⌊ x ⌋ᶜ ⟩
  length ⌊ x ⌋ᶜ + length ⌊ ins ⌋  ≡⟨ cong (_+ _) (⌊⌋ᶜ-length x) ⟩
  suc m + length ⌊ ins ⌋          ≡⟨ cong (suc m +_) (⌊⌋-length ins) ⟩
  suc m + n                       ≡⟨ cong suc (+-comm m n) ⟩
  suc (n + m)                     ∎
  where open ≡-Reasoning


open import np-complete1 using (MoveDirection; L; R; TuringMachine)

data δ : State × Instr → State × Instr × MoveDirection → Set where
  ⟶pop
      : {lo hi : Bool}
      → δ ((lo , hi)         , pop)
          ((lo ∧ hi , false) , nop , R)
  ⟶val
      : {x : Lit} {lo hi : Bool}
      → δ ((lo , hi)             , val x)
          ((lo , hi ∨ (x ↓ˡ bs)) , nop , R)

δ-deterministic
    : (qt : State × Instr)
    → {o₁ o₂ : State × Instr × MoveDirection}
    → δ qt o₁ → δ qt o₂
    → o₁ ≡ o₂
δ-deterministic (_ , pop) ⟶pop ⟶pop = refl
δ-deterministic (_ , val _) ⟶val ⟶val = refl

data Halted : State × Instr → Set where
  halted : {q : State} → Halted (q , nop)

Halted-dec : Decidable Halted
Halted-dec (_ , pop) = no λ ()
Halted-dec (_ , val x) = no λ ()
Halted-dec (_ , nop) = yes halted


open import Relation.Nullary using (¬_)

step-or-halt : (qi : State × Instr) →  ∃ (δ qi) ⊎ Halted qi
step-or-halt (q , pop) = inj₁ (_ , ⟶pop)
step-or-halt (q , val x) = inj₁ (_ , ⟶val)
step-or-halt (q , nop) = inj₂ halted

is-halted : ∀ {qi} → Halted qi → ∀ qir → ¬ δ qi qir
is-halted halted _ ()

open import Data.Product.Properties using (≡-dec)
open import Data.Bool.Properties using () renaming (_≟_ to _≟𝔹_)


δ-dec : (qi : State × Instr) → (qid : State × Instr × MoveDirection) → Dec (δ qi qid)
δ-dec _ (_ , _ , L) = no λ ()
δ-dec _ (_ , pop , _) = no λ ()
δ-dec _ (_ , (val _) , _) = no λ ()
δ-dec (_ , pop) ((_ , true) , _ , _) = no λ ()
δ-dec ((lo , hi) , pop) ((lo' , false) , nop , R)
  with lo' ≟ lo ∧ hi
... | yes refl = yes ⟶pop
... | no z = no λ { ⟶pop → ⊥-elim (z refl) }
δ-dec ((lo , hi) , val x) ((lo' , hi') , nop , R)
  with lo ≟ lo'
... | no z = no λ { ⟶val → ⊥-elim (z refl) }
... | yes refl with hi' ≟ hi ∨ (x ↓ˡ bs)
... | no z = no λ { ⟶val → ⊥-elim (z refl) }
... | yes refl = yes ⟶val
δ-dec (q , nop) _ = no λ ()

open import propisos

postulate
  δ-finite : IsFinite (∃[ qi ] ∃[ qid ] δ qi qid)

sat : TuringMachine (Instr) State
TuringMachine.δ sat = δ
TuringMachine.δ-dec sat = δ-dec
TuringMachine.δ-finite sat = δ-finite
TuringMachine.δ-deterministic sat = δ-deterministic
TuringMachine.H sat = Halted
TuringMachine.H-dec sat = Halted-dec
TuringMachine.step-or-halt sat = step-or-halt
TuringMachine.b sat = nop
TuringMachine.Q-ne-finite sat = nonempty-fin (finite-prod bool-fin bool-fin) 3 refl
TuringMachine.Γ-ne-finite sat = nonempty-fin instr-fin _ refl


open import np-complete2 sat

open import Data.Integer as ℤ using (ℤ)

mkTape : ℤ → List (Instr) → Tape
mkTape n [] = tape n [] nop []
mkTape n (r ∷ rs)  = tape n [] r rs


open import Relation.Binary.PropositionalEquality using (cong; sym)
open import Data.Bool.Properties using (∨-assoc; ∧-assoc; ∨-identityʳ; ∧-identityʳ)

lemma₁ : {n : ℤ} (rs : List (Instr)) → move R (tape n [] nop rs) ≡ mkTape (ℤ.suc n) rs
lemma₁ [] = refl
lemma₁ (x ∷ rs) = refl

open import Data.Nat.Properties
open import Data.List.Properties
import Data.Integer.Properties as ℤ

ℤ-+-suc : ∀ x y → x ℤ.+ (ℤ.suc y) ≡ ℤ.suc x ℤ.+ y
ℤ-+-suc x y =
  begin
    x ℤ.+ (ℤ.+ 1 ℤ.+ y)
  ≡⟨ ℤ.+-comm x _ ⟩
    (ℤ.+ 1 ℤ.+ y) ℤ.+ x
  ≡⟨ ℤ.+-assoc (ℤ.+ 1) y x ⟩
    ℤ.+ 1 ℤ.+ (y ℤ.+ x)
  ≡⟨ cong (ℤ._+_ (ℤ.+ 1)) (ℤ.+-comm y x) ⟩
    ℤ.+ 1 ℤ.+ (x ℤ.+ y)
  ≡⟨ sym (ℤ.+-assoc (ℤ.+ 1) x y) ⟩
    ℤ.suc x ℤ.+ y
  ∎
  where open ≡-Reasoning

equivClause
    : {m : ℕ}
    → (n : ℤ)
    → (lo hi : Bool)
    → (rs : List (Instr))
    → (cl : Clause m)
    → ((lo , hi) , mkTape n (⌊ cl ⌋ᶜ ++ rs)) -⟨ length ⌊ cl ⌋ᶜ ⟩→
      ( (lo ∧ (hi ∨ (cl ↓ᶜ bs)) , false)
      , mkTape (ℤ.+ length ⌊ cl ⌋ᶜ ℤ.+ n) rs
      )
equivClause n lo hi rs [] =
  begin
    (lo , hi) , mkTape _ (pop ∷ rs)
  ≈⟨ step ⟶pop ⟩
    (lo ∧ hi , false) , move R (tape _ [] nop rs)
  ≡⟨ cong (_ ,_) (lemma₁ rs) ⟩
    (lo ∧ hi , false) , mkTape _ rs
  ≡⟨ cong (λ φ → (lo ∧ φ , false) , _) (sym (∨-identityʳ hi)) ⟩
    (lo ∧ (hi ∨ false) , false) , _
  ∎
  where open ⟶-Reasoning
equivClause n lo hi rs (x ∷ xs) =
  begin
    (lo , hi) , mkTape _ (⌊ x ∷ xs ⌋ᶜ ++ rs)
  ≡⟨⟩
    (lo , hi) , tape _ [] (val x) ((map val (toList xs) ++ (pop ∷ [])) ++ rs)
  ≡ᵀ⟨ +-comm (length ⌊ xs ⌋ᶜ) 1 ⟩
    _
  ≈⟨ step ⟶val ⟩
    (lo , hi ∨ (x ↓ˡ bs)) , move R (tape _ [] nop (⌊ xs ⌋ᶜ ++ rs))
  ≡⟨ cong (_ ,_) (lemma₁ (⌊ xs ⌋ᶜ ++ rs)) ⟩
    (lo , hi ∨ (x ↓ˡ bs)) , mkTape _ (⌊ xs ⌋ᶜ ++ rs)
  ≈⟨ equivClause _ lo (hi ∨ (x ↓ˡ bs)) rs xs ⟩
    (lo ∧ ((hi ∨ (x ↓ˡ bs)) ∨ (xs ↓ᶜ bs)) , false) , mkTape _ rs
  ≡⟨ cong (λ φ → (lo ∧ φ , false) , mkTape _ rs) (∨-assoc hi (x ↓ˡ bs) (xs ↓ᶜ bs)) ⟩
    _ , mkTape (ℤ.+ length ⌊ xs ⌋ᶜ ℤ.+ ℤ.suc n) rs
  ≡⟨ cong (λ φ → _ , mkTape φ rs) (ℤ-+-suc (ℤ.+ length ⌊ xs ⌋ᶜ) n) ⟩
    _ , mkTape (ℤ.+ length ⌊ x ∷ xs ⌋ᶜ ℤ.+ n) rs
  ∎
  where open ⟶-Reasoning

open import Function using (flip; _$_; _∘_)

equiv
    : {m : ℕ} → (n : ℤ)
    → (lo : Bool)
    → (cnf : CNF m)
    → HaltsWith ((lo , false) , mkTape n ⌊ cnf ⌋)
                ((lo ∧ (cnf ↓ bs)) , false)
                (length ⌊ cnf ⌋)
equiv n lo [] = flip (halts-with _) halted $
  begin
    (lo , false) , mkTape _ ⌊ [] ⌋
  ≡⟨ cong (λ φ → (φ , _) , _) (sym (∧-identityʳ lo)) ⟩
    (lo ∧ true , false) , mkTape _ ⌊ [] ⌋
  ∎
  where open ⟶-Reasoning
equiv n lo (x ∷ cnf)
  = subst-halts refl refl (sym (length-++ ⌊ x ⌋ᶜ))
  $ halts-glue
      ( begin
          (lo , false) , mkTape _ ⌊ x ∷ cnf ⌋
        ≡⟨⟩
          (lo , false) , mkTape _ (⌊ x ⌋ᶜ ++ ⌊ cnf ⌋)
        ≈⟨ equivClause n lo false ⌊ cnf ⌋ x ⟩
          (lo ∧ (x ↓ᶜ bs) , false) , mkTape _ ⌊ cnf ⌋
        ∎
      )
  $ subst-halts
      refl
      (cong (_, false) (∧-assoc lo ((x ↓ᶜ bs)) ((cnf ↓ bs))))
      refl
      (equiv _ (lo ∧ (x ↓ᶜ bs)) cnf)
  where open ⟶-Reasoning

DONE : {m : ℕ} → (cnf : CNF m)
     → HaltsWith ((true , false) , mkTape ℤ.0ℤ ⌊ cnf ⌋)
                 ((cnf ↓ bs)     , false)
                 (length ⌊ cnf ⌋)
DONE = equiv _ true

open import np-complete5

open InNP

SAT : ℕ → Set
SAT = CNF

SAT-in-NP : InNP SAT
Γ SAT-in-NP = _
Q SAT-in-NP = _
tm SAT-in-NP = sat
compile SAT-in-NP ins = (true , false) , mkTape ℤ.0ℤ ⌊ ins ⌋
runtime SAT-in-NP sz = sz
runtime-poly SAT-in-NP sz = poly-refl
verify SAT-in-NP {sz} ins
  = ((ins ↓ bs) , false)
  , subst (HaltsWith _ _) (⌊⌋-length ins) (DONE ins)

```

