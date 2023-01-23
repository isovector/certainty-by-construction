```agda
open import np-complete1
open import Data.Product
open import Relation.Nullary using (¬_)
open import Relation.Unary using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_)

-- turing-machines
module np-complete2
  (Γ Q : Set)
  (δ : Q × Γ → Q × Γ × MoveDirection → Set)
  (H : Q × Γ → Set)
  (halted : {qi : Q × Γ} → H qi → (qir : Q × Γ × MoveDirection) → ¬ δ qi qir)
  (b : Γ)
  (b-dec : Decidable (_≡ b))
  where

open Tapes Γ b b-dec public

moveWrite : MoveDirection → Γ → Tape → Tape
moveWrite d i t = move d (write i t)


open import Data.Nat using (ℕ; _+_; suc)

data _-⟨_⟩→_ : Q × Tape → ℕ → Q × Tape → Set where
  refl
      : {qt : Q × Tape}
      → qt -⟨ 0 ⟩→ qt
  step-with
      : {i : Γ} {d : MoveDirection} {q₁ q₂ : Q} {t : Tape} {n : ℕ} {qt₃ : Q × Tape}
      → δ (q₁ , Tape.head t) (q₂ , i , d)
      → (q₂ , moveWrite d i t) -⟨ n ⟩→ qt₃
      → (q₁ , t) -⟨ suc n ⟩→ qt₃
open _-⟨_⟩→_

open import Data.Nat.Properties

trans : {qt₁ qt₂ qt₃ : Q × Tape} {n₁ n₂ : ℕ}
      → qt₁ -⟨ n₁ ⟩→ qt₂
      → qt₂ -⟨ n₂ ⟩→ qt₃
      → qt₁ -⟨ n₂ + n₁ ⟩→ qt₃
trans {n₂ = n₂} refl a₂ rewrite +-identityʳ n₂ = a₂
trans {n₂ = n₂} (step-with {n = n} x a₁) a₂ rewrite +-suc n₂ n =
  step-with x (trans a₁ a₂)

step : {i : Γ} {d : MoveDirection} {q₁ q₂ : Q} {t : Tape}
      → δ (q₁ , Tape.head t) (q₂ , i , d)
      → (q₁ , t) -⟨ 1 ⟩→ (q₂ , moveWrite d i t)
step x = step-with x refl

_⟶_ : Q × Tape → Q × Tape → Set
_⟶_ qt₁ qt₂ = ∀ {n : ℕ} → qt₁ -⟨ n ⟩→ qt₂


open import Relation.Binary.PropositionalEquality using (_≡_; refl)

⟶-subst
    : {qt₁ qt₁' qt₂ qt₂' : Q × Tape}
    → {n n' : ℕ}
    → qt₁ ≡ qt₁'
    → n ≡ n'
    → qt₂ ≡ qt₂'
    → qt₁ -⟨ n ⟩→ qt₂
    → qt₁' -⟨ n' ⟩→ qt₂'
⟶-subst refl refl refl x = x

record HaltsWith (qt : Q × Tape) (q : Q) (n : ℕ) : Set where
  constructor halts-with
  field
    final-tape : Tape
    arr : qt -⟨ n ⟩→ (q , final-tape)
    is-halted : H (q , Tape.head final-tape)

subst-halts
  : {qt qt' : Q × Tape} {q q' : Q} {n n' : ℕ}
  → qt ≡ qt'
  → q ≡ q'
  → n ≡ n'
  → HaltsWith qt q n
  → HaltsWith qt' q' n'
subst-halts refl refl refl x = x

halts-glue
  : {qt₁ qt₂ : Q × Tape} {q : Q} {n₁ n₂ : ℕ}
  → qt₁ -⟨ n₁ ⟩→ qt₂
  → HaltsWith qt₂ q n₂
  → HaltsWith qt₁ q (n₁ + n₂)
halts-glue {n₁ = n₁} {n₂} x₁ (halts-with t x₂ h)
  = subst-halts refl refl (+-comm n₂ n₁)
   (halts-with t (trans x₁ x₂) h)

module ⟶-Reasoning where
  begin_ : ∀ {qt₁ qt₂ n}
         → qt₁ -⟨ n ⟩→ qt₂
         → qt₁ -⟨ n ⟩→ qt₂
  begin_ x = x

  _≈⟨_⟩_ : ∀ {qt₂ qt₃ n₁ n₂}
         → (qt₁ : _)
         → qt₁ -⟨ n₁ ⟩→ qt₂
         → qt₂ -⟨ n₂ ⟩→ qt₃
         → qt₁ -⟨ n₂ + n₁ ⟩→ qt₃
  _≈⟨_⟩_ _ r a = trans r a

  _≡⟨_⟩_ : ∀ {qt₂ qt₃ n}
         → (qt₁ : _)
         → qt₁ ≡ qt₂
         → qt₂ -⟨ n ⟩→ qt₃
         → qt₁ -⟨ n ⟩→ qt₃
  _≡⟨_⟩_ _ refl a = a

  _≡ᵀ⟨_⟩_ : ∀ {qt₂ n₁ n₂}
         → (qt₁ : _)
         → n₁ ≡ n₂
         → qt₁ -⟨ n₁ ⟩→ qt₂
         → qt₁ -⟨ n₂ ⟩→ qt₂
  _≡ᵀ⟨_⟩_ _ refl a = a

  _≡⟨⟩_ : ∀ {qt₂ n}
         → (qt₁ : _)
         → qt₁ -⟨ n ⟩→ qt₂
         → qt₁ -⟨ n ⟩→ qt₂
  _≡⟨⟩_ _ a = a

  _∎ : ∀ qt
     → qt -⟨ 0 ⟩→ qt
  _∎ _ = refl

  infix  1 begin_
  infixr 2 _≈⟨_⟩_ _≡⟨⟩_ _≡⟨_⟩_ _≡ᵀ⟨_⟩_
  infix  3 _∎




  -- open import Relation.Binary.Reasoning.Base.Single _⟶_
  --     (λ {z} → refl {z})
  --     ?
  --     as Base public
  --   hiding (step-∼)

  -- infixr 2 step-≈

  -- step-≈ = Base.step-∼
  -- syntax step-≈ x y≈z x≈y = x ≈⟨ x≈y ⟩ y≈z
```


