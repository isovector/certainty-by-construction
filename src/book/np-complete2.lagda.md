```agda
open import np-complete1
open import Data.Product
open import Relation.Nullary using (¬_; yes; no; does)
open import Relation.Unary using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Sum

-- turing-machines
module np-complete2 {Γ Q : Set} (tm : TuringMachine Γ Q) where

open TuringMachine tm

open Tapes b _≟Γ_ public


moveWrite : MoveDirection → Γ → Tape → Tape
moveWrite d i t = move d (write i t)


open import Data.Nat using (ℕ; _+_; suc; _≤_; z≤n; s≤s)

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

record HaltsWith' (H : Q × Γ → Set) (qt : Q × Tape) (q : Q) (n : ℕ) : Set where
  constructor halts-with
  field
    final-tape : Tape
    arr        : qt -⟨ n ⟩→ (q , final-tape)
    is-halted  : H (q , Tape.head final-tape)

open import Function using (_∘_)

HaltsWith   = HaltsWith' H
AcceptsWith = HaltsWith' Accept
RejectsWith = HaltsWith' Reject

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

module Properties where
  open import Data.Sum

  n⊃q
    : (qt : Q × Tape)
    → (n : ℕ)
    → (∃[ q' ] ∃[ m ] HaltsWith qt q' m × m ≤ n)
    ⊎ (∃[ qt' ] qt -⟨ n ⟩→ qt')
  n⊃q (q , t) n with step-or-halt (q , Tape.head t)
  ... | inj₂ y = inj₁ (q , 0 , halts-with t refl y , z≤n)
  n⊃q (q , t) ℕ.zero | inj₁ ((q' , i , d) , delta) =
    inj₂ ((q , t) , refl)
  n⊃q (q , t) (suc n) | inj₁ ((q' , i , d) , delta)
    with n⊃q (q' , moveWrite d i t ) n
  ... | inj₁ (q0 , n' , hw , n'≤n) =
    inj₁ (q0 , suc n' , halts-glue (step delta) hw , s≤s n'≤n)
  ... | inj₂ (y , arr) =
    inj₂ (y , step-with delta arr)

  final-qt
    : Q × Tape
    → ℕ
    → Q × Tape
  final-qt qt₀ n with n⊃q qt₀ n
  ... | inj₁ (q , _ , halts-with t _ _ , _) = (q , t)
  ... | inj₂ (qt , _) = qt

  open import Data.Bool

  q-at-t-is : Q × Tape → ℕ → Q → Bool
  q-at-t-is qt n q? = does (q? ≟Q proj₁ (final-qt qt n))

  open import Data.Integer as ℤ using (ℤ)
  import Data.Integer.Properties as ℤ

  pos-at-t-is : Q × Tape → ℕ → ℤ → Bool
  pos-at-t-is qt n pos? = does (pos? ℤ.≟ Tape.index (proj₂ (final-qt qt n)))

  cell-at-t-is : Q × Tape → ℕ → ℤ → Γ → Bool
  cell-at-t-is qt n cell i? = does (i? ≟Γ read cell (proj₂ (final-qt qt n)))


```


