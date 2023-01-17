module playground.TNT where


open import Agda.Primitive

import Data.Nat renaming (ℕ to Var; zero to a)
open Data.Nat using (Var; a; suc)

_′ : Var → Var
_′ = suc

infixl 10 _′

open import Function using (flip; _∘_; id)
open import Data.Bool using (true)
open import Relation.Binary.PropositionalEquality

private variable
  v v₁ v₂ v₃ : Var

data Term : Set where
  O : Term
  S : Term → Term
  _+_ : Term → Term → Term
  _*_ : Term → Term → Term
  var : Var → Term

infixr 1 ~_
infix 3 _≈_


data String : Set where
  term : Term → String
  _≈_ : Term → Term → String
  ~_ : String → String
  _∧_ : String → String → String
  _∨_ : String → String → String
  _⊃_ : String → String → String
  Exists : String → String
  Forall : String → String

private variable
  u t t₁ t₂ t₃ : Term
  s s₁ s₂ s₃ : String

appT : Term → (Var → Term) → Term
appT O f = O
appT (S x) f = S (appT x f)
appT (x + y) f = (appT x f) + (appT y f)
appT (x * y) f = (appT x f) * (appT y f)
appT (var v) f = f v

app : String → (Var → Term) → String
app (term x) f = term (appT x f)
app ((x ≈ y)) f = (appT x f) ≈ (appT y f)
app ((~ x)) f = ~ (app x f)
app ((x ∧ y)) f = (app x f) ∧ (app y f)
app ((x ∨ y)) f = (app x f) ∨ (app y f)
app ((x ⊃ y)) f = (app x f) ⊃ (app y f)
app (Exists x) f = Exists (app x f)
app (Forall x) f = Forall (app x f)

_/_ : String → Term → String
x / u = app x λ { a → u
                ; (suc x) → var x
                }

vsuc : String → String
vsuc s = app s (var ∘ suc)

{-# NO_POSITIVITY_CHECK #-}
data Deriv : String → Set where
  axiom1 : Deriv (Forall (~ S (var a) ≈ O))
  axiom2 : Deriv (Forall ((var a + O) ≈ var a))
  axiom3 : Deriv (Forall (Forall (var a + S (var (a ′)) ≈ S (var a + var (a ′)))))
  axiom4 : Deriv (Forall (var a * O ≈ O))
  axiom5 : Deriv (Forall (Forall (var a * S (var (a ′)) ≈ (var a * var (a ′)) + var a)))
  specify : Deriv (Forall s) → (u : Term) → Deriv (s / u)
  generalize : Deriv s → Deriv (vsuc s)
  interchange₁ : Deriv (Forall (~ s)) → Deriv (~ (Exists s))
  interchange₂ : Deriv (~ (Exists s)) → Deriv (Forall (~ s))
  symmetry : Deriv (t₁ ≈ t₂) → Deriv (t₂ ≈ t₁)
  transitivity : Deriv (t₁ ≈ t₂) → Deriv (t₂ ≈ t₃) → Deriv (t₁ ≈ t₃)
  add-s : Deriv (t₁ ≈ t₂) → Deriv (S t₁ ≈ S t₂)
  drop-s : Deriv (S t₁ ≈ S t₂) → Deriv (t₁ ≈ t₂)
  premise : (Deriv s₁ → Deriv s₂) → Deriv (s₁ ⊃ s₂)
  apply : Deriv ((s₁ ⊃ s₂) ∧ s₁) → Deriv s₂




_ : Deriv (~ S O ≈ O)
_ = specify axiom1 O

_ : Deriv (S O + S O ≈ S (S O))
_ = transitivity (specify (specify axiom3 (S O)) O) (add-s (specify axiom2 (S O)))

b = a ′

_ : Deriv ((O + var b ≈ var b) ⊃ (O + S (var b) ≈ S (var b)))
_ = premise λ p →
  let ⟨3⟩ = specify (specify axiom3 O) (var b)
      ⟨6⟩ = add-s p
   in transitivity ⟨3⟩ ⟨6⟩

