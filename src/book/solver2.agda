module solver2 (𝔸 : Set) where

open import Relation.Binary.PropositionalEquality

module _ {A : Set} where
  open import Algebra.Definitions {A = A} _≡_ public

postulate
  0# 1# : 𝔸
  _+_ _*_ : 𝔸 → 𝔸 → 𝔸
  +-identityˡ : LeftIdentity 0# _+_
  +-identityʳ : RightIdentity 0# _+_
  *-identityˡ : LeftIdentity 1# _*_
  *-identityʳ : RightIdentity 1# _*_
  *-zeroˡ : LeftZero 0# _*_
  *-zeroʳ : RightZero 0# _*_
  +-comm : Commutative _+_
  *-comm : Commutative _*_
  +-assoc : Associative _+_
  *-assoc : Associative _*_
  *-distribˡ-+ : _*_ DistributesOverˡ _+_
  *-distribʳ-+ : _*_ DistributesOverʳ _+_

infixr 5 _+_
infixr 6 _*_

open import Data.Nat
  using (ℕ; zero; suc)

private variable
  n : ℕ

data HNF : ℕ → Set where
  const : 𝔸 → HNF zero
  coeff : HNF n → HNF (suc n)
  _*x+_ : HNF (suc n) → HNF n → HNF (suc n)

_+H_ : HNF n → HNF n → HNF n
const x +H const x₁ = const (x + x₁)
coeff x +H coeff x₁ = coeff (x +H x₁)
coeff x +H (x₁ *x+ x₂) = x₁ *x+ (x +H x₂)
(x *x+ x₁) +H coeff x₂ = x *x+ (x₁ +H x₂)
(x *x+ x₁) +H (x₂ *x+ x₃) = (x +H x₂) *x+ (x₁ +H x₃)
infixr 5 _+H_

↪ : 𝔸 → HNF n
↪ {zero} x = const x
↪ {suc n} x = coeff (↪ x)

0H : HNF n
0H = ↪ 0#

1H : HNF n
1H = ↪ 1#

x* : HNF (suc n) → HNF (suc n)
x* x = x *x+ 0H

_*H_ : HNF n → HNF n → HNF n
const x *H const x₁ = const (x * x₁)
coeff x *H coeff x₁ = coeff (x *H x₁)
coeff x *H (x₁ *x+ x₂) = (coeff x *H x₁) *x+ (x *H x₂)
(x *x+ x₁) *H coeff x₂ = (x *H coeff x₂) *x+ (x₁ *H x₂)
(x *x+ x₁) *H (x₂ *x+ x₃) = x* (x* (x *H x₂)) +H x* ((x *H coeff x₃) +H (x₂ *H coeff x₁)) +H coeff (x₁ *H x₃)
infixr 6 _*H_


open import Data.Fin
  using (Fin; suc; zero)

data Syn (n : ℕ) : Set where
  var : Fin n → Syn n
  con : 𝔸 → Syn n
  _:+_ : Syn n → Syn n → Syn n
  _:*_ : Syn n → Syn n → Syn n

⟦_⟧ : Syn n → (Fin n → 𝔸) → 𝔸
⟦ var v ⟧  vs = vs v
⟦ con c ⟧  vs = c
⟦ x :+ y ⟧ vs = ⟦ x ⟧ vs + ⟦ y ⟧ vs
⟦ x :* y ⟧ vs = ⟦ x ⟧ vs * ⟦ y ⟧ vs

open import Function using (_∘_)

to-var : Fin n → HNF n
to-var zero = x* 1H
to-var (suc x) = coeff (to-var x)

normalize : Syn n → HNF n
normalize (var x) = to-var x
normalize (con x) = ↪ x
normalize (x :+ x₁) = normalize x +H normalize x₁
normalize (x :* x₁) = normalize x *H normalize x₁

eval : (Fin n → 𝔸) → HNF n → 𝔸
eval v (const x) = x
eval v (coeff x) = eval (v ∘ suc) x
eval v (x *x+ x₁) = v zero * eval v x + eval (v ∘ suc) x₁

eval-↪ : (f : Fin n → 𝔸) → (x : 𝔸) → eval f (↪ x) ≡ x
eval-↪ {zero} f x = refl
eval-↪ {suc n} f x = eval-↪ (f ∘ suc) x

eval-to-var : (f : Fin n → 𝔸) → (x : Fin n) → eval f (to-var x) ≡ f x
eval-to-var f zero
  rewrite eval-↪ (f ∘ suc) 0#
  rewrite eval-↪ (f ∘ suc) 1#
  rewrite *-identityʳ (f zero)
    = +-identityʳ (f zero)
eval-to-var f (suc x) = eval-to-var (f ∘ suc) x

postulate
  …algebra… : {x y : 𝔸} → x ≡ y
  …via… : {B : Set} {x y : 𝔸} → B → x ≡ y

+-hom : (f : Fin n → 𝔸) → (h₁ h₂ : HNF n) → eval f (h₁ +H h₂) ≡ eval f h₁ + eval f h₂
+-hom f (const x) (const x₁) = refl
+-hom f (coeff h₁) (coeff h₂) = +-hom (f ∘ suc) h₁ h₂
+-hom f (coeff h₁) (h₂ *x+ h₃)
  rewrite +-hom (f ∘ suc) h₁ h₃
    = begin
      f zero * eval f h₂ + eval f' h₁ + eval f' h₃
    ≡⟨ …algebra… ⟩
      eval f' h₁ + f zero * eval f h₂ + eval f' h₃
    ∎
  where
    f' = f ∘ suc
    open ≡-Reasoning
+-hom f (h₁ *x+ h₂) (coeff h₃)
  rewrite +-hom (f ∘ suc) h₂ h₃ = sym (+-assoc _ _ _)
+-hom f (h₁ *x+ h₂) (h₃ *x+ h₄)
  rewrite +-hom f h₁ h₃
  rewrite +-hom (f ∘ suc) h₂ h₄ = begin
      f zero * (eval f h₁ + eval f h₃)
        + (eval f' h₂ + eval f' h₄)
    ≡⟨ …algebra… ⟩
      (f zero * eval f h₁ + eval f' h₂)
        + f zero * eval f h₃ + eval f' h₄
    ∎
  where
    f' = f ∘ suc
    open ≡-Reasoning

*-hom : (f : Fin n → 𝔸) → (h₁ h₂ : HNF n) → eval f (h₁ *H h₂) ≡ eval f h₁ * eval f h₂
*-hom f (const x) (const x₁) = refl
*-hom f (coeff h₁) (coeff h₂) = *-hom (f ∘ suc) h₁ h₂
*-hom f (coeff h₁) (h₂ *x+ h₃)
  rewrite *-hom f (coeff h₁) h₂
  rewrite *-hom (f ∘ suc) h₁ h₃ =
    begin
      f zero * eval f' h₁ * eval f h₂ + eval f' h₁ * eval f' h₃
    ≡⟨ …algebra… ⟩
      eval f' h₁ * f zero * eval f h₂ + eval f' h₁ * eval f' h₃
    ≡⟨ sym (*-distribˡ-+ _ _ _) ⟩
      eval f' h₁ * (f zero * eval f h₂ + eval f' h₃)
    ∎
  where
    f' = f ∘ suc
    open ≡-Reasoning
*-hom f (h₁ *x+ h₂) (coeff h₃)
  rewrite *-hom (f ∘ suc) h₂ h₃
  rewrite *-hom f h₁ (coeff h₃) =
    begin
      f zero * eval f h₁ * eval f' h₃ + eval f' h₂ * eval f' h₃
    ≡⟨ …algebra… ⟩
      (f zero * eval f h₁) * eval f' h₃ + eval f' h₂ * eval f' h₃
    ≡⟨ sym (*-distribʳ-+ _ _ _) ⟩
      (f zero * eval f h₁ + eval f' h₂) * eval f' h₃
    ∎
  where
    f' = f ∘ suc
    open ≡-Reasoning
-- TODO(sandy):
*-hom f (h₁ *x+ h₂) (h₃ *x+ h₄) = …algebra…


eval-norm : (f : Fin (n) → 𝔸) → (s : Syn n) → eval f (normalize s) ≡ ⟦ s ⟧ f
eval-norm f (var x) = eval-to-var f x
eval-norm f (con x) = eval-↪ f x
eval-norm f (s :+ s₁)
  rewrite +-hom f (normalize s) (normalize s₁)
  rewrite eval-norm f s
  rewrite eval-norm f s₁ = refl
eval-norm f (s :* s₁)
  rewrite *-hom f (normalize s) (normalize s₁)
  rewrite eval-norm f s
  rewrite eval-norm f s₁ = refl


open import Data.Vec using (Vec; []; _∷_; map; lookup)

fins : Vec (Fin n) n
fins {zero} = []
fins {suc n} = zero ∷ map suc fins

vars : Vec (Syn n) n
vars = map var fins

solve
    : (n : ℕ)
    → (x y : Vec (Syn n) n → Syn n)
    → (v : Vec 𝔸 n)
    → normalize (x vars) ≡ normalize (y vars)
    → ⟦ x vars ⟧ (lookup v) ≡ ⟦ y vars ⟧ (lookup v)
solve n x y v x=y = begin
  ⟦ x vars ⟧ f                 ≡⟨ sym (eval-norm f (x vars)) ⟩
  eval f (normalize (x vars))  ≡⟨ cong (eval f) x=y ⟩
  eval f (normalize (y vars))  ≡⟨ eval-norm f (y vars) ⟩
  ⟦ y vars ⟧ f                 ∎
  where
    f = lookup v
    open ≡-Reasoning

