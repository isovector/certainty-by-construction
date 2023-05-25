module solver2 where

module Solver {𝔸 : Set}
    (0# 1# : 𝔸)
    (_+_ _*_ : 𝔸 → 𝔸 → 𝔸)
    (let infixr 5 _+_; _+_ = _+_) (let infixr 6 _*_; _*_ = _*_) where
  open import Relation.Binary.PropositionalEquality

  module _ {A : Set} where
    open import Algebra.Definitions {A = A} _≡_ public

  postulate
    -- +-identityˡ : LeftIdentity 0# _+_
    +-identityʳ : RightIdentity 0# _+_
    -- *-identityˡ : LeftIdentity 1# _*_
    *-identityʳ : RightIdentity 1# _*_
    -- *-zeroˡ : LeftZero 0# _*_
    -- *-zeroʳ : RightZero 0# _*_
    -- +-comm : Commutative _+_
    -- *-comm : Commutative _*_
    +-assoc : Associative _+_
    -- *-assoc : Associative _*_
    *-distribˡ-+ : _*_ DistributesOverˡ _+_
    *-distribʳ-+ : _*_ DistributesOverʳ _+_

  open import Data.Nat
    using (ℕ; zero; suc)

  private variable
    n : ℕ

  data HNF : ℕ → Set where
    const : 𝔸 → HNF zero
    coeff : HNF n → HNF (suc n)
    _*x+_ : HNF (suc n) → HNF n → HNF (suc n)

  _⊕_ : HNF n → HNF n → HNF n
  const a ⊕ const b = const (a + b)
  coeff a ⊕ coeff b = coeff (a ⊕ b)
  coeff a ⊕ (b *x+ c) = b *x+ (a ⊕ c)
  (a *x+ b) ⊕ coeff c = a *x+ (b ⊕ c)
  (a *x+ b) ⊕ (c *x+ d) = (a ⊕ c) *x+ (b ⊕ d)
  infixr 5 _⊕_

  ↪ : 𝔸 → HNF n
  ↪ {zero} a = const a
  ↪ {suc n} a = coeff (↪ a)

  0H : HNF n
  0H = ↪ 0#

  1H : HNF n
  1H = ↪ 1#

  x* : HNF (suc n) → HNF (suc n)
  x* a = a *x+ 0H

  _⊗_ : HNF n → HNF n → HNF n
  const a ⊗ const b = const (a * b)
  coeff a ⊗ coeff b = coeff (a ⊗ b)
  coeff a ⊗ (b *x+ c) = (coeff a ⊗ b) *x+ (a ⊗ c)
  (a *x+ b) ⊗ coeff c = (a ⊗ coeff c) *x+ (b ⊗ c)
  (a *x+ b) ⊗ (c *x+ d)
      = x* (x* (a ⊗ c))
     ⊕ x* ((a ⊗ coeff d)
     ⊕ (c ⊗ coeff b))
     ⊕ coeff (b ⊗ d)
  infixr 6 _⊗_


  open import Data.Fin
    using (Fin; suc; zero)

  data Syn (n : ℕ) : Set where
    var : Fin n → Syn n
    con : 𝔸 → Syn n
    _:+_ : Syn n → Syn n → Syn n
    _:*_ : Syn n → Syn n → Syn n
  infixr 5 _:+_
  infixr 6 _:*_

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
  normalize (x :+ b) = normalize x ⊕ normalize b
  normalize (x :* b) = normalize x ⊗ normalize b

  eval : (Fin n → 𝔸) → HNF n → 𝔸
  eval v (const a) = a
  eval v (coeff a) = eval (v ∘ suc) a
  eval v (a *x+ b) = v zero * eval v a + eval (v ∘ suc) b

  eval-↪ : (f : Fin n → 𝔸) → (a : 𝔸) → eval f (↪ a) ≡ a
  eval-↪ {zero} f a = refl
  eval-↪ {suc n} f a = eval-↪ (f ∘ suc) a

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

  open ≡-Reasoning

  eval-coeff : (f : Fin (suc n) → 𝔸) → (h : HNF n) → eval f (coeff h) ≡ eval (f ∘ suc) h
  eval-coeff f a = refl

  eval-⊕ : (f : Fin n → 𝔸) → (a b : HNF n) → eval f (a ⊕ b) ≡ eval f a + eval f b
  eval-⊕ f (const a) (const b) = refl
  eval-⊕ f (coeff a) (coeff b) = eval-⊕ (f ∘ suc) a b
  eval-⊕ f (coeff a) (b *x+ c)
    rewrite eval-⊕ (f ∘ suc) a c = begin
      f zero * eval f b + eval f' a + eval f' c
    ≡⟨ …algebra… ⟩
      eval f' a + f zero * eval f b + eval f' c
    ∎
    where f' = f ∘ suc
  eval-⊕ f (a *x+ b) (coeff c)
    rewrite eval-⊕ (f ∘ suc) b c = sym (+-assoc _ _ _)
  eval-⊕ f (a *x+ b) (c *x+ d)
    rewrite eval-⊕ f a c
    rewrite eval-⊕ (f ∘ suc) b d = begin
      f zero * (eval f a + eval f c)
        + (eval f' b + eval f' d)
    ≡⟨ …algebra… ⟩
      (f zero * eval f a + eval f' b)
        + f zero * eval f c + eval f' d
    ∎
    where f' = f ∘ suc

  eval-x* : (f : Fin (suc n) → 𝔸) → (h : HNF (suc n)) → eval f (x* h) ≡ f zero * eval f h
  eval-x* f (coeff a) =
    begin
      f zero * eval f' a + eval f' (↪ 0#)
    ≡⟨ cong ((f zero * eval f' a) +_) (eval-↪ f' 0#) ⟩
      f zero * eval f' a + 0#
    ≡⟨ +-identityʳ _ ⟩
      f zero * eval f' a
    ∎
    where
      f' = f ∘ suc
  eval-x* f (a *x+ b) =
    begin
      f zero * (f zero * eval f a + eval f' b) + eval f' (↪ 0#)
    ≡⟨ cong (f zero * (f zero * eval f a + eval f' b) +_) (eval-↪ f' 0#) ⟩
      f zero * (f zero * eval f a + eval f' b) + 0#
    ≡⟨ +-identityʳ _ ⟩
      f zero * (f zero * eval f a + eval f' b)
    ∎
    where
      f' = f ∘ suc

  eval-⊗ : (f : Fin n → 𝔸) → (b c : HNF n) → eval f (b ⊗ c) ≡ eval f b * eval f c
  eval-⊗ f (const a) (const b) = refl
  eval-⊗ f (coeff a) (coeff b) = eval-⊗ (f ∘ suc) a b
  eval-⊗ f (coeff a) (b *x+ c)
    rewrite eval-⊗ f (coeff a) b
    rewrite eval-⊗ (f ∘ suc) a c =
      begin
        f zero * eval f' a * eval f b + eval f' a * eval f' c
      ≡⟨ …algebra… ⟩
        eval f' a * f zero * eval f b + eval f' a * eval f' c
      ≡⟨ sym (*-distribˡ-+ _ _ _) ⟩
        eval f' a * (f zero * eval f b + eval f' c)
      ∎
    where
      f' = f ∘ suc
      open ≡-Reasoning
  eval-⊗ f (a *x+ b) (coeff c)
    rewrite eval-⊗ (f ∘ suc) b c
    rewrite eval-⊗ f a (coeff c) =
      begin
        f zero * eval f a * eval f' c + eval f' b * eval f' c
      ≡⟨ …algebra… ⟩
        (f zero * eval f a) * eval f' c + eval f' b * eval f' c
      ≡⟨ sym (*-distribʳ-+ _ _ _) ⟩
        (f zero * eval f a + eval f' b) * eval f' c
      ∎
    where
      f' = f ∘ suc
      open ≡-Reasoning
  eval-⊗ f (a *x+ b) (c *x+ d) =
    begin
      v * (↓ (x* (a ⊗ c) ⊕ a ⊗ coeff d ⊕ c ⊗ coeff b)) + ↓' (↪ 0# ⊕ ↪ 0# ⊕ b ⊗ d)
    ≡⟨ …algebra… ⟩
      v * (↓ (x* (a ⊗ c) ⊕ a ⊗ coeff d ⊕ c ⊗ coeff b)) + ↓' (b ⊗ d)
    ≡⟨ …via… (eval-⊕ f) ⟩
      v * (↓ (x* (a ⊗ c)) + ↓ (a ⊗ coeff d ⊕ c ⊗ coeff b)) + ↓' (b ⊗ d)
    ≡⟨ …via… (eval-⊕ f) ⟩
      v * (↓ (x* (a ⊗ c)) + ↓ (a ⊗ coeff d) + ↓ (c ⊗ coeff b)) + ↓' (b ⊗ d)
    ≡⟨ …via… (eval-⊗ f a (coeff d)) ⟩
      v * (↓ (x* (a ⊗ c)) + ↓ a * ↓ (coeff d) + ↓ (c ⊗ coeff b)) + ↓' (b ⊗ d)
    ≡⟨ …via… (eval-coeff f d) ⟩
      v * (↓ (x* (a ⊗ c)) + ↓ a * ↓' d + ↓ (c ⊗ coeff b)) + ↓' (b ⊗ d)
    ≡⟨ …algebra… ⟩ -- …via… (eval-⊗ f c (coeff b)) ⟩
      v * (↓ (x* (a ⊗ c)) + ↓ a * ↓' d + ↓ c * ↓ (coeff b)) + ↓' (b ⊗ d)
    ≡⟨ …via… (eval-coeff f b) ⟩
      v * (↓ (x* (a ⊗ c)) + ↓ a * ↓' d + ↓ c * ↓' b) + ↓' (b ⊗ d)
    ≡⟨ …via… (eval-⊗ f' b d) ⟩
      v * (↓ (x* (a ⊗ c)) + ↓ a * ↓' d + ↓ c * ↓' b) + ↓' b * ↓' d
    ≡⟨ …via… (eval-x* f (a ⊗ c)) ⟩
      v * (v * ↓ (a ⊗ c) + ↓ a * ↓' d + ↓ c * ↓' b) + ↓' b * ↓' d
    ≡⟨ …via… (eval-⊗ f a c) ⟩
      v * (v * ↓ a * ↓ c + ↓ a * ↓' d + ↓ c * ↓' b) + ↓' b * ↓' d
    ≡⟨ …algebra… ⟩
      v * v * ↓ a * ↓ c + v * ↓ a * ↓' d + v * ↓ c * ↓' b + ↓' b * ↓' d
    ≡⟨ …algebra… ⟩
      (v * ↓ a) * (v * ↓ c) + v * ↓ a * ↓' d +  v * ↓ c * ↓' b + ↓' b * ↓' d
    ≡⟨ …algebra… ⟩
      (v * ↓ a) * (v * ↓ c)  + ↓' b * v * ↓ c   + v * ↓ a * ↓' d + ↓' b * ↓' d
    ≡⟨ …algebra… ⟩
      ((v * ↓ a) * (v * ↓ c) + ↓' b * (v * ↓ c)) + v * ↓ a * ↓' d + ↓' b * ↓' d
    ≡⟨ …algebra… ⟩
      ((v * ↓ a) * (v * ↓ c) + ↓' b * (v * ↓ c)) + (v * ↓ a * ↓' d + ↓' b * ↓' d)
    ≡⟨ …via… *-distribʳ-+ ⟩
      ((v * ↓ a) * (v * ↓ c) + ↓' b * (v * ↓ c)) + (v * ↓ a + ↓' b) * ↓' d
    ≡⟨ cong (_+ ((v * ↓ a + ↓' b) * ↓' d)) (sym (*-distribʳ-+ _ _ _)) ⟩
      (v * ↓ a + ↓' b) * (v * ↓ c) + (v * ↓ a + ↓' b) * ↓' d
    ≡⟨ sym (*-distribˡ-+ _ _ _) ⟩
      (v * ↓ a + ↓' b) * (v * ↓ c + ↓' d)
    ∎
    where
      f' = f ∘ suc
      ↓ = eval f
      ↓' = eval f'
      v = f zero


  eval-normalize : (f : Fin n → 𝔸) → (s : Syn n) → eval f (normalize s) ≡ ⟦ s ⟧ f
  eval-normalize f (var a) = eval-to-var f a
  eval-normalize f (con a) = eval-↪ f a
  eval-normalize f (s :+ s₁)
    rewrite eval-⊕ f (normalize s) (normalize s₁)
    rewrite eval-normalize f s
    rewrite eval-normalize f s₁ = refl
  eval-normalize f (s :* s₁)
    rewrite eval-⊗ f (normalize s) (normalize s₁)
    rewrite eval-normalize f s
    rewrite eval-normalize f s₁ = refl


  open import Data.Vec using (Vec; []; _∷_; map; lookup)

  fins : Vec (Fin n) n
  fins {zero} = []
  fins {suc n} = zero ∷ map suc fins

  vars : Vec (Syn n) n
  vars = map var fins

  solve₀
      : (n : ℕ)
      → (x y : Vec (Syn n) n → Syn n)
      → normalize (x vars) ≡ normalize (y vars)
      → (v : Vec 𝔸 n)
      → ⟦ x vars ⟧ (lookup v) ≡ ⟦ y vars ⟧ (lookup v)
  solve₀ n x y x=y v = begin
    ⟦ x vars ⟧ f                 ≡⟨ sym (eval-normalize f (x vars)) ⟩
    eval f (normalize (x vars))  ≡⟨ cong (eval f) x=y ⟩
    eval f (normalize (y vars))  ≡⟨ eval-normalize f (y vars) ⟩
    ⟦ y vars ⟧ f                 ∎
    where
      f = lookup v

  open import Data.Product
    using (_×_)
    renaming ( proj₁ to lhs
             ; proj₂ to rhs
             ; _,_ to _:=_
             ) public

  N-ary : (n : ℕ) → (A : Set) → (Vec A n → Set) → Set
  N-ary zero A B = B []
  N-ary (suc n) A B = (a : A) → N-ary n A (B ∘ (a ∷_))

  N-ary′ : ℕ → Set → Set → Set
  N-ary′ n A B = N-ary n A (λ _ → B)

  _$ⁿ_ : {n : ℕ} → {A : Set} → {B : Vec A n → Set} → N-ary n A B → ((v : Vec A n) → B v)
  _$ⁿ_ {zero} f [] = f
  _$ⁿ_ {suc n} f (x ∷ v) = _$ⁿ_ (f x) v

  curryⁿ : {n : ℕ} → {A : Set} → {B : Vec A n → Set} → ((v : Vec A n) → B v) → N-ary n A B
  curryⁿ {zero} x = x []
  curryⁿ {suc n} x a = curryⁿ (x ∘ (a ∷_))

  solve
      : (n : ℕ)
      → (eq : N-ary′ n (Syn n) (Syn n × Syn n))
      → (let x := y = eq $ⁿ vars {n})
      → normalize x ≡ normalize y
      → N-ary n 𝔸 (λ v → ⟦ x ⟧ (lookup v) ≡ ⟦ y ⟧ (lookup v))
  solve n eq x=y =
    let x := y = eq $ⁿ vars {n}
     in curryⁿ (solve₀ n (λ _ → x) (λ _ → y) x=y)

open import Data.Nat

open import Data.Vec using ([]; _∷_)

open Solver 0 1 _+_ _*_
open import Relation.Binary.PropositionalEquality



test : (a b : ℕ) → a * (5 * a + b) + b * b ≡ b * b + (a * 5 * a + a * b)
test a b =
  solve 2 (λ x y → x :* ((con 5 :* x) :+ y) :+ (y :* y)
                := y :* y :+ (x :* con 5) :* x :+ x :* y )
    refl a b


