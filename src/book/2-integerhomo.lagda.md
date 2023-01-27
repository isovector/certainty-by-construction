```agda
{-# OPTIONS --allow-unsolved-metas #-}
module 2-integerhomo where

import Data.Nat as Nat
open Nat using (ℕ; zero; suc) renaming (_+_ to _ℕ+_)
import Data.Nat.Properties as Nat
open import Data.Product hiding (swap)
open import Data.Sum hiding (map₁; map; map₂; swap)
open import 2-numbers
open Sandbox-Integers hiding (_+_; _*_; suc)
open import Relation.Binary.PropositionalEquality
open import Function



toℕ×ℕ : ℤ → ℕ × ℕ
toℕ×ℕ (+ x) = x , 0
toℕ×ℕ -[1+ x ] = 0 , suc x

fromℕ×ℕ : ℕ × ℕ → ℤ
fromℕ×ℕ (p , zero) = + p
fromℕ×ℕ (zero , suc n) = -[1+ n ]
fromℕ×ℕ (suc p , suc n) = fromℕ×ℕ (p , n)

fromℕ×ℕ-suc : (xp xn : ℕ) → fromℕ×ℕ (suc xp , suc xn) ≡ fromℕ×ℕ (xp , xn)
fromℕ×ℕ-suc zero xn = refl
fromℕ×ℕ-suc (suc xp) zero = refl
fromℕ×ℕ-suc (suc xp) (suc xn) = refl

fromℕ×ℕ-zeroˡ : (xn : ℕ) → fromℕ×ℕ (zero , suc xn) ≡ -[1+ xn ]
fromℕ×ℕ-zeroˡ xn = refl

fromℕ×ℕ-zeroʳ : (xp : ℕ) → fromℕ×ℕ (xp , zero) ≡ + xp
fromℕ×ℕ-zeroʳ xp = refl

data _≈_ : ℕ × ℕ → ℕ × ℕ → Set where
  equiv : {xp xn yp yn : ℕ} → xp Nat.+ yn ≡ yp Nat.+ xn → (xp , xn) ≈ (yp , yn)

module _ where
  private variable
    x y z w : ℕ × ℕ

  ≈-refl : x ≈ x
  ≈-refl = equiv refl

  ≈-sym : x ≈ y → y ≈ x
  ≈-sym (equiv x=y) = equiv (sym x=y)

  ≈-trans : x ≈ y → y ≈ z → x ≈ z
  ≈-trans (equiv {xp} {xn} {yp} {yn} x=y) (equiv {.yp} {.yn} {zp} {zn} y=z)
    = equiv
    $ Nat.+-cancelˡ-≡ yp
    $ Nat.+-cancelˡ-≡ yn
    $ begin
    yn ℕ+ (yp ℕ+ (xp ℕ+ zn))  ≡⟨ swap yn xp zn ⟩
    zn ℕ+ (yp ℕ+ (xp ℕ+ yn))  ≡⟨ cong (λ φ → zn ℕ+ (yp ℕ+ φ)) x=y ⟩
    zn ℕ+ (yp ℕ+ (yp ℕ+ xn))  ≡⟨ swap zn yp xn ⟩
    xn ℕ+ (yp ℕ+ (yp ℕ+ zn))  ≡⟨ cong (λ φ → xn ℕ+ (yp ℕ+ φ)) y=z ⟩
    xn ℕ+ (yp ℕ+ (zp ℕ+ yn))  ≡⟨ swap xn zp yn ⟩
    yn ℕ+ (yp ℕ+ (zp ℕ+ xn))  ∎
    where
      open ≡-Reasoning

      swap : (i j k : ℕ) → i ℕ+ (yp ℕ+ (j ℕ+ k)) ≡ k ℕ+ (yp ℕ+ (j ℕ+ i))
      swap i j k = begin
        i ℕ+ (yp ℕ+ (j ℕ+ k))  ≡⟨ cong (i ℕ+_) (sym (Nat.+-assoc yp j k)) ⟩
        i ℕ+ ((yp ℕ+ j) ℕ+ k)  ≡⟨ cong (i ℕ+_) (Nat.+-comm (yp ℕ+ j) k) ⟩
        i ℕ+ (k ℕ+ (yp ℕ+ j))  ≡⟨ sym (Nat.+-assoc i k (yp ℕ+ j)) ⟩
        (i ℕ+ k) ℕ+ (yp ℕ+ j)  ≡⟨ cong (_ℕ+ (yp ℕ+ j)) (Nat.+-comm i k) ⟩
        (k ℕ+ i) ℕ+ (yp ℕ+ j)  ≡⟨ Nat.+-assoc k i (yp ℕ+ j) ⟩
        k ℕ+ (i ℕ+ (yp ℕ+ j))  ≡⟨ cong (k ℕ+_) (sym (Nat.+-comm (yp ℕ+ j) i)) ⟩
        k ℕ+ ((yp ℕ+ j) ℕ+ i)  ≡⟨ cong (k ℕ+_) (Nat.+-assoc yp j i) ⟩
        k ℕ+ (yp ℕ+ (j ℕ+ i))  ∎

  open import Relation.Binary.Bundles
  open import Agda.Primitive
  open import Relation.Binary.Structures

  ≈-setoid : Setoid lzero lzero
  Setoid.Carrier ≈-setoid = ℕ × ℕ
  Setoid._≈_ ≈-setoid = _≈_
  IsEquivalence.refl (Setoid.isEquivalence ≈-setoid) = ≈-refl
  IsEquivalence.sym (Setoid.isEquivalence ≈-setoid) = ≈-sym
  IsEquivalence.trans (Setoid.isEquivalence ≈-setoid) = ≈-trans

  module ≈-Reasoning where
    open import Relation.Binary.Reasoning.Setoid ≈-setoid public


  ≈-suc-inj : map suc suc x ≈ x
  ≈-suc-inj {fst , snd} = equiv (sym (Nat.+-suc fst snd))

  ≈-suc-injˡ : x ≈ y → map suc id x ≈ map suc id y
  ≈-suc-injˡ {fst , snd} z = equiv ?

  ≈-suc-injʳ : x ≈ y → map id suc x ≈ map id suc y
  ≈-suc-injʳ {fst , snd} z = equiv ?

  ≈-cong-+ : x ≈ y → z ≈ w → (proj₁ x ℕ+ proj₁ z , proj₂ x ℕ+ proj₂ z) ≈ (proj₁ y ℕ+ proj₁ w , proj₂ y ℕ+ proj₂ w)
  ≈-cong-+ (equiv {xp} {xn} {yp} {yn} x=y) (equiv {zp} {zn} {wp} {wn} z=w) = equiv {! !}

  record Same (ff : ℕ × ℕ → ℕ × ℕ → ℕ × ℕ) : Set where
    field
      f : ℕ → ℕ → ℕ
      proof : (xp xn yp yn : ℕ) → (f xp yp , f yp yn) ≡ ff (xp , xn) (yp , yn)


  -- topbot₂ : (f : ℕ → ℕ → ℕ) → f (posof x) (posof y) ≈ posof z → f (negof x) (negof y) ≈ negof z →

module _ where
  private variable
    x y z w : ℤ

  infix 2 _≋_
  data _≋_ : ℤ → ℤ → Set where
    equiv : toℕ×ℕ x ≈ toℕ×ℕ y → x ≋ y

  ≋-refl : x ≋ x
  ≋-refl = equiv ≈-refl

  ≋-sym : x ≋ y → y ≋ x
  ≋-sym (equiv xy) = equiv (≈-sym xy)

  ≋-trans : x ≋ y → y ≋ z → x ≋ z
  ≋-trans (equiv xy) (equiv yz) = equiv (≈-trans xy yz)

  open import Relation.Binary.Bundles
  open import Agda.Primitive
  open import Relation.Binary.Structures

  ≋-setoid : Setoid lzero lzero
  Setoid.Carrier ≋-setoid = ℤ
  Setoid._≈_ ≋-setoid = _≋_
  IsEquivalence.refl (Setoid.isEquivalence ≋-setoid) = ≋-refl
  IsEquivalence.sym (Setoid.isEquivalence ≋-setoid) = ≋-sym
  IsEquivalence.trans (Setoid.isEquivalence ≋-setoid) = ≋-trans

  module ≋-Reasoning where
    open import Relation.Binary.Reasoning.Setoid ≋-setoid public

from∘to : (z : ℤ) → fromℕ×ℕ (toℕ×ℕ z) ≡ z
from∘to (+ x) = refl
from∘to -[1+ x ] = refl

to∘from : (n : ℕ × ℕ) → toℕ×ℕ (fromℕ×ℕ n) ≈ n
to∘from (zero , zero) = ≈-refl
to∘from (zero , suc snd) = ≈-refl
to∘from (suc fst , zero) = ≈-refl
to∘from (suc fst , suc snd) =
  let x = to∘from (fst , snd)
   in ≈-trans x (≈-sym ≈-suc-inj)

posof : ℤ → ℕ
posof = proj₁ ∘ toℕ×ℕ

negof : ℤ → ℕ
negof = proj₂ ∘ toℕ×ℕ

infixl 5 _+_
_+_ : ℤ → ℤ → ℤ
x + y = fromℕ×ℕ (posof x Nat.+ posof y , negof x Nat.+ negof y)


+-assoc' : (x y z : ℤ) → (x + y) + z ≋ x + (y + z)
+-assoc' (+ zero) y z = {! !}
+-assoc' +[1+ x ] y z = {! !}
+-assoc' -[1+ x ] y z = {! !}
  where open ≋-Reasoning

+-comm : (x y : ℤ) → x + y ≡ y + x
+-comm x y
  rewrite Nat.+-comm (posof x) (posof y)
  rewrite Nat.+-comm (negof x) (negof y) = refl

build-≈ : {x y z q : ℕ} → x ≡ y → z ≡ q → (x , z) ≈ (y , q)
build-≈ refl refl = equiv refl

build-ℤ : {x : ℤ} → (posof x , negof x) ≈ toℕ×ℕ x
build-ℤ = equiv refl

+-hom : (x y : ℤ) → toℕ×ℕ (x + y) ≈ (posof x ℕ+ posof y , negof x ℕ+ negof y)
+-hom x y =
  begin
    toℕ×ℕ (x + y)
  ≡⟨⟩
    toℕ×ℕ (fromℕ×ℕ (proj₁ (toℕ×ℕ x) ℕ+ proj₁ (toℕ×ℕ y) , proj₂ (toℕ×ℕ x) ℕ+ proj₂ (toℕ×ℕ y)))
  ≈⟨ to∘from (proj₁ (toℕ×ℕ x) ℕ+ proj₁ (toℕ×ℕ y) , proj₂ (toℕ×ℕ x) ℕ+ proj₂ (toℕ×ℕ y)) ⟩
    proj₁ (toℕ×ℕ x) ℕ+ proj₁ (toℕ×ℕ y) , proj₂ (toℕ×ℕ x) ℕ+ proj₂ (toℕ×ℕ y)
  ≡⟨⟩
    posof x ℕ+ posof y , negof x ℕ+ negof y
  ∎
  where open ≈-Reasoning



hmm : (z p n : ℕ) → fromℕ×ℕ (z ℕ+ p , z ℕ+ n) ≡ fromℕ×ℕ (p , n)
hmm zero p n = refl
hmm (suc z) p n = hmm z p n

ok : {x y : ℤ} → toℕ×ℕ x ≈ toℕ×ℕ y → x ≡ y
ok {x} {y} (equiv x=y) = begin
  x                                                  ≡⟨ sym (from∘to x) ⟩
  fromℕ×ℕ (toℕ×ℕ x)                                  ≡⟨⟩
  fromℕ×ℕ (posof x , negof x)                        ≡⟨ sym (hmm (negof y) (posof x) (negof x)) ⟩
  fromℕ×ℕ (negof y ℕ+ posof x , negof y ℕ+ negof x)  ≡⟨ cong (λ φ → fromℕ×ℕ (φ , negof y ℕ+ negof x)) (Nat.+-comm (negof y) (posof x)) ⟩
  fromℕ×ℕ (posof x ℕ+ negof y , negof y ℕ+ negof x)  ≡⟨ cong (λ φ → fromℕ×ℕ (φ , negof y ℕ+ negof x)) x=y ⟩
  fromℕ×ℕ (posof y ℕ+ negof x , negof y ℕ+ negof x)  ≡⟨ cong (λ φ → fromℕ×ℕ (φ , negof y ℕ+ negof x)) (Nat.+-comm (posof y) (negof x)) ⟩
  fromℕ×ℕ (negof x ℕ+ posof y , negof y ℕ+ negof x)  ≡⟨ cong (λ φ → fromℕ×ℕ (negof x ℕ+ posof y , φ)) (Nat.+-comm (negof y) (negof x)) ⟩
  fromℕ×ℕ (negof x ℕ+ posof y , negof x ℕ+ negof y)  ≡⟨ hmm (negof x) (posof y) (negof y) ⟩
  fromℕ×ℕ (posof y , negof y)                        ≡⟨⟩
  fromℕ×ℕ (toℕ×ℕ y)                                  ≡⟨ from∘to y ⟩
  y                                                  ∎
  where open ≡-Reasoning

lift-+-assoc : (x y z : ℤ) → toℕ×ℕ ((x + y) + z) ≈ toℕ×ℕ (x + (y + z))
lift-+-assoc x y z =
  begin
    toℕ×ℕ ((x + y) + z)
  ≈⟨ +-hom (x + y) z ⟩
    posof (x + y) ℕ+ posof z , negof (x + y) ℕ+ negof z
  ≡⟨⟩
    proj₁ (toℕ×ℕ (x + y)) ℕ+ posof z , proj₂ (toℕ×ℕ (x + y)) ℕ+ negof z
  ≈⟨ ? ⟩
    posof x ℕ+ posof (y + z) , negof x ℕ+ negof (y + z)
  ≈⟨ ≈-sym (+-hom x (y + z)) ⟩
    toℕ×ℕ (x + (y + z))
  ∎
  where open ≈-Reasoning

+-assoc : (x y z : ℤ) → (x + y) + z ≡ x + (y + z)
+-assoc x y z = ok $ begin
    toℕ×ℕ (x + y + z)
  ≡⟨⟩
    let lhs = toℕ×ℕ (fromℕ×ℕ (posof x ℕ+ posof y , negof x ℕ+ negof y)) in
    let rhs = toℕ×ℕ (fromℕ×ℕ (posof y ℕ+ posof z , negof y ℕ+ negof z)) in
    toℕ×ℕ (fromℕ×ℕ (proj₁ lhs ℕ+ posof z , proj₂ lhs ℕ+ proj₂ (toℕ×ℕ z)))
  ≡⟨ ? ⟩
    toℕ×ℕ (fromℕ×ℕ (posof x ℕ+ proj₁ rhs , negof x ℕ+ proj₂ rhs))
  ≡⟨⟩
    toℕ×ℕ (x + (y + z))
  ∎
  where open ≈-Reasoning

```
