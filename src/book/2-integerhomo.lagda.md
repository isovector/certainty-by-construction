```agda
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

  -- begin
  --   (x + y) + z
  -- ≡⟨ sym (from∘to ((x + y) + z)) ⟩
  --   fromℕ×ℕ (toℕ×ℕ (x + y + z))
  -- ≡⟨ same-same {toℕ×ℕ (x + y + z)} {toℕ×ℕ (x + (y + z))} {! !} ⟩
  --   fromℕ×ℕ (toℕ×ℕ (x + (y + z)))
  -- ≡⟨ from∘to (x + (y + z)) ⟩
  --   x + (y + z)
  -- ∎
  where open ≈-Reasoning

-- -- +-distribˡ : (x y z : ℤ) → x + (y + z)
-- -- +-assoc2 x y z = {! !}

-- -- +-assoc : (x y z : ℤ) → (x + y) + z ≡ x + (y + z)
-- -- +-assoc x y z with toℕ×ℕ-normal x | toℕ×ℕ-normal y | toℕ×ℕ-normal z
-- -- +-assoc (+ x) (+ y) (+ z) | inj₁ refl | inj₁ refl | inj₁ refl = refl
-- -- +-assoc (+ x) (+ y) (+ z) | inj₁ refl | inj₁ refl | inj₂ refl = refl
-- -- +-assoc (+ x) (+ y) (+ z) | inj₁ refl | inj₂ refl | inj₁ refl = refl
-- -- +-assoc (+ x) (+ y) (+ z) | inj₁ refl | inj₂ refl | inj₂ refl = refl
-- -- +-assoc (+ x) (+ y) (+ z) | inj₂ refl | inj₁ refl | inj₁ refl
-- --   rewrite Nat.+-identityʳ x
-- --   rewrite Nat.+-identityʳ x
-- --     = refl
-- -- +-assoc (+ x) (+ y) (+ z) | inj₂ refl | inj₁ refl | inj₂ refl
-- --   rewrite Nat.+-identityʳ x
-- --     = refl
-- -- +-assoc (+ x) (+ y) (+ z) | inj₂ refl | inj₂ refl | inj₁ refl
-- --   rewrite Nat.+-identityʳ y
-- --   rewrite Nat.+-identityʳ (x Nat.+ y)
-- --     = refl
-- -- +-assoc (+ x) (+ y) (+ z) | inj₂ refl | inj₂ refl | inj₂ refl =
-- --   cong +_ (Nat.+-assoc x y z)
-- -- +-assoc (+ x) (+ y) -[1+ z ] | inj₁ refl | inj₁ refl | inj₁ refl = refl
-- -- +-assoc (+ x) (+ y) -[1+ z ] | inj₁ refl | inj₂ refl | inj₁ refl
-- --   rewrite Nat.+-identityʳ y
-- --   rewrite from∘to (fromℕ×ℕ (y , suc z))
-- --     = refl
-- -- +-assoc (+ x) (+ y) -[1+ z ] | inj₂ refl | inj₁ refl | inj₁ refl
-- --   rewrite Nat.+-identityʳ x
-- --   rewrite Nat.+-identityʳ x
-- --     = refl
-- -- +-assoc (+ x) (+ y) -[1+ z ] | inj₂ refl | inj₂ refl | inj₁ refl
-- --   rewrite Nat.+-identityʳ (x Nat.+ y)
-- --   rewrite Nat.+-identityʳ y
-- --     = {! !}
-- -- +-assoc (+ x) -[1+ y ] (+ z) | inj₁ refl | inj₁ refl | inj₁ refl = refl
-- -- +-assoc (+ x) -[1+ y ] (+ z) | inj₁ refl | inj₁ refl | inj₂ refl
-- --   rewrite Nat.+-identityʳ y
-- --   rewrite from∘to (fromℕ×ℕ (z , suc y))
-- --     = refl
-- -- +-assoc (+ x) -[1+ y ] (+ z) | inj₂ refl | inj₁ refl | inj₁ refl
-- --   rewrite Nat.+-identityʳ x
-- --   rewrite Nat.+-identityʳ y
-- --   rewrite Nat.+-identityʳ (proj₁ (toℕ×ℕ (fromℕ×ℕ (x , suc y))))
-- --   rewrite Nat.+-identityʳ (proj₂ (toℕ×ℕ (fromℕ×ℕ (x , suc y))))
-- --   rewrite ok x (suc y)
-- --     = refl
-- -- +-assoc (+ zero) -[1+ y ] (+ z) | inj₂ refl | inj₁ refl | inj₂ refl
-- --   rewrite Nat.+-identityʳ y
-- --   rewrite from∘to (fromℕ×ℕ (z , suc y))
-- --     = refl
-- -- +-assoc +[1+ x ] -[1+ y ] (+ zero) | inj₂ refl | inj₁ refl | inj₂ refl
-- --   rewrite Nat.+-identityʳ x
-- --   rewrite Nat.+-identityʳ y
-- --   rewrite Nat.+-identityʳ (proj₁ (toℕ×ℕ (fromℕ×ℕ (x , y))))
-- --   rewrite Nat.+-identityʳ (proj₂ (toℕ×ℕ (fromℕ×ℕ (x , y))))
-- --   rewrite ok x y
-- --     = refl
-- -- +-assoc +[1+ x ] -[1+ y ] +[1+ z ] | inj₂ refl | inj₁ refl | inj₂ refl
-- --   rewrite Nat.+-identityʳ x
-- --   rewrite Nat.+-identityʳ y
-- --   rewrite Nat.+-identityʳ (proj₁ (toℕ×ℕ (fromℕ×ℕ (x , y))))
-- --   rewrite Nat.+-identityʳ (proj₂ (toℕ×ℕ (fromℕ×ℕ (x , y))))
-- --     = {! !}
-- -- +-assoc (+ x) -[1+ y ] -[1+ z ] | inj₁ refl | inj₁ refl | inj₁ refl = refl
-- -- +-assoc (+ x) -[1+ y ] -[1+ z ] | inj₂ refl | inj₁ refl | inj₁ refl
-- --   rewrite Nat.+-identityʳ x
-- --   rewrite Nat.+-identityʳ (proj₁ (toℕ×ℕ (fromℕ×ℕ (x , suc y))))
-- --     = {! !}
-- -- +-assoc -[1+ x ] (+ y) (+ z) | inj₁ refl | inj₁ refl | inj₁ refl
-- --   rewrite Nat.+-identityʳ x
-- --   rewrite Nat.+-identityʳ x
-- --     = refl
-- -- +-assoc -[1+ x ] (+ y) (+ z) | inj₁ refl | inj₁ refl | inj₂ refl
-- --   rewrite Nat.+-identityʳ x
-- --   rewrite Nat.+-identityʳ x
-- --     = refl
-- -- +-assoc -[1+ x ] (+ y) (+ z) | inj₁ refl | inj₂ refl | inj₁ refl
-- --   rewrite Nat.+-identityʳ x
-- --   rewrite Nat.+-identityʳ y
-- --   rewrite Nat.+-identityʳ (proj₁ (toℕ×ℕ (fromℕ×ℕ (y , suc x))))
-- --   rewrite Nat.+-identityʳ (proj₂ (toℕ×ℕ (fromℕ×ℕ (y , suc x))))
-- --   rewrite ok y (suc x)
-- --     = refl
-- -- +-assoc -[1+ x ] (+ y) (+ z) | inj₁ refl | inj₂ refl | inj₂ refl
-- --   rewrite Nat.+-identityʳ x
-- --   rewrite Nat.+-identityʳ (proj₁ (toℕ×ℕ (fromℕ×ℕ (y , suc x))))
-- --   rewrite Nat.+-identityʳ (proj₂ (toℕ×ℕ (fromℕ×ℕ (y , suc x))))
-- --     = {! !}
-- -- +-assoc -[1+ x ] (+ y) -[1+ z ] | inj₁ refl | inj₁ refl | inj₁ refl
-- --   rewrite Nat.+-identityʳ x
-- --     = refl
-- -- +-assoc -[1+ x ] (+ y) -[1+ z ] | inj₁ refl | inj₂ refl | inj₁ refl
-- --   rewrite Nat.+-identityʳ x
-- --   rewrite Nat.+-identityʳ y
-- --   rewrite Nat.+-identityʳ (proj₁ (toℕ×ℕ (fromℕ×ℕ (y , suc x))))
-- --   rewrite Nat.+-identityʳ (proj₂ (toℕ×ℕ (fromℕ×ℕ (y , suc x))))
-- --     = {! !}
-- -- +-assoc -[1+ x ] -[1+ y ] (+ z) | inj₁ refl | inj₁ refl | inj₁ refl
-- --   rewrite Nat.+-identityʳ y
-- --   rewrite Nat.+-identityʳ (x Nat.+ suc y)
-- --     = refl
-- -- +-assoc -[1+ x ] -[1+ y ] (+ zero) | inj₁ refl | inj₁ refl | inj₂ refl
-- --   rewrite Nat.+-identityʳ y
-- --   rewrite Nat.+-identityʳ (x Nat.+ suc y)
-- --     = refl
-- -- +-assoc -[1+ x ] -[1+ y ] +[1+ z ] | inj₁ refl | inj₁ refl | inj₂ refl
-- --   rewrite Nat.+-identityʳ y
-- --   rewrite Nat.+-identityʳ (x Nat.+ suc y)
-- --     = {! !}
-- -- +-assoc -[1+ x ] -[1+ y ] -[1+ z ] | inj₁ refl | inj₁ refl | inj₁ refl
-- --   rewrite Nat.+-assoc x (suc y) (suc z)
-- --     = refl


-- -- +-assoc (+ .0) (+ .0) (+ .0) | inj₁ refl | inj₁ refl | inj₁ refl = refl
-- -- +-assoc (+ .0) (+ .0) -[1+ x₁ ] | inj₁ refl | inj₁ refl | inj₁ refl = refl
-- -- +-assoc (+ .0) -[1+ x ] (+ .0) | inj₁ refl | inj₁ refl | inj₁ refl = refl
-- -- +-assoc (+ .0) -[1+ x ] (+ x₁) | inj₁ refl | inj₁ refl | inj₂ refl
-- --   rewrite Nat.+-identityʳ x
-- --   rewrite from∘to (fromℕ×ℕ (x₁ , suc x)) = refl
-- -- +-assoc (+ .0) -[1+ x ] -[1+ x₁ ] | inj₁ refl | inj₁ refl | inj₁ refl = refl
-- -- +-assoc -[1+ x ] (+ .0) (+ .0) | inj₁ refl | inj₁ refl | inj₁ refl =
-- --   cong (λ φ → -[1+ φ Nat.+ 0 ]) (Nat.+-identityʳ x)
-- -- +-assoc -[1+ x ] (+ .0) (+ x₁) | inj₁ refl | inj₁ refl | inj₂ refl =
-- --   cong (λ φ → fromℕ×ℕ (x₁ , suc (φ Nat.+ 0))) (Nat.+-identityʳ x)
-- -- +-assoc -[1+ x ] (+ .0) -[1+ x₁ ] | inj₁ refl | inj₁ refl | inj₁ refl =
-- --   cong (λ φ → -[1+ φ Nat.+ suc x₁ ]) (Nat.+-identityʳ x)
-- -- +-assoc -[1+ x ] (+ x₁) (+ .0) | inj₁ refl | inj₂ refl | inj₁ refl
-- --   rewrite Nat.+-identityʳ x
-- --   rewrite Nat.+-identityʳ x₁
-- --   rewrite Nat.+-identityʳ (proj₁ (toℕ×ℕ (fromℕ×ℕ (x₁ , suc x))))
-- --   rewrite Nat.+-identityʳ (proj₂ (toℕ×ℕ (fromℕ×ℕ (x₁ , suc x)))) = ok x₁ (suc x)
-- -- +-assoc -[1+ x ] (+ x₁) (+ x₂) | inj₁ refl | inj₂ refl | inj₂ refl
-- --   rewrite Nat.+-identityʳ x
-- --   rewrite Nat.+-identityʳ (proj₂ (toℕ×ℕ (fromℕ×ℕ (x₁ , suc x)))) = ok₂ x x₁ x₂
-- -- +-assoc -[1+ x ] (+ zero) -[1+ x₂ ] | inj₁ refl | inj₂ refl | inj₁ refl
-- --   rewrite Nat.+-identityʳ x = refl
-- -- +-assoc -[1+ x ] +[1+ x₁ ] -[1+ x₂ ] | inj₁ refl | inj₂ refl | inj₁ refl
-- --   rewrite Nat.+-identityʳ x
-- --   rewrite Nat.+-identityʳ x₁
-- --   rewrite Nat.+-identityʳ (proj₁ (toℕ×ℕ (fromℕ×ℕ (x₁ , x))))
-- --   rewrite ok x₁ x = ?
-- -- +-assoc -[1+ x ] -[1+ x₁ ] (+ .0) | inj₁ refl | inj₁ refl | inj₁ refl
-- --   rewrite Nat.+-identityʳ x₁
-- --   rewrite Nat.+-identityʳ (x Nat.+ suc x₁) = refl
-- -- +-assoc -[1+ x ] -[1+ x₁ ] (+ x₂) | inj₁ refl | inj₁ refl | inj₂ refl = ?
-- -- +-assoc -[1+ x ] -[1+ x₁ ] -[1+ x₂ ] | inj₁ refl | inj₁ refl | inj₁ refl =
-- --   cong -[1+_] (Nat.+-assoc x (suc x₁) (suc x₂))

-- -- +-assoc : (x y z : ℤ) → (x + y) + z ≡ x + (y + z)
-- -- +-assoc x y z =
-- --   begin
-- --     (x + y) + z
-- --   ≡⟨⟩
-- --     fromℕ×ℕ (proj₁ (toℕ×ℕ lhs) Nat.+ proj₁ (toℕ×ℕ z) , proj₂ (toℕ×ℕ lhs) Nat.+ proj₂ (toℕ×ℕ z))
-- --   ≡⟨ cong (λ φ → fromℕ×ℕ (proj₁ φ Nat.+ proj₁ (toℕ×ℕ z) , proj₂ φ Nat.+ proj₂ (toℕ×ℕ z))) (to∘from  ⟩
-- --     ?

-- --   ≡⟨ ? ⟩
-- --     x + (y + z)
-- --   ∎
-- --   where
-- --     open ≡-Reasoning
-- --     x+y = (posof x Nat.+ posof y , negof x Nat.+ negof y)
-- --     lhs = fromℕ×ℕ x+y
-- --     rhs = fromℕ×ℕ (posof y Nat.+ posof z , negof y Nat.+ negof z)

-- infixl 6 _*_
-- _*_ : ℤ → ℤ → ℤ
-- x * y = fromℕ×ℕ (posof x Nat.* posof y Nat.+ negof x Nat.* negof y
--                , negof x Nat.* posof y Nat.+ posof x Nat.* negof y)

-- _ : + 12 * + 12 ≡ + 144
-- _ = refl

-- _ : -[1+ 11 ] * + 12 ≡ -[1+ 143 ]
-- _ = refl




-- ```
