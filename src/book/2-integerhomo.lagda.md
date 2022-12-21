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

normalize : ℕ × ℕ → ℕ × ℕ
normalize (zero , snd) = zero , snd
normalize (suc fst , zero) = suc fst , zero
normalize (suc fst , suc snd) = normalize (fst , snd)

fromℕ×ℕ : ℕ × ℕ → ℤ
fromℕ×ℕ (p , zero) = + p
fromℕ×ℕ (zero , suc n) = -[1+ n ]
fromℕ×ℕ (suc p , suc n) = fromℕ×ℕ (p , n)

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


  ≈-suc-inj : map suc suc x ≈ x
  ≈-suc-inj {fst , snd} = equiv (sym (Nat.+-suc fst snd))

  ≈-suc-injˡ : x ≈ y → map suc id x ≈ map suc id y
  ≈-suc-injˡ {fst , snd} z = equiv ?

  ≈-suc-injʳ : x ≈ y → map id suc x ≈ map id suc y
  ≈-suc-injʳ {fst , snd} z = equiv ?

  ≈-cong-+ : x ≈ y → z ≈ w → (proj₁ x ℕ+ proj₁ z , proj₂ x ℕ+ proj₂ z) ≈ (proj₁ y ℕ+ proj₁ w , proj₂ y ℕ+ proj₂ w)
  ≈-cong-+ = ?

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

toℕ×ℕ-normal : (x : ℤ) → posof x ≡ 0 ⊎ negof x ≡ 0
toℕ×ℕ-normal (+ x) = inj₂ refl
toℕ×ℕ-normal -[1+ x ] = inj₁ refl

infixl 5 _+_
_+_ : ℤ → ℤ → ℤ
x + y = fromℕ×ℕ (posof x Nat.+ posof y , negof x Nat.+ negof y)

+-comm : (x y : ℤ) → x + y ≡ y + x
+-comm x y
  rewrite Nat.+-comm (posof x) (posof y)
  rewrite Nat.+-comm (negof x) (negof y) = refl

ok : (x y : ℕ) → fromℕ×ℕ (proj₁ (toℕ×ℕ (fromℕ×ℕ (x , y))) ,  proj₂ (toℕ×ℕ (fromℕ×ℕ (x , y)))) ≡ fromℕ×ℕ (x , y)
ok zero zero = refl
ok zero (suc y) = refl
ok (suc x) zero = refl
ok (suc x) (suc y) = ok x y

ok₂ : (x x₁ x₂ : ℕ) → fromℕ×ℕ (proj₁ (toℕ×ℕ (fromℕ×ℕ (x₁ , suc x))) Nat.+ x₂ ,  proj₂ (toℕ×ℕ (fromℕ×ℕ (x₁ , suc x)))) ≡ fromℕ×ℕ (x₁ Nat.+ x₂ , suc x)
ok₂ zero zero x₂ = refl
ok₂ zero (suc x₁) x₂ = refl
ok₂ (suc x) zero x₂ = refl
ok₂ (suc x) (suc x₁) x₂ = ok₂ x x₁ x₂

same-same : {x y : ℕ × ℕ} → x ≈ y → fromℕ×ℕ x ≡ fromℕ×ℕ y
same-same {zero , xn} {zero , yn} (equiv x=y) =
  cong (λ φ → fromℕ×ℕ (zero , φ)) (sym x=y)
same-same {zero , xn} {suc yp , yn} (equiv x=y) = {! !}
same-same {suc xp , xn} {zero , yn} (equiv x=y) = {! !}
same-same {suc xp , xn} {suc yp , yn} (equiv x=y) = {! (same-same {xp , xn} (equiv (Nat.suc-injective x=y))) !}

+-assoc : (x y z : ℤ) → (x + y) + z ≡ x + (y + z)
+-assoc x y z with same-same (to∘from (toℕ×ℕ (x + y)))
... | k = {! !}

-- +-distribˡ : (x y z : ℤ) → x + (y + z)
-- +-assoc2 x y z = {! !}

-- +-assoc : (x y z : ℤ) → (x + y) + z ≡ x + (y + z)
-- +-assoc x y z with toℕ×ℕ-normal x | toℕ×ℕ-normal y | toℕ×ℕ-normal z
-- +-assoc (+ x) (+ y) (+ z) | inj₁ refl | inj₁ refl | inj₁ refl = refl
-- +-assoc (+ x) (+ y) (+ z) | inj₁ refl | inj₁ refl | inj₂ refl = refl
-- +-assoc (+ x) (+ y) (+ z) | inj₁ refl | inj₂ refl | inj₁ refl = refl
-- +-assoc (+ x) (+ y) (+ z) | inj₁ refl | inj₂ refl | inj₂ refl = refl
-- +-assoc (+ x) (+ y) (+ z) | inj₂ refl | inj₁ refl | inj₁ refl
--   rewrite Nat.+-identityʳ x
--   rewrite Nat.+-identityʳ x
--     = refl
-- +-assoc (+ x) (+ y) (+ z) | inj₂ refl | inj₁ refl | inj₂ refl
--   rewrite Nat.+-identityʳ x
--     = refl
-- +-assoc (+ x) (+ y) (+ z) | inj₂ refl | inj₂ refl | inj₁ refl
--   rewrite Nat.+-identityʳ y
--   rewrite Nat.+-identityʳ (x Nat.+ y)
--     = refl
-- +-assoc (+ x) (+ y) (+ z) | inj₂ refl | inj₂ refl | inj₂ refl =
--   cong +_ (Nat.+-assoc x y z)
-- +-assoc (+ x) (+ y) -[1+ z ] | inj₁ refl | inj₁ refl | inj₁ refl = refl
-- +-assoc (+ x) (+ y) -[1+ z ] | inj₁ refl | inj₂ refl | inj₁ refl
--   rewrite Nat.+-identityʳ y
--   rewrite from∘to (fromℕ×ℕ (y , suc z))
--     = refl
-- +-assoc (+ x) (+ y) -[1+ z ] | inj₂ refl | inj₁ refl | inj₁ refl
--   rewrite Nat.+-identityʳ x
--   rewrite Nat.+-identityʳ x
--     = refl
-- +-assoc (+ x) (+ y) -[1+ z ] | inj₂ refl | inj₂ refl | inj₁ refl
--   rewrite Nat.+-identityʳ (x Nat.+ y)
--   rewrite Nat.+-identityʳ y
--     = {! !}
-- +-assoc (+ x) -[1+ y ] (+ z) | inj₁ refl | inj₁ refl | inj₁ refl = refl
-- +-assoc (+ x) -[1+ y ] (+ z) | inj₁ refl | inj₁ refl | inj₂ refl
--   rewrite Nat.+-identityʳ y
--   rewrite from∘to (fromℕ×ℕ (z , suc y))
--     = refl
-- +-assoc (+ x) -[1+ y ] (+ z) | inj₂ refl | inj₁ refl | inj₁ refl
--   rewrite Nat.+-identityʳ x
--   rewrite Nat.+-identityʳ y
--   rewrite Nat.+-identityʳ (proj₁ (toℕ×ℕ (fromℕ×ℕ (x , suc y))))
--   rewrite Nat.+-identityʳ (proj₂ (toℕ×ℕ (fromℕ×ℕ (x , suc y))))
--   rewrite ok x (suc y)
--     = refl
-- +-assoc (+ zero) -[1+ y ] (+ z) | inj₂ refl | inj₁ refl | inj₂ refl
--   rewrite Nat.+-identityʳ y
--   rewrite from∘to (fromℕ×ℕ (z , suc y))
--     = refl
-- +-assoc +[1+ x ] -[1+ y ] (+ zero) | inj₂ refl | inj₁ refl | inj₂ refl
--   rewrite Nat.+-identityʳ x
--   rewrite Nat.+-identityʳ y
--   rewrite Nat.+-identityʳ (proj₁ (toℕ×ℕ (fromℕ×ℕ (x , y))))
--   rewrite Nat.+-identityʳ (proj₂ (toℕ×ℕ (fromℕ×ℕ (x , y))))
--   rewrite ok x y
--     = refl
-- +-assoc +[1+ x ] -[1+ y ] +[1+ z ] | inj₂ refl | inj₁ refl | inj₂ refl
--   rewrite Nat.+-identityʳ x
--   rewrite Nat.+-identityʳ y
--   rewrite Nat.+-identityʳ (proj₁ (toℕ×ℕ (fromℕ×ℕ (x , y))))
--   rewrite Nat.+-identityʳ (proj₂ (toℕ×ℕ (fromℕ×ℕ (x , y))))
--     = {! !}
-- +-assoc (+ x) -[1+ y ] -[1+ z ] | inj₁ refl | inj₁ refl | inj₁ refl = refl
-- +-assoc (+ x) -[1+ y ] -[1+ z ] | inj₂ refl | inj₁ refl | inj₁ refl
--   rewrite Nat.+-identityʳ x
--   rewrite Nat.+-identityʳ (proj₁ (toℕ×ℕ (fromℕ×ℕ (x , suc y))))
--     = {! !}
-- +-assoc -[1+ x ] (+ y) (+ z) | inj₁ refl | inj₁ refl | inj₁ refl
--   rewrite Nat.+-identityʳ x
--   rewrite Nat.+-identityʳ x
--     = refl
-- +-assoc -[1+ x ] (+ y) (+ z) | inj₁ refl | inj₁ refl | inj₂ refl
--   rewrite Nat.+-identityʳ x
--   rewrite Nat.+-identityʳ x
--     = refl
-- +-assoc -[1+ x ] (+ y) (+ z) | inj₁ refl | inj₂ refl | inj₁ refl
--   rewrite Nat.+-identityʳ x
--   rewrite Nat.+-identityʳ y
--   rewrite Nat.+-identityʳ (proj₁ (toℕ×ℕ (fromℕ×ℕ (y , suc x))))
--   rewrite Nat.+-identityʳ (proj₂ (toℕ×ℕ (fromℕ×ℕ (y , suc x))))
--   rewrite ok y (suc x)
--     = refl
-- +-assoc -[1+ x ] (+ y) (+ z) | inj₁ refl | inj₂ refl | inj₂ refl
--   rewrite Nat.+-identityʳ x
--   rewrite Nat.+-identityʳ (proj₁ (toℕ×ℕ (fromℕ×ℕ (y , suc x))))
--   rewrite Nat.+-identityʳ (proj₂ (toℕ×ℕ (fromℕ×ℕ (y , suc x))))
--     = {! !}
-- +-assoc -[1+ x ] (+ y) -[1+ z ] | inj₁ refl | inj₁ refl | inj₁ refl
--   rewrite Nat.+-identityʳ x
--     = refl
-- +-assoc -[1+ x ] (+ y) -[1+ z ] | inj₁ refl | inj₂ refl | inj₁ refl
--   rewrite Nat.+-identityʳ x
--   rewrite Nat.+-identityʳ y
--   rewrite Nat.+-identityʳ (proj₁ (toℕ×ℕ (fromℕ×ℕ (y , suc x))))
--   rewrite Nat.+-identityʳ (proj₂ (toℕ×ℕ (fromℕ×ℕ (y , suc x))))
--     = {! !}
-- +-assoc -[1+ x ] -[1+ y ] (+ z) | inj₁ refl | inj₁ refl | inj₁ refl
--   rewrite Nat.+-identityʳ y
--   rewrite Nat.+-identityʳ (x Nat.+ suc y)
--     = refl
-- +-assoc -[1+ x ] -[1+ y ] (+ zero) | inj₁ refl | inj₁ refl | inj₂ refl
--   rewrite Nat.+-identityʳ y
--   rewrite Nat.+-identityʳ (x Nat.+ suc y)
--     = refl
-- +-assoc -[1+ x ] -[1+ y ] +[1+ z ] | inj₁ refl | inj₁ refl | inj₂ refl
--   rewrite Nat.+-identityʳ y
--   rewrite Nat.+-identityʳ (x Nat.+ suc y)
--     = {! !}
-- +-assoc -[1+ x ] -[1+ y ] -[1+ z ] | inj₁ refl | inj₁ refl | inj₁ refl
--   rewrite Nat.+-assoc x (suc y) (suc z)
--     = refl


-- +-assoc (+ .0) (+ .0) (+ .0) | inj₁ refl | inj₁ refl | inj₁ refl = refl
-- +-assoc (+ .0) (+ .0) -[1+ x₁ ] | inj₁ refl | inj₁ refl | inj₁ refl = refl
-- +-assoc (+ .0) -[1+ x ] (+ .0) | inj₁ refl | inj₁ refl | inj₁ refl = refl
-- +-assoc (+ .0) -[1+ x ] (+ x₁) | inj₁ refl | inj₁ refl | inj₂ refl
--   rewrite Nat.+-identityʳ x
--   rewrite from∘to (fromℕ×ℕ (x₁ , suc x)) = refl
-- +-assoc (+ .0) -[1+ x ] -[1+ x₁ ] | inj₁ refl | inj₁ refl | inj₁ refl = refl
-- +-assoc -[1+ x ] (+ .0) (+ .0) | inj₁ refl | inj₁ refl | inj₁ refl =
--   cong (λ φ → -[1+ φ Nat.+ 0 ]) (Nat.+-identityʳ x)
-- +-assoc -[1+ x ] (+ .0) (+ x₁) | inj₁ refl | inj₁ refl | inj₂ refl =
--   cong (λ φ → fromℕ×ℕ (x₁ , suc (φ Nat.+ 0))) (Nat.+-identityʳ x)
-- +-assoc -[1+ x ] (+ .0) -[1+ x₁ ] | inj₁ refl | inj₁ refl | inj₁ refl =
--   cong (λ φ → -[1+ φ Nat.+ suc x₁ ]) (Nat.+-identityʳ x)
-- +-assoc -[1+ x ] (+ x₁) (+ .0) | inj₁ refl | inj₂ refl | inj₁ refl
--   rewrite Nat.+-identityʳ x
--   rewrite Nat.+-identityʳ x₁
--   rewrite Nat.+-identityʳ (proj₁ (toℕ×ℕ (fromℕ×ℕ (x₁ , suc x))))
--   rewrite Nat.+-identityʳ (proj₂ (toℕ×ℕ (fromℕ×ℕ (x₁ , suc x)))) = ok x₁ (suc x)
-- +-assoc -[1+ x ] (+ x₁) (+ x₂) | inj₁ refl | inj₂ refl | inj₂ refl
--   rewrite Nat.+-identityʳ x
--   rewrite Nat.+-identityʳ (proj₂ (toℕ×ℕ (fromℕ×ℕ (x₁ , suc x)))) = ok₂ x x₁ x₂
-- +-assoc -[1+ x ] (+ zero) -[1+ x₂ ] | inj₁ refl | inj₂ refl | inj₁ refl
--   rewrite Nat.+-identityʳ x = refl
-- +-assoc -[1+ x ] +[1+ x₁ ] -[1+ x₂ ] | inj₁ refl | inj₂ refl | inj₁ refl
--   rewrite Nat.+-identityʳ x
--   rewrite Nat.+-identityʳ x₁
--   rewrite Nat.+-identityʳ (proj₁ (toℕ×ℕ (fromℕ×ℕ (x₁ , x))))
--   rewrite ok x₁ x = ?
-- +-assoc -[1+ x ] -[1+ x₁ ] (+ .0) | inj₁ refl | inj₁ refl | inj₁ refl
--   rewrite Nat.+-identityʳ x₁
--   rewrite Nat.+-identityʳ (x Nat.+ suc x₁) = refl
-- +-assoc -[1+ x ] -[1+ x₁ ] (+ x₂) | inj₁ refl | inj₁ refl | inj₂ refl = ?
-- +-assoc -[1+ x ] -[1+ x₁ ] -[1+ x₂ ] | inj₁ refl | inj₁ refl | inj₁ refl =
--   cong -[1+_] (Nat.+-assoc x (suc x₁) (suc x₂))

-- +-assoc : (x y z : ℤ) → (x + y) + z ≡ x + (y + z)
-- +-assoc x y z =
--   begin
--     (x + y) + z
--   ≡⟨⟩
--     fromℕ×ℕ (proj₁ (toℕ×ℕ lhs) Nat.+ proj₁ (toℕ×ℕ z) , proj₂ (toℕ×ℕ lhs) Nat.+ proj₂ (toℕ×ℕ z))
--   ≡⟨ cong (λ φ → fromℕ×ℕ (proj₁ φ Nat.+ proj₁ (toℕ×ℕ z) , proj₂ φ Nat.+ proj₂ (toℕ×ℕ z))) (to∘from  ⟩
--     ?

--   ≡⟨ ? ⟩
--     x + (y + z)
--   ∎
--   where
--     open ≡-Reasoning
--     x+y = (posof x Nat.+ posof y , negof x Nat.+ negof y)
--     lhs = fromℕ×ℕ x+y
--     rhs = fromℕ×ℕ (posof y Nat.+ posof z , negof y Nat.+ negof z)

infixl 6 _*_
_*_ : ℤ → ℤ → ℤ
x * y = fromℕ×ℕ (posof x Nat.* posof y Nat.+ negof x Nat.* negof y
               , negof x Nat.* posof y Nat.+ posof x Nat.* negof y)

_ : + 12 * + 12 ≡ + 144
_ = refl

_ : -[1+ 11 ] * + 12 ≡ -[1+ 143 ]
_ = refl




```
