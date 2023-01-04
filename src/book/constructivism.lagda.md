# Constructivism

```agda
module constructivism where

open import Data.Empty
open import Relation.Nullary
open import Relation.Nullary.Decidable as Dec
open import Relation.Unary
open import 9-posets
open import Relation.Binary.PropositionalEquality
open import Data.Sum
open import Data.Product
open import Data.Nat
open import Data.Nat.Properties
open import Function.Base using (case_of_)

record _IsPrime (n : ℕ) : Set where
  constructor is-prime
  field
    1<n : 1 < n
    primal : (x : ℕ) → 1 < x → x < n → ¬ x Divides n

open _IsPrime

open import 6-setoids
open mod-base

lemma₁ : (a b x y n : ℕ) → a < n → b < n → a + x * n ≡ b + y * n → a ≡ b
lemma₁ = ?

mod-eq? : (a b n : ℕ) → a < n → b < n → Dec (a ≈ b ⟨mod n ⟩)
mod-eq? a b n a<n b<n with a ≟ b
... | yes a=b = yes (≈-mod 0 0 (cong (_+ 0) a=b))
... | no a≠b = no λ { (≈-mod x y p) → a≠b (lemma₁ a b x y n a<n b<n p) }

open import Relation.Binary.Definitions

lemma₂ : {a n : ℕ} → a ≈ n ⟨mod n ⟩ → a ≈ 0 ⟨mod n ⟩
lemma₂ {a} {n} a=n =
  begin
    a
  ≈⟨ a=n ⟩
    n
  ≈⟨ mod-sym n (mod-properties.0≈n n) ⟩
    0
  ∎
  where open mod-reasoning n

lemma₃ : {a n : ℕ} → a ≈ 0 ⟨mod n ⟩ → a ≈ n ⟨mod n ⟩
lemma₃ {a} {n} a=0 =
  begin
    a
  ≈⟨ a=0 ⟩
    0
  ≈⟨ mod-properties.0≈n n ⟩
    n
  ∎
  where open mod-reasoning n

mod-helper : ℕ → ℕ → ℕ → ℕ → ℕ
mod-helper k m zero j = k
mod-helper k m (suc n) zero = mod-helper 0 m n m
mod-helper k m (suc n) (suc j) = mod-helper (suc k) m n j

_mod_ : (a n : ℕ) → .{{ _ : NonZero n }} → ℕ
a mod (suc n) = mod-helper 0 n a n

zero-mod-n : (n : ℕ) → .{{ _ : NonZero n }} → 0 mod n ≡ 0
zero-mod-n (suc n) = refl

ok : (a n : ℕ) → suc (mod-helper 0 n a n) ≈ mod-helper 0 n (suc a) n ⟨mod (suc n) ⟩
ok zero zero = mod-sym 1 (mod-properties.0≈n 1)
ok zero (suc n) = mod-refl (suc (suc n))
ok (suc a) zero = ok a zero
ok (suc a) (suc n) = {! !}

suc-hom-n : (a n : ℕ) → .⦃ _ : NonZero n ⦄ → suc (a mod n) ≈ suc a mod n ⟨mod n ⟩
suc-hom-n zero (suc n) = {! mod-properties.mod-suc-cong (suc n)  !}
suc-hom-n (suc a) n@(suc x) with suc-hom-n a n | >-nonZero⁻¹ n
... | z | (s≤s z≤n) =
  begin
    suc (suc a mod n)
  ≡⟨⟩
    suc (mod-helper 0 x (suc a) x)
  ≈⟨ ? ⟩
    mod-helper 0 x (suc (suc a)) x
  ≡⟨⟩
    (suc (suc a)) mod n
  ∎
  where open mod-reasoning n

mod-is-mod : (a n : ℕ) → .{{ _ : NonZero n }} → a ≈ (a mod n) ⟨mod n ⟩
mod-is-mod zero n =
  begin
    0
  ≡⟨ sym (zero-mod-n n) ⟩
    0 mod n
  ∎
  where open mod-reasoning n
mod-is-mod (suc a) n =
  begin
    suc a
  ≈⟨ mod-properties.mod-suc-cong n (mod-is-mod a n) ⟩
    suc (a mod n)
  ≈⟨ ? ⟩
    (suc a) mod n
  ∎
  where open mod-reasoning n

{-
--

mod-helper-< : (k m n j : ℕ) → k ≤ m → mod-helper k m n j ≤ m
mod-helper-< k m zero j k≤m = k≤m
mod-helper-< k m (suc n) zero k≤m = mod-helper-< 0 m n m z≤n
mod-helper-< k m (suc n) (suc j) k≤m = mod-helper-< (suc k) m n j {! !}

mod-< : (a n : ℕ) → .⦃ _ : NonZero n ⦄ → a mod n < n
mod-< a (suc n) = s≤s (mod-helper-< 0 n a n z≤n)

mod-eq?2 : (a b n : ℕ) → .⦃ _ : NonZero n ⦄ → Dec (a ≈ b ⟨mod n ⟩)
mod-eq?2 a b n with mod-eq? (a mod n) (b mod n) n (mod-< a n) (mod-< b n)
... | yes z = yes (
  begin
    a
  ≈⟨ mod-is-mod a n ⟩
    a mod n
  ≈⟨ z ⟩
    b mod n
  ≈⟨ mod-sym n (mod-is-mod b n) ⟩
    b
  ∎
  )
  where open mod-reasoning n
... | no z = ?



-- mod-eq?3 : (a b n : ℕ) → a < n → Dec (a ≈ b ⟨mod n ⟩)
-- mod-eq?3 a b n x with anyUpTo? = {! !}

-- mod-eq?2 : (a b n : ℕ) → Dec (a ≈ b ⟨mod n ⟩)
-- mod-eq?2 a b n with <-cmp a n
-- mod-eq?2 a b n | tri< a<n ¬b ¬c with <-cmp b n
-- ... | tri< b<n _ _ = mod-eq? a b n a<n b<n
-- ... | tri≈ _ b=n _ rewrite b=n = Dec.map′ lemma₃ lemma₂ (mod-eq? a 0 n a<n ?)
-- ... | tri> _ _ n<b = Dec.map′ ? ? (mod-eq?2 a (b ∸ n) n)
-- mod-eq?2 a b n | tri≈ _ a=n _ with <-cmp b n
-- ... | tri< b<n _ _ = {! !}
-- ... | tri≈ _ b=n _ = {! !}
-- ... | tri> _ _ n<b = {! !}
-- mod-eq?2 a b n | tri> ¬a ¬b c = {! !}

∸-zero : (m : ℕ) → m ∸ m ≡ 0
∸-zero zero = refl
∸-zero (suc m) = ∸-zero m

mod-to-div : {a n : ℕ} → a ≈ 0 ⟨mod n ⟩ → n Divides a
mod-to-div {a} {n} (≈-mod x y p) = divides (y ∸ x) 0<y∸x (begin
  n * (y ∸ x)          ≡⟨ *-comm n (y ∸ x) ⟩
  (y ∸ x) * n          ≡⟨ *-distribʳ-∸ n y x ⟩
  y * n ∸ x * n        ≡⟨ cong (_∸ x * n) (sym p) ⟩
  (a + x * n) ∸ x * n  ≡⟨ +-∸-assoc a (≤-refl {x * n}) ⟩
  a + (x * n ∸ x * n)  ≡⟨ cong (a +_) (∸-zero (x * n)) ⟩
  a + 0                ≡⟨ +-identityʳ a ⟩
  a                    ∎)
  where
    open ≡-Reasoning
    postulate
      0<y∸x : 0 < y ∸ x

div-to-mod : {a n : ℕ} → n Divides a → a ≈ 0 ⟨mod n ⟩
div-to-mod {a} {n} (divides x 0<x proof) = ≈-mod 0 x ( begin
  a + 0  ≡⟨ +-identityʳ a ⟩
  a      ≡⟨ sym proof ⟩
  n * x  ≡⟨ *-comm n x ⟩
  x * n  ∎)
  where open ≡-Reasoning

-- _Divides?_ : (a b : ℕ) → Dec (a Divides b)
-- zero Divides? zero = yes (divides 1 (s≤s z≤n) refl)
-- zero Divides? suc b = no λ { () }
-- -- suc a Divides? zero = no λ { (divides zero () proof₁)
-- --                            ; (divides (suc n) 0<n ())
-- --                            }
-- suc a Divides? b = Dec.map′ mod-to-div div-to-mod (mod-eq? b 0 (suc a))

lemma : (a b n : ℕ) → b < a → a * suc n ≡ b → ⊥
lemma .(suc _) zero n (s≤s b<a) ()
lemma (suc a) (suc b) n (s≤s b<a) p = ?

<-does-not-divide : (a b : ℕ) → b < a → ¬ a Divides b
<-does-not-divide a b b<a (divides (suc n) (s≤s 0<n) p) = lemma a b n b<a p

-- 2-is-prime : 2 IsPrime
-- 2-is-prime (suc zero) x₁ x₂ = inj₁ refl
-- 2-is-prime (suc (suc .zero)) (s≤s (s≤s z≤n)) x₂ = inj₂ refl

0-is-not-prime : ¬ 0 IsPrime
0-is-not-prime ()

1-is-not-prime : ¬ 1 IsPrime
1-is-not-prime (is-prime (s≤s ()) primal)

2-is-prime : 2 IsPrime
1<n 2-is-prime = s≤s (s≤s z≤n)
primal 2-is-prime (suc zero) (s≤s ()) x<2 (divides (suc n) 0<n proof₁)
primal 2-is-prime (suc (suc x)) 1<x (s≤s (s≤s ())) (divides (suc n) 0<n proof₁)

-- is-prime : (n : ℕ) → ((x : ℕ) → x ≢ 1 → x < n → ¬ x Divides n) → n IsPrime
-- is-prime n f x = {! !}

-- dec-prime : Decidable _IsPrime
-- dec-prime zero = no λ 0-prime → case 0-prime 1 of λ { x → {! !} }
-- dec-prime (suc x) = {! !}

postulate
  excluded-middle : {A : Set} → ¬ ¬ A → A

infinitude-of-primes : (x : ℕ) → ∃[ n ] n IsPrime × x < n
infinitude-of-primes x = {! !}

infinitude-of-primes₂ : (x : ℕ) → ∃[ n ] n IsPrime × x < n
infinitude-of-primes₂ x = excluded-middle λ { no-bigger → no-bigger (? , {! !}) }

-}

```


