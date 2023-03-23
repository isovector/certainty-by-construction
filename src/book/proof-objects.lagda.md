```agda
module proof-objects where

data Bool : Set where
  true : Bool
  false : Bool

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

one : ℕ
one = suc zero

two : ℕ
two = suc one

three : ℕ
three = suc two

_+_ : ℕ → ℕ → ℕ
zero + y = y
suc x + y = suc (x + y)
infixr 6 _+_


four : ℕ
four = two + two

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x


data _≤_ : ℕ → ℕ → Set where
  z≤n : {n : ℕ} → zero ≤ n
  s≤s : {x y : ℕ} → x ≤ y → suc x ≤ suc y


2≤3 : two ≤ three
2≤3 = s≤s (s≤s z≤n)

cong : {A B : Set} → {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

suc-injective : {x y : ℕ} → suc x ≡ suc y → x ≡ y
suc-injective refl = refl


data ⊥ : Set where

¬_ : Set → Set
¬ P = P → ⊥


data Dec (P : Set) : Set where
  yes :   P → Dec P
  no  : ¬ P → Dec P

_≟_ : (x y : ℕ) → Dec (x ≡ y)
zero ≟ zero = yes refl
zero ≟ suc y = no λ { () }
suc x ≟ zero = no λ { () }
suc x ≟ suc y with x ≟ y
... | yes x=y = yes (cong suc x=y)
... | no  x≠y = no λ { p → x≠y (suc-injective p) }

```
