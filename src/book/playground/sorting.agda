module playground.sorting where

-- i spent 24 minutes putting this module together
-- so that is probably ALL THE TIME WE HAVE

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero + y = y
suc x + y = suc (x + y)

infix 5 _+_

data _≤_ : ℕ → ℕ → Set where
  z≤n : {n : ℕ} → zero ≤ n
  s≤s : {m n : ℕ} → m ≤ n → suc m ≤ suc n

≤-refl : {x : ℕ} → x ≤ x
≤-refl {zero} = z≤n
≤-refl {suc x} = s≤s ≤-refl

_<_ : ℕ → ℕ → Set
x < y = suc x ≤ y

data _≡_ {A : Set} (a : A) : A → Set where
  refl : a ≡ a

infix 3 _≡_

infixr 2 _,_
record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

cong : {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

+-identityʳ : (x : ℕ) → x + zero ≡ x
+-identityʳ zero = refl
+-identityʳ (suc x) = cong suc (+-identityʳ x)

+-suc : (x y : ℕ) → x + suc y ≡ suc x + y
+-suc zero y = refl
+-suc (suc x) y = cong suc (+-suc x y)

bigger : (n : ℕ) → Σ ℕ (λ m → n < m)
bigger n = suc n , s≤s ≤-refl

sym : {A : Set} → {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} → {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

+-comm : (x y : ℕ) → x + y ≡ y + x
+-comm zero y = sym (+-identityʳ y)
+-comm (suc x) y = sym (trans (+-suc y x) (cong suc (+-comm y x)))

data Vec (A : Set) : ℕ → Set where
  [] : Vec A zero
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

infixr 5 _∷_

_++_ : {m n : ℕ} {A : Set} → Vec A m → Vec A n → Vec A (m + n)
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

_×_ : Set → Set → Set
A × B = Σ A (λ _ → B)

splitAt : {A : Set} → (m : ℕ) → {n : ℕ} → (v : Vec A (m + n)) → Σ (Vec A m) (λ v1 → Σ (Vec A n) (λ v2 → v ≡ v1 ++ v2))
splitAt zero v = [] , v , refl
splitAt (suc m) (x ∷ v) with splitAt m v
... | l , r , p = x ∷ l , r , cong (x ∷_) p

