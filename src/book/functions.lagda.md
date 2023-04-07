# Functions Big and Small

```agda
module functions where
```

- maps
- subsets
- matrices

```agda
-- presentation as given by
-- https://personal.cis.strath.ac.uk/james.wood.100/blog/html/VecMat.html
module matrices where
  open import Data.Nat using (ℕ; zero; suc)
  open import Data.Vec

  private variable
    m n p : ℕ
    c ℓ : Agda.Primitive.Level
    A B C : Set ℓ

  open import Relation.Binary.PropositionalEquality

  Mat : Set c → ℕ → ℕ → Set c
  Mat A m n = Vec (Vec A n) m

  open import Data.Product
    using (_×_; _,_)
  import Data.Product as Σ

  left/rest : Mat A m (suc n) → Vec A m × Mat A m n
  left/rest [] = [] , []
  left/rest ((x ∷ v) ∷ m) = Σ.map (x ∷_) (v ∷_) (left/rest m)

  left/rest-map-∷ : (x : A) (M : Mat A m n) →
                    left/rest (map (x ∷_) M) ≡ (replicate x , M)
  left/rest-map-∷ x [] = refl
  left/rest-map-∷ x (u ∷ M) rewrite left/rest-map-∷ x M = refl

  outer : (A → B → C) → (Vec A m → Vec B n → Mat C m n)
  outer f [] ys = []
  outer f (x ∷ xs) ys = map (f x) ys ∷ outer f xs ys

  column : Vec A m → Mat A m 1
  column [] = []
  column (x ∷ xs) = (x ∷ []) ∷ column xs

  open import Algebra
    using (Semiring)
  module WithSemiring (R : Semiring c ℓ) where
    open Semiring R renaming (Carrier to X) using (0#; 1#; _+_; _*_)

    0ᵥ : Vec X m
    0ᵥ = replicate 0#

    _+ᵥ_ : Vec X m → Vec X m → Vec X m
    _+ᵥ_ = zipWith _+_

    _*ᵥ_ : X → Vec X m → Vec X m
    x *ᵥ y = map (x *_) y

    0ₘ : Mat X m n
    0ₘ = replicate 0ᵥ

    _+ₘ_ : Mat X m n → Mat X m n → Mat X m n
    _+ₘ_ = zipWith _+ᵥ_

    1ₘ : Mat X m m
    1ₘ {zero} = []
    1ₘ {suc m} = (1# ∷ 0ᵥ) ∷ map (0# ∷_) 1ₘ

    _⊗ₒ_ : Vec X m → Vec X n → Mat X m n
    _⊗ₒ_ = outer _*_

    _*ₘ_ : Mat X m n → Mat X n p → Mat X m p
    x *ₘ [] = 0ₘ
    x *ₘ (y ∷ ys) =
      let u , m = left/rest x
       in (u ⊗ₒ y) +ₘ (m *ₘ ys)

    _$_ : Mat X m n → Mat X n 1 → Mat X m 1
    _$_ = _*ₘ_

    ⌊_⌋ : Mat X m n → Vec X n → Vec X m
    ⌊ m ⌋ v with left/rest (m $ column v)
    ... | fst , _ = fst

    open import Function using (id; _∘_)

    postulate
      *-zeroˡ : ∀ x → 0# * x ≡ 0#
      +-identityʳ : ∀ x → x + 0# ≡ x
      +-identityˡ : ∀ x → 0# + x ≡ x
      *-identityˡ : ∀ x → 1# * x ≡ x

    left/1ₘ : left/rest (1ₘ {suc m}) ≡ ((1# ∷ replicate 0#) , replicate 0# ∷ 1ₘ {m})
    left/1ₘ {zero} = refl
    left/1ₘ {suc m}
      rewrite left/rest-map-∷ {m = m} 0# (map (0# ∷_) 1ₘ) = refl

    left/+ : (x y : Mat X m (suc n)) → left/rest (x +ₘ y) ≡ Σ.zip′ (zipWith _+_) _+ₘ_ (left/rest x) (left/rest y)
    left/+ [] [] = refl
    left/+ ((x ∷ xx) ∷ xs) ((y ∷ yy) ∷ ys) rewrite left/+ xs ys = refl

    map/*0 : ∀ xs → map {n = n} (0# *_) xs ≡ replicate 0#
    map/*0 [] = refl
    map/*0 (x ∷ xs) rewrite *-zeroˡ x | map/*0 xs = refl

    outer/replicate0
      : {m n : ℕ}
      → (x : Vec X n)
      → replicate {n = m} 0# ⊗ₒ x ≡ replicate (replicate 0#)
    outer/replicate0 {zero} x = refl
    outer/replicate0 {suc m} [] rewrite outer/replicate0 {m} [] = refl
    outer/replicate0 {suc m} (x ∷ xs)
      rewrite *-zeroˡ x
            | map/*0 xs
            | outer/replicate0 {m} (x ∷ xs)
            = refl

    dunno : (xs : Vec X m) → (replicate 0# ∷ 1ₘ) *ₘ column xs ≡ column (0# ∷ xs)
    dunno [] = refl
    dunno (x ∷ xs) rewrite *-zeroˡ x | *-identityˡ x =
      begin
        zipWith (zipWith _+_) ((0# ∷ []) ∷ (x ∷ []) ∷ outer _*_ (Σ.proj₁ (left/rest (map (_∷_ 0#) 1ₘ))) (x ∷ [])) ((replicate 0# ∷ replicate 0# ∷ Σ.proj₂ (left/rest (map (_∷_ 0#) 1ₘ))) *ₘ column xs)
      ≡⟨ ? ⟩
        (0# ∷ []) ∷ (x ∷ []) ∷ column xs
      ∎
      where open ≡-Reasoning

    left/column : (xs : Vec X m) → left/rest (column xs) ≡ (xs , replicate [])
    left/column [] = refl
    left/column (x ∷ xs) rewrite left/column xs = refl

    left/replicate : left/rest (replicate {n = m} (0# ∷ [])) ≡ (replicate 0# , replicate [])
    left/replicate {zero} = refl
    left/replicate {suc m} rewrite left/replicate {m} = refl

    zip/0#+ : ∀ xs → zipWith _+_ (replicate {n = m} 0#) xs ≡ xs
    zip/0#+ [] = refl
    zip/0#+ (x ∷ xs) rewrite +-identityˡ x | zip/0#+ xs = refl

    ⌊1ₘ⌋ : ⌊ 1ₘ {m} ⌋ ≗ id
    ⌊1ₘ⌋ {zero} [] = _≡_.refl
    ⌊1ₘ⌋ {suc m} (x ∷ xs) =
      begin
        ⌊ 1ₘ ⌋ (x ∷ xs)
      ≡⟨⟩
        let left : ∀ {m} → Mat X m 1 → Vec X m
            left = Σ.proj₁ ∘ left/rest in
        left (1ₘ *ₘ column (x ∷ xs))
      ≡⟨⟩
        left (1ₘ *ₘ ((x ∷ []) ∷ column xs))
      ≡⟨⟩
        left ((Σ.proj₁ (left/rest (1ₘ {suc m})) ⊗ₒ (x ∷ [])) +ₘ (Σ.proj₂ (left/rest (1ₘ {suc m})) *ₘ (column xs)))
      ≡⟨ cong Σ.proj₁ (left/+ (Σ.proj₁ (left/rest (1ₘ {suc m})) ⊗ₒ (x ∷ [])) (Σ.proj₂ (left/rest (1ₘ {suc m})) *ₘ (column xs))) ⟩
        zipWith _+_ (left (Σ.proj₁ (left/rest 1ₘ) ⊗ₒ (x ∷ []))) (Σ.proj₁ (left/rest (Σ.proj₂ (left/rest 1ₘ) *ₘ column xs)))
      ≡⟨ cong (λ φ → zipWith _+_ (left (Σ.proj₁ φ ⊗ₒ (x ∷ []))) (Σ.proj₁ (left/rest (Σ.proj₂ φ *ₘ column xs)))) (left/1ₘ {m}) ⟩
        zipWith _+_ (left ((1# ∷ replicate 0#) ⊗ₒ (x ∷ []))) (left ((replicate 0# ∷ 1ₘ) *ₘ column xs))
      ≡⟨ cong (λ φ → zipWith _+_ (φ ∷ left (replicate 0# ⊗ₒ _)) _) (*-identityˡ x) ⟩
        zipWith _+_ (x ∷ left (replicate 0# ⊗ₒ (x ∷ []))) (left ((replicate 0# ∷ 1ₘ) *ₘ column xs))
      ≡⟨ cong (λ φ → zipWith _+_ (x ∷ left φ) _) (outer/replicate0 (x ∷ [])) ⟩
        zipWith _+_ (x ∷ (left (replicate (replicate 0#)))) (left ((replicate {n = m} 0# ∷ 1ₘ {m}) *ₘ column xs))
      ≡⟨ cong (λ φ → zipWith _+_ (x ∷ (left (replicate (replicate 0#)))) (left φ)) (dunno xs) ⟩
        zipWith _+_ (x ∷ left (replicate (replicate 0#))) (left (column (0# ∷ xs)))
      ≡⟨ cong (λ φ → zipWith _+_ (x ∷ left (replicate (replicate 0#))) (Σ.proj₁ φ)) (left/column (0# ∷ xs)) ⟩
        x + 0# ∷ zipWith _+_ (Σ.proj₁ (left/rest (replicate (0# ∷ [])))) xs
      ≡⟨ cong (_∷ _) (+-identityʳ x) ⟩
        x ∷ zipWith _+_ (Σ.proj₁ (left/rest (replicate (0# ∷ [])))) xs
      ≡⟨ cong (λ φ → x ∷ zipWith _+_ (Σ.proj₁ φ) xs) left/replicate ⟩
        x ∷ zipWith _+_ (replicate 0#) xs
      ≡⟨ cong (x ∷_) (zip/0#+ xs) ⟩
        x ∷ xs
      ∎
      where open ≡-Reasoning

    -- this would be a really nice thing to show
```

