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
      +-identityʳ : ∀ x → x + 0# ≡ x
      *-identityˡ : ∀ x → 1# * x ≡ x

    ⌊1ₘ⌋ : ⌊ 1ₘ {m} ⌋ ≗ id
    ⌊1ₘ⌋ {zero} [] = _≡_.refl
    ⌊1ₘ⌋ {1} (x ∷ [])
      rewrite *-identityˡ x
            | +-identityʳ x = refl
    ⌊1ₘ⌋ {suc (suc m)} (x₁ ∷ x₂ ∷ xs) =
      begin
        ⌊ 1ₘ ⌋ (x₁ ∷ x₂ ∷ xs)
      ≡⟨⟩
        Σ.proj₁ (left/rest (1ₘ $ column (x₁ ∷ x₂ ∷ xs)))
      ≡⟨⟩
        Σ.proj₁ (left/rest (1ₘ *ₘ column (x₁ ∷ x₂ ∷ xs)))
      ≡⟨⟩
        Σ.proj₁ (left/rest (1ₘ *ₘ ((x₁ ∷ []) ∷ (x₂ ∷ []) ∷ column xs)))
      ≡⟨⟩
        let u , ma = left/rest (1ₘ {suc m}) in
        ? -- Σ.proj₁ (left/rest ((u ⊗ₒ (x₁ ∷ [])) +ₘ (ma *ₘ ((x₂ ∷ []) ∷ column xs))))
      -- ≡⟨⟩
      --   Σ.proj₁ (left/rest (zipWith (zipWith _+_) ((1# * x ∷ []) ∷ outer _*_ (Σ.proj₁ (left/rest (map (_∷_ 0#) 1ₘ))) (x ∷ [])) ((replicate {_} {_} {m} 0# ∷ Σ.proj₂ (left/rest (map (_∷_ 0#) 1ₘ))) *ₘ column xs)))
      ≡⟨ ? ⟩
        x₁ ∷ x₂ ∷ ⌊ 1ₘ ⌋ xs
      ≡⟨ cong (λ φ → x₁ ∷ x₂ ∷ φ) (⌊1ₘ⌋ xs) ⟩
        x₁ ∷ x₂ ∷ xs
      ∎
      where open ≡-Reasoning

    -- this would be a really nice thing to show
```

