# Functions Big and Small

```agda
module functions where
```

- maps
- subsets
- matrices

```agda
open import Data.Nat using (ℕ; zero; suc)
private variable
  m n p : ℕ
  c ℓ : Agda.Primitive.Level
  A B C : Set ℓ

open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality

open import Algebra
  using (Semiring)
module matrices where
  -- presentation as given by
  -- https://personal.cis.strath.ac.uk/james.wood.100/blog/html/VecMat.html
  open import Data.Vec


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

    postulate
      dunno : (xs : Vec X m) → (replicate 0# ∷ 1ₘ) *ₘ column xs ≡ column (0# ∷ xs)
    -- dunno [] = refl
    -- dunno (x ∷ xs) =
    --   begin
    --     (replicate 0# ∷ 1ₘ) *ₘ column (x ∷ xs)
    --   ≡⟨⟩
    --     (replicate 0# ∷ 1ₘ) *ₘ ((x ∷ []) ∷ column xs)
    --   ≡⟨⟩
    --     (Σ.proj₁ (left/rest (replicate 0# ∷ 1ₘ)) ⊗ₒ (x ∷ [])) +ₘ (Σ.proj₂ (left/rest (replicate 0# ∷ 1ₘ)) *ₘ (column xs))
    --   ≡⟨ ? ⟩
    --     (0# ∷ []) ∷ (x ∷ []) ∷ column xs
    --   ∎
    --   where open ≡-Reasoning

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

```agda
module WithSemiring₂ (R : Semiring c ℓ) where
    open Semiring R renaming (Carrier to X) using (0#; 1#; _+_; _*_)

    open import Data.Fin using (Fin; zero; suc)

    Vec : ℕ → Set c
    Vec m = Fin m → X

    postulate
      fin-ext : {v₁ v₂ : Vec m} → (∀ i → v₁ i ≡ v₂ i) → v₁ ≡ v₂

    postulate
      *-zeroˡ : ∀ x → 0# * x ≡ 0#
      *-zeroʳ : ∀ x → x * 0# ≡ 0#
      +-identityʳ : ∀ x → x + 0# ≡ x
      +-identityˡ : ∀ x → 0# + x ≡ x
      *-identityˡ : ∀ x → 1# * x ≡ x
      *-+-distribˡ : ∀ x y z → z * (x + y) ≡ z * x + z * y
      *-+-distribʳ : ∀ x y z → (x + y) * z ≡ x * z + y * z
      *-comm : ∀ x y → x * y ≡ y * x

    Matrix : ℕ → ℕ → Set c
    Matrix m n = Fin m → Fin n → X

    0ₘ : Matrix m n
    0ₘ _ _ = 0#

    open import Data.Bool using (Bool; true; false; if_then_else_)

    _==_ : Fin n → Fin n → Bool
    zero == zero = true
    zero == suc y = false
    suc x == zero = false
    suc x == suc y = x == y

    1ₘ : Matrix m m
    1ₘ i j = if i == j then 1# else 0#

    sum : Vec n → X
    sum {zero} v = 0#
    sum {suc n} v = v zero + sum {n} (v ∘ suc)

    sum/0* : (f : Fin m → X) → sum (λ j → 0# * f j) ≡ 0#
    sum/0* {zero} f = refl
    sum/0* {suc m} f
      rewrite sum/0* {m} (f ∘ suc)
            | *-zeroˡ (f zero)
            | +-identityʳ 0#
            = refl


    _*ₘ_ : Matrix m n → Matrix n p → Matrix m p
    (m₁ *ₘ m₂) i k = sum λ j → m₁ i j * m₂ j k

    column : Vec m → Matrix m 1
    column v i _ = v i

    ⌊_⌋ : Matrix m n → Vec n → Vec m
    ⌊ m ⌋ v i = (m *ₘ column v) i zero
```

We will first need a little lemma that states that the sum of anything
pointwise-multiplied by zero is also zero:

```agda
    sum/*0 : (f : Fin m → X) → sum (λ j → f j * 0#) ≡ 0#
    sum/*0 {zero} f = refl
    sum/*0 {suc m} f
      rewrite sum/*0 {m} (f ∘ suc)
            | *-zeroʳ (f zero)
            | +-identityˡ 0#
            = refl
```

And we are now ready to show the first of two facts demonstrating that matrices
are just encodings of functions. The first is that `⌊ 1ₘ ⌋` corresponds to the
`id` function:

```agda
    ⌊1ₘ⌋ : (x : Vec m)
         → (i : Fin m)
         → ⌊ 1ₘ {m} ⌋ x i ≡ x i
```

The type here would be clearer as `⌊ 1ₘ {m} ⌋ ≗ id`, but adding in the `x` and
`i` points allow us to avoid dealing with function extentionality in our proof.
The proof itself is straightforward: pattern match on `i`, and add rewrites to
eliminate the obvious algebraic identities:

```agda
    ⌊1ₘ⌋ x zero
      rewrite (*-identityˡ (x zero))
            | sum/0* (x ∘ suc)
            | +-identityʳ (x zero)
            = refl
    ⌊1ₘ⌋ x (suc i)
      rewrite (*-zeroˡ (x zero))
            | ⌊1ₘ⌋ (x ∘ suc) i
            | +-identityˡ (x (suc i))
            = refl
```


```agda
    *ₘ⟶∘
      : (m₁ : Matrix m n)
      → (m₂ : Matrix n p)
      → (v : Vec p)
      → (i : Fin m)
      → ⌊ m₁ *ₘ m₂ ⌋ v i ≡ (⌊ m₁ ⌋ ∘ ⌊ m₂ ⌋) v i
```

Giving a proof of `*ₘ⟶∘` isn't particularly hard on a conceptual level, although
Agda forces us to jump through several hoops to make everything work out
properly. Now that we are working with the function representation of matrices,
we no longer need to play silly games doing induction on the shape of the
matrix; instead, we can do induction on the indices. By binding the implicits
`m`, `n` and `p`, we can see what subgoals fall out when we try destructing on
each.

Destructing on `m` doesn't help simplify anything, but we notice that when
either `n = zero` or `p = zero`, the whole expression must simplify down to
`0#`. Let's do those two cases first, leaving the `suc`/`suc` case for later:

```agda
    *ₘ⟶∘ {m} {n} {zero} m₁ m₂ v i rewrite sum/*0 (m₁ i) = refl
    *ₘ⟶∘ {m} {zero} {p} m₁ m₂ v i rewrite sum/0* v = refl
```

We start by opening a new `≡-Reasoning block:

```agda
    *ₘ⟶∘ {m} {suc n} {suc p} m₁ m₂ v i = begin
        ⌊ m₁ *ₘ m₂ ⌋ v i
```

Unfortunately, our usual tool of dropping down a reflexive hole and asking Agdda
to normalize-solve it doesn't work here:

```agda
      ≡⟨⟩
        (m₁ *ₘ m₂) i zero * column v zero zero + sum (λ x → (m₁ *ₘ m₂) i (suc x) * column v (suc x) zero)
```

The issue is that Agda is trying to be *too helpful* here and doing an awful job
of it. In fact, Agda normalizes our expression past the point at which the proof
becomes obvious. The solution is tedious, but we must expand out our definitions
ourselves, first, with `⌊_⌋`:

```agda
      ≡⟨⟩
        ((m₁ *ₘ m₂) *ₘ column v) i zero
```

and then the outermost `_*ₘ_`:

```agda
      ≡⟨⟩
        sum (λ j → (m₁ *ₘ m₂) i j * (column v) j zero)
```

We can now eliminate `column`:

```agda
      ≡⟨⟩
        sum (λ j → (m₁ *ₘ m₂) i j * v j)
```

and then the remaining `_*ₘ_`:

```agda
      ≡⟨⟩
        sum (λ j → sum (λ k → m₁ i k * m₂ k j) * column v j zero)
```

Again, eliminate the `column`:

```agda
      ≡⟨⟩
        sum (λ j → sum (λ k → m₁ i k * m₂ k j) * v j)
```

Playing the same game, except from the bottom up, we arrive at:

```agda
      ≡⟨ lemma ⟩
        sum (λ k → m₁ i k * sum (λ j → m₂ k j * v j))
      ≡⟨⟩  -- eliminate column
        sum (λ k → m₁ i k * sum (λ j → m₂ k j * column v j zero))
      ≡⟨⟩  -- expand _*ₘ_
        sum (λ k → m₁ i k * (m₂ *ₘ column v) k zero)
      ≡⟨⟩  -- expand ⌊_⌋
        sum (λ k → m₁ i k * ⌊ m₂ ⌋ v k)
      ≡⟨⟩  -- eliminate column
        sum (λ k → m₁ i k * column (⌊ m₂ ⌋ v) k zero)
      ≡⟨⟩  -- expand  _*ₘ_
        (m₁ *ₘ column (⌊ m₂ ⌋ v)) i zero
      ≡⟨⟩  -- expand ⌊_⌋
        ⌊ m₁ ⌋ (⌊ m₂ ⌋ v) i
      ≡⟨⟩  -- expand _∘_
        (⌊ m₁ ⌋ ∘ ⌊ m₂ ⌋) v i
        ∎
      where
        open ≡-Reasoning
```

Most of the work in this proof this proof is already done; it comes from
performing *just enough* evaluation of terms to see that `lemma` is the
interesting piece of the proof. Adding `lemma` to our `where` block:

```agda
        postulate
          lemma
            : sum (λ j → sum (λ k → m₁ i k * m₂ k j) * v j)
            ≡ sum (λ k → m₁ i k * sum (λ j → m₂ k j * v j))
```

we can inspect its type. From here, it's easy to spot that is a trivial fact of
algebra. We must prove the fact that:

$$
\sum_{j}{\left(\sum_{k} {m_{1ik} \times m_{2kj}\right) \times v_j} =
\sum_{k}{m_{1ik} \times \sum_{j} {m_{2kj} \times v_j}
$$

The proof (in Agda) is uninteresting and tedious, thus we will omit it from
presentation here, satisfying ourselves with a postulate. The result, however,
is straightforward, relying only on the associativity and distributivity of
multiplication, and the commutativity of addition:

$$
\begin{align}
\sum_{j}{\left(\sum_{k} {m_{1ik} \times m_{2kj}\right)} \times v_j}
  &= \sum_{j}{\sum_{k} {m_{1ik} \times m_{2kj} \times v_j}} \\
  &= \sum_{k}{\sum_{j} {m_{1ik} \times m_{2kj} \times v_j}} \\
  &= \sum_{k}{m_{1ik} \times \sum_{k} {m_{1ik} \times m_{2kj} \times v_j}}
\end{align}
$$

Here are the gory details if you aren't happy postulating `lemma`:

```agda
            -- ≡⟨ cong sum (fin-ext λ j → sum-scalar (λ k → m₁ i k * m₂ k j) (v j))  ⟩
        -- sum (λ j → sum (λ k → m₁ i k * m₂ k j * v j))
            -- ≡⟨ sum-sum (λ j k → m₁ i k * m₂ k j * v j) ⟩
        -- sum (λ k → sum (λ j → m₁ i k * m₂ k j * v j))    ≡⟨ obvious ⟩
        -- sum (λ k → sum (λ j → m₁ i k * (m₂ k j * v j)))  ≡⟨ obvious ⟩

    sum-scalar : (f : Fin m → X) → (y : X) → sum (λ x → f x) * y ≡ sum (λ x → f x * y)
    sum-scalar {zero} f y = *-zeroˡ y
    sum-scalar {suc m} f y =
      begin
        (f zero + sum (λ x → f (suc x))) * y
      ≡⟨ *-+-distribʳ (f zero) _ y ⟩
        f zero * y + sum (λ x → f (suc x)) * y
      ≡⟨ cong (f zero * y +_) (sum-scalar (f ∘ suc) y) ⟩
        f zero * y + sum (λ x → f (suc x) * y)
      ∎
      where open ≡-Reasoning

    postulate
      obvious : {x y : X} → x ≡ y

    +-sum : (f₁ f₂ : Fin m → X) → sum f₁ + sum f₂ ≡ sum (λ x → f₁ x + f₂ x)
    +-sum {zero} f₁ f₂ = +-identityʳ 0#
    +-sum {suc m} f₁ f₂ =
      begin
        f₁ zero + sum (λ x → f₁ (suc x)) + (f₂ zero + sum (λ x → f₂ (suc x)))
      ≡⟨ obvious ⟩
        f₁ zero + f₂ zero + (sum (λ x → f₁ (suc x)) + sum (λ x → f₂ (suc x)))
      ≡⟨ cong (λ φ → f₁ zero + f₂ zero + φ) (+-sum (f₁ ∘ suc) (f₂ ∘ suc)) ⟩
        f₁ zero + f₂ zero + sum (λ x → f₁ (suc x) + f₂ (suc x))
      ∎
      where
        open ≡-Reasoning


    sum-sum : (f : Fin m → Fin n → X) → sum (λ j → sum (λ k → f j k)) ≡ sum (λ k → sum (λ j → f j k))
    sum-sum {zero} {zero} f = refl
    sum-sum {zero} {suc n} f = obvious
    sum-sum {suc m} {zero} f = obvious
    sum-sum {suc m} {suc n} f =
      begin
        sum {suc m} (λ j → sum {suc n} (λ k → f j k))
      ≡⟨⟩
        sum {suc n} (λ k → f zero k) + sum {m} (λ j → sum {suc n} (λ k → f (suc j) k))
      ≡⟨ cong (λ φ → sum {suc n} (λ k → f zero k) + φ) (sum-sum (λ j k → f (suc j) k)) ⟩
        sum {suc n} (λ k → f zero k) + sum {suc n} (λ k → sum {m} (λ j → f (suc j) k))
      ≡⟨ +-sum (λ k → f zero k) (λ k → sum {m} (λ j → f (suc j) k)) ⟩
        sum {suc n} (λ k → f zero k + sum {m} (λ j → f (suc j) k))
      ≡⟨⟩
        sum {suc n} (λ k → sum {suc m} (λ j → f j k))
      ∎
      where open ≡-Reasoning
```

So, what kind of functions are representable as matrices? As it happens, they
are precisely the *linear maps* --- that is, the two properties must hold:

```agda
    map : (X → X) → Vec m → Vec m
    map f v i = f (v i)

    zip : (X → X → X) → Vec m → Vec m → Vec m
    zip f v₁ v₂ i = f (v₁ i) (v₂ i)

    record LinearFunction (f : Vec m → Vec n) : Set c where
      field
        additive : ∀ v₁ v₂ → f (zip _+_ v₁ v₂) ≗ zip _+_ (f v₁) (f v₂)
        homogeneity : ∀ v x → f (map (x *_) v) ≗ map (x *_) (f v)
    open LinearFunction

    ⌊⌋-linear : (M : Matrix m n) → LinearFunction ⌊ M ⌋
    additive (⌊⌋-linear M) v₁ v₂ i =
      begin
        ⌊ M ⌋ (zip _+_ v₁ v₂) i
      ≡⟨⟩
        sum (λ j → M i j * (v₁ j + v₂ j))
      ≡⟨ cong sum (fin-ext λ j → *-+-distribˡ _ _ (M i j)) ⟩
        sum (λ j → M i j * v₁ j + M i j * v₂ j)
      ≡⟨ sym (+-sum (λ j → M i j * v₁ j) (λ j → M i j * v₂ j)) ⟩
        sum (λ j → M i j * v₁ j) + sum (λ j → M i j * v₂ j)
      ≡⟨⟩
        ⌊ M ⌋ v₁ i + ⌊ M ⌋ v₂ i
      ∎
      where open ≡-Reasoning
    homogeneity (⌊⌋-linear M) v x i =
      begin
        ⌊ M ⌋ (map (x *_) v) i
      ≡⟨⟩
        sum (λ j → M i j * (x * v j))
      ≡⟨ obvious ⟩
        sum (λ j → M i j * (v j * x))
      ≡⟨ obvious ⟩
        sum (λ j → (M i j * v j) * x)
      ≡⟨ obvious ⟩
        sum (λ j → (M i j * v j) * x)
      ≡⟨ sym (sum-scalar (λ j → (M i j * v j)) x) ⟩
        sum (λ j → M i j * v j) * x
      ≡⟨ *-comm _ x ⟩
        x * sum (λ j → M i j * v j)
      ≡⟨⟩
        map (x *_) (⌊ M ⌋ v) i
      ∎
      where open ≡-Reasoning
```

```agda

open import Data.Bool using (true; false)
open import Relation.Nullary using (Dec; yes; no; _because_; ofʸ)

module dictionaries {K : Set} (_≟_ : (x y : K) → Dec (x ≡ y)) where
  open import Data.Maybe using (Maybe; just; nothing)
  open import Data.Product using (_×_; _,_; ∃; Σ; proj₁; proj₂)

  open import Data.List using (List; []; _∷_; map)
  open import Data.List.Relation.Unary.All using (All; []; _∷_)
  open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
  open import Data.List.Relation.Unary.Unique.Propositional using (Unique; []; _∷_)

  private variable
    V : Set

  UniqueAssocList : (K V : Set) → List (K × V) → Set
  UniqueAssocList _ _ = AllPairs λ { (k₁ , _) (k₂ , _) → k₁ ≢ k₂ }

  Dict : Set → Set → Set
  Dict K V = ∃ (UniqueAssocList K V)

  lookup : List (K × V) → K → Maybe V
  lookup [] i = nothing
  lookup ((k , v) ∷ l) i with i ≟ k
  ... | yes refl = just v
  ... | no _ = lookup l i

  ⌊_⌋ : Dict K V → (K → Maybe V)
  ⌊ l , _ ⌋ = lookup l

  data Preimage_∋_ (f : K → Maybe V) : K → Set where
    im : ∀ {x} y → f x ≡ just y → Preimage f ∋ x

  open import Data.List.Membership.Propositional

  record ComputablePreimage (f : K → Maybe V) (l : List K) : Set where
    field
      is-unique : Unique l
      is-preimage : All (Preimage f ∋_) l
      is-total : ∀ k v → f k ≡ just v → k ∈ l
  open ComputablePreimage

  preimage : Dict K V → List K
  preimage (l , _) = map proj₁ l

  open import Data.List.Relation.Unary.Unique.Propositional.Properties

  postulate
    ≟-refl : ∀ k → k ≟ k ≡ (true because ofʸ refl)

  open import Data.Empty using (⊥-elim)


  ⌊⌋-preimage : (d : Dict K V) → ComputablePreimage ⌊ d ⌋ (preimage d)
  is-unique (⌊⌋-preimage (l , u)) = map⁺ ? ?
  is-preimage (⌊⌋-preimage ([] , _)) = []
  is-preimage (⌊⌋-preimage d@((k , v) ∷ l , _ ∷ p)) with ⌊ d ⌋ k in eq
  ... | just v rewrite eq = im v eq ∷ is-preimage {! ⌊⌋-preimage (l , p) !}
  ... | nothing = ⊥-elim {! !}
  is-total (⌊⌋-preimage d) = {! !}








  -- record ComputablePreimage (f : K → Maybe V) : Set where
  --   field
  --     inv : (f x ≡ just y) → x

  --     { x | ∃ y. f x = just y }


```


