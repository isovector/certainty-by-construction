# Functions, Big and Small

```agda
module functions where
```

Computer science is chocked full of data structures. A great many come from the
official pantheon---things like binary search trees, hash maps, stacks, graphs,
and heaps. But, dwarfing all of these, there exists orders of magnitude more
data structures in the arcane vault, from the
passingly-familiar-but-unlikely-to-have-implemented *rope* to the obscure *Judy
array.* With so many options to choose from, how can we even hope to make an
informed choice?

The reason there exist many more data structures than any practitioner can
possibly know about is that most data structures are minor tweaks of other
well-known structures. For example, the UB-tree is a variation on the B+ tree,
which itself is a B-tree that maintains a particular invariant, while a B-tree
is a generalization of the binary search tree (BST henceforth). Unrolling the
lineage here shows us that whatever the UB-tree is, it's probably a BST that has
more desirable computational properties for certain shapes of data.

As Donald Knuth said, "premature optimization is the root of all evil." For the
vast majority of tasks, you can start with (and subsequently get away with) a
BST, upgrading to the more complex UB-tree in the future only if it turns out to
be mission critical. This is a well-understood idea in the modern age.

However, most programmers coming to Agda make an error in the spirit of the
Co-Blub paradox. After years of honing their taste and cutting their teeth on
picking the simplest data structure for the job, they come to Agda and
immediately fall down the rabbit-hole of long, arduous proofs. As I have gotten
older and more experienced, my guiding philosophy for writing software has
become *if it feels too hard, it probably is.*

As it happens, your choice of representation matters much more in Agda than it
does in most programming languages. That arises from the fact that your proofs
will inevitably trace the same grooves as the implementations they are proofs
*about.* In other words, the proof follows the implementation. It's not hard to
imagine that a complicated implementation will warrant a complicated proof.


## Matrices

Let's work through an example together, to get a feel for just how important a
representation can be. Our object of investigation will be *matrices*---that is,
rectangular arrays of numbers. Matrices are often used in computational
geometry, including 3D graphics, and are the back-bone of modern machine
learning techniques. As an exercise in honing our
translating-mathematics-to-Agda chops, let's take a look at the definition of a
matrix.

Matrix
:   A rectangular array of numbers.

Matrices have a predefined height and width, often referred to as $m$ and $n$
respectively, and given in that order. For example, the following is a 3x2
matrix:

```text
1   1
5  -42
0  2.5
```

Note that the numbers inside a matrix are rather flexible. Depending on the
circumstances, we might prefer them to be naturals, while in others we might
want reals, or even functions. In order to avoid the complexities here, we will
simply parameterize the our module over the type of numbers, and postulate any
properties of those numbers as the need occurs. Let's call this number type
parameter `𝔸`:

```agda
module matrix₁ {𝔸 : Set} where
```

Returning to the problem of modeling matrices in Agda, note that we don't have
any good, inductive primitives for two-dimensional data, I think most
programmers would thus come up with the next best thing: the "vector of vectors"
model---indeed, it's what I first thought of.

```agda
  open import Data.Product
    as Σ
    using (_×_; _,_)
  open import Data.Nat
    using (ℕ; zero; suc)
  open import Data.Vec
    using (Vec; []; _∷_)

  Matrix : ℕ → ℕ → Set
  Matrix m n = Vec (Vec 𝔸 n) m

  private variable
    m n p : ℕ
```

This representation is known as the "row-major order" of matrices, that is, the
rows have contiguous data, while the columns do not. There are immediate
repercussions here. For example, let's implement the function `top/rest` which
separates the first row from the rest of the matrix:

```agda
  top/rest
      : Matrix (suc m) n
      → Vec 𝔸 n × Matrix m n
  top/rest (x ∷ xs) = x , xs
```

Compare `top/rest` to the analogous function that pulls the leftmost column off
of a matrix:

```agda
  left/rest
      : Matrix m (suc n)
      → Vec 𝔸 m × Matrix m n
  left/rest [] = [] , []
  left/rest ((x ∷ v) ∷ m)
    = Σ.map (x ∷_) (v ∷_) (left/rest m)
```

The dramatic difference in complexity between these two analogous functions is
telling. Clearly, row-major order significantly privileges working with rows
over working with columns.

Nevertheless, we can continue by implementing a few special matrices of note.
First is the zero-matrix, which is the matrix that is full only of zeroes. Note
that we will also need to postulate the existence of `0# : 𝔸`.

```agda
  postulate 0# : 𝔸

  open Data.Vec
    using (replicate)

  0ₘ : Matrix m n
  0ₘ = replicate (replicate 0#)
```

Two matrices of the same dimensions support a kind of addition, given by adding
the respective cells in each of the two columns. That is:

$$
\begin{bmatrix}
a & b & c\\
d & e & f
\end{bmatrix}
+
\begin{bmatrix}
x & y & z\\
t & u & v
\end{bmatrix}
=
\begin{bmatrix}
a + x & b + y & c + z\\
d + t & e + u & f + v
\end{bmatrix}
$$

We can implement this operation over matrices by positing the existence of an
addition over `𝔸`, as well as some common-sense identity laws:

```agda
  open import Relation.Binary.PropositionalEquality

  postulate
    _+_ : 𝔸 → 𝔸 → 𝔸
    +-identityˡ : ∀ x → 0# + x ≡ x
    +-identityʳ : ∀ x → x + 0# ≡ x

  open Data.Vec
    using (zipWith)
```

Addition of matrices doesn't present us any problems, as pointwise operations
don't need to distinguish between rows and columns. Thus, we can zip the rows
together, zip the corresponding cells together, and add each pair:

```agda
  _+ₘ_ : Matrix m n → Matrix m n → Matrix m n
  x +ₘ y = zipWith (zipWith _+_) x y
```

Let's now prove the trivial fact that `0ₘ` is a left identity for `+ₘ`:

```agda
  +ₘ-identityˡ : (x : Matrix m n) → 0ₘ +ₘ x ≡ x
```

We can begin, as always, with induction on our argument. The first case, in
which `m ≡ 0`, is easy:

```agda
  +ₘ-identityˡ [] = refl
```

The case that `n ≡ 0` is also easy, although slightly more work, as our
row-major order would suggest:

```agda
  +ₘ-identityˡ ([] ∷ rs)
    rewrite +ₘ-identityˡ rs
      = refl
```

We're now left with the induction case. After some obvious rewriting to
eliminate the `0# +_` and the row-recursive case, we're left here:

```agda
  +ₘ-identityˡ ((c ∷ cs) ∷ rs)
    rewrite +-identityˡ c
    rewrite +ₘ-identityˡ rs
```

with the goal

```goal
  (c ∷ zipWith _+_ (replicate 0#) cs) ∷ rs
≡
  (c ∷ cs) ∷ rs
```

and it's unclear how to move forwards. It would be nice if our induction just
worked, but, unfortunately, it doesn't. Crossing our fingers that this is not a
serious problem, we can write a little lemma to solve the goal for us:

```agda
      = cong (λ φ → (c ∷ φ) ∷ rs) (lemma cs)

    where
      lemma
          : ∀ {m} (cs : Vec 𝔸 m)
          → zipWith _+_ (replicate 0#) cs ≡ cs
      lemma [] = refl
      lemma (c ∷ cs)
        rewrite +-identityˡ c
        rewrite lemma cs
          = refl
```

It's not the tidiest proof in the world, but it certainly gets the job done.
However, we should be wary here; this is our second function in which dealing
with the columns was clunkier than the same operation over the rows.

Addition, however, is not the primary task for which programmers and
mathematicians use matrices. No, the more interesting operation is *matrix
multiplication*







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

  Matrix : Set c → ℕ → ℕ → Set c
  Matrix A m n = Vec (Vec A n) m

  open import Data.Product
    using (_×_; _,_)
  import Data.Product as Σ

  left/rest : Matrix A m (suc n) → Vec A m × Matrix A m n
  left/rest [] = [] , []
  left/rest ((x ∷ v) ∷ m) = Σ.map (x ∷_) (v ∷_) (left/rest m)

  outer : (A → B → C) → (Vec A m → Vec B n → Matrix C m n)
  outer f [] ys = []
  outer f (x ∷ xs) ys = map (f x) ys ∷ outer f xs ys

  column : Vec A m → Matrix A m 1
  column [] = []
  column (x ∷ xs) = (x ∷ []) ∷ column xs

  left/rest-map-∷ : (x : A) (M : Matrix A m n) →
                    left/rest (map (x ∷_) M) ≡ (replicate x , M)
  left/rest-map-∷ x [] = refl
  left/rest-map-∷ x (u ∷ M) rewrite left/rest-map-∷ x M = refl

  module WithSemiring (R : Semiring c ℓ) where
    open Semiring R renaming (Carrier to X) using (0#; 1#; _+_; _*_)

    0ᵥ : Vec X m
    0ᵥ = replicate 0#

    _+ᵥ_ : Vec X m → Vec X m → Vec X m
    _+ᵥ_ = zipWith _+_

    _*ᵥ_ : X → Vec X m → Vec X m
    x *ᵥ y = map (x *_) y

    0ₘ : Matrix X m n
    0ₘ = replicate 0ᵥ

    _+ₘ_ : Matrix X m n → Matrix X m n → Matrix X m n
    _+ₘ_ = zipWith _+ᵥ_

    1ₘ : Matrix X m m
    1ₘ {zero} = []
    1ₘ {suc m} = (1# ∷ 0ᵥ) ∷ map (0# ∷_) 1ₘ

    _⊗ₒ_ : Vec X m → Vec X n → Matrix X m n
    _⊗ₒ_ = outer _*_

    _*ₘ_ : Matrix X m n → Matrix X n p → Matrix X m p
    x *ₘ [] = 0ₘ
    x *ₘ (y ∷ ys) =
      let u , m = left/rest x
       in (u ⊗ₒ y) +ₘ (m *ₘ ys)

    _$_ : Matrix X m n → Matrix X n 1 → Matrix X m 1
    _$_ = _*ₘ_

    ⌊_⌋ : Matrix X m n → Vec X n → Vec X m
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

    left/+ : (x y : Matrix X m (suc n)) → left/rest (x +ₘ y) ≡ Σ.zip′ (zipWith _+_) _+ₘ_ (left/rest x) (left/rest y)
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
        let left : ∀ {m} → Matrix X m 1 → Vec X m
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


--   ⌊⌋-preimage : (d : Dict K V) → ComputablePreimage ⌊ d ⌋ (preimage d)
--   is-unique (⌊⌋-preimage (l , u)) = map⁺ ? ?
--   is-preimage (⌊⌋-preimage ([] , _)) = []
--   is-preimage (⌊⌋-preimage d@((k , v) ∷ l , _ ∷ p)) with ⌊ d ⌋ k in eq
--   ... | just v rewrite eq = im v eq ∷ is-preimage {! ⌊⌋-preimage (l , p) !}
--   ... | nothing = ⊥-elim {! !}
--   is-total (⌊⌋-preimage d) = {! !}

-- Fuck preimages.
```

subsets


