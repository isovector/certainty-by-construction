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
module matrix-induction {𝔸 : Set} where
```


### The Row-Major Representation

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
multiplication.* Matrix multiplication, unlike your everyday multiplication, has
a stronger type, and requires our two matrices to have an equal dimension
between them. That is, the matrix on the left must have the same width as the
height of the matrix on the right. That is, given `a : Matrix m n` and `b :
Matrix n p`, we can write the operation `a *ₘ b` in symbols as:

$$
\begin{bmatrix}
a_{1,1} & a_{1,2} & \cdots & a_{1,n}\\
a_{2,1} & a_{2,2} & \cdots & a_{2,n}\\
\vdots & \vdots & \ddots & \vdots \\
a_{m,1} & a_{m,2} & \cdots & a_{m,n}
\end{bmatrix}
\times
\begin{bmatrix}
b_{1,1} & b_{1,2} & \cdots & b_{1,p}\\
b_{2,1} & b_{2,2} & \cdots & b_{2,p}\\
\vdots & \vdots & \ddots & \vdots \\
b_{n,1} & b_{n,2} & \cdots & b_{n,p}
\end{bmatrix}
$$

with the result being `c : Matrix m p`, where each cell is given by the formula:

$$
c_{i,j} = \sum_{k = 1}^{n} a_{i,k} \times b_{k, j}
$$

Said another way, the product matrix resulting from a multiplication pairs the
rows of the first matrix with the columns of the second, adding each cell up
pointwise.

If this is your first time seeing matrix multiplication (or even if it isn't,)
it might be unclear what the *intuition* behind matrix multiplication is. Why
does it exist, what does it do, and why should we care about it? We will return
to this question in a moment, but for the time being, resign ourselves to
implementing it in our row-major matrix representation.

We will implement matrix multiplication in two steps; first, by computing the
*outer-product*, which is the analogous operation on vectors (matrices with one
dimension set to 1.) The outer product of two vectors is a matrix using the
length of the first as its height, and the length of the second as its width. In
symbols, the result of:

$$
\begin{bmatrix}
a_{1} \\
a_{2} \\
\vdots \
a_{m}
\end{bmatrix}
\otimes
\begin{bmatrix}
b_{1} \\
b_{2} \\
\vdots \
b_{n}
\end{bmatrix}
$$

is a matrix:

$$
\begin{bmatrix}
a_{1}\times b_{1} & a_{1}\times b_{2} & \cdots & a_{1}\times b_{n}\\
a_{2}\times b_{1} & a_{2}\times b_{2} & \cdots & a_{2}\times b_{n}\\
\vdots & \vdots & \ddots & \vdots \\
a_{m}\times b_{1} & a_{m}\times b_{2} & \cdots & a_{m}\times b_{n}
\end{bmatrix}
$$

It's not too tricky to implement such a thing in Agda; the secret is to write
down the type and use the type-checker to help us ensure that we haven't lost a
case anywhere.

```agda
  open Data.Vec
    using (map)

  postulate
    _*_ : 𝔸 → 𝔸 → 𝔸

  _⊗_ : Vec 𝔸 m → Vec 𝔸 n → Matrix m n
  []       ⊗ ys = []
  (x ∷ xs) ⊗ ys = map (x *_) ys ∷ xs ⊗ ys
```

Now that we have the outer product, we can implement matrix multiplication by
taking the outer product of each row/column pair and doing a matrix addition
with the multiplication of the rest of the matrix. Start with the type:

```agda
  _*ₘ_ : Matrix m n → Matrix n p → Matrix m p
```

Recall that in the definition of matrix multiplication, the *columns* of the
first matrix get paired with the *rows* of the latter. Since our matrices are in
row-major order, our induction naturally will proceed on the second argument,
since that's where the rows are. If we're out of rows, the result is
conceptually zero, but that doesn't typecheck, so instead we use `0ₘ` which is
the matrix analogue:

```agda
  x *ₘ [] = 0ₘ
```

Otherwise, we must pair a column from `x` with the row we just pulled off. We
can use `left/rest` to get the column, and then proceed with our outer product
added to the resultant multiplication:

```agda
  x *ₘ (r ∷ rs) =
    let c , cs = left/rest x
      in (c ⊗ r) +ₘ (cs *ₘ rs)
```

As it happens, this definition of `_*ₘ_` *is* indeed correct, but it's rather
hard to convince ourselves of that, isn't it? Recall the definition we gave
earlier, where the $c_{i,j}$ element in the resultant matrix was given by the
formula:

$$
c_{i,j} = \sum_{k = 1}^{n} a_{i,k} \times b_{k, j}
$$

Our implementation instead gives us a recursive definition:

$$
a \times_m b = (a_{-, 1} \otimes b_{1, -}) +_m ((a_{-, 2\dots}) \times_m (b_{2\dots, -}))
$$

which uses nonstandard notation to suggest pulling a column off a matrix via
$a_{-, 1}$ and the rest of the matrix as $a_{-, 2\dots}$. We can convince
ourselves of the correctness here by noticing that the induction is actually on
`p`, which means the rows and the columns on which we're doing the outer product
remain of length `m` and `n` respectively. Thus, each outer product still
results in a matrix of size $m \times n$, of which we add up exactly `p` in
number. Thus, our definition here performs `p` matrix additions, while the
mathematical definition performs `p` scalar additions in each cell.

These two definitions are thus equivalent, but there is significantly more
algebraic manipulation necessary to use `_*ₘ_` as written. Notice that if we
wanted to prove anything about it, we would first need to inline the definitions
of `left/rest`, `_⊗_`, and `_+ₘ_`, each of which is annoyingly recursive and
none of which will Agda automatically compute for us. It's thus rather more work
than we'd like to do! In choosing the row-major order as our representation,
we've obscured the mathematics we're trying to prove. Not only do we need to
still do the original mathematics, we also need to juggle the weight of our
representation.


### Function Representation

Rather than go forward with the row-major representation, we will try again with
a different representation and see how all the same things roll-out. We note
that where things really went wrong was that rows and columns were citizens of
differing standing. It was easy to work with rows, but difficult to work with
columns. Of course, we could always try a column-major ordering instead, but
that would merely move the challenges.

Instead, we find ourselves looking for a representation which doesn't make any
distinctions between the two dimensions. Any sort of inductive definition is
sure to build up matrices from smaller matrices, which is likely to give rise to
the same issues. Let's thus turn our attention to a function representation:

```agda
module matrix-functions {𝔸 : Set} where
  open import Data.Nat
    using (ℕ; zero; suc)
  open import Data.Fin
    using (Fin; zero; suc)

  Matrix : ℕ → ℕ → Set
  Matrix m n = (i : Fin m) → (j : Fin n) → 𝔸
```

A matrix is thus parameterized by its dimensions, and is represented by a
function which takes those indices and gives you back an element of `𝔸`. Giving
names to the `Fin` arguments here isn't strictly necessary, but it helps Agda
give meaningful names to indices as we work with matrices.

We can implement the zero matrix trivially, by simply ignoring the indices:

```agda
  private variable
    m n p : ℕ

  postulate 0# : 𝔸

  0ₘ : Matrix m n
  0ₘ _ _ = 0#
```

Furthermore, we can now implement the identity matrix straightforwardly. In
symbols, the identity function is a square ($n \times n$) matrix whose cells are
given by:

$$
c_{i,j} =
\begin{cases}
  1 & i = j \\
  0 & \text{otherwise}
\end{cases}
$$

In Agda:

```agda
  open import Data.Bool
    using (Bool; true; false; if_then_else_)

  _==_ : Fin n → Fin n → Bool
  zero == zero = true
  zero == suc y = false
  suc x == zero = false
  suc x == suc y = x == y

  postulate 1# : 𝔸

  1ₘ : Matrix m m
  1ₘ i j = if i == j then 1# else 0#
```

We can implement the summation operator by way of `sum`, which takes a function
out of `Fin n` and adds up every term:

```agda
  postulate
    _+_ : 𝔸 → 𝔸 → 𝔸

  open import Function
    using (id; _∘_)

  sum : (Fin n → 𝔸) → 𝔸
  sum {zero} v = 0#
  sum {suc n} v = v zero + sum {n} (v ∘ suc)
```

With all of these pieces under our belt, the definition of matrix multiplication
is now extremely simple, and mirrors its mathematical counterpart exactly:

```agda
  postulate
    _*_ : 𝔸 → 𝔸 → 𝔸

  _*ₘ_ : Matrix m n → Matrix n p → Matrix m p
  (a *ₘ b) i j = sum λ k → a i k * b k j
```

Implementing matrix addition is also exceptionally easy under our new scheme,
corresponding again exactly with the mathematical definition:

```agda
  _+ₘ_ : Matrix m n → Matrix m n → Matrix m n
  (a +ₘ b) i j = a i j + b i j
```

With a little bit of machinery in order to express equality of matrices:

```agda
  open import Relation.Binary.PropositionalEquality

  infix 0 _≡ₘ_
  _≡ₘ_ : (a b : Matrix m n) → Set
  a ≡ₘ b = ∀ i j → a i j ≡ b i j
```

We can now prove `+ₘ-identityˡ` again.

```agda
  postulate
    +-identityˡ : ∀ x → 0# + x ≡ x

  +ₘ-identityˡ : (a : Matrix m n) → 0ₘ +ₘ a ≡ₘ a
  +ₘ-identityˡ a i j
    rewrite +-identityˡ (a i j)
      = refl
```

Compare the simplicity of this proof to the previous one we wrote for the
row-major implementation:

```agda
--  +ₘ-identityˡ ([] ∷ rs)
--    rewrite +ₘ-identityˡ rs
--      = refl
--  +ₘ-identityˡ ((c ∷ cs) ∷ rs)
--    rewrite +-identityˡ c
--    rewrite +ₘ-identityˡ rs
--      = cong (λ φ → (c ∷ φ) ∷ rs) (lemma cs)
--    where
--      lemma
--          : ∀ {m} (cs : Vec 𝔸 m)
--          → zipWith _+_ (replicate 0#) cs ≡ cs
--      lemma [] = refl
--      lemma (c ∷ cs)
--        rewrite +-identityˡ c
--        rewrite lemma cs
--          = refl
```

Clearly we are onto something with our new representation.








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


