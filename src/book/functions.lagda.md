# Functions, Big and Small

```agda
module functions where

open import Level using (Level)
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

  infix 3 _==_
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

Clearly we are onto something with our new representation. A problem which once
was hard is now much easier. Content with our new representation, we can explore
the question of what *is* a matrix, and why do practitioners care so much about
them.


### Matrices as Functions

The type of `_*ₘ_ : Matrix m n → Matrix n p → Matrix m p` is somewhat suspicious
in its requirement that both matrices have a `n` dimension, in different
positions, which gets eliminated being pushed through the multiplication.
Compare this type against that of function composition, namely `_∘_ : (B → C) →
(A → B) → (A → C)`, which seems oddly similar: the functions both need a `B`
parameter, on opposite sides of the arrow, which gets eliminated in the result.

This is not a coincidence, because nothing is ever a coincidence. Whenever the
indices need to align, you should immediately think "function" (or at least
"morphism," as we will discuss in @sec:categorytheory.) But, if matrices
correspond to functions, exactly which functions are we talking about? The
indices give us a clue --- the input must be parameterized by exactly one of
`m`, `n`, and the output must be the other. In every day tasks, matrices are
usually multiplied against column vectors. For example, if we think about a
2-dimensional space with XY coordinates, the corresponds to a 90 degree
rotation clockwise:

$$
\begin{bmatrix}
0 & -1\\
1 & 0
\end{bmatrix}
$$

We can thus apply this matrix to a particular coordinate, let's say $(5, 6)$, as
follows:

$$
\begin{bmatrix}
0 & -1\\
1 & 0
\end{bmatrix}
\times
\begin{bmatrix}
5 \\
6
\end{bmatrix}
$$

Viewed in this light, the XY coordinate is the input, the rotation matrix is the
function, and the result of the multiplication is the output. Thus, it seems
natural to call the "width" of the matrix its input index. Let's define the type
of vectors as functions into our scalar:

```agda
  Vec : ℕ → Set
  Vec n = Fin n → 𝔸
```

Nothing goes particularly wrong if we were to use the standard `Data.Vec`
encoding instead, but this saves us some lemmas to more naturally turn vectors
into matrices and vice versa. Given vectors, we can lift them into column
matrices:

```agda
  column : Vec m → Matrix m 1
  column v i _ = v i
```

which gives rise to a natural definition of the interpretation of a matrix as a
function from vectors to vectors:

```agda
  ⌊_⌋ : Matrix m n → Vec n → Vec m
  ⌊ M ⌋ v i = (M *ₘ column v) i zero
```

This is merely a convention; nothing prevents us from multiplying on the left
instead. In fact, we will prove this fact later (see `ᵀ-*ₘ-braid`.) For the time
being, we'd like to prove that function composition is indeed a specification
for `_*ₘ_`. That is, we'd like to work our way towards a proof of `⌊*ₘ⌋⟶⌊⌋∘⌊⌋ :
(g : Matrix m n) → (f : Matrix n p) → ∀ v → ⌊ g *ₘ f ⌋ v ≗ (⌊ g ⌋ ∘ ⌊ f ⌋) v`.
It's a bit of a mouthful, but really what we're saying here is that the
interpretation of matrix multiplication is the composition of the matrices
interpreted as functions.

We will build our way towards this proof, but as a helper lemma, it will be
valuable to show the extensionality of sum---that is, if we can show the
equivalence of each term in the sum, we can thus show the two sums themselves
are equal. This function requires a little bit of induction on the `Fin`ite
numbers, but is a straightforward application of rewriting:

```agda
  sum-ext
      : {f g : Fin m → 𝔸}
      → f ≗ g
      → sum f ≡ sum g
  sum-ext {zero} x = refl
  sum-ext {suc m} same
    rewrite same zero
    rewrite sum-ext (same ∘ suc)
      = refl
```

Our next lemma is to show that multiplication distributes over `sum`. This is a
straightforward application of the fact that multiplication distributes over
addition; only, we need to repeat the argument for every term in the sum. We
assume two non-controversial facts about `𝔸`:

```agda
  postulate
    *-zeroˡ : ∀ x → 0# * x ≡ 0#
    *-+-distribʳ : ∀ x y z → (x + y) * z ≡ (x * z) + (y * z)
```

and then can show `*-sum-distribʳ` in earnest:

```agda
  *-sum-distribʳ
    : {f : Fin m → 𝔸}
    → (k : 𝔸)
    → sum f * k ≡ sum (λ i → f i * k)
  *-sum-distribʳ {zero} k = *-zeroˡ k
  *-sum-distribʳ {suc m} {f} k
    rewrite *-+-distribʳ (f zero) (sum (f ∘ suc)) k
    rewrite *-sum-distribʳ {f = f ∘ suc} k
      = refl

  sum-zero : sum {m} (λ _ → 0#) ≡ 0#
  sum-zero {zero} = refl
  sum-zero {suc m}
    rewrite sum-zero {m}
      = +-identityˡ 0#
```

There are a few more facts to prove about sums before we can get to the meat of
our proof. But first, another reasonable assumption about `𝔸` --- namely that
it's multiplication is commutative:

```agda
  postulate
    *-comm : ∀ x y → x * y ≡ y * x
```

and, for the sake of the reader's (and the author's) sanity, we will postulate
`…algebra…` stating that the intermediary step is a tedious-but-straightforward
application of grade-school algebra:

```agda
    …algebra… : {ℓ : Level} {A : Set ℓ} {x y : A} → x ≡ y
```

Returning to our final two lemmas: first, we can show that the sum of two `sum`s
over the same bounds is the `sum` of the sum.

```agda
  +-sum-hom
    : (f g : Fin m → 𝔸)
    → sum f + sum g ≡ sum (λ i → f i + g i)
```

The proof of this is rather verbose, but is just some shuffling of the addition
terms and a recursive call:

```agda
  +-sum-hom {zero} f g = +-identityˡ 0#
  +-sum-hom {suc m} f g = begin
      (f zero + sum (f ∘ suc)) + (g zero + sum (g ∘ suc))
    ≡⟨ …algebra… ⟩
      (f zero + g zero) + (sum (f ∘ suc) + sum (g ∘ suc))
    ≡⟨ cong ((f zero + g zero) +_)
            (+-sum-hom (f ∘ suc) (g ∘ suc)) ⟩
      (f zero + g zero) + sum (λ i → f (suc i) + g (suc i))
    ∎
    where open ≡-Reasoning
```

Our final necessary lemma before showing that matrix multiplication is a model
for function composition is to show that we can arbitrarily swap nested `sum`s,
so long as doing so doesn't introduce any scoping issues. The idea is that,
given some function `f : Fin m → Fin n → 𝔸`, we can freely interchange nested
`sum`s which iterate over `m` and `n`. First, the type:

```agda
  postulate
    *-zeroʳ : ∀ x → x * 0# ≡ 0#

  -- TODO(sandy): write some prose about this, pull from above, fix it
  sum-0 : sum {m} (λ k → 0#) ≡ 0#
  sum-0 = begin
    sum (λ k → 0#)       ≡⟨ sym (sum-ext (λ _ → *-zeroˡ 0#)) ⟩
    sum (λ k → 0# * 0#)  ≡⟨ sym (*-sum-distribʳ 0#) ⟩
    sum (λ k → 0#) * 0#  ≡⟨ *-zeroʳ _ ⟩
    0#                   ∎
    where open ≡-Reasoning
```

```agda
  sum-sum-distrib
      : (f : Fin m → Fin n → 𝔸)
      → sum (λ j → sum (λ k → f j k))
      ≡ sum (λ k → sum (λ j → f j k))
```

Take a moment to really understand what's going on in this type signature before
continuing. The only difference in the terms we'd like to show equivalence of is
which `sum` binds `j` and which binds `k`. We can proceed by induction on `m`,
which first requires us to show the sum of many 0 terms is itself zero:

```agda
  sum-sum-distrib {zero} {n} f = sym (sum-0)
```

The inductive case isn't particularly interesting, we just need to get
everything into the right shape that we can invoke `sum-sum-distrib`:

```agda
  sum-sum-distrib {suc m} {n} f =
    begin
      sum (λ k → f zero k) + sum (λ j → sum (λ k → f (suc j) k))
    ≡⟨ cong (sum _ +_) (sum-sum-distrib (λ j → f (suc j))) ⟩
      sum (λ k → f zero k) + sum (λ k → sum (λ j → f (suc j) k))
    ≡⟨ +-sum-hom _ _ ⟩
      sum (λ k → f zero k + sum (λ j → f (suc j) k))
    ∎
    where open ≡-Reasoning
```

Finally we get to the meat of our goal: to show that the interpretation of
matrix multiplication is the composition of the interpretation of matrices as
functions. Start with the type:

```agda
  ⌊*ₘ⌋⟶⌊⌋∘⌊⌋
    : (g : Matrix m n)
    → (f : Matrix n p)
    → (v : Fin p → 𝔸)
    → ⌊ g *ₘ f ⌋ v ≗ (⌊ g ⌋ ∘ ⌊ f ⌋) v
```

The proof mostly writes itself, given the lemmas we've already proven. Of
course, if you were working this out for yourself, you'd start with `⌊*ₘ⌋⟶⌊⌋∘⌊⌋`
and work backwards, determining which lemmas you need and proving them. This is
one flaw of presenting a book as a literate Agda document; it's hard to show
things in the order they happen "in real life."

```agda
  ⌊*ₘ⌋⟶⌊⌋∘⌊⌋ g f v i = begin
      sum (λ j → sum (λ k → g i k * f k j) * v j)
    ≡⟨ sum-ext (λ j → *-sum-distribʳ (v j))  ⟩
      sum (λ j → sum (λ k → (g i k * f k j) * v j))
    ≡⟨ sum-sum-distrib (λ j k → (g i k * f k j) * v j) ⟩
      sum (λ k → sum (λ j → (g i k * f k j) * v j))
    ≡⟨ …algebra… ⟩
      sum (λ k → sum (λ j → (f k j * v j) * g i k))
    ≡⟨ sym (sum-ext (λ k → *-sum-distribʳ (g i k))) ⟩
      sum (λ k → sum (λ j → f k j * v j) * g i k)
    ≡⟨ sum-ext (λ k → *-comm _ _) ⟩
      sum (λ k → g i k * sum (λ j → f k j * v j))
    ∎
    where open ≡-Reasoning
```

As a nice sanity check, we would like it if `⌊ 1ₘ ⌋` were the `id` function. So
let's show it!

```agda
  postulate
    *-identityˡ : ∀ x → 1# * x ≡ x
    +-identityʳ : ∀ x → x + 0# ≡ x

  ⌊1ₘ⌋ : ∀ v → ⌊ 1ₘ {m} ⌋ v ≗ v
  ⌊1ₘ⌋ {suc m} v zero
    rewrite *-identityˡ (v zero)
    rewrite sum-ext (λ x → *-zeroˡ (v (suc x)))
    rewrite sum-0 {m}
    rewrite +-identityʳ (v zero)
      = refl
  ⌊1ₘ⌋ v (suc x)
    rewrite *-zeroˡ (v zero)
    rewrite ⌊1ₘ⌋ (v ∘ suc) x
      = +-identityˡ _
```

Let's return now to the question of whether we made a bad choice when defining
our interpretation as multiplication on the right by a column vector. To
contrast, we can implement `⌊_⌋′`, which performs multiplication on the left
with a row vector:

```agda
  row : (Fin n → 𝔸) → Matrix 1 n
  row v _ j = v j

  ⌊_⌋′ : Matrix m n → Vec m → Vec n
  ⌊ M ⌋′ v i = (row v *ₘ M) zero i
```

My claim is that we don't need `⌊_⌋′`; instead, we can simply use `⌊_⌋` with the
*transpose* of the matrix. The transpose swaps a matrix's width for its height,
and vice versa:

```agda
  infix 100 _ᵀ
  _ᵀ : Matrix m n → Matrix n m
  (M ᵀ) i j = M j i
```

It's trivial now to show that `⌊_⌋'` is nothing more than `⌊_⌋ ∘ _ᵀ` --- that
is, the interpretation of the transpose of the original matrix! The proof
depends only on the commutativity of multiplication, which makes sense when you
think about what these two operations must be doing:

```agda
  ⌊⌋′-is-⌊ᵀ⌋
      : (a : Matrix m n)
      → (v : Vec m)
      → ⌊ a ⌋′ v ≗ ⌊ a ᵀ ⌋ v
  ⌊⌋′-is-⌊ᵀ⌋ a v x = sum-ext λ k → *-comm _ _

  ⌊gᵀ∘fᵀ⌋-⌊f∘g⌋ᵀ
      : (g : Matrix n m)
     →  (f : Matrix p n)
      → g ᵀ *ₘ f ᵀ ≡ₘ (f *ₘ g) ᵀ
  ⌊gᵀ∘fᵀ⌋-⌊f∘g⌋ᵀ g f i j = sum-ext λ _ → *-comm _ _
```

Because of `⌊⌋′-is-⌊ᵀ⌋`, we are able to make the arbitrary decision to multiply
on the right without any loss of generalization. Anyone who thinks we've made
the wrong decision is welcome to transpose their matrix first.



So, what kind of functions are representable as matrices? As it happens, they
are precisely the *linear maps* --- that is, the two properties must hold:

```agda
  map : (𝔸 → 𝔸) → Vec m → Vec m
  map f v i = f (v i)

  zip : (𝔸 → 𝔸 → 𝔸) → Vec m → Vec m → Vec m
  zip f v₁ v₂ i = f (v₁ i) (v₂ i)

  record LinearFunction (f : Vec m → Vec n) : Set where
    constructor _⊢_
    field
      additive
          : ∀ v₁ v₂
          → f (zip _+_ v₁ v₂) ≗ zip _+_ (f v₁) (f v₂)
      homogeneity
          : ∀ v x
          → f (map (x *_) v) ≗ map (x *_) (f v)
  open LinearFunction

  open import Data.Product
    using (Σ; proj₁; proj₂)

  ⌈_⌉ : {f : Vec n → Vec m} → LinearFunction f → Matrix m n
  ⌈_⌉ {f = f} _ i j = f (1ₘ j) i

  postulate
    vec-ext : {f g : Vec m} → (∀ i → f i ≡ g i) → f ≡ g
    *-identityʳ : ∀ x → x * 1# ≡ x
    matrix-ext : {f g : Matrix m n} → f ≡ₘ g → f ≡ g

--   _*ᵥ_ : 𝔸 → Vec m → Vec m
--   a *ᵥ v = map (a *_) v

--   basis-sum : (v : Vec m) → Vec m
--   basis-sum v x = sum λ { k → (v k *ᵥ 1ₘ k) x }

--   v-is-basis : (v : Vec m) → basis-sum v ≗ v
--   v-is-basis {suc m} v zero
--     rewrite *-identityʳ (v zero)
--     rewrite sum-ext (λ k → *-zeroʳ (v (suc k)))
--     rewrite sum-zero {m}
--       = +-identityʳ (v zero)
--   v-is-basis v (suc x)
--     rewrite *-zeroʳ (v zero)
--     rewrite v-is-basis (v ∘ suc) x
--     rewrite +-identityˡ (v (suc x))
--       = refl


  raise : Vec m → Vec (suc m)
  raise v zero = 0#
  raise v (suc i) = v i

  +-raise-hom
      : ∀ v₁ v₂ x
      → raise {m} (λ i → v₁ i + v₂ i) x ≡ raise v₁ x + raise v₂ x
  +-raise-hom v₁ v₂ zero rewrite +-identityʳ 0# = refl
  +-raise-hom v₁ v₂ (suc x) = refl

  *-raise-hom
      : ∀ v x → raise {m} (map (x *_) v) ≗ map (x *_) (raise v)
  *-raise-hom v x zero
    rewrite *-zeroʳ x = refl
  *-raise-hom v x (suc i) = refl

  linear-raise
      : {f : Vec (suc m) → Vec n}
      → LinearFunction f
      → LinearFunction (λ i j → f (raise i) j)
  additive (linear-raise {f = f} (add ⊢ _)) v₁ v₂ x =
    begin
      f (raise (λ i → v₁ i + v₂ i)) x
    ≡⟨ cong (λ φ → f φ x) (vec-ext (+-raise-hom v₁ v₂)) ⟩
      f (λ i → raise v₁ i + raise v₂ i) x
    ≡⟨ add _ _ x ⟩
      f (raise v₁) x + f (raise v₂) x
    ∎
    where open ≡-Reasoning
  homogeneity (linear-raise {f = f} (_ ⊢ hom)) v x i =
    begin
      f (raise (map (_*_ x) v)) i
    ≡⟨ cong (λ φ → f φ i) (vec-ext (*-raise-hom _ _)) ⟩
      f (map (_*_ x) (raise v)) i
    ≡⟨ hom _ x i ⟩
      map (_*_ x) (f (raise v)) i
    ∎
    where open ≡-Reasoning

  lemma : ∀ (f : Vec (suc m) → Vec n)
            (i : Fin n) (j : Fin m) →
          f (1ₘ (suc j)) i ≡ f (raise (1ₘ j)) i
  lemma f i x =
    cong (λ φ → f φ i)
      (vec-ext λ { zero → refl
                 ; (suc n) → refl
                 })

  lemma₁ : (v : Vec (suc m)) (i : Fin (suc m)) →
          ((v zero * (if zero == i then 1# else 0#)) +
            raise (λ x₁ → v (suc x₁)) i)
          ≡ v i
  lemma₁ v zero
    rewrite *-identityʳ (v zero)
      = +-identityʳ (v zero)
  lemma₁ v (suc i)
    rewrite *-zeroʳ (v zero)
      = +-identityˡ (v (suc i))

  linear-to-matrix
      : {f : Vec m → Vec n}
      → (lf : LinearFunction f)
      → ∀ v
      → ⌊ ⌈ lf ⌉ ⌋ v ≗ f v
  linear-to-matrix {zero} {n} {f} (add ⊢ hom) v x = begin
    0#                    ≡⟨ sym (*-zeroˡ _) ⟩
    0# * f v x            ≡⟨ sym (hom v 0# x) ⟩
    f (λ i → 0# * v i) x  ≡⟨ cong (λ φ → f φ x) (vec-ext λ ()) ⟩
    f v x                 ∎
    where open ≡-Reasoning
  linear-to-matrix {suc m} {n} {f} (add ⊢ hom) v x =
    begin
      ⌊ ⌈ add ⊢ hom ⌉ ⌋ v x
    ≡⟨⟩
      ((λ i j → f (1ₘ j) i) *ₘ column v) x zero
    ≡⟨⟩
      sum (λ i → f (1ₘ i) x * v i)
    ≡⟨⟩
      (f (1ₘ zero) x * v zero) + sum (λ i → f (1ₘ (suc i)) x * v (suc i))
    ≡⟨⟩
      (f (1ₘ zero) x * v zero) + (((λ i j → f (1ₘ (suc j)) i) *ₘ column (v ∘ suc)) x zero)
    ≡⟨⟩
      (f (1ₘ zero) x * v zero) + ⌊ (λ i j → f (1ₘ (suc j)) i)⌋ (v ∘ suc) x
    ≡⟨ cong (λ φ → (f (1ₘ zero) x * v zero) + ⌊ φ ⌋ (v ∘ suc) x) (matrix-ext (lemma f)) ⟩
      (f (1ₘ zero) x * v zero) + ⌊ ⌈ linear-raise (add ⊢ hom) ⌉ ⌋ (v ∘ suc) x
    ≡⟨ cong (λ φ → (f (1ₘ zero) x * v zero) + φ) (linear-to-matrix (linear-raise (add ⊢ hom)) (v ∘ suc) x)  ⟩
      (f (1ₘ zero) x * v zero) + f (raise (v ∘ suc)) x
    ≡⟨ …algebra… ⟩
      (v zero * f (1ₘ zero) x) + f (raise (v ∘ suc)) x
    ≡⟨ sym (cong (_+ f (raise (v ∘ suc)) x) (hom _ _ _)) ⟩
      f (map (_*_ (v zero)) (1ₘ zero)) x + f (raise (v ∘ suc)) x
    ≡⟨ sym (add _ _ x) ⟩
      f (λ i → (v zero * (if zero == i then 1# else 0#)) + raise (λ x₁ → v (suc x₁)) i) x
    ≡⟨ cong (λ φ → f φ x) (vec-ext (lemma₁ v)) ⟩
      f v x
    ∎
    where open ≡-Reasoning

  ⌊⌋-linear : (M : Matrix m n) → LinearFunction ⌊ M ⌋
  additive (⌊⌋-linear M) v₁ v₂ i = begin
    ⌊ M ⌋ (zip _+_ v₁ v₂) i                      ≡⟨⟩
    sum (λ j → M i j * (v₁ j + v₂ j))            ≡⟨ …algebra… ⟩
    sum (λ j → (M i j * v₁ j) + (M i j * v₂ j))  ≡⟨ sym (+-sum-hom _ _) ⟩
    ⌊ M ⌋ v₁ i + ⌊ M ⌋ v₂ i                      ∎
    where open ≡-Reasoning
  homogeneity (⌊⌋-linear M) v x i = begin
    ⌊ M ⌋ (map (x *_) v) i         ≡⟨⟩
    sum (λ j → M i j * (x * v j))  ≡⟨ …algebra… ⟩
    sum (λ j → (M i j * v j) * x)  ≡⟨ sym (*-sum-distribʳ x) ⟩
    sum (λ j → M i j * v j) * x    ≡⟨ *-comm _ x ⟩
    x * sum (λ j → M i j * v j)    ≡⟨⟩
    map (x *_) (⌊ M ⌋ v) i         ∎
    where open ≡-Reasoning

```

subsets


