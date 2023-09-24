# Monoids and Setoids

Hidden

:   ```agda
{-# OPTIONS --allow-unsolved-metas #-}
    ```

```agda
module Chapter7-Structures where
```

Prerequisites

:   ```agda
open import Chapter1-Agda
    ```

:   ```agda
open import Chapter2-Numbers
    ```

:   ```agda
open import Chapter3-Proofs
  hiding (refl; sym; trans)
import Chapter3-Proofs as ≡
    ```

:   ```agda
open import Chapter4-Relations
    ```

:   ```agda
open import Chapter5-Modular-Arithmetic
  using (equiv-to-preorder; ≡-is-equivalence; refl; sym; trans)
    ```

In this chapter we will now try our hands at interpreting abstract mathematical
structures. We will see how we can translate them into Agda definitions and
explore what can go wrong when we use only our existing notions of equality. But
most excitingly, we will look at a bevy of usual functions in computer science,
and see how they all arise "for free" by instantiating the same generic code
with different abstract mathematical objects.

This is one of my favorite examples for bridging between pure math and computer
science, as it shows an exciting side-effect---not only is the math interesting
for its own sake, but it also is real-world applicable, and serves to illustrate
patterns in code that you might never have noticed before.

Without further ado, let's begin.


## Structured Sets

A huge chunk of "real" mathematics is done over the *structured sets,* which, as
you might expect, are sets equipped with some structure. That structure usually
comes in three flavors: elements, operations, and laws. We've already seen
examples of structured sets---equivalence relations are sets that satisfy the
laws of reflexivity, symmetry, and transitivity.

When you encounter the definition of a structured set in the wild, it's often
presented in a sort of mad-libs style, instantiating the following template:

> A *widget* is a *variety of set* equipped with *some operations* and *some
> elements*, subject to *laws*.

Structured sets are usually given in a concise form, very similar to the above.
Being able to quickly parse definitions like these is essential to getting real
work done. That being said, having the definition is only the first
hurdle---what's much more important is gaining the related intuition behind what
this widget is and why we should care about it.

In the next section, we will work our way through parsing and subsequently
understanding a particularly rich example of a structured set: the unassuming
and understated *monoid.*


## Monoids

The terse, textbook definition of a *monoid* is:

> A monoid is a set equipped with an associative binary operation `_∙_` and an
> identity element `ε`.

We can parse out the mad-libs here, which tells us a monoid is a *set* (that is
to say, it's not a special case of some other structured set), equipped with one
*binary operation* `_∙_`, and has *one element* `ε`. The *laws* are left implicit
in this definition, but not unsaid.

Reading between the lines, we see that the binary operation is said to be
*associative*, and that `ε` is an *identity.* An identity must always be
relative to some operation, and there is only one operation around, so we infer
that `ε` must be an identity for `_∙_`. Furthermore, we are not told whether `ε`
is a left- or a right- identity on `_∙_`, so we assume it must be both.

Therefore, we can see that there are three laws hidden in the original
definition: `_∙_` is associative, `ε` is a left-identity on `_∙_`, and that `ε`
is a right-identity on `_∙_`. Fleshing these laws out into symbols, they say:

$$
a \cdot (b \cdot c) = (a \cdot b) \cdot c
$$

$$
\epsilon \cdot x = x
$$

$$
x \cdot \epsilon = x
$$

As a note on terminology, the element `ε` is often called the *unit* of the
monoid, and the operation `_∙_` is often called *multiplication.* These names
are historical, but come from the fact that monoids generalize a lot of the
intuition we have regarding everyday multiplication over numbers.

Having now mentally parsed the definition of a monoid, let's see about coding it
all up in Agda. We'll start with some variables to simplify some definitions:

```agda
private variable
  ℓ ℓ₁ ℓ₂ : Level
  A : Set ℓ
  B : Set ℓ
  C : Set ℓ
```

And will introduce `type:Op₂`, which is the type of a binary operation:

```agda
private
  Op₂ : {ℓ : Level} → Set ℓ → Set ℓ
  Op₂ A = A → A → A
```

Note that we have marked `type:Op₂` as `keyword:private` only as a technical
detail. A `keyword:private` definition can still be used in the current module,
but it isn't automatically exported. This is because we'd like to export
`type:Op₂` from the standard library at the end of this chapter, and can't be
bothered to deal with identifier conflicts.

With that digression made, we can now make a new module to encode monoids. I
happen to know that something will go wrong in the process, so we will call this
module `module:Sandbox-Naive-Monoids`.

```agda
module Sandbox-Naive-Monoids where
```

We will now formalize monoids. Recall their definition:

> A monoid is *a set* equipped with an associative binary operation `_∙_` and an
> identity element `ε`.

Given this definition, we'd like to build a type `type:IsMonoid` which states
that `_∙_` and `ε` form a monoid. This is not the only way to do things, but it
does lead to very clear type signatures. I've italicized the words *a set* in
the definition to emphasize that this definition is also parameterized over some
`type:Set`, which we call the *carrier set.*

All of this lends itself to a concise definition of `type:IsMonoid`:

```agda
  record IsMonoid {Carrier : Set ℓ}
                  (_∙_ : Op₂ Carrier)
                  (ε : Carrier)
        : Set (lsuc ℓ) where
    field
      assoc      : (x y z : Carrier) → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)
      identityˡ  : (x : Carrier) → ε ∙ x ≡ x
      identityʳ  : (x : Carrier) → x ∙ ε ≡ x

  open IsMonoid
```

It's a good habit to look for concrete examples of mathematical structures
whenever you come across them. Studying concrete examples is an excellent way of
building intuition for the otherwise abstract nonsense that higher-level math
can often feel like.


## Examples of Monoids

I mentioned above that the terminology of "unit" and "multiplication" for
monoids' object and operation, respectively, comes historically from the fact
that monoids generalize multiplication. And indeed, there is a monoid over
`def:ℕ`, literally using `def:_*_` as the multiplication and 1 as the unit:

```agda
  -- TODO(sandy): Maybe just import the chapter qualified at the beginning, and
  -- import these definitions as needed.

  *-1 : IsMonoid _*_ 1
  assoc      *-1 = *-assoc
  identityˡ  *-1 = *-identityˡ
  identityʳ  *-1 = *-identityʳ
```

The idea behind monoids is that their multiplication corresponds to some
abstract "operation" (in the usual sense of the word), together with some means
of *doing nothing.* In the `def:*-1` example, multiplication by one doesn't
change the result, and therefore does nothing. The associativity requirement is
a little more subtle, which we will explore in more detail when discussing how
to actually *use* monoids.

Let's take some time to look for other examples of monoids. Staying on the
natural numbers, is there some other operation you can think of that also comes
with a notion of "don't do anything?"

Addition with zero seems to satisfy the intuition. And indeed, we can show it
also forms a monoid:

```agda
  +-0 : IsMonoid _+_ 0
  assoc      +-0 = +-assoc
  identityˡ  +-0 = +-identityˡ
  identityʳ  +-0 = +-identityʳ
```

When you start looking for them, you'll begin to monoids everywhere. Let's
consider the booleans. Recall our two functions `def:_∨_` and `def:_∧_`---are
they components of any monoids?

```agda
  ∨-false : IsMonoid _∨_ false
  assoc      ∨-false = ∨-assoc
  identityˡ  ∨-false = ∨-identityˡ
  identityʳ  ∨-false = ∨-identityʳ

  ∧-true : IsMonoid _∧_ true
  assoc      ∧-true = ∧-assoc
  identityˡ  ∧-true = ∧-identityˡ
  identityʳ  ∧-true = ∧-identityʳ
```

As we have seen, for any given carrier set, there can be many different monoids.
Interestingly, there can also be different monoids for the same carrier set and
identity element, as seen below. The `def:xor` function computes whether exactly
one of its two arguments is `ctor:true`:

```agda
  xor : Bool → Bool → Bool
  xor false  y = y
  xor true   y = not y
```

We can directly read off of this definition that `ctor:false` is a
left-identity. As you might expect, `def:xor` also forms a monoid:

```agda
  xor-false : IsMonoid xor false
  assoc xor-false false y z        = refl
  assoc xor-false true false z     = refl
  assoc xor-false true true false  = refl
  assoc xor-false true true true   = refl
  identityˡ xor-false x     = refl
  identityʳ xor-false false = refl
  identityʳ xor-false true  = refl
```

Notice that we have not proven the intermediary results `def:xor-assoc`,
`def:xor-identityˡ` or `def:xor-identityʳ`, choosing instead to inline their
definitions. Each of those theorems does indeed hold, and it's good practice to
write them out for any future proofs that might require such. We will not do it
here, but you are encouraged to define them on your own.

There are lots more monoids (infinitely many, in fact) but this is a good
starting point for us to build some intuition. In the next section we'll explore
what sorts of problems monoids can help us solve.


## Monoids as Queries

I like to mentally associate a catchphrase with every abstract mathematical
idea I come across. Doing so gives me an informal hook on which to hang
examples, and a convenient question to ask when encountering new problems. After
all, if I know that structure X solves problems that look like Y, whenever I
come across a Y problem, I immediately start thinking about X. In the case of
monoids, my catchphrase is:

> Monoids generate summaries.

Fleshed out in more detail, the carrier set of a monoid corresponds to the
type of answer I'd like to get. The unit corresponds to the "default" summary,
and multiplication gives us a means of combining summaries together. Another way
of thinking about this is that monoids generalize the answers you get when
querying a database.

We'll see many examples of exactly what I mean by this momentarily. But first,
we require a little more machinery in Agda.

I said earlier that `type:IsMonoid` is a convenient type for showing off
monoids, but it's a rather frustrating thing to work with generically. Whenever
we'd like to talk about `type:IsMonoid`, we'd better have a *particular* `_∙_`
and `ε` that we can use as parameters. This is great when we'd like to discuss a
single monoid, but it grows in complexity when we'd like to talk about the
structure abstractly.

A common solution in Agda is to "bundle" a type's parameters with its contents,
so you just pass the whole structure around at once. The bundled version of
`type:IsMonoid` is just `type:Monoid`, and it looks like this:

```agda
  record Monoid {c : Level} (Carrier : Set c) : Set (lsuc c) where
    infixl 7 _∙_
    field
      _∙_  : Op₂ Carrier
      ε    : Carrier
      is-monoid : IsMonoid _∙_ ε
```

We could have also chosen to bundle up the carrier set inside
`type:Monoid`[^as-the-stdlib], but such will be inconvenient for us, as we'd
like to give `type:Monoid` instances to Agda so we can overload the syntax of
`field_∙_` and `field:ε`. Doing so, however, requires *something* for Agda to
dispatch on, and we will use the carrier set for that purpose.

[^as-the-stdlib]: The standard library does indeed bundle the carrier set. This
makes some tasks easier, and some harder.

With our new `type:Monoid` bundle in hand, we can use the `def:bundle` function
to repackage a `type:IsMonoid` as a `type:Monoid`:

```agda
  bundle
      : {c : Level} {A : Set c} {∙ : Op₂ A} {ε : A}
      → IsMonoid ∙ ε
      → Monoid A
  Monoid._∙_  (bundle {∙ = ∙}  x)  = ∙
  Monoid.ε    (bundle  {ε = ε} x)  = ε
  Monoid.is-monoid (bundle x) = x
```

Finally, we will open `type:Monoid` as as typeclass:

```agda
  open Monoid ⦃ ... ⦄
```

We are now ready to investigate the sense in which a monoid can be considered a
summary of data. Let's make a new module parameterized by some `expr:Monoid
Bool` instance. Doing so will allow us to use `field:_∙_` and `field:ε`
abstractly:

```agda
  module _ ⦃ _ : Monoid Bool ⦄ where
    ex₁ : Bool
    ex₁ = false ∙ true ∙ false ∙ false

    ex₂ : Bool
    ex₂ = true ∙ true ∙ true ∙ true

    ex₃ : Bool
    ex₃ = ε
  -- FIXEXPR
```

The way to think about `def:ex₁` and friends is that they compute abstract
summaries of the booleans multiplied together in each. By instantiating them
with different `def:Monoid`s, we can get different summaries of the data. For
example, if we were to use `expr:bundle ∨-false`, we could compute if there
exists at least one `ctor:true` in each data set:

```agda
  module _ where
    private instance
      _ = bundle ∨-false

    _ : ex₁ ≡ true
    _ = refl

    _ : ex₂ ≡ true
    _ = refl

    _ : ex₃ ≡ false
    _ = refl
  -- FIXEXPR
```

Alternatively, if we were to use `expr:bundle ∧-true`, we would instead compute
whether *every* boolean in the dataset be `ctor:true`:

```agda
  module _ where
    private instance
      _ = bundle ∧-true

    _ : ex₁ ≡ false
    _ = refl

    _ : ex₂ ≡ true
    _ = refl

    _ : ex₃ ≡ true
    _ = refl
```

Note that in the `def:ex₃` case, there are *no* booleans, and so vacuously they
are all `ctor:true`.

As a third illustration of summarizing this dataset, we can use the
`def:xor-false` monoid to determine whether there is an *odd* number of
`ctor:true`s in each example. This summary is often known as a "parity" or
"checksum," and is used as a simple way of checking for errors when transmitting
data across a noisy channel[^checksum].

[^checksum]: The idea is to compute the parity of the data you'd like to send,
  and then to add an extra bit which ensures the parity is always `ctor:false`.
  When you receive the data, you can *check* the parity *sum* for yourself, and
  if it's `ctor:true`, you know something went wrong during transmission. Of
  course, an even number of things could have gone wrong and you wouldn't know,
  so checksums in practice often consist of many different parity checks at
  once.

```agda
  module _ where
    private instance
      _ = bundle xor-false

    _ : ex₁ ≡ true
    _ = refl

    _ : ex₂ ≡ false
    _ = refl

    _ : ex₃ ≡ false
    _ = refl
  -- FIXEXPR
```

There you have it---three different monoids give us three different answers when
summarizing each of `def:ex₁`, `def:ex₂`, and `def:ex₃`. When we conceptualize
`def:ex₁` and friends as datasets, our different monoids correspond to different
questions we can ask about that data.

Of course, the booleans are such a small type that the sort of questions we can
ask are extremely limited. Let's therefore take some time to find more examples
of monoids, keeping our catchphrase that "monoids generate summaries" in mind as
we do so.


## More Monoids

In @sec:maybe we looked at the `type:Maybe` type, which is parameterized by
another type, extending it with the possibility that there might not be any data
inside. Recall that we use the `ctor:nothing` constructor to give this lack of
data, and the `ctor:just` constructor to inject a value of type `A` into
`expr:Maybe A`.

A natural operation over `type:Maybe` is thus to combine two maybe values,
hoping that at least one of them is a `ctor:just`. This operation is called
`def:_<∣>_` and pronounced "alt." Make sure you type the vertical bar via
[`|`](AgdaMode), because the usual vertical bar on your keyboard has special
meaning in Agda and you will get mysterious errors if you use it.

```agda
  _<∣>_ : Maybe A → Maybe A → Maybe A
  just x  <∣> my = just x
  nothing <∣> my = my
```

Given `def:_<∣>_`, we can show it forms a monoid with `ctor:nothing` as the
unit:

```agda
  <∣>-nothing : IsMonoid {Carrier = Maybe A} _<∣>_ nothing
  assoc <∣>-nothing (just x)  y z = refl
  assoc <∣>-nothing nothing   y z  = refl
  identityˡ <∣>-nothing x = refl
  identityʳ <∣>-nothing (just x)  = refl
  identityʳ <∣>-nothing nothing   = refl
```

Because we'd like `def:<∣>-nothing` to work over any type at all, we must
explicitly state its carrier is `type:Maybe` `A` in the type signature.

As a summarizing mechanism, `def:<∣>-nothing` gives us back the first
`ctor:just` in a dataset, ignoring everything that comes afterwards. In case
that there are no `ctor:just`s to be found, we will get back a `ctor:nothing`.
While this is nice, you might wonder if there is a corresponding monoid that
takes the *last* `ctor:just` that it finds. And of course, there is.

But rather than going through all of the effort of writing a right-biased
version of `def:_<∣>_`, we can instead consider the problem more generally.
Since `field:ε` is both a left- and a right-identity for `field:_∙_`, the only
asymmetry here comes from `field:_∙_` itself. However, nothing in the problem
statement enforces this asymmetry on us; it just reflects an arbitrary choice on
which of the two arguments to `field:_∙_` we decide to privilege.

Whenever you find yourself at the whim of an arbitrary choice made, your spidey
senses should start tingling. Usually it's an opportunity for us to get a
different arbitrary choice for free. This is the motivation behind the
`def:dual` monoid, which states that we can always derive a new monoid by
flipping the order of the arguments on `field:_∙_`.

We can construct the dual in two pieces. First, we must show that for any
non-dependent function, we can flip the order of its arguments:

```agda
  flip : (A → B → C) → B → A → C
  flip f b a = f a b
```

and now, we can show that given some `type:IsMonoid`, we can derive another
whose operation has been `def:flip`ped:

```agda
  dual : {_∙_ : Op₂ A} {ε : A}
       → IsMonoid _∙_         ε
       → IsMonoid (flip _∙_)  ε
  assoc      (dual m) x y z  = sym (assoc m z y x)
  identityˡ  (dual m)        = identityʳ m
  identityʳ  (dual m)        = identityˡ m
```

We can now get the last-`just`-wins monoid for free, since it's just
`expr:dual <∣>-nothing`.

As another example of monoids, we note that lists form one under concatenation
and the empty list. Rather incredibly, we've made it all the way to chapter 7
in a book on function programming without mentioning lists, so let's quickly
give a definition:

```agda
  data List (A : Set ℓ) : Set ℓ where
    []   : List A
    _∷_  : A → List A → List A
  infixr 5 _∷_
```

Lists of `A` are either empty (given by `ctor:[]`), or they are given by an `A`
stuck in front of another list. With this definition, we can quickly define list
concatenation:

```agda
  _++_ : List A → List A → List A
  []        ++ ys = ys
  (x ∷ xs)  ++ ys = x ∷ (xs ++ ys)
  infixr 5 _++_
```

and now show that there is indeed a monoid under `def:_++_` and `ctor:[]`:

```agda
  ++-[] : IsMonoid {Carrier = List A} _++_ []
  assoc ++-[] [] y z = refl
  assoc ++-[] (x ∷ xs) y z
    rewrite assoc ++-[] xs y z
      = refl
  identityˡ ++-[] x   = refl
  identityʳ ++-[] []  = refl
  identityʳ ++-[] (x ∷ xs)
    rewrite identityʳ ++-[] xs
      = refl
```

Again, `def:++-[]` should really be pulled apart into three additional
definitions: `def:++-assoc`, `def:++-identityˡ` and `def:++-identityʳ` for
maximum reusability of the sub-proofs. The reader is encouraged to give these
proofs on ones own, and redefine `def:++-[]` in terms of them.

Considered as a summary, `def:++-[]` allows us to inspect each individual term
of the dataset. This is the usual way in which a relational database is
queried, where we'd just like to get back each of the actual rows without any
aggregation.


## Monoidal Origami

```agda
  summarizeList : ⦃ Monoid B ⦄ → (A → B) → List A → B
  summarizeList f [] = ε  -- ! 1
  summarizeList f (x ∷ l) = f x ∙ summarizeList f l

  any? : (A → Bool) → List A → Bool
  any? = summarizeList ⦃ bundle ∨-false ⦄

  all? : (A → Bool) → List A → Bool
  all? = summarizeList ⦃ bundle ∧-true ⦄

  id : A → A
  id a = a

  sum : List ℕ → ℕ
  sum = summarizeList ⦃ bundle +-0 ⦄ id

  _ : sum (1 ∷ 10 ∷ 100 ∷ []) ≡ 111
  _ = refl


  flatten : List (List A) → List A
  flatten = summarizeList ⦃ bundle ++-[] ⦄ id



  _ : flatten  ( (1 ∷ 2 ∷ 3 ∷ [])
               ∷ (4 ∷ 5 ∷ []) ∷ []
               )
        ≡ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []
  _ = refl

  head : List A → Maybe A
  head = summarizeList ⦃ bundle <∣>-nothing ⦄ just

  foot : List A → Maybe A
  foot = summarizeList ⦃ bundle (dual <∣>-nothing) ⦄ just

  reverse : List A → List A
  reverse = summarizeList ⦃ bundle (dual ++-[]) ⦄ (_∷ [])

  const : A → B → A
  const a _ = a

  size : List A → ℕ
  size = summarizeList ⦃ bundle +-0 ⦄ (const 1)

  _ : size (true ∷ false ∷ []) ≡ 2
  _ = refl

  empty? : List A → Bool
  empty? = summarizeList ⦃ bundle ∧-true ⦄ (const false)

  record Foldable {ℓ₁ ℓ₂ : Level} (Container : Set ℓ₁ → Set ℓ₂)
      : Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
    field
      fold
        : {B : Set ℓ₂} → ⦃ monoid : Monoid B ⦄
        → (A → B)
        → Container A
        → B

  open Foldable ⦃ ... ⦄



  foldable-list : Foldable {ℓ} List
  Foldable.fold foldable-list = summarizeList

  import  Chapter6-Decidability
  open Chapter6-Decidability.BinaryTrees
    using (BinTree; leaf; branch; empty)

  foldable-bintree : Foldable {ℓ} BinTree
  Foldable.fold foldable-bintree f empty = ε
  Foldable.fold foldable-bintree f (branch l x r)
    = Foldable.fold foldable-bintree f l
        ∙ f x ∙ Foldable.fold foldable-bintree f r

  size′ : ∀ {Container} → ⦃ Foldable Container ⦄ → Container A → ℕ
  size′ = fold ⦃ monoid = bundle +-0 ⦄ (const 1)

  instance
    _ = foldable-list
    _ = foldable-bintree

  _ : size′ (1 ∷ 1 ∷ 2 ∷ 3 ∷ []) ≡ 4
  _ = refl

  _ : size′ (branch (leaf true) false (leaf true)) ≡ 3
  _ = refl

  toList : ∀ {Container} → ⦃ Foldable Container ⦄ → Container A → List A
  toList = fold ⦃ monoid = bundle ++-[] ⦄ (_∷ [])

  module _ ⦃ m₁ : Monoid A ⦄ ⦃ m₂ : Monoid B ⦄ where
    _⊗_ : Op₂ (A × B)
    (a₁ , b₁) ⊗ (a₂ , b₂) = (a₁ ∙ a₂) , (b₁ ∙ b₂)

    ×-is-monoid : IsMonoid _⊗_ (ε , ε)
    assoc ×-is-monoid (a₁ , b₁) (a₂ , b₂) (a₃ , b₃)
      rewrite assoc is-monoid  a₁ a₂ a₃
      rewrite assoc is-monoid  b₁ b₂ b₃
        = refl
    identityˡ ×-is-monoid (a , b)
      rewrite identityˡ is-monoid a
      rewrite identityˡ is-monoid b
        = refl
    identityʳ ×-is-monoid (a , b)
      rewrite identityʳ is-monoid a
      rewrite identityʳ is-monoid b
        = refl

  _∘_ : (B → C) → (A → B) → (A → C)
  (g ∘ f) x = g (f x)

  ∘-id : IsMonoid {Carrier = A → A} _∘_ id
  assoc      ∘-id x y z = refl
  identityˡ  ∘-id x = refl
  identityʳ  ∘-id x = refl

  ⊙ : ⦃ Monoid B ⦄ → Op₂ (A → B)
  ⊙ f g = λ x → f x ∙ g x

  →ε : ⦃ Monoid B ⦄ → (A → B)
  →ε = λ _ → ε

  pointwise : ⦃ Monoid B ⦄ → Monoid (A → B)
  Monoid._∙_  pointwise = ⊙
  Monoid.ε    pointwise = →ε
  assoc (Monoid.is-monoid pointwise) = {! !}
  identityˡ (Monoid.is-monoid pointwise) = {! !}
  identityʳ (Monoid.is-monoid pointwise) = {! !}

module Sandbox-IntensionalExtensional where
  open import Data.Nat
    using (ℕ; _+_;  _*_)
  open ℕ

  ex₁ : ℕ → ℕ
  ex₁ x = x + 2

  ex₂ : ℕ → ℕ
  ex₂ x = 2 * x

  ex₃ : ℕ → ℕ
  ex₃ x = suc (suc x)

  open import Relation.Binary using (Rel)

  _≗_
      : {A : Set ℓ₁} {B : A → Set ℓ₂}  -- ! 1
      → Rel ((x : A) → B x) _ -- ! 2
  _≗_ f g = ∀ x → f x ≡ g x


  ex₁≗ex₃ : ex₁ ≗ ex₃
  ex₁≗ex₃ zero = refl
  ex₁≗ex₃ (suc x) = cong suc (+-comm x 2)

  module _ {a b : Level} {A : Set a} {B : A → Set b} where

    private
      Fn : Set _
      Fn = (x : A) → B x

    ≗-refl : Reflexive {A = Fn} _≗_
    ≗-refl x = refl

    ≗-sym : Symmetric {A = Fn} _≗_
    ≗-sym f≗g a = sym (f≗g a)

    ≗-trans : Transitive {A = Fn} _≗_
    ≗-trans f≗g g≗h a = trans (f≗g a) (g≗h a)

    ≗-equiv : IsEquivalence {A = Fn} _≗_
    IsPreorder.refl (IsEquivalence.isPreorder ≗-equiv) = ≗-refl
    IsPreorder.trans (IsEquivalence.isPreorder ≗-equiv) = ≗-trans
    IsEquivalence.sym ≗-equiv = ≗-sym

    instance
      ≗-is-equiv = ≗-equiv

  postulate
    fun-ext
        : {a b : Level} {A : Set a} {B : A → Set b}
        → {f g : (x : A) → B x}
        → f ≗ g → f ≡ g

  ex₁≡ex₃ : ex₁ ≡ ex₃
  ex₁≡ex₃ = fun-ext ex₁≗ex₃

module Sandbox-Monoids where
  record Monoid₂ {a} (Carrier : Set a) (ℓ : Level)
        : Set (a ⊔ lsuc ℓ) where
    infix   4 _≈_
    infixl  7 _∙_
    field
      _∙_      : Op₂ Carrier
      ε        : Carrier
      _≈_      : Rel Carrier ℓ  -- ! 1
      isEquivalence : IsEquivalence _≈_  -- ! 2
      assoc      : (x y z : Carrier) → (x ∙ y) ∙ z ≈ x ∙ (y ∙ z)
      identityˡ  : (x : Carrier) → ε ∙ x ≈ x
      identityʳ  : (x : Carrier) → x ∙ ε ≈ x
      ∙-cong     : {x y z w : Carrier} → x ≈ y → z ≈ w → x ∙ z ≈ y ∙ w

  record Setoid (c ℓ : Level) : Set (lsuc (c ⊔ ℓ)) where
    field
      Carrier        : Set c
      _≈_            : (x y : Carrier) → Set ℓ
      isEquivalence  : IsEquivalence _≈_

  fun-ext : Set → Set → Setoid _ _
  Setoid.Carrier (fun-ext A B) = A → B
  Setoid._≈_ (fun-ext A B) f g = ∀ (x : A) → f x ≡ g x
  IsPreorder.refl (IsEquivalence.isPreorder (Setoid.isEquivalence (fun-ext A B))) {f} a = refl
  IsPreorder.trans (IsEquivalence.isPreorder (Setoid.isEquivalence (fun-ext A B))) {f} {g} {h} f=g g=h a
    rewrite f=g a rewrite g=h a = refl
  IsEquivalence.sym (Setoid.isEquivalence (fun-ext A B)) {f} {g} f=g a = {! !}

  test1 : ℕ → ℕ
  test1 x = 0

  test2 : ℕ → ℕ
  test2 _ = 1

  module _ where
    open Setoid (fun-ext ℕ ℕ)

    is-it-eq : test1 ≈ test2
    is-it-eq x = {! !}



  prop-setoid : Set ℓ → Setoid _ _
  Setoid.Carrier (prop-setoid A) = A
  Setoid._≈_ (prop-setoid A) = _≡_
  IsPreorder.refl (IsEquivalence.isPreorder (Setoid.isEquivalence (prop-setoid A))) = refl
  IsPreorder.trans (IsEquivalence.isPreorder (Setoid.isEquivalence (prop-setoid A))) = trans
  IsEquivalence.sym (Setoid.isEquivalence (prop-setoid A)) = sym

  record Monoid (c ℓ : Level) : Set (lsuc (c ⊔ ℓ)) where
    field
      setoid : Setoid c ℓ

    open Setoid setoid  -- ! 1
      renaming (_≈_ to infix 4 _≈_)   -- ! 2
      public

    infixl  7 _∙_
    field
      _∙_      : Op₂ Carrier
      ε        : Carrier
      assoc      : (x y z : Carrier) → (x ∙ y) ∙ z ≈ x ∙ (y ∙ z)
      identityˡ  : (x : Carrier) → ε ∙ x ≈ x
      identityʳ  : (x : Carrier) → x ∙ ε ≈ x
      ∙-cong     : {x y z w : Carrier} → x ≈ y → z ≈ w → x ∙ z ≈ y ∙ w

  --   module Reasoning where
  --     open import Relation.Binary.Reasoning.Setoid setoid public

  module Naive = Sandbox-Naive-Monoids
  import Relation.Binary.PropositionalEquality as PropEq

  recover : Naive.Monoid A → Monoid _ _
  recover {A = A} x = record
    { setoid     = prop-setoid A
    ; _∙_        = _∙_
    ; ε          = ε
    ; assoc      = assoc
    ; identityˡ  = identityˡ
    ; identityʳ  = identityʳ
    ; ∙-cong     = λ { ≡.refl ≡.refl → refl }
    }
    where
      open Naive.Monoid x
      open Naive.IsMonoid is-monoid


  module _ {c a ℓ : Level} (X : Set a) (setoid : Setoid c ℓ) where
    open Setoid renaming (isEquivalence to eq)
    open IsEquivalence
    open Setoid setoid
      using ()
      renaming ( Carrier to Y
               ; _≈_ to _≈ᵇ_
               )

    _≗_ : Rel (X → Y) _
    f ≗ g = (x : X) → f x ≈ᵇ g x

--     ≗-setoid : Setoid _ _
--     Carrier  ≗-setoid = A → B
--     _≈_      ≗-setoid = _≗_
--     refl   (eq ≗-setoid)          a  = refl   setoid
--     sym    (eq ≗-setoid) f≗g      a  = sym    setoid (f≗g a)
--     trans  (eq ≗-setoid) f≗g g≗h  a  = trans  setoid (f≗g a) (g≗h a)

  -- module _ (A : Set a) (mb : Monoid c ℓ) where
  --   -- open ≗-Def {A = A}
  --   open Monoid mb
  --     using ()
  --     renaming ( _∙_  to _∙ᵇ_
  --              ; ε    to εᵇ
  --              )

    -- open Monoid

    -- pointwise : Monoid _ _
    -- setoid pointwise      = ≗-setoid A (Monoid.setoid mb)
    -- _∙_    pointwise f g  = λ x → f x ∙ᵇ g x
    -- ε      pointwise      = λ _ → εᵇ
    -- assoc      pointwise f g h a    = assoc      mb _ _ _
    -- identityˡ  pointwise f a        = identityˡ  mb _
    -- identityʳ  pointwise f a        = identityʳ  mb _
    -- ∙-cong     pointwise f≗g h≗i a  = ∙-cong     mb (f≗g a) (h≗i a)
```


$$
f(\varepsilon) = \varepsilon
$$

and

$$
f(a \cdot b) = f(a) \cdot f(b)
$$

$$
f(\varepsilon_1) =_2 \varepsilon_2
$$

and

$$
f(a \cdot_1 b) =_2 f(a) \cdot_2 f(b)
$$

$$
\begin{aligned}
f(13) &= f(10) \cdot f(3) \\
f(13) &= f(13) \cdot f(0) \\
f(13) &= 1 \cdot f(13) \\
f(13) &= 30
\end{aligned}
$$

```agda
module Sandbox-MonoidHomomorphisms where
  -- open Sandbox-Monoids

  -- private variable
  --   c c₁ c₂ ℓ ℓ₁ ℓ₂ : Level

  -- module _ (m₁ : Monoid c₁ ℓ₁) (m₂ : Monoid c₂ ℓ₂) where
  --   open import Relation.Binary using (_Preserves_⟶_)
  --   open Monoid m₁ using () renaming (Carrier to A)
  --   open Monoid m₂ using () renaming (Carrier to B)
  --   open Monoid ⦃ ... ⦄

  --   instance
  --     _ = m₁
  --     _ = m₂

  --   record MonHom (f : A → B)
  --        : Set (c₁ ⊔ c₂ ⊔ ℓ₁ ⊔ ℓ₂) where
  --     field
  --       preserves-ε  : f ε ≈ ε
  --       preserves-∙  : (x y : A) → f (x ∙ y) ≈ f x ∙ f y
  --       f-cong       : f Preserves _≈_ ⟶ _≈_

  -- ∧-true   = recover Naive.∧-true
  -- ∨-false  = recover Naive.∨-false
  -- +-0      = recover Naive.+-0
  -- *-1      = recover Naive.*-1

  -- private variable
  --   a : Level
  --   A : Set a

  -- ++-[] first last : (A : Set a) → Monoid _ _
  -- ++-[]  A = recover (Naive.++-[] {A = A})
  -- first  A = recover (Naive.first A)
  -- last   A = recover (Naive.last A)


  -- open import Data.Bool
  --   using (true; false; not)

  -- open MonHom
  -- module _ where
  --   open import Relation.Binary.PropositionalEquality

  --   not-hom₁ : MonHom ∧-true ∨-false not
  --   preserves-ε  not-hom₁           = refl
  --   preserves-∙  not-hom₁ false  y  = refl
  --   preserves-∙  not-hom₁ true   y  = refl
  --   f-cong       not-hom₁ refl      = refl

    -- open import Function using (const)

    -- false-hom : MonHom ∧-true ∨-false (const false)
    -- preserves-ε  false-hom       = refl
    -- preserves-∙  false-hom x y   = refl
    -- f-cong       false-hom refl  = refl
```

$$
\neg (a \wedge b) = \neg a \vee \neg b
$$

$$
\neg (a \vee b) = \neg a \wedge \neg b
$$

```agda
    -- not-hom₂ : MonHom ∨-false ∧-true not
    -- preserves-ε  not-hom₂           = refl
    -- preserves-∙  not-hom₂ false  y  = refl
    -- preserves-∙  not-hom₂ true   y  = refl
    -- f-cong       not-hom₂ refl      = refl

    -- open import Relation.Nullary

    -- not-false-hom₂ : ¬ MonHom ∨-false ∧-true (const false)
    -- not-false-hom₂ x with preserves-ε x
    -- ... | ()

  -- open import Data.Nat using (ℕ)
  -- open import Data.List
  --   using (List; []; _∷_)

  -- open import Relation.Binary.PropositionalEquality
  --   using ()
  --   renaming (setoid to prop-setoid)

  -- module _ where
  --   open import Relation.Binary.PropositionalEquality

  --   length : List A → ℕ
  --   length = Naive.size

  --   length-hom : (A : Set a) → MonHom (++-[] A) +-0 length
  --   preserves-ε (length-hom A) = refl
  --   preserves-∙ (length-hom A) [] y = refl
  --   preserves-∙ (length-hom A) (x ∷ xs) y
  --     rewrite preserves-∙ (length-hom A) xs y
  --       = refl
  --   f-cong (length-hom A) refl = refl

    -- open import Function using (_∘_; id)

    -- ∘-id : Set a → Monoid _ _
    -- Monoid.setoid  (∘-id A)      = ≗-setoid A (prop-setoid A)
    -- Monoid._∙_     (∘-id A) g f  = g ∘ f
    -- Monoid.ε       (∘-id A)      = id
    -- Monoid.assoc      (∘-id A) x y z a  = refl
    -- Monoid.identityˡ  (∘-id A) x a      = refl
    -- Monoid.identityʳ  (∘-id A) x a      = refl
    -- Monoid.∙-cong     (∘-id A) x≗y u≗v a
    --   rewrite u≗v a = x≗y _

    -- module DList where
    --   open Data.List using (_++_)
    --   open import Data.List.Properties
    --     using (++-identityʳ; ++-assoc)

    --   dlist-mon : Set a → Monoid _ _
    --   dlist-mon A = ∘-id (List A)

    --   DList : Set a → Set a
    --   DList A = Monoid.Carrier (dlist-mon A)

      -- toDList : List A → DList A
      -- toDList = _++_

      -- fromDList : DList A → List A
      -- fromDList dl = dl []

      -- dlist-hom : MonHom (++-[] A) (dlist-mon A) toDList
      -- preserves-ε  dlist-hom a = refl
      -- preserves-∙  dlist-hom = ++-assoc
      -- f-cong       dlist-hom refl a = refl

      -- ex-dlist
      --   = fromDList
      --     ( toDList (1 ∷ 2 ∷ [])
      --     ∙ toDList (3 ∷ 4 ∷ [])
      --     ∙ toDList (5 ∷ [])
      --     )
      --   where
      --     open Monoid (dlist-mon ℕ)

      -- _ : ex-dlist  ≡ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []
      -- _ = refl

  -- module KeyValStore (Key : Set c₁) (val-monoid : Monoid c₂ ℓ₂) where
  --   open Monoid val-monoid using () renaming (Carrier to Val)

  --   KVStore : Set (c₁ ⊔ c₂)
  --   KVStore = Key → Val

  --   _[_] : KVStore → Key → Val
  --   kv [ ix ] = kv ix


  -- open import Function using (const; id)

  -- trivial : (m : Monoid c₂ ℓ₂) → MonHom m m id
  -- trivial m = record
  --   { preserves-ε  = refl
  --   ; preserves-∙  = λ  x y → refl
  --   ; f-cong       = λ  x → x
  --   }
  --   where open Monoid m

  -- degenerate
  --     : {m₁ : Monoid c₁ ℓ₁}
  --     → (m : Monoid c₂ ℓ₂)
  --     → MonHom m₁ m (const (Monoid.ε m))
  -- degenerate m = record
  --   { preserves-ε  = refl
  --   ; preserves-∙  = λ  x y → sym (identityʳ _)
  --   ; f-cong       = λ  x → refl
  --   }
  --   where open Monoid m

  -- -- -- TODO(sandy): fixme; haven't discussed isos
  -- -- open import propisos

  -- -- module _ (m₁ : Monoid c₁ ℓ₁) (m₂ : Monoid c₂ ℓ₂) where
  -- --   open import Relation.Binary using (_Preserves_⟶_)
  -- --   open Monoid m₁ using () renaming (Carrier to X; ε to ε₁; _∙_ to _∙₁_)
  -- --   open Monoid m₂ using () renaming (Carrier to Y; ε to ε₂; _∙_ to _∙₂_)
  -- --   open Monoid

  -- --   invertible
  -- --       : (iso : Monoid.setoid m₁ ↔ Monoid.setoid m₂)
  -- --       → MonHom m₁ m₂ (_↔_.to iso)
  -- --       → MonHom m₂ m₁ (_↔_.from iso)
  -- --   preserves-ε (invertible iso hom) =
  -- --     begin
  -- --       from ε₂
  -- --     ≈⟨ from-cong (sym m₂ (preserves-ε hom)) ⟩
  -- --       from (to ε₁)
  -- --     ≈⟨ left-inv-of ε₁ ⟩
  -- --       ε₁
  -- --     ∎
  -- --     where
  -- --       open _↔_ iso
  -- --       open Reasoning m₁
  -- --   preserves-∙ (invertible iso hom) a b =
  -- --     begin
  -- --       from (a ∙₂ b)
  -- --     ≈⟨ sym m₁ (from-cong (∙-cong m₂ (right-inv-of _) (right-inv-of _))) ⟩
  -- --       from (to (from a) ∙₂ to (from b))
  -- --     ≈⟨ from-cong (sym m₂ (preserves-∙ hom _ _)) ⟩
  -- --       from (to (from a ∙₁ from b))
  -- --     ≈⟨ left-inv-of (from a ∙₁ from b) ⟩
  -- --       from a ∙₁ from b
  -- --     ∎
  -- --     where
  -- --       open _↔_ iso
  -- --       open Reasoning m₁
  -- --   f-cong (invertible iso hom) {x} {y} x≈₂y = _↔_.from-cong iso x≈₂y

  -- -- -- identities are unique
```

```agda
open import Algebra
  using (Op₂) public
```

