# Monoids and Setoids {#sec:chapter7}

Hidden

:   ```agda
{-# OPTIONS --allow-unsolved-metas #-}
    ```

```agda
module Chapter7-Structures where
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


Prerequisites

:   ```agda
open import Chapter1-Agda
    ```

:   ```agda
open import Chapter2-Numbers
    ```

:   ```agda
open import Chapter3-Proofs
  renaming (module PropEq to ≡)
    ```

:   ```agda
open import Chapter4-Relations
    ```

:   ```agda
open import Chapter5-Modular-Arithmetic
  using (equiv-to-preorder; ≡-is-equivalence; refl; sym; trans)
    ```

:   ```agda
open import Chapter6-Decidability
  using (¬_; ⊥)
open Chapter6-Decidability.BinaryTrees
  using (BinTree; leaf; branch; empty)
    ```


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


## Monoids {#sec:monoids}

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
\varepsilon \cdot x = x
$$

$$
x \cdot \varepsilon = x
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
  assoc      xor-false false y z        = refl
  assoc      xor-false true false z     = refl
  assoc      xor-false true true false  = refl
  assoc      xor-false true true true   = refl
  identityˡ  xor-false x      = refl
  identityʳ  xor-false false  = refl
  identityʳ  xor-false true   = refl
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

Finally, we will open `type:Monoid` as typeclass:

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
```


Hidden

:     ```agda
  -- FIX
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
```


Hidden

:     ```agda
  -- FIX
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
```


Hidden

:     ```agda
  -- FIX
      ```


There you have it---three different monoids give us three different answers when
summarizing each of `def:ex₁`, `def:ex₂`, and `def:ex₃`. When we conceptualize
`def:ex₁` and friends as datasets, our different monoids correspond to different
questions we can ask about that data.

Of course, the booleans are such a small type that the sort of questions we can
ask are extremely limited. Let's therefore take some time to find more examples
of monoids, keeping our catchphrase that "monoids generate summaries" in mind as
we do so.


## More Monoids {#sec:more-mons}

In @sec:maybe we looked at the `type:Maybe` type, which is parameterized by
another type, extending it with the possibility that there might not be any data
inside. Recall that we use the `ctor:nothing` constructor to give this lack of
data, and the `ctor:just` constructor to inject a value of type `A` into
`type:Maybe` `A`.

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
  assoc      <∣>-nothing (just x)  y z = refl
  assoc      <∣>-nothing nothing   y z = refl
  identityˡ  <∣>-nothing x = refl
  identityʳ  <∣>-nothing (just x)  = refl
  identityʳ  <∣>-nothing nothing   = refl
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

We can now get the last-`ctor:just`-wins monoid for free, since it's just
`expr:dual <∣>-nothing`.

As another example of monoids, we note that lists form one under concatenation
and the empty list. Rather incredibly, we've made it all the way to chapter 7
in a book on function programming without mentioning lists, so let's quickly
give a definition:

```agda
  module Definition-List where
    data List (A : Set ℓ) : Set ℓ where
      []   : List A
      _∷_  : A → List A → List A
    infixr 5 _∷_
```

You can type `∷` by way of [`::`](AgdaMode).

Lists of `A` are either empty (given by `ctor:[]`), or they are given by an `A`
stuck in front of another list (via `ctor:_∷_`.) With this definition, we can
quickly define list concatenation:

```agda
    _++_ : List A → List A → List A
    []        ++ ys = ys
    (x ∷ xs)  ++ ys = x ∷ (xs ++ ys)
    infixr 5 _++_
```


and now show that there is indeed a monoid under `def:_++_` and `ctor:[]`---but
not before getting their definitions from the standard library for maximum
reusability:

```agda
  open import Data.List using (List; []; _∷_; _++_)

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

One interesting monoid is the monoid of *endomorphisms*, which is just a
fancy word for saying "functions of type `A → A`." First we can define function
composition:

```agda
  _∘_ : (B → C) → (A → B) → (A → C)
  (g ∘ f) x = g (f x)
```

Furthermore, we have the *identity* function which simply does nothing, merely
immediately gives back its argument:

```agda
  id : A → A
  id a = a
```

By now fixing `A = B = C`, we can show that `def:_∘_` forms a monoid with `def:id` as
the unit:

```agda
  ∘-id : IsMonoid {Carrier = A → A} _∘_ id
  assoc      ∘-id x y z = refl
  identityˡ  ∘-id x = refl
  identityʳ  ∘-id x = refl
```

I personally really like the `def:∘-id` monoid, which is extremely useful in
pure functional programming settings. Many languages, including Agda, don't have
any notion of mutable variables, and so we must get creative in order to achieve
the same effect. Instead of having a mutable variable of type `A`, we can
instead represent *mutations*  as functions `A → A`. The `def:∘-id` monoid
therefore corresponds to performing one mutation after another.


## Monoidal Origami

When we previously looked at examples of "datasets" that we wanted to summarize,
we built them out of explicit invocations of `field:_∙_` and `field:ε`. A more
modular way of doing this is to instead put all of the data we're interested in
into a list, and then *folding* that list into the summary we care about. The
high-level idea is to take a `type:List` `A`, transform each element into a `B`
for which we have a `type:Monoid`, and then combine all of the `B`s together via
`field:_∙_`. This is all put together in `def:foldList`:

```agda
  module ListSummaries where
    foldList : ⦃ Monoid B ⦄ → (A → B) → List A → B
    foldList f []       = ε                   -- ! 1
    foldList f (x ∷ l)  = f x ∙ foldList f l  -- ! 2
```

Note that at [1](Ann) we are forced to return `field:ε`, because we don't have
any other means of getting a `B`. The recursive call to `def:foldList` at
[2](Ann) must therefore eventually multiply in this unit, but don't worry! Such
a thing can never change the result of our summary, because we know that
`field:ε` is a unit for `field:_∙_` and thus that we can multiply it in as often
as we'd like without changing anything. It is exactly for this reason that we
desire the existence of `field:ε`, as it gives us a meaningful (if boring)
answer for how to summarize an absence of data.

By instantiating `def:foldList` with different monoids, we change how it
*combines* the summaries of each element in the list. But we also have this `A →
B` parameter to play with, and it corresponds to the way we'd like to summarize
each element in the first place.

For example, by requiring a function that turns an `A` into a `def:Bool`, we can
use `def:∨-false` to determine whether any element in the list makes the
function true:

```agda
    any? : (A → Bool) → List A → Bool
    any? = foldList ⦃ bundle ∨-false ⦄
```

Similarly, `def:∧-true` lets us determine if the function is true of *every*
element in the list .

```agda
    all? : (A → Bool) → List A → Bool
    all? = foldList ⦃ bundle ∧-true ⦄
```

In some cases, we might not need to perform this initial summarization of the
data, like in the case of `def:sum` which adds up all of the numbers in a list.
Here, the list already contains the data we want to combine, so no mapping is
necessary. In cases like these, it can be helpful to use the *identity function*
which simply gives back its argument:

```agda

    sum : List ℕ → ℕ
    sum = foldList ⦃ bundle +-0 ⦄ id
```

Our new `def:sum` function works exactly as you'd expect:

```agda
    _ : sum (1 ∷ 20 ∷ 300 ∷ []) ≡ 321
    _ = refl
```

We can do the same trick with `def:*-1`:

```agda
    product : List ℕ → ℕ
    product = foldList ⦃ bundle *-1 ⦄ id
```

which instead multiples all of the values in the list.

Many functions we don't traditionally consider "summaries" can also be written
by way of `def:foldList` with a well-chosen monoid. We can, for example,
flatten nested lists:

```agda
    flatten : List (List A) → List A
    flatten = foldList ⦃ bundle ++-[] ⦄ id
```

or find their first and last elements:

```agda
    head : List A → Maybe A
    head = foldList ⦃ bundle <∣>-nothing ⦄ just

    foot : List A → Maybe A
    foot = foldList ⦃ bundle (dual <∣>-nothing) ⦄ just
```

We can even reverse lists by using the `def:dual` monoid to `def:++-[]`.

```agda
    reverse : List A → List A
    reverse = foldList ⦃ bundle (dual ++-[]) ⦄ (_∷ [])
```

Sometimes we'd like to summarize the *structure* of the list, rather than
inspect any of its elements. For this we can introduce the `def:const`
function, which always ignores its second argument:

```agda
    const : A → B → A
    const a _ = a
```

We can then compute the `def:size` of a list by replacing each of its elements
with the number 1 and then using `def:+-0`:

```agda
    size : List A → ℕ
    size = foldList ⦃ bundle +-0 ⦄ (const 1)
```

or we can determine whether a list is empty by mapping each element to
`ctor:false`:

```agda
    empty? : List A → Bool
    empty? = foldList ⦃ bundle ∧-true ⦄ (const false)
```

If you look closely, you'll notice that there is nothing intrinsically special
about lists---they merely happen to be a convenient data structure. If we
move away from lists, we'll see that there are *lots* of data structures
that we can fold over. We can reify this idea via `type:Foldable`, which
gives us a means of folding over some `Container`:

```agda
  open import Function using (id; const)

  record Foldable {ℓ₁ ℓ₂ : Level} (Container : Set ℓ₁ → Set ℓ₂)
      : Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
    field
      fold
        : {B : Set ℓ₂} → ⦃ monoid : Monoid B ⦄
        → (A → B)
        → Container A
        → B
```

We will use `type:Foldable` as a typeclass, and note that as already shown,
`type:List` is `def:Foldable`:

```agda
  open Foldable ⦃ ... ⦄

  instance
    fold-list : Foldable {ℓ} List
    Foldable.fold fold-list = ListSummaries.foldList
```

However, most other containers are `def:Foldable` too. In @sec:bintrees we
defined `type:BinTree`, which also admits folding:

```agda
    fold-bintree : Foldable {ℓ} BinTree
    Foldable.fold fold-bintree f empty = ε
    Foldable.fold fold-bintree f (branch l x r)
      = Foldable.fold fold-bintree f l
          ∙ f x ∙ Foldable.fold fold-bintree f r
```

as does `type:Maybe`:

```agda
    fold-maybe : Foldable {ℓ} Maybe
    Foldable.fold fold-maybe f (just x)  = f x
    Foldable.fold fold-maybe f nothing   = ε
```

Almost every data structure you've ever encountered also admits an instance of
`def:Foldable`, and it's left as an exercise to the reader to work out the
details for any particular examples that might come to mind.

Armed with a definition of `def:Foldable`, we can now write container-agnostic
folds, which summarize their data in any of the ways we saw above for lists. As
one example, we can reimplement `def:size` to now count the number of elements
in any container:

```agda
  size  : {A : Set ℓ} {Container : Set ℓ → Set}
        → ⦃ Foldable Container ⦄
        → Container A → ℕ
  size  = fold ⦃ monoid = bundle +-0 ⦄ (const 1)

  _ : size (1 ∷ 1 ∷ 2 ∷ 3 ∷ []) ≡ 4
  _ = refl

  _ : size (branch (leaf true) false (leaf true)) ≡ 3
  _ = refl
```

Or we can extract every element from a container into a `def:List`:

```agda
  build : ∀ {Container} → ⦃ Foldable Container ⦄ → Container A → List A
  build = fold ⦃ monoid = bundle ++-[] ⦄ (_∷ [])
```

You are encouraged to work through the other examples in `module:ListSummaries`
and see how they generalize to arbitrary `def:Foldable` containers. How do the
types need to change, and what can you say about the resulting functions?


## Composition of Monoids

A common theme in mathematics and functional programming is composition---the
building of larger objects out of smaller ones. Here, we'd like to explore how
we can combine simple monoids to make more complicated ones. For the time being,
we will content ourselves with two examples: building a monoid over *products,*
and building one over *functions*.

Let's consider the case of a product type `A` `type:×` `B`. Is there a general
means of constructing a monoid over this carrier set? As it happens, such a
thing is possible whenever we have a monoid on both of `A` and `B`. The
construction isn't particularly insightful---we just work on both monoids at
once. That is, we give the operation as:

$$
(a_1, b_1) \cdot (a_2, b_2) = (a_1 \cdot a_2, b_1 \cdot b_2)
$$

and the identity as:

$$
\varepsilon = (\varepsilon, \varepsilon)
$$

The laws fall out for free, since we're just combining two monoids "in
parallel." We can construct the whole thing in Agda by way of a module that
binds the monoids:

```agda
  module _ ⦃ m₁ : Monoid A ⦄ ⦃ m₂ : Monoid B ⦄ where
```

We can now define the multiplication:

```agda
    _⊗_ : Op₂ (A × B)
    (a₁ , b₁) ⊗ (a₂ , b₂) = (a₁ ∙ a₂) , (b₁ ∙ b₂)
```

and build the monoid over the product as follows:

```agda
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
```

All of the rewriting here is a little annoying, but is much terser than doing
the equational reasoning ourselves and showing that both sides respect their
respective identity laws.

Because functions `A → B` can be thought of as really big pairs of `B` (in
particular, one for every possible value of `A`)---a fact that we will prove in
@sec:exponents---we should be able to build a similar monoid over functions.
That is, whenever `B` is a monoid, we should be able to build a monoid over `A →
B` given by the *pointwise* action on the functions. That is, the unit in `A →
B` is a constant function that produces the unit in `B`:

$$
\varepsilon = x \mapsto \varepsilon
$$

and the operation on `A → B` invokes the operation on `B` after calling both
functions, that is:

$$
f \cdot g = x \mapsto f(x) \cdot g(x)
$$

We can try to build this monoid in Agda, first by defining the operation:

```agda
  ⊙ : ⦃ Monoid B ⦄ → Op₂ (A → B)
  ⊙ f g = λ x → f x ∙ g x
```

and then filling out `def:pointwise` results in:

```agda
  pointwise : ⦃ _ : Monoid B ⦄ → IsMonoid (⊙ {A = A}) (const ε)
  assoc      pointwise f g h = {! !}
  identityˡ  pointwise = {! !}
  identityʳ  pointwise = {! !}
```

Unfortunately, here is where we get stuck. The first hole here has type

```info
⊙ (⊙ f g) h ≡ ⊙ f (⊙ g h)
```

which doesn't seem too bad until you expand the definition of `def:⊙`, which
results in:

```info
(λ x → (f x ∙ g x) ∙ h x)
  ≡ (λ x → f x ∙ (g x ∙ h x))
```

Something we've been carefully avoiding throughout this entire text is the
equality of functions. If you look back closely, you'll notice that we have
always had functions which return equality of terms; we have never once needed
to show the equality of *two functions!* We've avoided doing so because this is
where things get surprisingly hairy, but we can't kick the can any further. Our
monoid `def:pointwise` really and truly is perfectly acceptable mathematically,
but try as we might, we are unable to fill the above holes.


## Function Extensionality

All of this bring up an interesting question at the foundation of
mathematics---when exactly are two functions equal? The answer is not very cut
and dry, and it's quite a hard a hard problem. Consider functions `def:f₁`,
and `def:f₂`:


```agda
module Sandbox-Extensionality where
  f₁ : ℕ → ℕ
  f₁ x = x + 2

  f₂ : ℕ → ℕ
  f₂ x = 2 + x
```

Are these two functions equal? It's unclear exactly what the question means. Are
they syntactically the same function? No, not at all! But do they compute the
same output for every input? Absolutely! Do they follow the same computation to
get that answer? No again. And so the problem really cashes out as "what do we
mean when we ask if two functions are equal?"

Many programming languages sidestep the issue by saying two functions are equal
if their underlying pointer is equal. Thus two functions are the same if they
exist at the same place in memory, but this is mathematically abhorrent for many
reasons---the worst of which is that the runtime gets to decide whether two
functions are equal, and it might make a different choice if you run the
program a second time. There are many ways to describe this behavior, but
none of "sane", "mathematical", or even "good programming practice" are one.

The answer in most of mathematics is that two functions are equal if and only if
they produce the same output for every input. This is known both as *extensional
equality* of functions, and as *Leibniz equality.* The question was less salient
when it was originally posed, as computation hadn't yet been invented. Under
extensional equality, bubblesort and quicksort are equal functions, even though
their computational properties are wildly divergent.

We can define extensional equality between dependent functions `f` and `g` in
Agda as:

```agda
  _≗_
      : {A : Set ℓ₁} {B : A → Set ℓ₂}
      → Rel ((x : A) → B x) _
  _≗_ {A = A} f g = (x : A) → f x ≡ g x
```

where the `≗` symbol is input as (AgdaMode). The type here is a little
hairy, but it shouldn't give you too much challenge by this point. The idea is
that `def:_≗_` forms a relation over functions that ensures their images are
propositionally equal at all points. Under this relation, we can now show that
`def:f₁` and `def:f₂` from above are extensionally equal:

```agda
  f₁≗f₂ : f₁ ≗ f₂
  f₁≗f₂ zero = refl
  f₁≗f₂ (suc x) = ≡.cong suc (+-comm x 2)
```

As you'd expect, in order for `def:_≗_` to be a model of equality, it certainly
ought to form an equivalence relation. And in fact it does. The construction is
a little annoying to type due to the high parametricity, but we can build it
together. For some types `A and `B`:

```agda
  module _ {A : Set ℓ₁} {B : A → Set ℓ₂} where
```

we can build the type of dependent functions between them:

```agda
    private
      Fn : Set _
      Fn = (x : A) → B x
```

and now show that `def:_≗_` is a `type:Fn`-typed equivalence relation:

```agda
    ≗-refl : Reflexive {A = Fn} _≗_
    ≗-refl x = refl

    ≗-sym : Symmetric {A = Fn} _≗_
    ≗-sym f≗g a = sym (f≗g a)

    ≗-trans : Transitive {A = Fn} _≗_
    ≗-trans f≗g g≗h a = trans (f≗g a) (g≗h a)

    ≗-equiv : IsEquivalence {A = Fn} _≗_
    IsPreorder.refl   (IsEquivalence.isPreorder ≗-equiv) = ≗-refl
    IsPreorder.trans  (IsEquivalence.isPreorder ≗-equiv) = ≗-trans
    IsEquivalence.sym ≗-equiv = ≗-sym
```

For good measure, we can also add `def:≗-equiv` to the `keyword:instance`
environment, allowing us to use `field:refl`, `field:sym`, and `field:trans`
polymorphically to work with it:

```agda
    instance
      ≗-is-equiv = ≗-equiv
```

We have thus shown that extensional equality is a meaningful notion of equality.

If you are working in more of a mathematical domain (as opposed to a
computational one), you might now want to postulate *function extensionality*:
the notion that extensionally equal functions are in fact *propositionally
equal.* As we have seen, this doesn't make sense when computation is your main
goal, but if you are simply modeling the world, it's an extremely convenient
thing to have around. Agda has no opinion as to whether function extensionality
holds or not, and its underlying theory is compatible with or without it.
Therefore, the decision is up to us. If we'd like it, we must postulate
`postulate:fun-ext`, which upgrades `def:_≗_` into `def:_≡_`:

```agda
  postulate
    fun-ext
        : {A : Set ℓ₁} {B : A → Set ℓ₂}
        → {f g : (x : A) → B x}
        → f ≗ g → f ≡ g
```

Given `postulate:fun-ext`, we can show that `def:f₁` and `def:f₂` are
*propositionally equal:*

```agda
  f₁≡f₃ : f₁ ≡ f₂
  f₁≡f₃ = fun-ext f₁≗f₂
```

Similarly, if we were to return to our `def:pointwise` example showing we can
lift a monoid over arbitrary functions, we could now invoke `postulate:fun-ext`
in order to help fill our holes. While that's a perfectly good solution, in the
next section we will instead explore a different---and much, much
worse---solution to the problem.


## Setoid Hell {#sec:setoids}

An alternative to postulating function extensionality is to parameterize
*everything* by "what exactly do we mean by equality?" This approach is
significantly messier and much more annoying to work with than simply positing
`postulate:fun-ext`, but applies in many more situations. For example, we might
want a more relaxed notion of equality when comparing two lists, requiring not
that they be on-the-nose equal, but merely that corresponding elements be
*equivalent* in some way.

The actual construction here is the `def:Setoid`, which is a bundled version of
an equivalence relation and its carrier set:

```agda
record Setoid (c ℓ : Level) : Set (lsuc (c ⊔ ℓ)) where
  infix 4 _≈_
  field
    Carrier        : Set c
    _≈_            : (x y : Carrier) → Set ℓ
    isEquivalence  : IsEquivalence _≈_

  open IsEquivalence isEquivalence public
```

Notice the three fields here, corresponding to the carrier set, a relation over
that set, and a proof that the relation is an equivalence. The idea now is
whenever we'd like to discuss equality, we instead discuss equality *modulo some
setoid.* In practice, that means parameterizing things by a setoid and replacing
every use of `type:_≡_` with the `field:_≈_` field above. Since they're both
equivalence relations, everything works out, but as we will see, it comes with a
significant proof burden.

But I'm getting ahead of myself. Before we finish the definition of
`type:Setoid`, we will add a `module:Reasoning` sub-module which simply
repackages the `module:Preorder-Reasoning` reasoning syntax applied to our
particular equivalence relation:

```agda
  module Reasoning where
    open Preorder-Reasoning
      (IsEquivalence.isPreorder isEquivalence)
      public
```

Given all of this work, we can now define a few setoids to get a flavor for
them. However, by this point, building objects out of copatterns on copatterns
results in extremely long names, so we'll take great care to rename everything.
We'll need all of this renaming several times, as we define a couple of setoids,
and then give some examples, and then define a few more, so we can do the
necessary work in a new module:

```agda
module Setoid-Renaming where
  open Setoid
    hiding (refl; trans; sym)
    renaming (isEquivalence to equiv)
    public
  open IsPreorder
    using ()
    renaming (refl to refl′; trans to trans′)
    public
  open IsEquivalence
    using ()
    renaming (isPreorder to pre; sym to sym′)
    public
```

In particular, we must rename `field:refl` to `field:refl′`, since when we
opened `type:IsPreorder` as a typeclass earlier, we brought `field:refl` into
scope with the wrong type to work here. It's reasons like this that I often feel
the hardest part of working in Agda is avoiding identifier clashes.

Having done the hard work, we can lift propositional equality on any type into a
setoid, as in `def:prop-setoid`:

```agda
module _ where
  open Setoid-Renaming

  prop-setoid : Set ℓ → Setoid ℓ ℓ
  Carrier (prop-setoid A)  = A
  _≈_     (prop-setoid A)  = _≡_
  refl′   (pre (equiv (prop-setoid A))) = refl
  trans′  (pre (equiv (prop-setoid A))) = trans
  sym′    (equiv (prop-setoid A)) = sym
```

which we will then give as an keyword for future shenanigans.

```agda
  instance
    prop-setoid-inst : {c : Level} {A : Set c} → Setoid c c
    prop-setoid-inst {A = A} = prop-setoid A
```

Now that we our first setoid under our belt, let's try cutting our teeth on some
harder ones. For example, we can make a setoid for the `type:_×_` type, which
lifts a setoid over each projection. That is, two pairs `a₁` `ctor:,` `b₁` and
`a₂` `ctor:,` `b₂` are equal only when `a₁` is equivalent to `a₂` under the
first setoid, and when `b₁` and `b₂` do under the second. In other words, a
setoid for pairs is a pair of setoids.

We'll begin with some setup, just to get everything into scope with reasonable
names:

```agda
  private variable
    c c₁ c₂ : Level

  module _ (s₁ : Setoid c₁ ℓ₁) (s₂ : Setoid c₂ ℓ₂) where
    private instance
      s₁-equiv  = equiv s₁
      s₂-equiv  = equiv s₂

    private
      Carrier₁  = s₁ .Carrier
      Carrier₂  = s₂ .Carrier
      _≈₁_  = s₁  ._≈_
      _≈₂_  = s₂  ._≈_
```

and then we can construct our setoid for `type:_×_`:

```agda
    ×-setoid : Setoid _ _
    Carrier ×-setoid = s₁ .Carrier × s₂ .Carrier
    _≈_ ×-setoid (a₁ , b₁) (a₂ , b₂) = (a₁ ≈₁ a₂) × (b₁ ≈₂ b₂)
    refl′   (pre (equiv ×-setoid)) = refl , refl
    trans′  (pre (equiv ×-setoid)) (a₁₂ , b₁₂) (a₂₃ , b₂₃)
      = trans a₁₂ a₂₃ , trans b₁₂ b₂₃
    sym′ (equiv ×-setoid) (a , b) = sym a , sym b
```

That wasn't too bad, was it? Now let's do one for coproducts. Here we're not so
lucky as to just lift `type:_⊎_` for our equivalence relation, since the indices
don't work out. Instead, we can define `type:⊎-Pointwise`, whose sole purpose of
existence is to act as an equivalence relation for `def:⊎-setoid`:

```agda
    data ⊎-Pointwise : Rel (Carrier₁ ⊎ Carrier₂) (ℓ₁ ⊔ ℓ₂) where
      inj₁  : {x y : Carrier₁} → x ≈₁  y → ⊎-Pointwise (inj₁ x) (inj₁ y)
      inj₂  : {x y : Carrier₂} → x ≈₂  y → ⊎-Pointwise (inj₂ x) (inj₂ y)
```

We then resign ourselves to showing `type:⊎-Pointwise` is indeed an equivalence
relation:

```agda
    ⊎-equiv : IsEquivalence ⊎-Pointwise
    refl′   (pre ⊎-equiv) {inj₁  x} = inj₁ refl
    refl′   (pre ⊎-equiv) {inj₂  y} = inj₂ refl
    trans′  (pre ⊎-equiv) (inj₁  x=y) (inj₁  y=z) = inj₁  (trans x=y y=z)
    trans′  (pre ⊎-equiv) (inj₂  x=y) (inj₂  y=z) = inj₂  (trans x=y y=z)
    sym′    ⊎-equiv (inj₁  x) = inj₁  (sym x)
    sym′    ⊎-equiv (inj₂  x) = inj₂  (sym x)
```

and then thankfully, giving `def:⊎-setoid` is no additional work:

```agda
    ⊎-setoid : Setoid (c₁ ⊔ c₂) (ℓ₁ ⊔ ℓ₂)
    Carrier  ⊎-setoid = s₁ .Carrier ⊎ s₂ .Carrier
    _≈_      ⊎-setoid = ⊎-Pointwise
    equiv    ⊎-setoid = ⊎-equiv
```

Welcome to the godawful world of *setoid hell,* where the burden of the
should-be-mechanical congruence proofs are handed over to you, poor, sweet
reader. As a general rule, you are going to need to make a helper data type that
looks a lot like the thing you're trying to show a setoid over, use that thing
as your setoid carrier, and then give a relation that preserves all the relevant
equivalences. It's a nightmare. And don't worry; we'll see a great deal more of
them in our future.


## Function Extensionality

Now that we're familiar (if not *comfortable*) with how to set up setoids, we
can try our hand at building one for function extensionality:

```agda
  fun-ext⅋ : Set ℓ₁ → Set ℓ₂ → Setoid _ _
  Carrier  (fun-ext⅋ A B)      = A → B
  _≈_      (fun-ext⅋ A B) f g  = (x : A) → f x ≡ g x
  refl′    (pre (equiv (fun-ext⅋ A B))) _ = refl
  trans′   (pre (equiv (fun-ext⅋ A B))) f=g g=h a
    rewrite f=g a
    rewrite g=h a
      = refl
  sym′     (equiv (fun-ext⅋ A B)) f=g a = sym (f=g a)
```

Oh sorry, I did that wrong. Recall that the trick to setoids is to parameterize
*everything* by a new notion of equality. We can't just hard-code `type:_≡_`
here in the definition of `field:_≈_`. No, instead we'd like to parameterize the
whole thing by a setoid on `B`:

```agda
  fun-ext⅋₁ : Set ℓ₁ → Setoid ℓ₂ ℓ → Setoid _ _
  Carrier  (fun-ext⅋₁ A B)      = A → B .Carrier
  _≈_      (fun-ext⅋₁ A B) f g  = (x : A) → (B ._≈_) (f x) (g x)
  refl′    (pre (equiv (fun-ext⅋₁ A B))) _ = refl′ (pre (equiv B))
  trans′   (pre (equiv (fun-ext⅋₁ A B))) f=g g=h a
    = trans′ (pre (equiv B)) (f=g a) (g=h a)
  sym′     (equiv (fun-ext⅋₁ A B)) f=g a = B .equiv .sym′ (f=g a)
```

Wait, is *this* one right? Still no! Because we have an *implicit* use of
propositional equality here. Where? In the `A` we're passing around in the
relation. Instead, a real notion of function extensionality over setoids should
map equal elements in one setoid to equal elements in the other. Of course, this
is not true of all functions between the carriers of `A` and `B`---it is exactly
those which are congruent. So we can't yet define this setoid, we must first
define a type corresponding to congruent functions between our two carrier sets:


```agda
  module _ {a b : Level} (s₁ : Setoid a ℓ₁) (s₂ : Setoid b ℓ₂) where
    open Setoid s₁  renaming (Carrier to From;  _≈_ to _≈₁_)
    open Setoid s₂  renaming (Carrier to To;    _≈_ to _≈₂_)

    record Fn : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
      constructor fn
      field
        func  : From → To
        cong  : {x y : From}
              → x ≈₁ y
              → func x ≈₂ func y

    open Fn
```

The type `type:Fn` now encodes functions between the carriers of `A` and `B`,
along with a proof that those functions are congruent with respect to the setoid
equality on either end. You might be wondering where exactly this type came
from---the answer is that I tried to give a setoid over functions whose carrier
was just a function over carriers, but got stuck needing to show congruence.
That congruence must come from somewhere, and so we push the burden of
congruence up to the setoid carrier itself.

This proof of `field:cong` is important, since equality is now a relation we're
stating should hold, rather than showing it does simply by construction.  This
is where a great deal of the pain of setoids comes from, since it requires us to
prove that every function we'd care to work with is well-behaved when it comes
to equality. We'll get a firsthand feel for the agony when we soon return to
build the `def:pointwise` monoid.

Given `type:Fn`, we're finally ready to encode the proper version of setoid
function extensionality, known as `type:_⇒_` and typed as [`=>`](AgdaMode). This
type generates a setoid whose *carrier* is now these `type:Fn` types, and
relation is a proof that everything does in fact hold:

```agda
    fun-ext : Setoid _ _
    Carrier fun-ext = Fn
    _≈_ fun-ext f g = {x y : From} → x ≈₁ y → f .func x ≈₂ g .func y
    refl′   (pre (equiv fun-ext)) {f}    x=y = f .cong x=y
    trans′  (pre (equiv fun-ext)) ij jk  x=y
      = trans′  (pre (equiv s₂))
                (ij x=y)
                (jk (refl′ (pre (equiv s₁))))
    sym′ (equiv fun-ext) ij x=y
      = sym′ (equiv s₂) (ij (sym′ (equiv s₁) x=y))

    _⇒_ = fun-ext
```

Before you ask, no, I don't understand all the details of the proofs in
`def:_⇒_`---I just set up the types and bashed my way through the implementation
for twenty minutes. `def:_⇒_` is an egregious example of a setoid, but not
particularly so. Setoids, dude...

We've taken a great detour from our original discussion about monoids, so let's
now unwind the stack and return there, seeing how setoids can help (and hinder)
the problems we ran into previously.


## The Pointwise Monoid

The catchphrase of setoids is "always parameterize equality," so returning to
our example of monoids, we must put a `type:Setoid` inside of our `type:Monoid`
bundle. Doing so will allow us to use a custom notion of equality when proving
the monoid laws for `def:pointwise`, and therefore allow us to sidestep the
issue that our two functions were not propositionally equal. Thus:

```agda
record Monoid (c ℓ : Level) : Set (lsuc (c ⊔ ℓ)) where
  field
    setoid : Setoid c ℓ

  open Setoid setoid
    hiding (refl; sym; trans)
    public
```

As it happens, we can `keyword:open` records inside of other records; doing so
brings everything relevant into scope for the remainder of our fields. With the
setoid in scope, we can carry on with our definition of `type:Monoid`. There are
two salient differences here: all of our previous uses of `type:_≡_` are now
replaced with `field:_≈_`, and we have an additional proof burden---we must
showw that `field:_∙_` is congruent with respect to our equivalence relation:

```agda
  infixl  7 _∙_
  field
    _∙_  : Op₂ Carrier
    ε    : Carrier
    assoc  : (x y z : Carrier)
           → (x ∙ y) ∙ z ≈ x ∙ (y ∙ z)
    identityˡ  : (x : Carrier) → ε ∙ x ≈ x
    identityʳ  : (x : Carrier) → x ∙ ε ≈ x
    ∙-cong  : {x y z w : Carrier}
            → x ≈ y → z ≈ w
            → x ∙ z ≈ y ∙ w
```

It's possible to recover all of our previous, propositionally-equal monoids,
moving them to this new and exciting land of setoids, by way of `def:recover`:


```agda
module Naive = Sandbox-Naive-Monoids

recover : {_∙_ : Op₂ A} {ε : A} → Naive.IsMonoid _∙_ ε → Monoid _ _
recover {A = A} {_∙_} {ε} x = record
  { setoid     = prop-setoid A
  ; _∙_        = _∙_
  ; ε          = ε
  ; assoc      = assoc
  ; identityˡ  = identityˡ
  ; identityʳ  = identityʳ
  ; ∙-cong     = λ { ≡.refl ≡.refl → refl }
  }
  where open Naive.IsMonoid x
```

which we can then use to actually recover our "naive" monoids:

```agda
∧-true   = recover Naive.∧-true
∨-false  = recover Naive.∨-false
+-0      = recover Naive.+-0
*-1      = recover Naive.*-1

++-[] <∣>-nothing : {A : Set ℓ} → Monoid _ _
++-[]        {A = A} = recover (Naive.++-[] {A = A})
<∣>-nothing  {A = A} = recover (Naive.<∣>-nothing {A = A})
```

So how does any of this help us write `def:pointwise`, the long-standing thorn
in our side? The construction is not particularly elucidating---as it is just a
very long-winded way of lifting a monoid over a function---but we can finally
build it for ourselves:

```agda
module _ {a c : Level} (A : Set a) (mb : Monoid c ℓ) where
  open Monoid
  open Monoid mb
    renaming  ( ε to εᴮ; _∙_ to _∙ᴮ_; _≈_ to _≈ᴮ_
              ; setoid to setoidᴮ
              )
  open Fn

  reflᴮ : Reflexive _≈ᴮ_
  reflᴮ = refl′ (pre (equiv setoidᴮ))
    where open Setoid-Renaming

  pointwise : Monoid _ _
  setoid pointwise                 = prop-setoid A ⇒ setoidᴮ
  func (_∙_ pointwise f g) a       = func f a ∙ᴮ func g a
  cong (_∙_ pointwise f g) ≡.refl  = ∙-cong mb reflᴮ reflᴮ
  func (ε pointwise) a       = εᴮ
  cong (ε pointwise) ≡.refl  = reflᴮ
  assoc pointwise f g h {x} ≡.refl  = assoc mb  (func f x)
                                                (func g x)
                                                (func h x)
  identityˡ pointwise f {x} ≡.refl  = identityˡ mb (func f x)
  identityʳ pointwise f {x} ≡.refl  = identityʳ mb (func f x)
  ∙-cong pointwise x=y z=y ≡.refl   = ∙-cong mb (x=y refl) (z=y refl)
```

The `def:pointwise` function is an excellent demonstration of why setoids are
awful to work with, since the compiler forces upon us the burden of showing the
congruence of everything involved. Not only do we need to show `field:∙-cong`
for our monoid, which seems like it might be a reasonable ask, but we must
*also* show the congruence of `field:_∙_` and `field:ε` themselves.

The necessity, ubiquity, and pain of setoids in Martin--Löf Type Theory (the
underpinning logic of Agda) is a major driver behind modern type theory
research. Homotopy Type Theory in particular is based on the idea that
equivalence is equivalent to equality, which would allow us to immediately lift
our equivalence relation into a honest-to-goodness equality relation. Other type
theories are beyond the scope of this book, however, but the interested reader
is encouraged to explore this direction on their own.


## Monoid Homomorphisms

One particularly fruitful area to find mathematics that "work" for real problems
is to investigate functions which *preserve structure* between mathematical
structures. Since we're still jiving and excited about monoids, let's consider
these structure-preserving functions in the context of monoids.

Consider therefore what it would mean for a function to preserve the structure
of a monoid. It's worth asking ourselves exactly what structure monoids have in
the first place! Recall, there is an associative binary operator `field:_∙_`,
with a unit `field:ε`.

Now, if we have two `type:Monoid`s, one whose carrier is `A`, and the other
whose carrier is `B`, a monoidal-structure-preserving function `f : A → B` seems
like it ought to (at least) map the identity element in `A` to the identity
element in `B`. Symbolically, that is:

$$
f(\varepsilon_A) = \varepsilon_B
$$

But we have a much more stringent requirement on `f`---we'd like it to also
preserve multiplication. Symbolically then, we'd like:

$$
f(x \cdot_A y) = f(x) \cdot_B f(y)
$$

In the literature, the subscripts here are often omitted, giving us laws that
require mental typechecking in order to make sense of:

$$
f(\varepsilon) = \varepsilon
$$

$$
f(x \cdot y) = f(x) \cdot f(y)
$$

It's important to point out that while these equations look simple, they are
much harder to satisfy than they might seem. The reason is that the notation
$f(x \cdot_A y)$ is merely *syntax.* Assuming a potential monoid homomorphism
between `def:+-0` and `def:*-1`, in the wild these equations might look like any
of the following:

$$
\begin{aligned}
f(13) &= f(10) \cdot f(3) \\
f(13) &= f(13) \cdot f(0) \\
f(13) &= 1 \cdot f(13) \\
f(13) &= 150
\end{aligned}
$$

depending on exactly how much normalization occurred before we got a chance to
look at it. As you can see, being a homomorphism is an extremely stringent
requirement of a function, due to the astronomical number of equations that it
must satisfy.

These structure-preserving functions are known as *homomorphisms,* and are often
qualified by the object they preserve---thus, we have been looking at *monoid
homomorphisms.* Now that we have our setoid machinery sorted out, coding up
monoid homomorphisms is piece of cake. After setting up some environment:

```agda
private variable
  c c₁ c₂ : Level

module _ (m₁ : Monoid c₁ ℓ₁) (m₂ : Monoid c₂ ℓ₂) where
  open Monoid ⦃ ... ⦄

  private instance
    _ = m₁
    _ = m₂

  From = m₁  .Monoid.Carrier
  To   = m₂  .Monoid.Carrier
```

we are ready to give a definition `type:MonHom`, witnessing the fact that some
function `f : X → Y` is a homomorphism. The only potential gotcha here is, as
always when dealing with setoids, a proof of congruence:

```agda
  record MonHom (f : From → To)
        : Set (c₁ ⊔ c₂ ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      preserves-ε  : f ε ≈ ε
      preserves-∙  : (a b : From) → f (a ∙ b) ≈ f a ∙ f b
      f-cong       : {a b : From} → a ≈ b → f a ≈ f b
```


Hidden

:     ```agda
-- FIX
      ```


Now that we have the machinery in place to prove we're not fooling ourselves,
let's begin our hunt for a monoid homomorphism. The simplest monoids we have are
those over the booleans, so let's look there. The monoids we have at hand are
`def:∧-true` and `def:∨-false`. How can we find a homomorphism here?

Given the constraints of the problem, we must be looking for a function `f :`
`type:Bool` `→` `type:Bool`, with the property that `f` `ctor:true` `type:≡`
`ctor:false`. There are only two such functions[^cardinality], `def:const`
`ctor:false` and `def:not`. The latter seems more promising, so let's try that.
We are therefore looking for an inhabitant of the type `expr:MonHom ∧-true
∨-false not`, and after phrasing the problem, Agda does most of the work:

[^cardinality]: This fact comes from an argument about the cardinality of the
type `type:Bool` `→` `type:Bool`, which we will prove for ourselves in
@sec:exponents.


```agda
open MonHom

not-hom : MonHom ∧-true ∨-false not
preserves-ε  not-hom           = refl
preserves-∙  not-hom false  y  = refl
preserves-∙  not-hom true   y  = refl
f-cong       not-hom ≡.refl    = refl
```

We have therefore proven that `def:not` is in fact a monoid homomorphism between
`def:∧-true` and `def:∨-false`. But is it the only one? For a giggle, we can
also try to see if our only other option---`def:const` `ctor:false`---also forms a
homomorphism. Rather surprisingly, it does:

```agda
open import Function using (const)

false-hom : MonHom ∧-true ∨-false (const false)
preserves-ε  false-hom         = refl
preserves-∙  false-hom x y     = refl
f-cong       false-hom ≡.refl  = refl
```

And therefore we have proven that there might several different homomorphisms
between any two monoids. In fact, we can formally prove this by way of a helper
function:

```agda
obviously-untrue : true ≡ false → ⊥
obviously-untrue ()
```

and can then falsify any claim that the existence of two monoid homomorphisms
implies the equality of their mappings over the carriers:

```agda
mon-hom-not-unique
  : ¬ (  {s₁ : Monoid lzero lzero} {s₂ : Monoid lzero lzero}
         {f g : s₁ .Monoid.Carrier → s₂ .Monoid.Carrier}
      →  (hom₁ : MonHom s₁ s₂ f)
      →  (hom₂ : MonHom s₁ s₂ g)
      →  f ≡ g
      )
mon-hom-not-unique claim
  with claim not-hom false-hom
... | not=false = obviously-untrue
  (begin
    true               ≡⟨⟩
    not false          ≡⟨ ≡.cong (λ φ → φ false) not=false ⟩
    const false false  ≡⟨⟩
    false              ∎
  )
  where open ≡-Reasoning
```


Hidden

:     ```agda
-- FIX
      ```


For technical reasons, we are forced to say that `s₁` and `s₂` are monoids over
`expr:lzero`---you're encouraged to work through where the quantification
if you'd like to see why. This is not a fundamental limitation in Agda, but
working around it here is much more effort than it's worth.[^level-lifting]

[^level-lifting]: The construction, for those interested, requires showing that
    we can lift a `type:Monoid` up levels, that is, we require a function
    `expr:{c c′ ℓ ℓ′ : Level} → Monoid c ℓ → Monoid (c ⊔ c′) (ℓ ⊔ ℓ′)`, give a
    similar lift for `def:MonHom`s, and then use this to lift `def:not-hom` and
    `def:false-hom` to the necessary levels.

Returning to `def:not-hom`, expanding out the definition of `field:preserves-∙`
gives us the following equation:

$$
\neg (a \wedge b) = \neg a \vee \neg b
$$

This is an exceptionally famous mathematical theorem, known as one half of *De
Morgan's laws.* The other half is the fact that

$$
\neg (a \vee b) = \neg a \wedge \neg b
$$

which also looks suspiciously like a monoid homomorphism---albeit this time
from `def:∨-false` to `def:∧-true`, which is no harder to prove:

```agda
not-hom′ : MonHom ∨-false ∧-true not
preserves-ε  not-hom′           = refl
preserves-∙  not-hom′ false  y  = refl
preserves-∙  not-hom′ true   y  = refl
f-cong       not-hom′ ≡.refl    = refl
```

Perhaps you're beginning to see the importance---if maybe not yet the *use*
---of monoid homomorphisms. We managed to rediscover an important mathematical
fact simply by trying to find an example! In looking for monoid homomorphisms,
we have seemingly stumbled across a good "pruning" strategy in the search of
interesting theorems. This shouldn't come as much of a surprise; there are
crushingly many functions out there, and most of them *can't* be interesting.
Homomorphisms sufficiently constrain the search space without being so
restrictive that they're hard to find.

Hot off the success of deriving `def:not-hom′` from looking only at
`def:not-hom`, can we switch around the monoids in `def:false-hom` to find a
homomorphism going the other direction for `expr:const false`? A little
investigation shows that no, we cannot find such a homomorphism. Its existence
would violate the law stating identities must be sent to identities. While
`expr:const false` sends everything to `ctor:false`, the identity we're looking
for is `ctor:true`, and thus we are unable to get where we need:

```agda
¬false-hom′ : ¬ MonHom ∨-false ∧-true (const false)
¬false-hom′ x with preserves-ε x
... | ()
```

which therefore immediately tells us that homomorphisms are not, in general,
invertible.


## Finding Equivalent Computations

Armed with some understanding of the importance of monoid homomorphisms, let's
now attempt to develop an intuition as to what they *are.* If a function `f` is
a monoid homomorphism it means we can play fast-and-loose about when we want to
apply `f`. Maybe `f` is expensive, so we'd like to batch all of our monoidal
combining work first, and only ever call `f` once. Alternatively, maybe
`field:_∙₁_` is expensive, in which case we might prefer to first map every `A`
term into a `B` before accumulating them together.

Consider the case of list appending; each call to `def:_++_` is $O(n)$ time, and
thus we run in quadratic time when we have a linear number of lists to append.
If all we'd like to do is count the number of elements in the resulting list, we
have two options: concatenate the lists and subsequently take the length of the
result, or take the lengths individually and add them. Because addition runs in
$O(1)$ time[^in-reality], it is asymptotically faster to add the lengths rather
than taking the length of the concatenation. And it is *precisely* the existence
of the `def:length-hom` monoid homomorphism that ensures these two algorithms
compute the same result:

[^in-reality]: At least, on real computers, for small enough numbers.

```agda
open import Data.List using (List; []; _∷_; _++_)

length : {A : Set} → List A → ℕ
length = Naive.size

length-hom : MonHom (++-[] {A = A}) +-0 length
preserves-ε length-hom = refl
preserves-∙ length-hom [] y = refl
preserves-∙ length-hom (x ∷ xs) y
  rewrite preserves-∙ length-hom xs y
    = refl
f-cong length-hom ≡.refl = refl
```

It's interesting to note that list concatenation is not *intrinsically* slow;
merely that `bind:x y:x ++ y` has *linear* runtime in the length of `x`, but
*constant* runtime in the length of `y`. Therefore, it's *much* more efficient
to compute `bind:x y z w:x ++ (y ++ (z ++ w))` than it is to compute `bind:x y z
w:((x ++ y) ++ z) ++ w`.

Unfortunately, it's very natural to write code that produces the slow,
left-associative tree of `def:_++_` expressions. This is because we prefer to
think about algorithms running forwards, and thus it makes more sense to build
the beginning of a string before the subsequent pieces. Nothing prevents us from
building a string backwards, it's just an unnatural way to structure code. But
what if there were some way to write our code in the usual "beginning-first"
style, and have the computer automatically restructure things so we get the fast
performance we'd like.

This is the key insight behind *string builders,* which are types that, as
expected, efficiently build big strings. String builders are cleverly
implemented to ensure that all the strings they combine are right-associated,
and thus take advantage of this linear runtime.

Rather amazingly, string builders exploit a monoid homomorphism in order to
improve the asymptotics of producing large lists. Since we'd like to eventually
build a list, it *seems* like we should be looking for a monoid homomorphism
into `def:++-[]`. However, this thought is misleading. Recall that homomorphisms
preserve relevant structure, and the relevant structure we'd like to preserve is
the way that lists behave when you concatenate them. Thus we are looking for a
monoid homomorphism *out* of `def:++-[]`! The intuition here is that the
homomorphism proves that one structure can be *embedded* into another.

Therefore, the key insight is that the codomain of our homomorphism should be
some object that supports constant-time, right-associative "concatenation." Such
a thing is necessarily fast to build, and its right-associativity ensures that
building the eventual list will avoid the pathological $O(n^2)$ case.

Thus our goal is refined to finding a constant-time, right-associative monoid.
Here's where it's helpful to have wide knowledge of the monoid "zoo"---is such a
monoid already well-known? It is, and we have already seen it: this is none
other than the monoid of function composition `def:∘-id`!

While we already defined `def:∘-id` as a naive monoid, we're unable to
satisfactorily `def:recover` it to be used here; doing so would require an
explicit invocation of function extensionality when we go to show our
homomorphism respects associativity. Thus we resign ourselves to rewriting
`def:∘-id`, this time in its full setoid generality:

```agda
open import Function using (_∘_; id)
open Fn

module _ where
  open Monoid

  ∘-id : Set ℓ → Monoid _ _
  setoid (∘-id A) = prop-setoid A ⇒ prop-setoid A
  ε      (∘-id A)      = fn id                 λ { ≡.refl → refl }
  _∙_    (∘-id A) f g  = fn (func f ∘ func g)  λ { ≡.refl → refl }
  assoc     (∘-id A) f g h  ≡.refl  = refl
  identityˡ (∘-id A) f  ≡.refl      = refl
  identityʳ (∘-id A) f  ≡.refl      = refl
  ∙-cong (∘-id A) {x} {y} {z} {w} x=y z=w {a} ≡.refl = begin
    (func x ∘ func z) a  ≡⟨⟩
    func x (func z a)    ≡⟨ x=y refl ⟩
    func y (func z a)    ≡⟨ ≡.cong (func y) (z=w refl) ⟩
    func y (func w a)    ≡⟨⟩
    (func y ∘ func w) a  ∎
    where open ≡-Reasoning
```


Hidden

:     ```agda
-- FIX
      ```


Armed with `def:∘-id`, we can now implement our string builder---better known in
the literature (@hughes_novel_1986) as a *difference list*, or *dlist* for
short. It will be helpful to specialize `def:∘-id` for `bind:A:List A`, which we
will call the dlist monoid:

```agda
module DList where
  open Data.List using (_++_)

  dlist-mon : Set ℓ → Monoid _ _
  dlist-mon A = ∘-id (List A)
```

A `type:DList` is thus the carrier of this monoid:

```agda
  DList : Set ℓ → Set ℓ
  DList A = Monoid.Carrier (dlist-mon A)
```

Furthermore, we have an isomorphism between `bind:A:List A` and `bind:A:DList A`
witnessed by `def:hurry` (which speeds up concatenation of lists) and
`def:build` (which gives back the eventual list):

```agda
  hurry : List A → DList A
  hurry l = fn (l ++_) λ { ≡.refl → refl }

  build : DList A → List A
  build dl = func dl []
```

Practically speaking, at this point we're finished---we can `def:hurry` each
substring we'd like to append, use `field:_∙_` from `def:dlist-mon` to glue them
together, and construct the final list via `def:build`:

```agda
  ex-dlist
    = build
      ( hurry (1 ∷ 2 ∷ [])
      ∙ hurry (3 ∷ 4 ∷ [])
      ∙ hurry (5 ∷ [])
      )
    where open Monoid (dlist-mon ℕ)

  _ : ex-dlist ≡ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []
  _ = refl
```

However, as this book is on the topic of correctness, we are still on the hook
to actually *prove* that `def:build` and `def:hurry` work as promised. We will
do this in two steps; first show that `def:build` is indeed a left-inverse of
`def:hurry`. This fact follows immediately from the fact that `def:build`
appends the unit of the list monoid:

```agda
  build∘hurry : (x : List A) → build (hurry x) ≡ x
  build∘hurry = Monoid.identityʳ ++-[]
```

Our other proof burden is to show that `def:hurry` preserves all of the monoidal
structure over lists, which you will not be surprised to see is exactly the
homomorphism we've been searching for this whole time:

```agda
  open MonHom

  hurry-hom : MonHom ++-[] (dlist-mon A) hurry
  preserves-ε  hurry-hom ≡.refl             = refl
  preserves-∙  hurry-hom xs ys {zs} ≡.refl  = Monoid.assoc ++-[] xs ys zs
  f-cong       hurry-hom ≡.refl ≡.refl      = refl
```

Hidden

:     ```agda
  module _ where
    open Monoid (dlist-mon ℕ)
      ```

Recall that `def:hurry-hom` is (among other things) a proof that `def:hurry`
`x` `field:∙` `def:hurry` `y` `field:≈` `bind:x y:hurry (x ++ y)`, and when
combined with `def:build∘hurry`, we get our desired elimination of `def:hurry`,
leaving behind only the appended list.


## Wrapping Up

We introduced monoids in @sec:monoids, but in order to do so, needed a
definition `type:Op₂`, which you can find in `module:Algebra`:

```agda
open import Algebra
  using (Op₂)
  public
```

In @sec:more-mons, we came across `type:List`s, the alternative operator over
`type:Maybe`, which are present in the standard library under:

```agda
open import Data.List
  using (List; []; _∷_; _++_)
  public

open import Data.Maybe
  using (_<∣>_)
  public
```

Furthermore, when trying to give a pointwise monoid over functions, we looked at
several higher-order functions like `def:_∘_` and `def:flip`. You can find all
of these under `module:Function`:

```agda
open import Function
  using (id; _∘_; const; flip)
  public
```

We then looked at extensional equality of functions, witnessed by `type:_≗_`,
which you can find alongside everything else related to propositional equality:

```agda
open import Relation.Binary.PropositionalEquality
  using (_≗_)
  public
```

For technical reasons, we will not use the standard library's definitions of
`type:Monoid` or `type:Setoid`, preferring to export our own definitions facing
forwards. Users hoping to get their hands on the standard library's versions can
find them under `module:Algebra` and `module:Relation.Binary`, respectively.


---

```unicodetable
¬ U+00AC NOT SIGN (\neg)
× U+00D7 MULTIPLICATION SIGN (\x)
ʳ U+02B3 MODIFIER LETTER SMALL R (\^r)
ˡ U+02E1 MODIFIER LETTER SMALL L (\^l)
ε U+03B5 GREEK SMALL LETTER EPSILON (\Ge)
λ U+03BB GREEK SMALL LETTER LAMDA (\Gl)
φ U+03C6 GREEK SMALL LETTER PHI (\Gf)
ᴮ U+1D2E MODIFIER LETTER CAPITAL B (\^B)
′ U+2032 PRIME (\')
₁ U+2081 SUBSCRIPT ONE (\_1)
₂ U+2082 SUBSCRIPT TWO (\_2)
₃ U+2083 SUBSCRIPT THREE (\_3)
ℓ U+2113 SCRIPT SMALL L (\ell)
ℕ U+2115 DOUBLE-STRUCK CAPITAL N (\bN)
→ U+2192 RIGHTWARDS ARROW (\to)
⇒ U+21D2 RIGHTWARDS DOUBLE ARROW (\=>)
∀ U+2200 FOR ALL (\all)
∎ U+220E END OF PROOF (\qed)
∘ U+2218 RING OPERATOR (\o)
∙ U+2219 BULLET OPERATOR (\.)
∣ U+2223 DIVIDES (\|)
∧ U+2227 LOGICAL AND (\and)
∨ U+2228 LOGICAL OR (\or)
∷ U+2237 PROPORTION (\::)
≈ U+2248 ALMOST EQUAL TO (\~~)
≗ U+2257 RING EQUAL TO (\o=)
≡ U+2261 IDENTICAL TO (\==)
⊎ U+228E MULTISET UNION (\u+)
⊔ U+2294 SQUARE CUP (\lub)
⊗ U+2297 CIRCLED TIMES (\ox)
⊙ U+2299 CIRCLED DOT OPERATOR (\o.)
⊥ U+22A5 UP TACK (\bot)
⟨ U+27E8 MATHEMATICAL LEFT ANGLE BRACKET (\<)
⟩ U+27E9 MATHEMATICAL RIGHT ANGLE BRACKET (\>)
⦃ U+2983 LEFT WHITE CURLY BRACKET (\{{)
⦄ U+2984 RIGHT WHITE CURLY BRACKET (\}})
```

