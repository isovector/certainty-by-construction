# Decidability {#sec:decidability}


```agda
  -- TODO(sandy): fit me in! @sec:monus-no-left-id
  -- open import Relation.Nullary
  -- open import Data.Product

  -- ¬∸-identityˡ : ¬ (∃Σ ℕ λ e → (x : ℕ) → e ∸ x ≡ x)
  -- ¬∸-identityˡ (e , e-id) with e-id 0 | e-id 1
  -- ... | refl | ()
```


Hidden

:   ```agda
{-# OPTIONS --allow-unsolved-metas #-}
    ```


```agda
module Chapter4-Decidability where
```


Prerequisites

:   ```agda
import Chapter1-Agda
open Chapter1-Agda.Exports
  using (Bool; true; false)
    ```

:   ```agda
import Chapter2-Numbers
open Chapter2-Numbers.Exports
  using (ℕ; zero; suc)
    ```

:   ```agda
import Chapter3-Proofs
open Chapter3-Proofs.Exports
  using (_≡_; refl; sym; trans; cong; module ≡-Reasoning)
    ```


In the last chapter, we thoroughly investigated the notion of doing proof work
in Agda. We gave a propositional definition what it means for two things to be
equal, derived relevant properties of equality, built a domain-specific language
for doing equational reasoning, and proved many facts about the natural numbers.

Perhaps you are thinking you now know all there is to know about proofs, but
this is patently false: for example, we haven't yet discussed what it means for
a notion to be false! Furthermore, everything we've built so far works only for
*statically-known* values. But is it possible that we can use dependent types in
contexts where we don't know all the values we need to work with? Maybe the
values came from the user via an interactive system. Are we forced to throw away
everything we've done and degrade our guarantees to those of a weaker
programming language?

Thankfully the answer is "no," and we will explore the ideas no. In addition, we
will also get our hands dirty modeling and proving facts about objects that feel
significantly more *computer science-y.* After all, these techniques are
applicable outside of the ivory tower, too!


## Negation

Recall that we've now seen how to express that two values are (propositionally)
equal, via the `type:_≡_` type, proven via `ctor:refl`. We'd now like to determine a means
of discussing *inequality!*

Perhaps you might think we can make a slight tweak to the `type:_≡_` construction.
While `refl : x ≡ x`, perhaps we could try something along the lines of:

```agda
module Sandbox-Inequality where
  data _≢_ {A : Set} : A → A → Set where
    ineq : {x y : A} → x ≢ y
```

Unfortunately, this approach does not---and in fact, cannot---work. While we've
attempted to assert that `x` and `y` are inequal by virtue of being different
bindings of `A`, Agda gives us no guarantees that they are *distinct* values of
`A`! It's like if you write a function:

$$
(x, y) \mapsto x + y
$$

Here, $x$ and $y$ are different *variables,* but that doesn't mean I can't
*evaluate* this function at $x = y = 2$. Therefore, this approach is a dead-end,
and we will need to find an alternative means.

Recall the *principle of explosion,* the property of a contradictory system,
which states that "from false, anything is possible." This gives us a hint as to
how we might go about encoding an inequality. Rather than treating it as such,
we can instead rewrite $x \neq y$ as "$x = y$ is false."

Let's give it a go. First, rather than importing our hand-rolled natural numbers
from the previous sections, we can import them from the standard library. Don't
worry, the interface is identical to the ones we built, so there will be no
surprises in doing this:

```agda
-- open Chapter2-Numbers.Exports.Naturals
--   using (ℕ; zero; suc; _+_)
```

We will also need to import propositional equality, which we can also get from
the standard library. This too has an identical interface, so we're safe to do
so:

```agda
-- open Chapter3-Proofs.Exports
--   using (_≡_; refl; sym; trans; cong; module ≡-Reasoning)
```

With these out of the way, we can get started on our new attempt at the
principle of explosion. The idea being, in order to show that some proposition
`P` is false, we must be able to generate anything we'd like, of any type we'd
like. We can model this as:

```agda
module Sandbox-Explosion where
  False : Set → Set₁  -- ! 1
  False P = P → {A : Set} → A
```

You'll notice at [1](Ann) that the type of `type:False` is `type:Set → Set₁`, which is a
feature of Agda's type system we haven't yet covered, but will later this
chapter. For the time being, pretend this says `type:Set → Set`. We can now try to
find a proof that 2 is not equal to three, as per:

```agda
  2≠3⅋₀ : False (2 ≡ 3)
  2≠3⅋₀ = ?
```

Since `type:False` expands to a function type, we can (rather unintuitively) do a
[MakeCase:](AgdaCmd) here to get a *parameter* of type `2 ≡ 3`:

```agda
  2≠3⅋₁ : False (2 ≡ 3)
  2≠3⅋₁ x = {! !}
```

Asking Agda to [MakeCase:x](AgdaCmd) here produces a strange result:

```agda
  2≠3 : False (2 ≡ 3)
  2≠3 ()
```

What has happened is that Agda noticed that *there are no constructors for `2 ≡
3`,* and thus that this function cannot actually be called, because there is no
argument you can give it that would typecheck. Since the whole thing is moot
anyway, Agda doesn't require us to write an implementation of this function, and
allows us to get away with an *absurd pattern match,* which is the name for
those empty parentheses and the lack of an equals sign.

By virtue of having written a definition of `2≠3` that typechecks, we have
successfully proven the fact that two is not equal to three. Mission
accomplished! Nevertheless, while this is an absolutely valid encoding, it's not
how we usually write propositional negation in Agda. For that, we need the empty
type.


## Bottom

While it's acceptable to use the principle of explosion directly, there is a
simpler way of encoding the problem, namely by "factoring out" the pieces.
Rather than showing all contradictions lead to explosion, we can instead say all
contradictions lead to a specific type, and then show that all values of that
type lead to explosion. The resulting machinery means you can always use the
principle of explosion if you'd like, but in practice means your type signatures
and negative proofs become simpler to work with.

The "pre-explosive" type we'll work with is called the *bottom* type, written
`type:⊥` and input as [`bot`](AgdaMode). It's definition is short and sweet:

```agda
data ⊥ : Set where
```

That's it. There are no constructors for `type:⊥`. Besides a slightly different type
signature, we can show `2≠3` with an identical proof, this time using bottom:

```agda
2≠3 : 2 ≡ 3 → ⊥
2≠3 ()
```

Why does this work? Recall the definition of a function: for any input in the
domain, it maps it to an element in the codomain. But there are no elements in
bottom, so any function whose codomain is bottom cannot possibly be a function
unless its *domain* also has no elements. Otherwise, the function would have
elements in the domain with nowhere to map them to in the codomain.

By this argument, any function we can successfully define which maps into bottom
necessarily constrains at least one of its parameters to also have no elements.

We still need to show that an element of `type:⊥` leads to the principle of
explosion, which is another easy proof:

```agda
⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()
```

Mathematically, proofs of this flavor are called *vacuously true.* Which is to
say, they are true only because they depend on a contradiction in the first
place. Nevertheless, we can give a vacuous proof that all bottom elements (of
which there are none in the first place) are equal:

```agda
⊥-unique : {x y : ⊥} → x ≡ y
⊥-unique {x} = ⊥-elim x
```

We have now shown that bottom is a satisfactory definition of false, and that
functions into bottom are therefore a good definition of the falseness of their
input type considered as a proposition. Hence, we can define `type:¬_` ([`neg`](AgdaMode)), which
states that a given proposition is false:

```agda
open import Level
  using (Level)

¬_ : {ℓ : Level} → Set ℓ → Set ℓ
¬ P = P → ⊥
infix 3 ¬_
```

Again, ignore this `type:Level` stuff for the time being (although you can input `ℓ`
via [`ell`](AgdaMode).)


## Inequality

With a satisfactory definition for propositional negation, we can
define inequality (input as [`neq`](AgdaMode)):



```agda
_≢_ : {A : Set} → A → A → Set
x ≢ y = ¬ x ≡ y
infix 4 _≢_
```

When defining new relations, it's always a reward experience to investigate
which properties hold of the new construction. As you might expect, inequality
is symmetric:

```agda
≢-sym : {A : Set} {x y : A} → x ≢ y → y ≢ x
≢-sym x≠y y=x = x≠y (sym y=x)
```

and it is obviously *not* reflexive. Why obviously? Because reflexivity would
require that `x ≢ x` for any `x`, which is exactly the opposite of what we're
trying to encode here. Interestingly, however, we can prove that `type:_≢_` isn't
reflexive, but showing that if there were such a `refl : x ≢ x` construction, it
would lead to contradiction.

Let's show this in a few steps. First, we will define a type `type:Reflexive` which
will state the reflexivity property. This isn't strictly necessary, but it
lessens the cognitive burden later down the line:

```agda
Reflexive : {A : Set} → (A → A → Set) → Set
Reflexive {A} _≈_ = {x : A} → x ≈ x
```

Having a value of `Reflexive _≈_` states that `_≈_` is a reflexive relation.
Note that `_≈_` is on the left side of the equals sign, and is thus just a
parameter---allowing us to state *which* relation is reflexive. To illustrate
exactly what's happening here, we can show that propositional equality is
reflexive:

```agda
≡-refl : {A : Set} → Reflexive {A} _≡_
≡-refl = refl
```

Notice how the type `Reflexive _≡_` expands to the type of `refl : {x : A} → x ≡
x`. We are required to bind `A : Set` here, so that we can pass it over to
`type:Reflexive`, which could in principle infer it from the type of `type:_≡_`, but Agda
has no way of knowing if you'd like to talk about `type:_≡_` in its fully-general
polymorphic type, or about `type:_≡_` when specialized to something about the natural
numbers. The distinction isn't extremely poignant in this example, but there do
exist monomorphic relations which we might still want to say are reflexive.
Nevertheless, we have shown that `type:_≡_` is reflexive by giving a proof that
`ctor:refl` exists.

Contrasting against this is the proof that `type:_≢_` is *not* reflexive. The type of
such a statement is a very subtle thing:

```agda
¬≢-refl⅋₀ : ¬ ({A : Set} → Reflexive {A} _≢_)  -- ! 1
¬≢-refl⅋₀ = ?
```

Compare this type to the more "obvious" type:

```agda
¬≢-refl-bad⅋₀ : {A : Set} → ¬ Reflexive {A} _≢_  -- ! 2
¬≢-refl-bad⅋₀ = ?
```

The difference between [1](Ann) and [2](Ann) is that in the latter, we receive a
specific `A`, and are then required to give back a proof that there is no
`def:≢-refl` *for that specific type.* In [1](Ann) however, we are required to show
that there does not exist a `def:≢-refl` that works for *every* type `A`. End users
of `¬≢-refl` don't care one way or another, but the difference here is
absolutely crucial for actually *proving* the notion. Let's look at this more
closely.

At a high level, the proof here is "`def:≢-refl` must be false because it's the
negation of `def:≡-refl`, which is easily shown to be true." While the type of the
argument to `def:¬≢-refl` is `type:Reflexive _≢_`, we can use
[TypeContext/Normalise](AgdaCmd) to ask Agda to expand out this definition,
resulting in `x ≡ x → ⊥`. Under the lens of this expanded type, it seems
reasonable to call the argument `def:¬≡-refl`, as in the following:

```agda
¬≢-refl⅋₁ : ¬ ({A : Set} → Reflexive {A} _≢_)
¬≢-refl⅋₁ ¬≡-refl = {! !}
```

Of course, we do in fact have a proof of `type:x ≡ x`, namely `ctor:refl`, so we can try
solving the hole as:

```agda
¬≢-refl⅋₂ : ¬ ({A : Set} → Reflexive {A} _≢_)
¬≢-refl⅋₂ ¬≡-refl = ¬≡-refl refl
```

Uh oh, something went wrong. This yellow background means that elaboration
failed, which means that Agda was unable to determine some of the implicit
arguments. We can help it out by explicitly introducing holes for each implicit
argument and solving them ourselves:

```agda
¬≢-refl⅋₃ : ¬ ({A : Set} → Reflexive {A} _≢_)
¬≢-refl⅋₃ ¬≡-refl = ¬≡-refl {?} {?} refl
```

You'll notice that the yellow warning has disappeared, and we're left only with
some holes to fill. The first hole has type `type:Set`, while the second has type
`?0`, meaning its type depends on the answer to our first hole. We're free to
choose any type we'd like for this first hole, so let's try `type:ℕ`:

```agda
¬≢-refl⅋₄ : ¬ ({A : Set} → Reflexive {A} _≢_)
¬≢-refl⅋₄ ¬≡-refl = ¬≡-refl {ℕ} {?} refl
```

and now all we need is to pick an arbitrary value of type `type:ℕ`:

```agda
¬≢-refl : ¬ ({A : Set} → Reflexive {A} _≢_)
¬≢-refl ≢-refl = ≢-refl {ℕ} {0} refl
```

What was to be demonstrated has thus been proved. But let's see what goes wrong
if we try the same approach on `def:¬≢-refl-bad`. Since `A` is now a top-level
parameter, we can bind it in the function body, meaning we have one fewer
implicit to fill in:

```agda
¬≢-refl-bad : {A : Set} → ¬ Reflexive {A} _≢_
¬≢-refl-bad {A} ¬≡-refl = ¬≡-refl {?} refl
```

This hole unfortunately has type `A`, *for some unknown type `A`!* We can't
possibly fill this in, because we don't know what type `A` is. In fact, `A`
could be `type:⊥`, in which case there aren't any values we could put here even in
principle.

The takeaway from this is that it really matters where you put your quantifiers.
When the necessary parameters are *inside* the negation, we are able to
instantiate them at our convenience in order to find a counterexample. But if
they are outside, we are at the whim of the proof-caller, which might
dramatically change how we'd go about showing a counterexample, and often
precludes it entirely.


## Negation Considered as a Callback

There is an apt computational perspective to this problem of negating
quantifiers, which comes when we expand out all of our types. After fully
normalizing (expanding out) the types of both `def:¬≢-refl` and `def:¬≢-refl-bad`, we
are left with this:

```type
¬≢-refl     : ({A : Set} → {x : A} → x ≡ x → ⊥) → ⊥
¬≢-refl-bad : {A : Set} → ({x : A} → x ≡ x → ⊥) → ⊥
```

These types have much more going on, but the important thing to notice is that
they both take functions as arguments. Whenever you see a function as an
argument, you should immediately think "callback." Viewed as a callback, the
question becomes *who is responsible for providing the parameters?* In the first
case, it is `def:¬≢-refl` which gets to pick `A`, while in the second, it
is the *caller* of `def:¬≢-refl-bad` who gets to pick `A`. And true to the name,
this caller might pick an antagonistic `A` in an attempt to thwart us!


## Intransitivity of Inequality

In the same vein as `def:¬≢-refl`, we can also show that `type:_≢_` doesn't satisfy
transitivity. The pen and paper proof is straightforward, since if inequality
were transitive we could show:

$$
\begin{aligned}
2 &\neq 3 \\
&\neq 2
\end{aligned}
$$

This is known in the business as a "whoopsie daisy." Such a counterexample shows
inequality cannot be transitive, and we can prove it more formally in Agda by
giving a definition for transitivity:

```agda
Transitive : {A : Set} → (A → A → Set) → Set
Transitive {A} _≈_ = {x y z : A} → x ≈ y → y ≈ z → x ≈ z
```

Giving the counterexample is easy, since we already have a proof `def:2≠3`. Given a
hypothetical `def:≢-trans`, we could combine this with `sym 3≠2`, to get a proof
that `2 ≢ 2`. Such a thing is in direct contradiction with `refl : 2 ≡ 2`, and
thus we are done:

```agda
¬≢-trans : ¬ ({A : Set} → Transitive {A} _≢_)
¬≢-trans ≢-trans = ≢-trans {ℕ} 2≠3 (≢-sym 2≠3) refl
```


## Decidability

It is now time to return to the question of how does one combine dependent types
with the "real world." That is, the proofs we've seen so far work swell when
everything is known statically, but things begin to fall apart when you want to
get input from a user, or read from a file, or something of this nature. What do
we do when we don't have all of our information known statically?

The answer is unsurprising: we just compute it.

Recall that every concrete proof we've given is represented by a value. That
means it has a representation in memory, and therefore, that it's the sort of
thing we can build at runtime. The types shade the techniques that you already
know how to do from a career of elbow grease computing things.

In a language with a less powerful system, how do you check if the number the
user input is less than five? You just do a runtime check to see if it's less
than five before continuing. We can do exactly the same thing in Agda, except
that we'd like to return a *proof* that our number is equal to five, rather than
just a boolean. To a first approximation, you can imagine we could implement
such a thing like this:

```agda
module Sandbox-Decidability where
  open Chapter2-Numbers.Exports
    using (Maybe; just; nothing)

  n=5? : (n : ℕ) → Maybe (n ≡ 5)
  n=5? 5 = just refl
  n=5? _ = nothing
```

Given `def:n=5?`, we can call this function and branch on its result. If the result
is a `ctor:just`, we now have a proof that the argument was indeed 5, and can use it
as we'd please.

Of course, if the argument wasn't five, this definition doesn't allow us to
learn anything at all. When instead, it would be much more useful to learn that
`¬ (n ≡ 5)`, in case we'd like to do something with that information! From this,
we conclude that returning `type:Maybe` isn't quite the right choice. Instead, we'd
like a slightly-more structured type corresponding to *decisions*:

```agda
data Dec (P : Set) : Set where
  yes : P  → Dec P
  no : ¬ P → Dec P
```

`type:Dec` is a type which states if we know for sure that either `P` holds, or that
`P` *doesn't* hold. Of course, only one of these can ever be true at once, and
thus `Dec P` corresponds to an answer that we can definitively compute. For
example, given two numbers, it's not too hard to determine if the two are equal.

```agda
module Nat-Properties where
  _==_ : ℕ → ℕ → Bool
  zero  == zero  = true
  zero  == suc y = false
  suc x == zero  = false
  suc x == suc y = x == y
```

While `def:_==_` *is* a decision procedure, it doesn't give us back any
proof-relevant term. The goal is slightly modify this definition such that
whenever it returns `true` we instead give back a `ctor:yes`, and likewise replace
`false` with `ctor:no`. Giving back the `ctor:yes`es is easy enough, but the `ctor:no`s take a
little more thought:

```agda
  _≟⅋₀_ : (x y : ℕ) → Dec (x ≡ y)
  zero ≟⅋₀ zero = yes refl
  zero ≟⅋₀ suc y = no ?
  suc x ≟⅋₀ zero = no ?
  suc x ≟⅋₀ suc y with x ≟⅋₀ y
  ... | yes refl = yes refl
  ... | no x≠y   = no ?
```

The first hole here has type `zero ≡ suc y → ⊥`, which we can [Refine](AgdaCmd)
to a lambda:

```agda
  _≟⅋₁_ : (x y : ℕ) → Dec (x ≡ y)
  zero ≟⅋₁ zero = yes refl
  zero ≟⅋₁ suc y = no λ { x → {! !} }
  suc x ≟⅋₁ zero = no ?
  suc x ≟⅋₁ suc y with x ≟⅋₁ y
  ... | yes refl = yes refl
  ... | no x≠y   = no ?
```

Inside our lambda we have `x : zero ≡ suc y`, which can never happen, since
`ctor:zero` and `ctor:suc` are different constructors. Therefore, we can solve this (and
the next) hole with absurd pattern matches inside of the lambda:

```agda
  _≟⅋₂_ : (x y : ℕ) → Dec (x ≡ y)
  zero ≟⅋₂ zero = yes refl
  zero ≟⅋₂ suc y = no λ ()
  suc x ≟⅋₂ zero = no λ ()
  suc x ≟⅋₂ suc y with x ≟⅋₂ y
  ... | yes refl = yes refl
  ... | no x≠y   = no ?
```

We are left with only one hole, but it is `suc x ≡ suc y → ⊥`, and thus our
absurd pattern trick can't work here. However, we do have a proof that `x ≢ y`,
from which we must derive a contradiction. The idea is that if refine our hole
to a lambda, it will have a parameter of type `suc x ≡ suc y`, which if we
pattern match on, Agda will learn that `x ≡ y`. From there, we can invoke the
fact that `x ≢ y`, and we have the contradiction we've been looking for:

```agda
  _≟_ : (x y : ℕ) → Dec (x ≡ y)
  zero ≟ zero = yes refl
  zero ≟ suc y = no λ ()
  suc x ≟ zero = no λ ()
  suc x ≟ suc y with x ≟ y
  ... | yes refl = yes refl
  ... | no x≠y   = no λ { refl → x≠y refl }
```

Take a moment to reflect on this. Where before `def:_==_` simply returned `false`,
we are now responsible for *deriving a contradiction.* Alternatively said, we
must now *reify* our reasoning, and *prove* that our algorithm does what it
says. The advantage of returning a proof of the negation is that downstream
callers can use it to show impossible codepaths of their own.

We can package up decidable equality into its own type:

```agda
DecidableEquality : (A : Set) → Set
DecidableEquality A = (x y : A) → Dec (x ≡ y)
```

and give a more "semantically-inclined" type to our old function:


```agda
_≟ℕ_ : DecidableEquality ℕ
_≟ℕ_ = Nat-Properties._≟_
```


## Binary Trees

Perhaps you are tired of always working with numbers. After all, isn't this
supposed to be a book about applying mathematical techniques to computer
science? As it happens, all the techniques we have explored so far are
applicable to data structures just as much as they are to numbers and the
more mathematical purviews.

It is a matter of tradition to begin every exploration of data structures in
functional programming with lists. The author is personally exhausted of this
tradition, and suspects the audience is as well. Therefore, we will instead
touch upon the binary trees: how to construct them, and how to prove things
about them.

A binary tree is either empty, or it is a branching node containing a value and two
subtrees. We can codify this as follows:

```agda
module BinaryTrees where
  data BinTree (A : Set) : Set where
    empty : BinTree A
    branch : BinTree A → A → BinTree A → BinTree A
```

For convenience, it's often helpful to be able to talk about a single-element
tree, which we can encode as a `ctor:branch` with two `ctor:empty` children. Agda lets us
define pseudo-constructors called *patterns* for cases like these. The following
defines a new pattern called `leaf : A → BinTree A`:

```agda
  pattern leaf a = branch empty a empty
```

You might wonder why we use a `keyword:pattern` here rather than just a regular
old function:

```agda
  leaf′ : {A : Set} → A → BinTree A
  leaf′ a = branch empty a empty
```

The difference is all in the colors. Literally. The reason is that, as the name
implies, we can *pattern match* when `ctor:leaf` is defined as pattern:

```agda
  is-singleton : {A : Set} → BinTree A → Bool
  is-singleton (leaf _) = true
  is-singleton _ = false
```

In addition, we can use patterns as expressions, as in:

```agda
  five-tree : BinTree ℕ
  five-tree = leaf 5
```

Patterns don't buy us anything we couldn't do otherwise, but they are often
convenient when you have interesting special cases that you'd like to sometimes
highlight, without baking them directly into the definition of the type.

The first thing we might want to prove about a tree is whether it contains a
particular element. As usual, we do so by considering the base case, and the
inductive cases. The base case is that the thing you're looking for is at the
root:

```agda
  data _∈⅋_ {A : Set} : A → BinTree A → Set where
    here : {a : A} {l r : BinTree A} → a ∈⅋ branch l a r
```

Otherwise, the element you're looking for might be in the left subtree:

```agda
    left : {a b : A} {l r : BinTree A} → a ∈⅋ l → a ∈⅋ branch l b r
```

and of course, it could also be in the right subtree:

```agda
    right : {a b : A} {l r : BinTree A} → a ∈⅋ r → a ∈⅋ branch l b r
```

This definition works perfectly well, but it's a bit wordy. Notice that over
half of it is just bringing implicit bindings into scope. This is a perfect
use-case for Agda's `keyword:variable` block, which allows us to define implicit
bindings that should exist for the remainder of the scope.

Variable blocks are started with the keywords `keyword:private variable`, and then begin
a new layout. We can create a few variables:

```agda
  private variable
    A : Set
    a b : A
    l r : BinTree A
```

The definitions in a variable block are just type signatures. The semantics here
are that whenever we use an otherwise-undeclared variable `l` in our code, Agda
will instead look it up from the variable block, and insert it as an implicit
argument. With this feature, we can rewrite `type:_∈_` in a much terser, but
*completely-equivalent* way:

```agda
  data _∈_ : A → BinTree A → Set where
    here   :          a ∈ branch l a r
    left   : a ∈ l →  a ∈ branch l b r
    right  : a ∈ r →  a ∈ branch l b r
```

Just to demonstrate that everything works, we can make a little tree:

```agda
  tree : BinTree ℕ
  tree = branch (branch (leaf 0) 0 (leaf 2)) 4 (leaf 6)
```

and then show that six is somewhere in this `def:tree`, as per the very assertive
definition:

```agda
  6∈tree : 6 ∈ tree
  6∈tree = right here
```

It might also be desirable to show that every element in the tree satisfies some
property. Perhaps we'd like to build a binary tree consisting only of odd
numbers, for example. It's unclear why, but nevertheless it's something we
*might* want to do. There is no finger pointing here!

Building `type:All` is easy. We can replace every instance of `A` with `P A`, and
every instance of `type:BinTree` with `type:All`. Modulo a few indices at the end, we're
left with a reminiscent definition:

```agda
  data All (P : A → Set) : BinTree A → Set where
    empty   : All P empty
    branch  : All P l → P a → All P r → All P (branch l a r)
```

A pattern definition doesn't come with a type signature, and thus it only works
with whatever constructors existed when it was defined. Since in `type:All` we have
reused the constructor names `ctor:empty` and `ctor:branch`, we can redefine `ctor:leaf` again
so that it also works over `type:All`:

-- TODO(sandy): fact check


```agda
  pattern leaf a = branch empty a empty
```

In the `ctor:branch` case, we must show that everything holds in both subtrees, as
well as that the property holds for the value at the root. By induction, we have
now covered every element in the tree. We can show it works by coming up with a
quick predicate, maybe the evenness of a number. We defined a similar thing back
in @sec:even, however we cannot reuse it here, as it was defined over our custom
natural numbers, and does not exist in the standard library.

-- TODO(sandy): just fix this


```agda
  open Chapter2-Numbers.Exports
    using (IsEven; z-even; ss-even)

  -- data IsEven : ℕ → Set where
  --   z-even   : IsEven 0
  --   ss-even  : {n : ℕ} → IsEven n → IsEven (2 + n)
```

It's now possible to show every element in `def:tree` is even. In fact, Agda can
prove it for us, via [Auto](AgdaCmd):

```agda
  tree-all-even : All IsEven tree
  tree-all-even =
    branch
      (branch
        (branch empty z-even empty)
        z-even
        (branch empty (ss-even z-even) empty))
      (ss-even (ss-even z-even))
      (branch empty (ss-even (ss-even (ss-even z-even))) empty)
```

Of course, a little cleanup goes a long way:

```agda
  tree-all-even⅋ : All IsEven tree
  tree-all-even⅋ =
    branch
      (branch
        (leaf z-even)
        z-even
        (leaf (ss-even z-even)))
      (ss-even (ss-even z-even))
      (leaf (ss-even (ss-even (ss-even z-even))))
```

We've given decidability proofs for equality; can we also give one for `All P`?
Certainly we can; given a decidable procedure for `P`, we can just try it at
every node in the tree and see what shakes out. But before we write it, the
following definition will be useful to help corral the types:

```agda
  -- TODO(sandy): decidable in stdlib is over TWO arguments

  Decidable : (A → Set) → Set
  Decidable {A} P = (a : A) → Dec (P a)

  Decidable₂ : (A → A → Set) → Set
  Decidable₂ {A} _~_ = (x y : A) → Dec (x ~ y)
```

The `type:Dec` type corresponds to a particular *decision*, while `type:Decidable` states
that we can make a decision for *every input.* It's the difference between
saying that I, personally, have an age and saying that *everyone* has an age.

Notice that we used the variable `A` in our type definition for `type:Decidable`. In
order to bring `A` into scope in the *body* of `type:Decidable`, we need to bind it
as an implicit argument. This is the general way that variables are
used---implicitly (in the usual, non-technical sense) in the type, and
implicitly (in the Agda sense) in the definition.


Exercise

:   Show that `All P` is `type:Decidable`, given a decision procedure for `P`.


Solution

:   ```agda
  all? : {P : A → Set} → Decidable P → Decidable (All P)
  all? p? empty = yes empty
  all? p? (branch l a r) with p? a
  ... | no ¬pa = no λ { (branch _ pa _) → ¬pa pa }
  ... | yes pa
    with all? p? l
  ... | no ¬all-l =
          no λ { (branch all-l _ _) → ¬all-l all-l }
  ... | yes all-l
    with all? p? r
  ... | no ¬all-r =
          no λ { (branch _ _ all-r) → ¬all-r all-r }
  ... | yes all-r = yes (branch all-l pa all-r)
    ```

As this exercise shows, decision procedures are often extremely formulaic. You
decide each individual piece, and combine them together if you can, or witness a
contradiction from the bigger structure if you can't.


## Binary Search Trees

Binary search trees (BSTs) are a refinement of binary trees, with the property
that everything in the left subtree is less than or equal to the root, and
everything in the right subtree is greater than or equal to the root.

This one is a bit harder to encode, since it requires a notion of ordering. Of
course, we can always just add it as a parameter, as in:

```agda
  data IsBST (_≤_ : A → A → Set) : BinTree A → Set where
```

An empty BST is still a BST, so the base case is simple:

```agda
    bst-empty : IsBST _≤_ empty
```

The recursive case requires us to show several things, however. First, we
require that our invariants hold---everything in the left tree is smaller, and
everything in the right tree is larger:

```agda
    bst-branch
        : All (_≤ a) l →
          All (a ≤_) r →
```

Then, we require that both trees are themselves BSTs:

```agda
          IsBST _≤_ l →
          IsBST _≤_ r →
```

which is sufficient to show that the binary tree is itself a BST:

```agda
          IsBST _≤_ (branch l a r)
```

-- TODO(sandy): put this sooner in the book!

Given the standard notion of ordering over the natural numbers:

```agda
  data _≤_ : ℕ → ℕ → Set where
    z≤n : {n : ℕ} → zero ≤ n
    s≤s : {m n : ℕ} → m ≤ n → suc m ≤ suc n
```

we can again ask Agda for a proof that `def:tree` is a BST:

```agda
  tree-is-bst : IsBST _≤_ tree
  tree-is-bst =
    bst-branch
      (branch (leaf z≤n) z≤n (leaf (s≤s (s≤s z≤n))))
      (leaf (s≤s (s≤s (s≤s (s≤s z≤n)))))
      (bst-branch
        (leaf z≤n)
        (leaf z≤n)
        (bst-branch empty empty bst-empty bst-empty)
        (bst-branch empty empty bst-empty bst-empty))
      (bst-branch empty empty bst-empty bst-empty)
```

You'll notice several subexpressions of the form `ctor:bst-branch empty empty
bst-empty bst-empty`, which is the proof that a `ctor:leaf` is a BST. This is a good
opportunity for another pattern:

```agda
  pattern bst-leaf =
    bst-branch empty empty bst-empty bst-empty
```

which cleans up the above:

```agda
  tree-is-bst⅋ : IsBST _≤_ tree
  tree-is-bst⅋ =
    bst-branch
      (branch (leaf z≤n) z≤n (leaf (s≤s (s≤s z≤n))))
      (leaf (s≤s (s≤s (s≤s (s≤s z≤n)))))
      (bst-branch (leaf z≤n) (leaf z≤n) bst-leaf bst-leaf)
      bst-leaf
```

Proofs like this are an awful lot of work, but thankfully we never need to write
them by hand. For concrete values, we can always ask Agda to solve them for us,
and for parameterized values, we can build them by induction.

Speaking of induction, can we decide whether a given tree is a BST? Sure! The
pattern is exactly the same, decide each piece, derive contradictions on `ctor:no`,
and assemble the final proof if everything is `ctor:yes`:

```agda
  is-bst?
      : {_≤_ : A → A → Set}
      → Decidable₂ _≤_
      → Decidable (IsBST _≤_)
  is-bst? _≤?_ empty = yes bst-empty
  is-bst? _≤?_ (branch l a r)
    with all? (_≤? a) l
  ... | no ¬all≤a-l =
          no λ { (bst-branch all≤a-l _ _ _)
                    → ¬all≤a-l all≤a-l }
  ... | yes all≤a-l
    with all? (a ≤?_) r
  ... | no ¬arr≤a-r =
          no λ { (bst-branch _ arr≤a-r _ _)
                    → ¬arr≤a-r arr≤a-r }
  ... | yes arr≤a-r
    with is-bst? _≤?_ l
  ... | no ¬bst-l =
          no λ { (bst-branch _ _ bst-l _) → ¬bst-l bst-l }
  ... | yes bst-l
    with is-bst? _≤?_ r
  ... | no ¬bst-r =
          no λ { (bst-branch _ _ _ bst-r) → ¬bst-r bst-r }
  ... | yes bst-r =
          yes (bst-branch all≤a-l arr≤a-r bst-l bst-r)
```

You might be wondering whether there is an easier way to assemble these proofs.
Unfortunately, there is not. It's not theoretically impossible by any means, but
at time of writing, there is no automatic means of deriving these proofs.


## Insertion into BSTs

What we have done thus far is show that there exist things called binary search
trees, and we have given a definition of what properties we mean when we say
something is---or isn't---a binary search tree. This is a great start,
prescriptively speaking, but this is not exactly where most computer science
textbooks go when they discuss BSTs. Instead, they immediately dive into the
meat of "what can you do with a BST."

Insertion is something you can do with a BST, and lest we be left behind by the
traditional pedagogical material, let's now turn our discussion to insertion.
The algorithm is easy enough---if the tree is empty, add a leaf. Otherwise,
compare the value you'd like to insert with the value at the root. If they're
equal, you're done. Otherwise, recursively insert the value into the correct of
the subtree.

The implicit claim here is that this algorithm preserves the `type:IsBST` invariant,
but that is never explicitly pointed out. For posterity, this algorithm *does*
indeed preserve the `type:IsBST` invariant. However, this poses some challenges for
us, since in order to show this we must necessarily derive a proof, which is
going to depend on a proof that we picked the correct subtree to recurse on.

What we have to work with thus far is only the fact that `type:_<_` is decidable. But
if we were to work directly with the decidability `type:_<_`, our algorithm would
need to first check whether `a < x`, and if it isn't, check that `x < a`, and if
it isn't check that `x ≡ y`, and if *that isn't,* well then we definitely have a
problem. This doesn't sound like an enjoyable experience though; as we have seen
above, every invocation of decidability doubles the amount of work we need to
do, since we need to use the proof or show a subsequent contradiction.

Instead, we can generalize the idea of decidability to a *trichotomy*, which is
the idea that exactly one of three choices must hold. From this perspective,
`type:Dec` is merely a type that states exactly one of `P` or `¬ P` holds, and so the
notion of trichotomy shouldn't be earth-shattering. We can define `type:Tri`
(analogous to `type:Dec`) as as proof that exactly one of `A`, `B` or `C` holds:

```agda
  data Tri (A B C : Set) : Set where
    tri< :    A → ¬  B → ¬  C → Tri A B C
    tri≈ : ¬  A →    B → ¬  C → Tri A B C
    tri> : ¬  A → ¬  B →    C → Tri A B C
```

and we can lift this notion to `type:Trichotomous`, stating that for two relations,
one equality-like, and one less-than-like, we can always determine which holds:

```agda
  Trichotomous
      : (_≈_ : A → A → Set)
      → (_<_ : A → A → Set)
      → Set
  Trichotomous {A} _≈_ _<_ =
    (x y : A) → Tri (x < y) (x ≈ y) (y < x)
```

Working directly with `type:Tri`, rather than several invocations to `Decidable₂
_<_` will dramatically reduce the proof effort necessary to define `def:insert` and
show that it preserves `type:IsBST`.

We are going to require a `type:_<_` relation, and a proof that it forms a trichotomy
with `type:_≡_` in order to work through the implementation details here. Rather than
pollute all of our type signatures with the necessary plumbing, we can instead
define an anonymous module and add the common parameters to that instead, as in:

```agda
  -- TODO(sandy): this requires strict <, unlike the previous
  -- section; clean up previous
  module _
    {_<_ : A → A → Set}
    (<-cmp : Trichotomous _≡_ _<_) where
```

Anything defined in this module will now automatically inherit `{_<_ : A → A →
Set}` and `Trichotomous _≡_ _<_` arguments, which saves us some effort in
getting all the necessary arguments from one place to another.

Defining `def:insert` follows exactly the same template as our in-writing algorithm
above:

```agda
    insert
        : A
        → BinTree A
        → BinTree A
    insert a empty = leaf a
    insert a (branch l x r) with <-cmp a x
    ... | tri< _ _ _ = branch (insert a l) x r
    ... | tri≈ _ _ _ = branch l x r
    ... | tri> _ _ _ = branch l x (insert a r)
```

We would now like to show that `def:insert` preserves the `type:IsBST` invariant. That
is, we'd like to define the following function:

```agda
    bst-insert⅋
        : (a : A)
        → {t : BinTree A}
        → IsBST _<_ t
        → IsBST _<_ (insert a t)
    bst-insert⅋ = ?
```

Before diving into this proper, we will do a little thinking ahead and realize
that showing `type:IsBST` for a `ctor:branch` constructor requires showing that all
elements in either subtree are properly bounded by the root. Therefore, before
we show that `def:insert` preserves `type:IsBST`, we must first prove that `def:insert`
preserves `type:All`! The type we need to show is that if `P a` and `All P t` hold
(for any `P`), then so too must `All P (insert a t)`:

```agda
    all-insert⅋₀
        : {P : A → Set} → (a : A) → P a → {t : BinTree A}  -- ! 1
        → All P t → All P (insert a t)
    all-insert⅋₀ = ?
```

In this type, we have carefully chosen to position the implicit parameter `t` at
[1](Ann). In placing it directly before the `All P t` parameter, we can
simultaneously pattern match on both, which gives us easy bindings for the tree
being manipulated, as you can see here. After binding our variables:

```agda
    all-insert⅋₁
        : {P : A → Set} → (a : A) → P a → {t : BinTree A}
        → All P t → All P (insert a t)
    all-insert⅋₁ a pa {t} all-pt = {! !}
```

we can now ask for a [MakeCase:all-pt](AgdaCmd):

```agda
    all-insert⅋₂
        : {P : A → Set} → (a : A) → P a → {t : BinTree A}
        → All P t → All P (insert a t)
    all-insert⅋₂ a pa {.empty} empty = {! !}
    all-insert⅋₂ a pa {.(branch _ _ _)} (branch l<x px x<r) = {! !}
```

Notice that when we pattern matched on `all-pt`, Agda realized that this fully
determines the results of `t` as well, and it happily expanded them out into
these funny `ctor:.empty` and `ctor:.(branch...)` patterns. These are called *dot
patterns,* and they correspond to patterns whose form has been fully determined
by pattern matching on something else. However, whenever there's a dot pattern
we're allowed to replace it with a regular pattern match, as in:

```agda
    all-insert⅋₃
        : {P : A → Set} → (a : A) → P a → {t : BinTree A}
        → All P t → All P (insert a t)
    all-insert⅋₃ a pa {empty} empty = {! !}
    all-insert⅋₃ a pa {branch _ _ _} (branch l<x xp x<r) = {! !}
```

The point of this is really to get the pieces of the `t : BinTree` into scope,
so we can replace those underscores with real names, and clean up the
automatically generated other bindings at the same time:

```agda
    all-insert⅋₄
        : {P : A → Set} → (a : A) → P a → {t : BinTree A}
        → All P t → All P (insert a t)
    all-insert⅋₄ a pa {empty} empty = {! !}
    all-insert⅋₄ a pa {branch l x r} (branch l<x px x<r) = {! !}
```

Finally, there is no reason to pattern match on the `ctor:{empty}`, since it doesn't
help us bring any new variables into scope.

```agda
    all-insert⅋₅
        : {P : A → Set} → (a : A) → P a → {t : BinTree A}
        → All P t → All P (insert a t)
    all-insert⅋₅ a pa empty = {! !}
    all-insert⅋₅ a pa {branch l x r} (branch l<x px x<r) = {! !}
```

Filling the first hole is merely showing that we have `type:All` for a singleton,
which is our `ctor:leaf` constructor:

```agda
    all-insert⅋₆
        : {P : A → Set} → (a : A) → P a → {t : BinTree A}
        → All P t → All P (insert a t)
    all-insert⅋₆ a pa empty = leaf pa
    all-insert⅋₆ a pa {branch l x r} (branch l<x px x<r) = {! !}
```

A funny thing happens here. We know this remaining hole must be a `ctor:branch`, but
Agda will refuse to [Refine](AgdaCmd) it. If you ask for the type of the goal,
we see something peculiar:

```info
Goal: All P (insert <-cmp a (branch l x r) | <-cmp a x)
```

The vertical bar is not anything that you're allowed to write for yourself, but
the meaning here is that the result of `def:insert` is stuck until Agda knows the
result of `<-cmp a`. Our only means of unsticking it is to also do a `with`
abstraction over `<-cmp a x` and subsequently pattern match on the result:

```agda
    all-insert⅋₇
        : {P : A → Set} → (a : A) → P a → {t : BinTree A}
        → All P t → All P (insert a t)
    all-insert⅋₇ a pa empty = leaf pa
    all-insert⅋₇ a pa {branch l x r} (branch l<x px x<r)
      with <-cmp a x
    ... | tri< a<x _ _ = {! !}
    ... | tri≈ _ a=x _ = {! !}
    ... | tri> _ _ x<a = {! !}
```

Looking at this new set of goals, we see that they are no longer stuck and have
now computed to things we're capable of implementing. By now you should be able
to complete the function on your own:

```agda
    all-insert
        : {P : A → Set} → (a : A) → P a → {t : BinTree A}
        → All P t → All P (insert a t)
    all-insert a pa empty = leaf pa
    all-insert a pa {branch l x r} (branch l<x px x<r)
      with <-cmp a x
    ... | tri< a<x _ _  = branch (all-insert a pa l<x) px x<r
    ... | tri≈ _ a=x _  = branch l<x px x<r
    ... | tri> _ _ x<a  = branch l<x px (all-insert a pa x<r)
```

Now that we've finished the `def:all-insert` lemma, we're ready to show that
`def:insert` preserves `type:IsBST`. Again, when implementing this you will see that the
type will get stuck on `insert x t | <-cmp a x`, and will require another
pattern match on `<-cmp a x`. This will always be the case, and it is for this
reason that we say the proof has the same shape as the computation. In many ways
it is like poetry: it rhymes.

Implementing `def:bst-insert` isn't much more of a cognitive challenge than
`def:all-insert` was; just pattern match and then build a proof term via induction:

```agda
    bst-insert
        : (a : A)
        → {t : BinTree A}
        → IsBST _<_ t
        → IsBST _<_ (insert a t)
    bst-insert a bst-empty = bst-leaf
    bst-insert a {branch l x r} (bst-branch l<x x<r lbst rbst)
      with <-cmp a x
    ... | tri< a<x _ _ =
            bst-branch
              (all-insert a a<x l<x)
              x<r
              (bst-insert a lbst)
              rbst
    ... | tri≈ _ a=x _ = bst-branch l<x x<r lbst rbst
    ... | tri> _ _ x<a =
            bst-branch
              l<x
              (all-insert a x<a x<r)
              lbst
              (bst-insert a rbst)
```


## Intrinsic vs Extrinsic Proofs

This style of proof we have demonstrated, is called an *extrinsic* proof. The
idea here is that we have defined a type `BinTree A` and an operation `insert :
A → BinTree A → BinTree A` in such a way that they are not guaranteed to be
correct. In order to subsequently prove them correct, we added an additional
layer on top, namely `type:IsBST` and `def:bst-insert` which assert our invariants after
the fact. This is a very natural way of proving things, and is a natural
extension of the way we usually do computer science: do the implementation, and
tack the tests on afterwards.

However, extrinsic proofs are not the only possibility! We can instead make a
`BST A` type which satisfies the binary search tree invariant *by construction.*
By virtue of this being by construction, we are not required to tack on any
additional proof, since the existence of the thing itself is proof enough. We
call this notion of proof *intrisic*, as it is intrinsic to what the object is
in the first place.

Intrinsic proofs are desirable because they only require you to do the work
once. Recall that when defining both `def:bst-insert` and `def:all-insert`, we
essentially had to mirror the definition of `def:insert` modulo a few changes. It
was quite a lot of work, and you can imagine that this effort would multiply
substantially for each additional operations we'd like to define over BSTs.
Extrinsic proofs make you shoulder this burden.

However, intrinsic proofs do come with a downside, namely that every algorithm
you have ever seen is given with an extrinsic proof, if it comes with a proof at
all. Which is to say, not only are we as computer scientists better primed for
thinking about extrinsic proof, but worse: the field itself is riddled with
them. Almost every algorithm you have ever heard of isn't amenable to intrinsic
proof. This is because usually the invariant is a macro-level property, which
isn't preserved *inside* of operations.

For example, consider a heap data structure, which is a particular
implementation of a priority queue---at any time, you can get the
highest-priority thing in the queue. Heaps are binary trees (or sometimes,
clever encodings of binary trees as arrays) with the *heap property:* the root
node is larger than everything else in the tree. The heap property is also
satisfied recursively, so that we have a partial ordering over all elements in
the heap.

Now imagine we'd like to insert something new into the heap. We don't know where
it should go, so we insert it into the first empty leaf we can find, and then
recursively "bubble" it up. That is to say, you put it at a leaf, and then check
to see if it's larger than its parent. If so, you swap the two, and then recurse
upwards. Eventually the newly-insert element is somewhere in the tree such that
the heap invariant is met.

This algorithm works just fine, but it *cannot* be used in an intrinsic heap,
because when we first insert the new element into a bottom-most leaf, the heap
property is immediately broken! It doesn't matter if we eventually fix the
invariant; the intrinsic encoding means it's impossible to insert an element
somewhere it doesn't belong.

-- TODO(sandy): conflating between intrinsic proofs and objects defined
-- intrinsically

It is for reasons like these that intrinsic proofs are really hard for computer
scientists. Fully embracing them requires unlearning a great deal of what our
discipline has taught us, and that is a notoriously hard position to adopt.


## An Intrinsic BST

-- TODO(sandy): cite mcbride here


In order to define an intrinsic binary search tree, we will proceed in two
steps. First, we will define a BST indexed by its upper and lower bounds, which
we can subsequently use to ensure everything is in its right place, without
resorting to extrinsic techniques like `type:All`. We begin with a new module to
sandbox our first step:

```agda
module Intrinsic-BST-Impl {A : Set} (_<_ : A → A → Set) where
```

As before, we make a `type:BST` type, but this time parameterized by a `lo` and `hi`
bound. In the `ctor:empty` constructor we require a proof that `lo < hi`:

```agda
  data BST (lo hi : A) : Set where
    empty : lo < hi → BST lo hi
```

Our other constructor, `ctor:branch`, now restricts the bounds of its left and right
subtrees so their top and bottom bounds are the root, respectively:

```agda
    xbranch  -- ! 2
        : (a : A)  -- ! 1
        → BST lo a
        → BST a hi
        → BST lo hi
```

Notice at [1](Ann) that the root of the tree comes as the first argument! This
is unlike our extrinsic `ctor:branch`, but is necessary here so that `a` is in scope
when we build our subtrees. The discrepancy in argument order is why this
constructor has been named `ctor:xbranch`, as indicated at [2](Ann).

Fortunately, we can use a pattern synonym to shuffle our parameters back into
the correct shape:

```agda
  pattern branch lo a hi = xbranch a lo hi
```

And just as before, we will also add a `ctor:leaf` pattern:

```agda
  pattern leaf lo<a a a<hi = branch (empty lo<a) a (empty a<hi)
```

Returning to the issue of `def:insert`, we notice one big problem with putting the
bounds in the type index: it means that `def:insert` could *change the type* of the
`type:BST` if it is outside the original bounds! This is a bad state of affairs, and
will dramatically harm our desired ergonomics. For the time being, we will
sidestep the issue and merely require proofs that `a` is already in bounds.


The implementation of `def:insert` is nearly identical to our original,
extrinsically proven version:

```agda
  open BinaryTrees using (Trichotomous; Tri)
  open Tri

  insert
      : {lo hi : A}
      → (<-cmp : Trichotomous _≡_ _<_)
      → (a : A)
      → lo < a
      → a < hi
      → BST lo hi
      → BST lo hi
  insert <-cmp a lo<a a<hi (empty _) = leaf lo<a a a<hi
  insert <-cmp a lo<a a<hi (branch l x r)
    with <-cmp a x
  ... | tri< a<x _ _ = branch (insert <-cmp a lo<a a<x l) x r
  ... | tri≈ _ a=x _ = branch l x r
  ... | tri> _ _ x<a = branch l x (insert <-cmp a x<a a<hi r)
```

This concludes our first step of the problem. We now have an
intrinsically-proven BST---all that remains is to deal with the type-changing
problem, and put an ergonomic facade in front.

A cheeky solution to the problem of `def:insert` possibly changing the type is to
bound all BSTs by the equivalent of negative and positive infinity. This is, in
essence, throwing away the bounds---at least at the top level. If we can hide
those details, we will simultaneously have solved the problem of changing types
and the ergonomics of needing to juggle the bounds.

The first step is to define a type which *extends* `A` with the notions of
positive and negative infinity:

```agda
open BinaryTrees using (Trichotomous)

module Intrinsic-BST
          {A : Set}
          {_<_ : A → A → Set}
          (<-cmp : Trichotomous _≡_ _<_) where

  data ∞ : Set where
    -∞ +∞  : ∞
    [_]    : A → ∞
```

The `ctor:[_]` constructor lifts an `A` into `type:∞`, and it is through this mechanism by
which we are justified in saying that `type:∞` extends `A`. From here, it's not too
hard to define a `type:_<_` relationship over `type:∞`:

```agda
  data _<∞_ : ∞ → ∞ → Set where
    -∞<[] : {x    : A}          → -∞     <∞ [ x ]
    []<[] : {x y  : A} → x < y  → [ x ]  <∞ [ y ]
    []<+∞ : {x    : A}          → [ x ]  <∞ +∞
    -∞<+∞ : -∞ <∞ +∞
```

This has all the properties you'd expect, that `ctor:-∞` is less than everything
else, `ctor:+∞` is more than everything else, and that we can lift `type:_<_` over `A`.
The trick should be clear: we are not going to instantiate the
`module:Intrinsic-BST-Impl` module at type `A`, but rather at `type:∞`!

Before we can do that, however, we must show that our new `type:_<∞_` is
trichotomous. This is quite a lot of work, but the details are uninteresting to
us by now, and indeed Agda can do the first several cases for us automatically:

```agda
  open BinaryTrees using (Tri)
  open Tri

  <∞-cmp : Trichotomous _≡_ _<∞_
  <∞-cmp  -∞     -∞     = tri≈ (λ ())  refl    (λ ())
  <∞-cmp  -∞     +∞     = tri< -∞<+∞   (λ ())  (λ ())
  <∞-cmp  -∞     [ _ ]  = tri< -∞<[]   (λ ())  (λ ())
  <∞-cmp  +∞     -∞     = tri> (λ ())  (λ ())  -∞<+∞
  <∞-cmp  +∞     +∞     = tri≈ (λ ())  refl    (λ ())
  <∞-cmp  +∞     [ _ ]  = tri> (λ ())  (λ ())  []<+∞
  <∞-cmp  [ _ ]  -∞     = tri> (λ ())  (λ ())  -∞<[]
  <∞-cmp  [ _ ]  +∞     = tri< []<+∞   (λ ())  (λ ())
```

All that's left is lifting `<-cmp`, which we must do by hand:

```agda
  <∞-cmp [ x ] [ y ]
    with <-cmp x y
  ... | tri< x<y ¬x=y ¬y<x =
          tri<
            ([]<[] x<y)
            (λ { refl → ¬x=y refl })
            (λ { ([]<[] y<x) → ¬y<x y<x })
  ... | tri≈ ¬x<x refl _ =
          tri≈
            (λ { ([]<[] x<x) → ¬x<x x<x })
            refl
            (λ { ([]<[] x<x) → ¬x<x x<x })
  ... | tri> ¬x<y ¬x=y y<x =
          tri>
            (λ { ([]<[] x<y) → ¬x<y x<y })
            (λ { refl → ¬x=y refl })
            ([]<[] y<x)
```

The end is nigh! We can now define a `type:BST` as one bounded by `ctor:-∞` and `ctor:+∞`:

```agda
  open module Impl = Intrinsic-BST-Impl _<∞_
    hiding (BST; insert)

  BST : Set
  BST = Impl.BST -∞ +∞
```

and finally, define insertion by merely plugging in some trivial proofs:

```agda
  insert : (a : A) → BST → BST
  insert a t = Impl.insert <∞-cmp [ a ] -∞<[] []<+∞ t
```


```agda
module Exports where
  open import Relation.Binary
    using (Reflexive; Transitive; DecidableEquality; Trichotomous; Tri)
    public
  open Tri public

  open import Data.Empty
    using (⊥)
    public

  open import Relation.Nullary
    using (Dec; yes; no; ¬_)
    public

  open import Relation.Binary.PropositionalEquality
    using (_≢_; ≢-sym)
    public
```

