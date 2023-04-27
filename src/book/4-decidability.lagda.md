# Decidability

Hidden

:   ```agda
{-# OPTIONS --allow-unsolved-metas #-}
    ```

```agda
module 4-decidability where
```

In the last chapter, we thoroughly investigated the notion of doing proof in
Agda.  We defined what it means for two things to be propositionally equal,
derived relevant properties of equality, built a domain-specific language for
doing equational reasoning, and proved many facts about the natural numbers.

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
equal, via the `_≡_` type, proven via `refl`. We'd now like to determine a means
of discussing *inequality!*

Perhaps you might think we can make a slight tweak to the `_≡_` construction.
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
open import Data.Nat
  using (ℕ; zero; suc)
```

We will also need to import propositional equality, which we can also get from
the standard library. This too has an identical interface, so we're safe to do
so:

```agda
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; module ≡-Reasoning)
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

You'll notice at [1](Ann) that the type of `False` is `Set → Set₁`, which is a
feature of Agda's type system we haven't yet covered, but will later this
chapter. For the time being, pretend this says `Set → Set`. We can now try to
find a proof that 2 is not equal to three, as per:

```agda
  2≠3⅋₀ : False (2 ≡ 3)
  2≠3⅋₀ = ?
```

Since `False` expands to a function type, we can (rather unintuitively) do a
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
`⊥` and input as [`bot`](AgdaMode). It's definition is short and sweet:

```agda
data ⊥ : Set where
```

That's it. There are no constructors for `⊥`. Besides a slightly different type
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

We still need to show that an element of `⊥` leads to the principle of
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
input type considered as a proposition. Hence, we can define `¬_` (\neg), which
states that a given proposition is false:

```agda
open import Level
  using (Level)

¬_ : {ℓ : Level} → Set ℓ → Set ℓ
¬ P = P → ⊥
infix 3 ¬_
```

Again, ignore this `Level` stuff for the time being (although you can input `ℓ`
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
trying to encode here. Interestingly, however, we can prove that `_≢_` isn't
reflexive, but showing that if there were such a `refl : x ≢ x` construction, it
would lead to contradiction.

Let's show this in a few steps. First, we will define a type `Reflexive` which
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
`Reflexive`, which could in principle infer it from the type of `_≡_`, but Agda
has no way of knowing if you'd like to talk about `_≡_` in its fully-general
polymorphic type, or about `_≡_` when specialized to something about the natural
numbers. The distinction isn't extremely poignant in this example, but there do
exist monomorphic relations which we might still want to say are reflexive.
Nevertheless, we have shown that `_≡_` is reflexive by giving a proof that
`refl` exists.

Contrasting against this is the proof that `_≢_` is *not* reflexive. The type of
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
`≢-refl` *for that specific type.* In [1](Ann) however, we are required to show
that there does not exist a `≢-refl` that works for *every* type `A`. End users
of `¬≢-refl` don't care one way or another, but the difference here is
absolutely crucial for actually *proving* the notion. Let's look at this more
closely.

At a high level, the proof here is "`≢-refl` must be false because it's the
negation of `≡-refl`, which is easily shown to be true." While the type of the
argument to `¬≢-refl` is `Reflexive _≢_`, we can use
[TypeContext/Normalise](AgdaCmd) to ask Agda to expand out this definition,
resulting in `x ≡ x → ⊥`. Under the lens of this expanded type, it seems
reasonable to call the argument `¬≡-refl`, as in the following:

```agda
¬≢-refl⅋₁ : ¬ ({A : Set} → Reflexive {A} _≢_)
¬≢-refl⅋₁ ¬≡-refl = {! !}
```

Of course, we do in fact have a proof of `x ≡ x`, namely `refl`, so we can try
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
some holes to fill. The first hole has type `Set`, while the second has type
`?0`, meaning its type depends on the answer to our first hole. We're free to
choose any type we'd like for this first hole, so let's try `ℕ`:

```agda
¬≢-refl⅋₄ : ¬ ({A : Set} → Reflexive {A} _≢_)
¬≢-refl⅋₄ ¬≡-refl = ¬≡-refl {ℕ} {?} refl
```

and now all we need is to pick an arbitrary value of type `ℕ`:

```agda
¬≢-refl : ¬ ({A : Set} → Reflexive {A} _≢_)
¬≢-refl ≢-refl = ≢-refl {ℕ} {0} refl
```

What was to be demonstrated has thus been proved. But let's see what goes wrong
if we try the same approach on `¬≢-refl-bad`. Since `A` is now a top-level
parameter, we can bind it in the function body, meaning we have one fewer
implicit to fill in:

```agda
¬≢-refl-bad : {A : Set} → ¬ Reflexive {A} _≢_
¬≢-refl-bad {A} ¬≡-refl = ¬≡-refl {?} refl
```

This hole unfortunately has type `A`, *for some unknown type `A`!* We can't
possibly fill this in, because we don't know what type `A` is. In fact, `A`
could be `⊥`, in which case there aren't any values we could put here even in
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
normalizing (expanding out) the types of both `¬≢-refl` and `¬≢-refl-bad`, we
are left with this:

```type
¬≢-refl     : ({A : Set} → {x : A} → x ≡ x → ⊥) → ⊥
¬≢-refl-bad : {A : Set} → ({x : A} → x ≡ x → ⊥) → ⊥
```

These types have much more going on, but the important thing to notice is that
they both take functions as arguments. Whenever you see a function as an
argument, you should immediately think "callback." Viewed as a callback, the
question becomes *who is responsible for providing the parameters?* In the first
case, it is `¬≢-refl` which gets to pick `A`, while in the second, it
is the *caller* of `¬≢-refl-bad` who gets to pick `A`. And true to the name,
this caller might pick an antagonistic `A` in an attempt to thwart us!


## Intransitivity of Inequality

In the same vein as `¬≢-refl`, we can also show that `_≢_` doesn't satisfy
transitivity. The pen and paper proof is straightforward, since if inequality
were transitive we could show:

$$
\begin{align}
2 &\neq 3 \\
&\neq 2
\end{align}
$$

This is known in the business as a "whoopsie daisy." Such a counterexample shows
inequality cannot be transitive, and we can prove it more formally in Agda by
giving a definition for transitivity:

```agda
Transitive : {A : Set} → (A → A → Set) → Set
Transitive {A} _≈_ = {x y z : A} → x ≈ y → y ≈ z → x ≈ z
```

Giving the counterexample is easy, since we already have a proof `2≠3`. Given a
hypothetical `≢-trans`, we could combine this with `sym 3≠2`, to get a proof
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

  open import Data.Maybe
    using (Maybe; just; nothing)

  n=5? : (n : ℕ) → Maybe (n ≡ 5)
  n=5? 5 = just refl
  n=5? _ = nothing
```

Given `n=5?`, we can call this function and branch on its result. If the result
is a `just`, we now have a proof that the argument was indeed 5, and can use it
as we'd please.

Of course, if the argument wasn't five, this definition doesn't allow us to
learn anything at all. When instead, it would be much more useful to learn that
`¬ (n ≡ 5)`, in case we'd like to do something with that information! From this,
we conclude that returning `Maybe` isn't quite the right choice. Instead, we'd
like a slightly-more structured type corresponding to *decisions*:

```agda
data Dec (P : Set) : Set where
  yes : P  → Dec P
  no : ¬ P → Dec P
```

`Dec` is a type which states if we know for sure that either `P` holds, or that
`P` *doesn't* hold. Of course, only one of these can ever be true at once, and
thus `Dec P` corresponds to an answer that we can definitively compute. For
example, given two numbers, it's not too hard to determine if the two are equal.

```agda
module Nat-Properties where
  open import Data.Nat
    using (ℕ; zero; suc)

  open import Data.Bool
    using (Bool; true; false)

  _==_ : ℕ → ℕ → Bool
  zero  == zero  = true
  zero  == suc y = false
  suc x == zero  = false
  suc x == suc y = x == y
```

While `_==_` *is* a decision procedure, it doesn't give us back any
proof-relevant term. The goal is slightly modify this definition such that
whenever it returns `true` we instead give back a `yes`, and likewise replace
`false` with `no`. Giving back the `yes`es is easy enough, but the `no`s take a
little more thought:

```agda
  open import Relation.Binary.PropositionalEquality

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
`zero` and `suc` are different constructors. Therefore, we can solve this (and
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

Take a moment to reflect on this. Where before `_==_` simply returned `false`,
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
module Trees where
  data BinTree (A : Set) : Set where
    empty : BinTree A
    branch : BinTree A → A → BinTree A → BinTree A
```

For convenience, it's often helpful to be able to talk about a single-element
tree, which we can encode as a `branch` with two `empty` children. Agda lets us
define pseudo-constructors called *patterns* for cases like these. The following
defines a new pattern called `leaf : A → BinTree A`:

```agda
  pattern leaf a = branch empty a empty
```

You might wonder why we use a `pattern` here rather than just a regular old
function:

```agda
  leaf⅋ : {A : Set} → A → BinTree A
  leaf⅋ a = branch empty a empty
```

The difference is all in the colors. Literally. The reason is that, as the name
implies, we can *pattern match* when `leaf` is defined as pattern:

```agda
  open import Data.Bool
    using (Bool; true; false)

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
use-case for Agda's `variable` block, which allows us to define implicit
bindings that should exist for the remainder of the scope.

Variable blocks are started with the keywords `private variable`, and then begin
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
argument. With this feature, we can rewrite `_∈_` in a much terser, but
*completely-equivalent* way:

```agda
  data _∈_ : A → BinTree A → Set where
    here  :         a ∈ branch l a r
    left  : a ∈ l → a ∈ branch l b r
    right : a ∈ r → a ∈ branch l b r
```

Just to demonstrate that everything works, we can make a little tree:

```agda
  tree : BinTree ℕ
  tree = branch (branch (leaf 0) 0 (leaf 2)) 4 (leaf 6)
```

and then show that six is somewhere in this `tree`, as per the very assertive
definition:

```agda
  6∈tree : 6 ∈ tree
  6∈tree = right here
```

It might also be desirable to show that every element in the tree satisfies some
property. Perhaps we'd like to build a binary tree consisting only of odd
numbers, for example. It's unclear why, but nevertheless it's something we
*might* want to do. There is no finger pointing here!

Building `All` is easy. We can replace every instance of `A` with `P A`, and
every instance of `BinTree` with `All`. Modulo a few indices at the end, we're
left with a reminiscent definition:

```agda
  data All (P : A → Set) : BinTree A → Set where
    empty : All P empty
    branch : All P l → P a → All P r → All P (branch l a r)
```

A pattern definition doesn't come with a type signature, and thus it only works
with whatever constructors existed when it was defined. Since in `All` we have
reused the constructor names `empty` and `branch`, we can redefine `leaf` again
so that it also works over `All`:

-- TODO(sandy): fact check


```agda
  pattern leaf a = branch empty a empty
```

In the `branch` case, we must show that everything holds in both subtrees, as
well as that the property holds for the value at the root. By induction, we have
now covered every element in the tree. We can show it works by coming up with a
quick predicate, maybe the evenness of a number. We defined a similar thing back
in @sec:even, however we cannot reuse it here, as it was defined over our custom
natural numbers, and does not exist in the standard library.

```agda
  open Data.Nat
    using (_+_)

  data IsEven : ℕ → Set where
    z-even : IsEven 0
    ss-even : {n : ℕ} → IsEven n → IsEven (2 + n)
```

It's now possible to show every element in `tree` is even. In fact, Agda can
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

we can again ask Agda for a proof that `tree` is a BST:

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

You'll notice several subexpressions of the form `bst-branch empty empty
bst-empty bst-empty`, which is the proof that a `leaf` is a BST. This is a good
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

```agda
module Lists where
  data List (A : Set) : Set where
    [] : List A
    _∷_ : A → List A → List A
  infixr 5 _∷_

  module Deque where
    data Deque (A : Set) : Set where
      empty : Deque A
      [_] : A → Deque A
      _◁_▷_ : A → Deque A → A → Deque A

    push-front : {A : Set} → A → Deque A → Deque A
    push-front x empty       = [ x ]
    push-front x [ y ]     = x ◁ empty ▷ y
    push-front x (l ◁ q ▷ r) = x ◁ push-front l q ▷ r

    push-back : {A : Set} → A → Deque A → Deque A
    push-back x empty       = [ x ]
    push-back x [ y ]     = y ◁ empty ▷ x
    push-back x (l ◁ q ▷ r) = l ◁ push-front r q ▷ x

    open import Data.Maybe
      using (Maybe; nothing; just)

    open import Data.Product
      using (_×_; _,_)

    pop-front : {A : Set} → Deque A → Maybe (A × Deque A)
    pop-front empty = nothing
    pop-front [ x ] = just (x , empty)
    pop-front (l ◁ q ▷ r) = just (l , push-back r q)

    test : Deque ℕ
    test = 0 ◁ 1 ◁ [ 2 ] ▷ 3 ▷ 4


  module List-Properties {A : Set} (_≟A_ : DecidableEquality A) where
    _≟_ : DecidableEquality (List A)
    [] ≟ [] = yes refl
    [] ≟ (y ∷ ys) = no λ ()
    (x ∷ xs) ≟ [] = no λ ()
    (x ∷ xs) ≟ (y ∷ ys) with x ≟A y
    ... | no x≠y = no λ { refl → x≠y refl }
    ... | yes refl with xs ≟ ys
    ... | no xs≠ys = no λ { refl → xs≠ys refl }
    ... | yes refl = yes refl



  data _∈_ {A : Set} (a : A) : List A → Set where
    here : {xs : List A} → a ∈ (a ∷ xs)
    there : {x : A} → {xs : List A} → a ∈ xs → a ∈ (x ∷ xs)

  decide-membership
      : {A : Set}
      → DecidableEquality A
      → (a : A)
      → (xs : List A)
      → Dec (a ∈ xs)
  decide-membership _≟_ a [] = no λ ()
  decide-membership _≟_ a (x ∷ xs)
    with a ≟ x
  ... | yes refl = yes here
  ... | no a≠x
    with decide-membership _≟_ a xs
  ... | yes a∈xs = yes (there a∈xs)
  ... | no ¬a∈xs = no λ { here → a≠x refl
                        ; (there a∈xs) → ¬a∈xs a∈xs
                        }


  data All {A : Set} (P : A → Set) : List A → Set where
    [] : All P []
    _∷_ : {x : A} {xs : List A} → P x → All P xs → All P (x ∷ xs)

  decide-all
      : {A : Set} {P : A → Set}
      → (p? : (a : A) → Dec (P a))
      → (xs : List A)
      → Dec (All P xs)
  decide-all p? [] = yes []
  decide-all p? (x ∷ xs)
    with p? x
  ... | no ¬px = no λ { (px ∷ _) → ¬px px }
  ... | yes px
    with decide-all p? xs
  ... | yes all = yes (px ∷ all)
  ... | no ¬all = no λ { (_ ∷ all) → ¬all all }


  record Σ (A : Set) (B : A → Set) : Set where
    constructor _,_
    field
      proj₁ : A
      proj₂ : B proj₁

  infixr 4 _,_

  _×_ : Set → Set → Set
  A × B = Σ A (λ _ → B)


  filter
      : {A : Set} {P : A → Set}
      → ((x : A) → Dec (P x))
      → (xs : List A)
      → Σ (List A) (All P)
  filter p? [] = [] , []
  filter p? (x ∷ xs)
    with p? x  | filter p? xs
  ...  | yes p | ls , all = (x ∷ ls) , (p ∷ all)
  ...  | no ¬p | ls , all = ls , all



  weaken
      : {A : Set} {P : A → Set} {Q : A → Set} {ls : List A}
      → (P→Q : {a : A} → P a → Q a)
      → All P ls
      → All Q ls
  weaken Q→P [] = []
  weaken Q→P (x ∷ xs) = Q→P x ∷ weaken Q→P xs


  filter′
      : {A : Set} {P : A → Set}
      → ((x : A) → Dec (P x))
      → (xs : List A)
      → Σ (List A) λ l → All P l × All (_∈ xs) l
  filter′ p? [] = [] , [] , []
  filter′ p? (x ∷ xs)
    with p? x | filter′ p? xs
  ... | yes p | ls , all-P , all-in
      = (x ∷ ls) , p ∷ all-P , here ∷ weaken there all-in
  ... | no ¬p | ls , all-P , all-in
      = ls , all-P , weaken there all-in
```
