---
suppress-bibliography: true
...

# Relations {#sec:relations}

Hidden

:   ```agda
{-# OPTIONS --allow-unsolved-metas --large-indices #-}
open import Data.Integer using (ℤ)
open import Chapter1-Agda using () renaming (_,_ to _,⅋_; _×_ to _×⅋_)
    ```

```agda
module Chapter4-Relations where
```

In the last chapter we explored what equality *is*, and what sorts of things we
could prove with it. We turn our discussion now to *relations* more generally,
of which equality is only one example. In the process, we will learn about
universe polymorphism, pre-orders, partially ordered sets, and touch briefly on
graphs---all while learning much more about working with Agda interactively.


Prerequisites

:   ```agda
open import Chapter1-Agda
  using (Bool; false; true; not; _×_)
    ```

:   ```agda
open import Chapter2-Numbers
  using (ℕ; zero; suc; _+_)
    ```

:   ```agda
open import Chapter3-Proofs
    ```


## Universe Levels {#sec:levels}

Perhaps you have heard of Bertrand Russell's "barber paradox"---if there is a
barber who shaves only barbers who do not shave themselves, does he shave
himself? The paradox is that the barber does shave himself if he doesn't, and
doesn't if he does. The truth value of this proposition seems to flip-flop back
and forth, from yes to no and back to yes again, forever, never settling down,
never converging on an answer.

Of course, Russell wasn't actually wondering about barbers; the question was
posed to underline a problem with the now-called "naive set theory" that was in
vogue at the time. We call it naive set theory these days because it allowed for
paradoxes like the one above, and paradoxes are anathema to mathematics. Once
you have a contradiction, the entire mathematical system falls apart and it's
possible to prove anything whatsoever. We will look at how to correct this in
@sec:negation.

Modern mathematics' solution to the barber paradox is the realization that not
all collections are sets---some are simply "too big" to be sets. There is no
"set of all sets" because such a thing is too big. Therefore, the question of
the barber who doesn't cut his own hair is swept under the rug, much like the
hair at actual barbershops.

But this only punts on the problem. What is the corresponding mathematical
object here? If the set of all sets is not a set, then, what exactly is it? The
trick is to build a hierarchy of set-like things, no one of which contains
itself, but each subsequent object contains the previous one.

The usual, everyday sets and types that exist in other programming languages are
`type:Set₀`. `type:Set₀` can be written in Agda as `type:Set` like we have been
doing so far. But, what is the type of `type:Set` itself? Why, it's `type:Set₁`!

```agda
_ : Set₁
_ = Set
```

We can play the same game, asking what's the type of `type:Set₁`.
Unsurprisingly, it's `type:Set₂`:

```agda
_ : Set₂
_ = Set₁
```

This collection of sets is an infinite hierarchy, and we refer to each as a
*sort* or a *universe.* You're welcome to use an arbitrarily large universe if
you'd like:

```agda
_ = Set₉₈₆₀₂₅₀
```

Why do these universes matter? As we have seen, Agda makes no distinction
between values and types. So far, we've used this functionality primarily when
working on indexed types, where we've seen values used as indices on types. But
as we become more sophisticated Agda programmers (*e.g.* later in this chapter,)
we will start going the other direction: using types as values.

When we write a proof about values, such a thing lives in `type:Set`. But proofs
about *types* must necessarily exist in a higher universe so as to not taunt the
barber and his dreadful paradox. Of course, proofs about *those* proofs must
again live in a higher universe.

You can imagine we might want to duplicate some proofs in different universes.
For example, we might want to say the tuple `expr:1 ,⅋ (2 ,⅋ 3)` is "pretty much
the same thing[^same-thing]" as `expr:(1 ,⅋ 2) ,⅋ 3`. But then we might want to
say that a type-level tuple of `expr:ℕ ,⅋ (Bool ,⅋ ℤ)`---*not* `expr:ℕ ×⅋ (Bool
×⅋ ℤ)`, mind you--- is *also* "pretty much the same thing" as `expr:(ℕ ,⅋ Bool)
,⅋ ℤ`.

[^same-thing]: For some definition of "pretty much the same thing" that we will
  make precise in @sec:setoids.

Thankfully, Agda allows us to write this sort of proof once and for all, by
abstracting over universe levels in the form of *universe polymorphism.* The
necessary type is `type:Level` from `module:Agda.Primitive`:

```agda
open import Agda.Primitive
  using (Level; _⊔_; lzero; lsuc)
```

Before we play with our new `type:Level`s, let's force Agda to give us an error.
Recall our old definition of `type:Maybe` from @sec:maybe:

```agda
module Playground-Level where
  data Maybe₀ (A : Set) : Set where
    just₀     : A → Maybe₀ A
    nothing₀  : Maybe₀ A
```

We might try to generate a term of type `type:Maybe Set`, as in:

```illegal
  _ = just₀ ℕ
```

which Agda doesn't like, and isn't shy about telling us:

```info
Set₁ != Set
when checking that the solution Set of metavariable _A_8 has the
expected type Set
```

The problem, of course, is that we said `A` was of type `type:Set`, but then
tried to instantiate this with `A =` `type:Set`. But since `type:Set` `:`
`type:Set₁`, this is a universe error, and the thing fails to typecheck.

Instead, we can use universe polymorphism in the definition of `type:Maybe`, by
binding a `type:Level` named `ℓ` ([ell](AgdaMode)), and parameterizing both the
set `A` and `type:Maybe` by this `type:Level`:

```agda
  data Maybe₁ {ℓ : Level} (A : Set ℓ) : Set ℓ where
    just₁     : A → Maybe₁ A
    nothing₁  : Maybe₁ A
```

Agda is now happy to accept our previous definition:

```agda
  _ = just₁ ℕ
```

In the real world, it happens to be quite a lot of work to bind every level
every time, so we often use a `keyword:variable` block to define levels:

```agda
  private variable
    ℓ : Level

  data Maybe₂ (A : Set ℓ) : Set ℓ where
    just₂     : A → Maybe₂ A
    nothing₂  : Maybe₂ A
```

Variable blocks are a lovely feature in Agda; whenever you reference a binding
defined in a `keyword:variable`, Agda will automatically insert an implicit
variable for you. Thus, behind the scenes, Agda is just turning our definition
for `type:Maybe₂` into exactly the same thing as we wrote by hand for
`type:Maybe₁`.

Although we didn't define `type:Maybe` this way when we built it in @sec:maybe,
we don't need to make any changes. This is because
`module:Chapter2-Numbers` *re-exports* `type:Maybe` from the standard
library, which as a principle is always as universe-polymorphic as possible.

These `keyword:variable` bindings are life-saving when working with highly
polymorphic structures, and so let's pop the module stack and introduce a few in
the top level for our future definitions:

```agda
private variable
  ℓ ℓ₁ ℓ₂ a b c : Level
  A : Set a
  B : Set b
  C : Set c
```

There's quite a preponderance of levels we've defined here! As you can see,
variables can depend on one another; using one in a definition will
automatically pull it and any variables it depends on into scope. Therefore,
don't be surprised throughout the rest of this chapter if you see variables that
don't seem to be bound anywhere---this is where they come from!


Hidden

:   ```agda
-- fix bind
    ```


There are three other introduction forms for `type:Level` that bear discussion.
The first is `def:lzero`, which is the universe level of `type:Set₀`. In other
words, `type:Set₀` is an alias for `expr:Set lzero`. This brings us to our
second introduction form, `def:lsuc`, which acts exactly as `ctor:suc` does, but
over the `type:Level`s. That is, `type:Set₁` is an alias for `expr:Set (lsuc
lzero)`. As you'd expect, we can generate any `type:Level` by subsequent
applications of `def:lsuc` to `def:lzero`.

Our third and final introduction form for `type:Level` is `def:_⊔_` (input via
[lub](AgdaMode)), which takes the maximum of two levels. It's unnecessary to use
`def:_⊔_` when working with concrete levels, but it comes in handy when
you have multiple `def:Level` variables in scope. For example, you might have
two different sets with two different levels, lets say `ℓ₁` and `ℓ₂`. The
appropriate level for such a thing would be either `bind:ℓ₁ ℓ₂:ℓ₁ ⊔ ℓ₂` or
`bind:ℓ₁ ℓ₂:lsuc (ℓ₁ ⊔ ℓ₂)`, depending on the exact circumstances. Don't worry;
it's not as onerous in practice as it might seem.

As a beginner writing Agda, getting all of the universes right can be rather
daunting. I'd recommend you start by putting everything in `type:Set`, and
generalizing from there only when the typechecker insists that your levels are
wrong.

When that happens, simply introduce a new implicit `type:Level` for each
`type:Set` you're binding, and then follow the type errors until everything
compiles again. Sometimes the errors might be incomplete, complaining that the
level you gave it is not the level it should be. Just make the change and try
again; sometimes Agda will further complain, giving you an even higher bound
that you must respect in your level algebra. It can be frustrating, but keep
playing along, and Agda will eventually stop complaining.

As you gain more proficiency in Agda, you'll often find yourself trying to do
interesting things with `type:Set`s, like putting them inside of data
structures. If you wrote the data structures naively over `type:Set`, this will
invoke the ire of the universe checker, and Agda will refuse your program. After
running into this problem a few times, you will begin making all of your
programs universe-polymorphic. The result is being able to reuse code you wrote
to operate over values when you later decide you also need to be able to operate
over types. A little discipline in advance goes a long way.


## Dependent Pairs {#sec:sigma}

As we have seen, function arguments act as the *for-all* quantifier when
encoding mathematical statements as types. For example, we can read the
definition for `type:Transitive` above as "for all `x y z : A`, and for all
proofs `x ≈ y` and `y ≈ z`, it is the case that `x ≈ z`." The for-all quantifier
states that something holds true, regardless of the specific details.

Closely related to this is the *there-exists* quantifier, aptly stating that
there is at least one object which satisfies a given property. As an
illustration, there exists a number `n :` `type:ℕ` such that $n + 1 = 5$ ,
namely $n = 4$. But it is certainly not the case *for all* `n :` `type:ℕ`
that $n + 1 = 5$ holds!

True existential values like this don't exist in Agda since we are restricted to
a constructive world, in which we must actually build the thing we are claiming
to exist. This sometimes gets in the way of encoding non-constructive
mathematics, but it's not usually a problem.

How do we actually build such a there-exists type in Agda? The construction is
usually known as a *sigma* type, written `type:Σ` and input as [GS](AgdaMode).
Its definition is given by:

```agda
module Definition-DependentPair where
  open Chapter3-Proofs

  record Σ (A : Set ℓ₁) (B : A → Set ℓ₂)
      : Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
    constructor _,_
    field
      proj₁ : A
      proj₂ : B proj₁  -- ! 1
```

This definition should feel reminiscent of the tuple type we built in
@sec:tuples. Despite the gnarly universe polymorphism---which the typechecker
can help you write for yourself, even if you don't know what it should be---the
only difference between `type:Σ` and `type:_×_` from earlier is in the second
parameter. To jog your memory, we can redefine tuples here:

```agda
  record _×⅋₀_ (A : Set ℓ₁) (B : Set ℓ₂)
      : Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
    constructor _,_
    field
      proj₁ : A
      proj₂ : B
```

Contrasting the two, we see that in `type:Σ`, the `B` parameter is *indexed* by
`A`, while in `type:_×_`, `B` exists all by itself. This indexing is extremely
useful, as it allows us to encode a property about the `A` inside of `B`. As you
can see at [1](Ann), `field:proj₂` has type `B` `field:proj₁`---in other words,
that the *type* of `field:proj₂` depends on the *value* we put in for
`field:proj₁`!

As an example, we can give our earlier example again---typing `∃` as
[`ex`](AgdaMode):

```agda
  ∃n,n+1≡5 : Σ ℕ (λ n → n + 1 ≡ 5)
  ∃n,n+1≡5 = 4 , PropEq.refl
```

In the type of `def:∃n,n+1≡5`, we give two arguments to `type:Σ`, the first
indicating that there exists a `type:ℕ`, and the second being a function that
describes which property holds for that particular `type:ℕ`. In the value, we
need to give both the *actual* `type:ℕ`, and a proof that the property holds for
it.

The `type:Σ` type is one of the most useful constructions in Agda, and we will
see many examples of it in the upcoming sections. We will import it from the
standard library for the remainder of this module:

```agda
open import Data.Product
  using (Σ; _,_)
```


## Heterogeneous Binary Relations {#sec:hetgen-rels}

One extremely common mathematical construction is the *relation,* which, in the
canon, is used to categorize disparate things like functions, equalities,
orderings, and set membership, to name a few.

Let's begin with the mathematical definition, and decompile it into something
more sensible for our purposes.

> A binary relation `_R_` over sets $X$ and $Y$ is a subset of the Cartesian
> product $X \times Y$.

Hidden

:   ```agda
-- fix bind
    ```

As we saw when in @sec:even when discussing `type:IsEven`, subsets are best
encoded in Agda as functions into `type:Set`. Taken at face value, this would
make a relation have type `expr:{A B : Set} → A × B → Set`.

We can do slightly better however, by recalling the curry/uncurry isomorphism
(@sec:currying) and splitting the explicit Cartesian product into two arguments.
Such a transformation results then in `expr:{A B : Set} → A → B → Set`.

A fully-fledged solution here must be level polymorphic, since many of the
relations we'd like to be able to encode will be over higher-level sets. There
are actually three levels required here, one for `A`, another for `B`, and a
third for the resulting `type:Set`. Thus, we come up with our final definition
as `type:REL`:

```agda
module Sandbox-Relations where
  REL : Set a → Set b → (ℓ : Level)
      → Set (a ⊔ b ⊔ lsuc ℓ)
  REL A B ℓ = A → B → Set ℓ
```

Notice that the `ℓ` parameter is not implicit, as is usually the case with
`type:Level`s. This is because `type:REL` is almost always used as a type, in
which case we still need to give a level for the resulting set. Thankfully, we
can still infer levels `a` and `b` from the `type:Set` parameters to `type:REL`.

This `type:REL` is the type of *heterogeneous* relations, that is, relationships
between two distinct sets. Relations are required to satisfy no laws whatsoever,
meaning anything that can typecheck as a `type:REL` is in fact a relation. In a
very real way, this means that relations are themselves *meaningless* and
completely devoid of any semantics; they exist solely as a method of
organization.

To get a feel for how loosey-goosey relations are, we can define a few for
ourselves. There is the vacuous relation which relates no values:

```agda
  data Unrelated : REL A B lzero where
```

and the trivial relation which relates all values:

```agda
  data Related : REL A B lzero where
    related : {a : A} {b : B} → Related a b
```

While being "boring" relations, at least these two are principled. We can also
define arbitrary relations:

```agda
  data Foo : Set where
    f1 f2 f3 : Foo

  data Bar : Set where
    b1 b2 b3 : Bar

  data FooBar : REL Foo Bar lzero where
    f2-b2   : FooBar f2 b2
    f2-b2′  : FooBar f2 b2
    f2-b    : (b : Bar) → FooBar f2 b
    f3-b2   : FooBar f3 b2
```


Hidden

:   ```agda
  -- fix bind
    ```


Don't try to make sense of `type:FooBar`, I just made something up. This
relation does illustrate, however, that two values can be related in many
different ways. That is, we have *three* different ways of constructing a
`expr:FooBar f2 b2`---via `ctor:f2-b2`, `ctor:f2-b2′`, or `ctor:f2-b b2`. But
there is only one `type:Bar` that `ctor:f3` is related to, and poor `ctor:f1`
has no relations at all!

Our conclusion is that relations are too unconstrained to be interesting. Of
course, there do exist interesting *particular* relations, but as a class of
thing they are "too big." Much like how you can represent any value of any type
as a string if you are willing to suffer hard enough, many things in math can be
considered relations. But it's the constraints that necessarily make things
interesting.


## The Relationship Between Functions and Relations

The most salient heterogeneous relationship is the "function." I've added the
scare quotes here because while classical mathematicians will define a function
in terms of a relation when pressed, this is categorically the wrong way to
think about things. This is in stark contrast to constructivists and computer
scientists, who take the function as a fundamental building block and use *it*
to define relations---insofar as they care about relations at all.

Nevertheless, we will see how to think about functions as relations, and vice
versa. Doing so requires us to think of a function as a relation between the
inputs on one side and the outputs on the other.

We can transform a function `f` into a relation `def:FnToRel` `f` such that `x`
is in relation to `y` only when $f x = y$. The definition is a bit silly, but it
works out nevertheless. To build such a thing, we can use a `keyword:data` type
that maps from `f` into `def:REL` `A` `B` `def:lzero`. If you'll excuse the cute
notation,[^fun-notation] we can call such a thing `def:_maps_↦_` using
[`r-|`](AgdaMode) for the `↦` symbol.

[^fun-notation]: Frankly, half of the fun in writing Agda is coming up with good
  notation like this. I've tried to restrain myself throughout the book, but
  this one was too delightful to ignore.

```agda
  data _maps_↦_ (f : A → B) : REL A B lzero where
     app : {x : A} → f maps x ↦ f x
```

Believe it or not, this is everything we need. We can now show that the
`def:not` function relates `ctor:false` and `ctor:true` in both directions:

```agda
  _ : not maps false ↦ true
  _ = app

  _ : not maps true ↦ false
  _ = app
```

but it doesn't relate `ctor:false` to itself:

```illegal
  _ : not maps false ↦ false
  _ = app
```

Transforming a relation back into a function is harder, as functions have
significantly *more structure* than relations do. In particular, we require two
constraints on any relation we'd like to transform into a function:

1. for every distinct value on the left of the relation, there is exactly one
   value on the right, and
2. every value in the left type is related to something in the right.

These properties are called *functionality* and *totality* respectively. In
order to produce a function out a relation, we must first show the relation has
both properties, and thus it will do for us to define them.

More formally, the functional property states that if $x \mathrel{\sim} y$ and
$x \mathrel{\sim} z$, then it must be the case that $y = z$. We can encode this
in Agda by mapping from `type:REL` into `type:Set`, which you can think of as a
function which takes a relation and produces the necessary constraint it must
satisfy.

```agda
  Functional  : REL A B ℓ → Set _  -- ! 1
  Functional {A = A} {B = B} _~_  -- ! 2
    = {x : A} {y z : B}
    → x ~ y → x ~ z
    → y ≡ z
```


Hidden

:   ```agda
  -- fix bind
    ```


Footgun

:   Notice that in the definition of [1](Ann) we have given the resulting
    `type:Level` as `_`---asking Agda to do the work of inferring it for us. It
    gets correctly inferred as `bind:a b ℓ:a ⊔ b ⊔ ℓ`, but due to a misfeature
    in how Agda handles `keyword:variable`s, we are unable to write this for
    ourselves! In brief, the problem arises because variables get freshly
    instantiated every time they are used, meaning the `a` in the definition of
    `A` is *not* the same as the `a` we'd like to write here. Furthermore, there
    *is no way* to directly get our hands on the proper `a`. It's stupid.

At [2](Ann), pay attention to how we can bind the `A` and `B` variables as if
they were just regular implicit parameters to `type:Functional`. That's because
they *are* just regular implicit parameters---as long as they are mentioned
directly in the type. Modulo the footgun above, usage of `keyword:variable`s can
dramatically improve code's readability.

The total property says that for every $x$, there must exist some $y$ such that
$x \mathrel{\sim} y$. As before in @sec:sigma, we can turn this "there exists"
into a `type:Σ` type:

```agda
  Total  : REL A B ℓ → Set _
  Total {A = A} {B = B} _~_
    = (x : A) → Σ B (λ y → x ~ y)
```

Given `def:Functional` and `def:Total`, we're now ready to turn our relation
back into a function:

```agda
  relToFn : (_~_ : REL A B ℓ)
          → Functional _~_
          → Total _~_
          → A → B
  relToFn _~_ _ total x
    with total x
  ... | y , _ = y
```

As it happens, this implementation doesn't actually use the
`bind:_~_:Functional _~_` argument, but its existence in the type is necessary
to ensure we didn't just pick an *arbitrary* output from the `type:Total`
property.

Notice how cool it is that we can define `def:relToFn` without ever giving any
*actual implementations* of `type:Functional` or `type:Total`. As we get deeper
into doing math in Agda, most of the work we do will be of this form: put
together some definitions, and assume we have something that satisfies the
definition, and use that to show what we intend to. Very rarely do we actually
need to get our hands dirty and give any implementations.


## Homogeneous Relations {#sec:homgen-rels}

The relations we're much more familiar with are *homogeneous*---those which
relate two elements of the same type. It is under this category that things like
equality and orderings fall. You will not be surprised to learn that homogeneous
relations are a special case of heterogeneous ones. We will name such a thing
`type:Rel`, which comes with one fewer parameter:

```agda
  Rel : Set a → (ℓ : Level) → Set (a ⊔ lsuc ℓ)
  Rel A ℓ = REL A A ℓ
```

As an illustration of `type:Rel`, we previously defined propositional
equality in this way:

```agda
  module Example₂ where
    data _≡⅋₀_ {A : Set a} : A → A → Set a where
      refl : {x : A} → x ≡⅋₀ x
```

but we could have instead given it this type---stressing the fact that it is a
homogeneous relation:

```agda
    data _≡⅋_ {A : Set a} : Rel A a where
      refl⅋ : {x : A} → x ≡⅋ x
```

We will study more constrained (read: interesting) examples of homogeneous
relations in the remainder of this chapter, alongside their useful applications
of, and constructions over.


## Standard Properties of Relations {#sec:rel-props}

It's a good habit to look for what generalizes whenever you notice a connection
to something you already understand. In this case, how much of our understanding
of propositional equality lifts to relations in general?

Recall the three properties we showed about propositional equality: reflexivity,
symmetry, and transitivity. Reflexivity is the notion that every element is
equal to itself. Symmetry states that the left and right sides of equality are
equivalent, and therefore that we can swap between them at will. Transitivity
gives us a notion of composition on equality, saying that we can combine two
proofs of equality into one, if they share an identical member between them.

In order to generalize these properties, we need only replace the phrase "is
equal to" with "is in relation with." Not every relation satisfies each of these
properties of course, but having some shared vocabulary gives us things to look
out for when designing our own relations.

The first step is to formalize each of these notions in the flavor of
`type:Functional` and `type:Total` above. We can encode reflexivity as a
proposition stating that all elements are related to themselves:

```agda
  Reflexive : Rel A ℓ → Set _
  Reflexive {A = A} _~_
    = {x : A} → x ~ x
```

Similarly, symmetry is nothing other than a function which swaps the two sides
of the relation:

```agda
  Symmetric : Rel A ℓ → Set _
  Symmetric {A = A} _~_
    = {x y : A} → x ~ y → y ~ x
```

and transitivity merely glues two related terms together if they share one side
in common:

```agda
  Transitive : Rel A ℓ → Set _
  Transitive {A = A} _~_
    = {x y z : A} → x ~ y → y ~ z → x ~ z
```

Now that we have some common things to look for, let's dive into designing some
new relations and see what shakes out.


## Attempting to Order the Naturals

We have now spent several chapters discussing numbers and equality, but what
about concepts like "less than or equal to?" *Orderings* like these are
relations in their own regard, and as you might expect, they are just as
amenable to formalization in Agda as their more exact counterparts.

The first thing to notice is that this is not a *general* notion---it is very
much tied to the natural numbers. We can't build generic machinery that would
allow us to say a value of some arbitrary type is less than some other value of
the same. While there are many types that *do* admit the notion of an ordering
relationship, the nature of that relationship must be specialized for each
type. Besides, we don't even have a guarantee such an ordering would be
unique---for example, we might choose to order strings lexicographically or by
length. One might be the more familiar choice, but it's hard to argue that one
is *more correct* than the other.

A surprising amount of care is required in order to implement an ordering on the
natural numbers. There are many gotchas here that serve to illustrate a valuable
lesson in designing types in Agda, and so it is worthwhile to go slowly, take
our time, and learn what can go wrong.

How can we prove that one number is less than or equal to another? Recall
that there do not exist any negative natural numbers, so one possible means is
to say that $x \le y$ if there exists some $z$ such that $x + z = y$. We can set
this up, first by importing our previously-defined machinery directly from the
standard library:

```agda
open import Relation.Binary
  using (Rel; Reflexive; Transitive; Symmetric)
```

With surprising prescience, I can tell you that our first attempt at
implementing `type:_≤_` ([le](AgdaMode)) is going to fail, so let's make a new
module and define our type:

```agda
module Naive-≤₁ where
  data _≤_ : Rel ℕ lzero where
    lte : (a b : ℕ) → a ≤ a + b
  infix 4 _≤_
```

To a first approximation, it seems to work:

```agda
  _ : 2 ≤ 5
  _ = lte 2 3
```

Indeed, Agda can even solve the above definition for us via [`Auto`](AgdaCmd).
One of the few things we can prove about `type:_≤_` defined in this way is that
`ctor:suc` is *monotonic*---that is, that if `bind:x y:x ≤ y`, then
`bind:x y:suc x ≤ suc y`:

```agda
  suc-mono : {x y : ℕ} → x ≤ y → suc x ≤ suc y
  suc-mono (lte x y) = lte (suc x) y
```

If you attempted to write this for yourself, you might have been surprised that
[`Refine`](AgdaCmd) refused to introduce the `ctor:lte` constructor, instead
complaining about "no introduction forms found." This is a little surprising,
since the above definition *does* in fact work. Let's agree to scratch our
collective heads and hope nothing else weird happens.

Something else weird does in fact to happen when we try to show
`def:≤-refl`---which we should be able to do by picking $y = 0$:

```illegal
  ≤-refl⅋⅋ : Reflexive _≤_
  ≤-refl⅋⅋ {x} = lte x 0
```

Giving this definition results in an error from Agda:

```info
x + 0 != x of type ℕ
when checking that the expression lte x 0 has type x ≤ x
```

Unperturbed, we can try hitting `def:≤-refl` with some of our other proof
techniques, and see if we can make progress on it in that way. Let's proceed
with naught but brute force and ignorance, seeing if we can nevertheless bend
Agda to our will. Try running [MakeCase:x](AgdaCmd):

```agda
  ≤-refl⅋₀ : Reflexive _≤_
  ≤-refl⅋₀ {zero}   = {! !}
  ≤-refl⅋₀ {suc x}  = {! !}
```

It's easy to fill the first hole:

```agda
  ≤-refl⅋₁ : Reflexive _≤_
  ≤-refl⅋₁ {zero}   = lte zero zero
  ≤-refl⅋₁ {suc x}  = {! !}
```

This remaining goal has type `bind:x:suc x ≤ suc x`, which sounds like the sort
of thing we need recursion to solve. So we can introduce a `keyword:with`
abstraction:

```agda
  ≤-refl⅋₂ : Reflexive _≤_
  ≤-refl⅋₂ {zero} = lte zero zero
  ≤-refl⅋₂ {suc x}
    with ≤-refl⅋₂ {x}
  ... | x≤x = ?
```

giving us `x≤x` whose type is, appropriately, `bind:x:x ≤ x`. The usual move here
would be to pattern match on `x≤x` to open up its `ctor:lte` constructor, insert
a `ctor:suc`, and be on our merry way. Putting that plan into action, however,
immediately goes awry when we run [MakeCase:x≤x](AgdaCmd):

```info
I'm not sure if there should be a case for the constructor lte,
because I get stuck when trying to solve the following
unification problems (inferred index ≟ expected index):
  x₁ ≟ x₂
  x₁ + y ≟ x₂
Possible reason why unification failed:
  Cannot solve variable x₁ of type ℕ with solution x₁ + y because the
  variable occurs in the solution, or in the type of one of the
  variables in the solution.
when checking that the expression ? has type suc x ≤ suc x
```

Yikes! Something has gone horribly, horribly wrong. Let's turn our attention to
this problem momentarily, but out of sheer cheekiness, we can complete the proof
nevertheless. Spotting that `x≤x` has a satisfactory type for us to invoke
`def:suc-mono` is sufficient to make progress and fill our final hole:

```agda
  ≤-refl : Reflexive _≤_
  ≤-refl {zero} = lte zero zero
  ≤-refl {suc x} with ≤-refl {x}
  ... | x≤x = suc-mono x≤x
```


## Substitution {#sec:subst}

A surprising number of things went wrong when putting together such a simple
proof! Let's together analyze each of them in order to see what exactly
happened. Recall our original implementation which we assumed would work:

```illegal
  ≤-refl⅋⅋⅋⅋ : Reflexive _≤_
  ≤-refl⅋⅋⅋⅋ {x} = lte x 0
```

However, Agda gave us this error instead:

```info
x + 0 != x of type ℕ
when checking that the expression lte x 0 has type x ≤ x
```

The problem here is that `bind:x:lte x 0` has type `bind:x:x ≤ x + 0`. From our
discussion in @sec:cong, we saw just how much work it was to convince Agda that
$x = x + 0$---we had to go through all the work of proving `def:+-identityʳ`!

Thankfully, that work is not lost to us, and we can reuse it here by way of some
standard (if heavy-handed) machinery for rewriting propositional equalities at
the level of types. This machinery is called `def:subst`, short for
*substitution*:

```agda
  open Chapter3-Proofs
    using (+-identityʳ)

  subst
      : {x y : A}
      → (P : A → Set ℓ)  -- ! 1
      → x ≡ y
      → P x → P y
  subst _ PropEq.refl px = px
```

You can think of `def:subst` as a type-level `def:cong`, as it serves the same
purpose. At [1](Ann) it takes an argument `P` which is responsible for pointing
out where you'd like the substitution to happen---completely analogous to the
function we gave to `def:cong` for targeting where the rewrite should occur.

To illustrate the use of `def:subst`, we can reimplement `def:≤-refl` in terms
of it---though the experience is decidedly less than wholesome:

```agda
  ≤-refl′ : Reflexive _≤_
  ≤-refl′ {x} = subst (λ φ → x ≤ φ) (+-identityʳ x) (lte x 0)
```

It's nice to know that `def:subst` exists, but as a good rule of thumb, it's
usually the wrong tool for the job. When you find yourself reaching for
`def:subst` over and over again, it's indicative that you've painted yourself
into a corner and wrote a bad definition somewhere. Requiring substitution is
usually a symptom of an upstream problem.


## Unification

But not every problem we saw when implementing `def:≤-refl` for the first time can
be solved via `def:subst`. Recall our attempt to pattern match on `x≤x` in the
following:

```agda
  ≤-refl⅋₃ : Reflexive _≤_
  ≤-refl⅋₃ {zero} = lte zero zero
  ≤-refl⅋₃ {suc x} with ≤-refl⅋₂ {x}
  ... | x≤x = ?
```

to which Agda replied:

```info
I'm not sure if there should be a case for the constructor lte
```

For goodness sake's, *of course* there should be a case for the constructor
`ctor:lte`; *it's the only constructor after all!* Our indignation is well
deserved, but it's more instructive to think about what has gone wrong here, and
what can we do about it?

The problem is that Agda is usually really good at pattern matching, eliding
impossible patterns whenever the constructor can't possibly match. In this case,
Agda somehow can't decide if the `ctor:lte` constructor should definitely be
there, or whether it definitely shouldn't be. How can this be so?

Internally, Agda implements this functionality by attempting to *unify*---that
is, via matching syntactically---the indices on type's constructors with the
indices of your expression. In this case, we have `x≤x` `:` `bind:x:x ≤ x`,
which Agda needs to unify against `ctor:lte` whose eventual indices are
`bind:?a ?b:?a ≤ ?a + ?b` (after some renaming to avoid confusion.)

Doing so sets up the following series of equations that Agda must solve:

$$
\begin{aligned}
?a \mathrel{\sim}& x \\
?a + ?b \mathrel{\sim}& x
\end{aligned}
$$

where we read `~` as "unifies to." In order to correctly determine if a
constructor needs to exist in a pattern match, Agda must be able to
syntactically assign an expression to each *metavariable* (here, `?a` and `?b`).
While we can use the first equation to unify `?a` with `x`, there is
no way to syntactically unify `?a + ?b` with `x`. Even after replacing `?a`, we
get `x + ?b ~ x`.

The problem is that there's no syntactic way to get the `?b` term all on its own
in the equation `x + ?b ~ x`. You and I know that the only solution to this
problem is that `?b = 0`, but this is a statement about number theory, and Agda
doesn't know anything about number theory. The pattern checker knows only about
syntax and computation, neither of which make progress here.

Since there is no way to solve the unification problem `x + ?b ~ x`, Agda throws
up its hands and calls uncle. Unfortunately, it chooses to do so with an
extremely unhelpful error.

One possible solution here would be for Agda to simply allow you to give cases
that it can't be sure about, but this leads to downstream typechecking issues
that would make the implementation of Agda significantly harder. Since the
reasons you might want to do this as a user are dubious at best, Agda doesn't
support it, and requires you to find alternative ways to convince the language
that you are doing meaningful things. We will not investigate those alternative
ways here, except to point out how to avoid the situation altogether.


## Overconstrained by Dot Patterns {#sec:dot-patterns}

One last subtle point about unification: rather surprisingly, we successfully
implemented `def:suc-mono`, without encountering the dreaded "not sure if there
should be a case" problem. How can that have happened? We can get a feeling for
the unification algorithm behind the scenes by explicitly binding our
implicit arguments:

```agda
  suc-mono′⅋₀ : {x y : ℕ} → x ≤ y → suc x ≤ suc y
  suc-mono′⅋₀ {x} {y} x≤y = ?
```

Doing a [`MakeCase:x≤y`](AgdaCmd) in this hole will correctly split apart the
`x≤y`, but in doing so, will also leave behind dot patterns for variables that
it unified in the process. Recall that dot patterns arise from a
constructor showing you which indices it must have, and constraining other
variables in the process. Thus, dot patterns are an excellent way to look at
what exactly Agda has solved:

```agda
  suc-mono′⅋₁ : {x y : ℕ} → x ≤ y → suc x ≤ suc y
  suc-mono′⅋₁ {x} {.(x + b)} (lte .x b) = lte (suc x) b
```

It's worth going through the solved constraints here. In splitting `ctor:lte`,
Agda introduced two new variables, `a` and `b`, subject to the constraints:

$$
\begin{aligned}
a \mathrel{\sim}& x \\
a + b \mathrel{\sim}& y
\end{aligned}
$$

There is a solution here, namely:

$$
\begin{aligned}
a \mathrel{\sim}& x \\
y \mathrel{\sim}& x + b
\end{aligned}
$$

which corresponds exactly to how Agda filled in the dot patterns in
`def:suc-mono′⅋₁` above.

Rather interestingly, we can implement a monomorphic version of
`def:suc-mono′⅋₁` by restricting its type:

```agda
  suc-mono-mono⅋₁ : {x : ℕ} → x ≤ x → suc x ≤ suc x
  suc-mono-mono⅋₁ = suc-mono′⅋₁
```

but we *cannot* inline the definition of `def:suc-mono′⅋₁` here, since we will get
the "not sure" error. Looking at the constraints Agda must solve immediately
shows us the problem:

$$
\begin{aligned}
a \mathrel{\sim}& x \\
a + b \mathrel{\sim}& x
\end{aligned}
$$

There's simply no way to solve this system of equations just by substituting
variables with one another. We are required to express the constraint `x ~ a +
b` *somewhere* in the pattern match, but the only variable that isn't already
spoken for is `b` itself, and we don't have `b` isolated in our equation. Thus,
the constraint can't be satisfied, and therefore we are stuck.

The Agda folklore warns that one ought not use computing terms (that is to say,
anything other than constructors) as type indices---for exactly this reason.
This happens to be true, but as we have seen above, it's not the whole story.
The problem is not with computation per se, it's that when you pattern match and
bring these constraints into scope, they don't work out to nice constructors
that Agda can immediately pattern match on.

Instead, Agda's only recourse is to introduce a dot pattern, which reifies the
computation, but at the cost of eliminating one of your bindings---that is, by
removing a degree of freedom. When you run out of bindings, Agda has nowhere to
reify these additional constraints, and you get the dreaded "I'm not sure if
there should be a case" error.

The takeaway here is that type indices should always be bindings or
constructors, but never function calls---doing so risks running out of places to
put the indices and will prevent Agda from being able to pattern match on your
type. This is a particularly insidious problem because the errors happen far
away from the definition, and can be hard to diagnose without constant
vigilance.


## Ordering the Natural Numbers {#sec:nat-ord}

Having worked through this extremely long digression on the nature of Agda's
ability to perform pattern matching, we should now see what's gone wrong with
our first definition of `type:_≤_` and know how to fix it.

The solution here is to prevent Agda from introducing dot patterns, and the
simplest way to do *that* is to only ever use *constructors* as indices to your
data type.

A good way to proceed here is to work backwards; starting from each constructor,
we can determine how to use it in order to show our desired
less-than-or-equal-to relationship.

The case of `ctor:zero` is easy, since `ctor:zero` is the smallest element, we
have the case that `ctor:zero` `type:≤` `n`, for any other number `n`!

In the case of `ctor:suc`, we know that `ctor:suc` `m` `type:≤` `ctor:suc` `n`
if and only if `m` `type:≤` `n` in the first place. This gives rise to a very
natural type:

```agda
module Definition-LessThanOrEqualTo where
  data _≤_ : Rel ℕ lzero where
    z≤n : {n : ℕ} → zero ≤ n
    s≤s : {m n : ℕ} → m ≤ n → suc m ≤ suc n
  infix 4 _≤_
```

This does happen to be the right[^stdlib-approved] definition for `type:_≤_`. As
in other chapters, let's drop out of this definition module and import the same
thing from the standard library. In doing so, we will ensure everything else we
build will play nicely with future chapters and any other Agda code you might
want to write against the standard library itself.

[^stdlib-approved]: That is, equivalent to the definition given in the standard library.

```agda
open import Data.Nat
  using (_≤_; z≤n; s≤s)

module Sandbox-≤ where
```


Hidden

:   ```agda
  -- fix bind
    ```

Let's now again prove that `expr:2 ≤ 5`. Begin with a quick type:

```agda
  _ : 2 ≤ 5
  _ = ?
```

Asking Agda to [Refine](AgdaCmd) this hole has it use the `ctor:s≤s`
constructor:

```agda
  _ : 2 ≤ 5
  _ = s≤s {! !}
```

Something interesting has happened here. Invoke [TypeContext](AgdaCmd) on the
new hole, and you will see it has type `expr:1 ≤ 4`! By using `ctor:s≤s`, Agda
has moved *both* sides of the inequality closer to zero. It makes sense when you
stare at the definition of `ctor:s≤s`, but it's a rather magical thing to behold
for the first time.

Throw another `ctor:s≤s` in the hole:

```agda
  _ : 2 ≤ 5
  _ = s≤s (s≤s {! !})
```

whose new hole now has type `expr:0 ≤ 3`. From here, the constructor `ctor:z≤n`
now fits, which completes the definition:

```agda
  _ : 2 ≤ 5
  _ = s≤s (s≤s z≤n)
```

Thankfully, all our hard work now pays off, as we are able to implement our
desired `def:suc-mono` and `def:≤-refl` without any further hassle.


Exercise (Trivial)

:   Prove `def:suc-mono` `:` `expr:{x y : ℕ} → x ≤ y → suc x ≤ suc y`.


Solution

:   ```agda
  suc-mono : {x y : ℕ} → x ≤ y → suc x ≤ suc y
  suc-mono = s≤s
    ```


Exercise (Easy)

:   Prove `def:≤-refl` `:` `expr:{x : ℕ} → x ≤ x`.


Solution

:   ```agda
  ≤-refl : {x : ℕ} → x ≤ x
  ≤-refl {zero}   = z≤n
  ≤-refl {suc x}  = s≤s ≤-refl
    ```


Exercise (Easy)

:   Prove `def:≤-trans` `:` `expr:{x y z : ℕ} → x ≤ y → y ≤ z → x ≤ z`.

:     ```agda
  ≤-trans : {x y z : ℕ} → x ≤ y → y ≤ z → x ≤ z
  ≤-trans z≤n  y≤z = z≤n
  ≤-trans (s≤s x≤y) (s≤s y≤z)  = s≤s (≤-trans x≤y y≤z)
      ```


## Preorders {#sec:on-preorders}

As humans, we are naturally drawn to order, structure, and patterns, and thus
the properties of reflexivity and transitivity can seem mundane to us. But this
is a fact about the human mind, not about which mathematical properties are
interesting! By virtue of being able to spot "mundane" properties like these is
*exactly* what makes them of note.

There is in fact a great amount of structure hidden inside of reflexivity and
transitivity; the crushing majority of relations do not satisfy these two
properties. Those that do are called *preorders:*


```agda
module Sandbox-Preorders where
  open Sandbox-≤

  record IsPreorder {A : Set a} (_~_ : Rel A ℓ) : Set (a ⊔ ℓ) where
    field
      refl   : Reflexive   _~_
      trans  : Transitive  _~_
```

Unlike other constructions we've built for ourselves, we will not prefer to get
this one from the standard library. The standard library heads off into
astronaut territory when it comes to structures like this---generalizing away
from a hardcoded dependency on propositional equality to taking some notion of
equality as a parameter. We will investigate what exactly is going on there when
we discuss setoids in @sec:setoids. But that is a topic far in the future, and
for now, we will deal exactly with `type:IsPreorder` as it's defined here.

We have already seen three preorders in this book, perhaps without even
realizing it. Of course, `type:_≤_` forms one:

```agda
  ≤-preorder : IsPreorder _≤_
  IsPreorder.refl   ≤-preorder = ≤-refl
  IsPreorder.trans  ≤-preorder = ≤-trans
```

as does `type:_≡_`, though we need to be a little careful in showing it.

The most salient issue in showing `expr:IsPreorder _≡_` is that, given our new
definition of `type:IsPreorder`, the identifiers `refl` and `trans` are no
longer unambiguous. Agda just isn't sure if we want the `ctor:refl` constructor
for propositional equality, or `field:refl` from `def:IsPreorder`, and similar
problems arise for `trans`.

An easy solution is to give qualified identifiers for the particular things we'd
like. We can give the alias `module:PropEq` to `module:Chapter3-Proof`
(the module where we first defined `ctor:refl` and `def:trans`) by way of the
following syntax, which now gives us unambiguous access to `ctor:PropEq.refl`
and `def:PropEq.trans`:

```agda
  ≡-preorder⅋₀ : IsPreorder (_≡_)
  IsPreorder.refl   ≡-preorder⅋₀ = PropEq.refl
  IsPreorder.trans  ≡-preorder⅋₀ = PropEq.trans
```

The other issue arising from a naive implementation of `def:≡-preorder` can now
be seen---it's this bright saffron background on `type:IsPreorder`. Agda's
failed to fill in an implicit on our behalf. What's gone wrong is that
`type:_≡_` is polymorphic in the type for which it shows equality, and so Agda
doesn't know how we'd like to instantiate that polymorphism. In fact---we don't,
and would like to *keep* it polymorphic. This can be done by explicitly filling
in `type:_≡_`'s implicit `A` parameter, which we'd like to fill in
with our `keyword:variable`, conveniently also named `A`:

```agda
  ≡-preorder : IsPreorder (_≡_ {A = A})
  IsPreorder.refl   ≡-preorder = PropEq.refl
  IsPreorder.trans  ≡-preorder = PropEq.trans
```

Exercise (Trivial)

:   Should the reader be feeling industrious, they are encouraged to prove that
    `type:Sandbox-Relations.Unrelated` and `type:Sandbox-Relations.Related` are also
    preorders.

Solution

:     ```agda
  open Sandbox-Relations using (Related; related)
  Related-preorder : IsPreorder (Related {A = A})
  IsPreorder.refl   Related-preorder      = related
  IsPreorder.trans  Related-preorder _ _  = related
      ```


## Preorder Reasoning {#sec:preorder-reasoning}

In @sec:propreasoning, we built equational reasoning tools for working
with propositional equality. Now that we know a little more, recall that our
equational reasoning machinery used only reflexivity and transitivity. That is
to say, we can generalize equational reasoning so that it works over any
preorder whatsoever!

Let's quickly build this new reasoning for preorders. At any given point, we're
going to want to be working in only a single preorder, so we can define a new
module *parameterized* by the preorder we'd like:

```agda
  module Preorder-Reasoning
      {_~_ : Rel A ℓ} (~-preorder : IsPreorder _~_) where
```

By opening the `~-preorder` record, we can bring its record fields into scope.
The syntax here is a little odd, since we need to first tell Agda the type of
the record:

```agda
    open IsPreorder ~-preorder public
```

By opening it `keyword:public`, we ensure that `field:refl` and `field:trans`
both "leak" in when we open `module:Preorder-Reasoning`. In essence,
`keyword:public` makes it as if we explicitly defined the imported identifiers
in this module---just like when we list out our accomplishments at the end of
each chapter.

The rest of the preorder reasoning machinery will be presented without further
commentary, as there is nothing new here. The only changes are that we've
replaced `type:_≡_` with `~`, and renamed `def:_≡⟨_⟩_` to `def:_≈⟨_⟩_`:

```agda
    begin_ : {x y : A} → x ~ y → x ~ y
    begin_ x~y = x~y
    infix 1 begin_
```

```agda
    _∎ : (x : A) → x ~ x
    _∎ x = refl
    infix 3 _∎
```

```agda
    _≡⟨⟩_ : (x : A) → {y : A} → x ~ y → x ~ y
    x ≡⟨⟩ p = p
    infixr 2 _≡⟨⟩_
```

```agda
    _≈⟨_⟩_ : (x : A) → ∀ {y z} → x ~ y → y ~ z → x ~ z
    _ ≈⟨ x~y ⟩ y~z = trans x~y y~z
    infixr 2 _≈⟨_⟩_
```

We would, however, like to make one addition to this interface: making it play
nicely with propositional equality. If we happen to know that two terms are
propositionally equal, it would be nice to be able to use that
fact in a reasoning block. Thus, we also include `def:_≡⟨_⟩_`:

```agda
    _≡⟨_⟩_ : (x : A) → ∀ {y z} → x ≡ y → y ~ z → x ~ z
    _ ≡⟨ PropEq.refl ⟩ y~z = y~z
    infixr 2 _≡⟨_⟩_
```

Any code wanting to do equational reasoning over a preorder is now able to: it
need only `keyword:open` the `module:Preorder-Reasoning` module using its proof
of being a preorder (that is, `type:IsPreorder`) as an argument.


## Reasoning over `≤`

Let's quickly prove a non-trivial fact about the natural numbers, namely that $n
\le 1 + n$. You should be able to do this sort of thing in your sleep by now:

```agda
  n≤1+n : (n : ℕ) → n ≤ 1 + n
  n≤1+n zero = z≤n
  n≤1+n (suc n) = s≤s (n≤1+n n)
```

We can further use this fact and our preorder reasoning in order to show that $n
\le n + 1$:

```agda
  open Chapter3-Proofs using (+-comm)

  n≤n+1⅋₀ : (n : ℕ) → n ≤ n + 1
  n≤n+1⅋₀ n = begin
    n      ≈⟨ n≤1+n n ⟩  -- ! 1
    1 + n  ≡⟨ +-comm 1 n ⟩
    n + 1  ∎
    where open Preorder-Reasoning ≤-preorder
```

Hidden

:   ```agda
  -- fix bind
    ```

The proof here is fine, but the syntax leaves a little to be desired. Notice
that at [1](Ann) we are required to use `def:_≈⟨_⟩_` to show that `bind:n:n ≤ 1
+ n`. But (from the perspective of someone reading this code with fresh eyes)
what the heck is `≈`? We're proving something about `type:_≤_`!

While `≈` is a reasonable name for a *generic* preorder, many preorders have
existing names that it would be preferable to reuse. In this case, we'd like to
use `≤`!

The trick, as usual, is to make a new module that `keyword:public`ly opens
`module:Preorder-Reasoning`, using `keyword:renaming` to change whatever names
need work. Furthermore, while we're here, we might as well fill in the preorder
parameter with `def:≤-preorder`:

```agda
  module ≤-Reasoning where
    open Preorder-Reasoning ≤-preorder
      renaming (_≈⟨_⟩_ to _≤⟨_⟩_)
      public
```

By now using `module:≤-Reasoning` directly, our proof is worthy of much more
delight:

```agda
  n≤n+1 : (n : ℕ) → n ≤ n + 1
  n≤n+1 n = begin
    n      ≤⟨ n≤1+n n ⟩
    1 + n  ≡⟨ +-comm 1 n ⟩
    n + 1  ∎
    where open ≤-Reasoning
```

Don't be shy in introducing helper modules to put a specific spin on more
general notions. Their judicious use can dramatically improve the developer
experience, whether the developer be you or a user of your library. Either way,
the effort will be appreciated.


## Graph Reachability

We have shown that both `type:_≤_` and `type:_≡_` form preorders. From this
you might be tempted to think that preorders are just tools that are sorta like
ordering or equality. Not so. Let's look at another example to break that intuition.

Consider a graph (as in a network, not like a plot). Math textbooks often begin
their discussion around graphs with the telltale phrase:

> Let $G = (V, E)$ be a graph with vertices $V$ and edges $E$.

Left completely unsaid in this introduction is that $E$ is in fact a *relation*
on $V$; given a graph with vertices $V$, it really *ought to be* the case that
the edges do actually lie between the vertices!

As a computer scientist, you probably have implemented a graph before at some
point, whether it be via pointer-chasing or as an adjacency matrix. These are
indeed encodings of graphs, but they are concessions to computability, which we
are not particularly interested in. Playing with graphs in Agda requires only
some set `type:V` and an edge relation `type:_⇒_` ([`=>`](AgdaMode)) over it:

```agda
  module Reachability {V : Set ℓ₁} (_⇒_ : Rel V ℓ₂) where
```

What can we say about `_⇒_`? Does it satisfy any of the usual relation
properties? Think on that question for a moment before continuing.

Does `_⇒_` satisfy any relation properties? The question is not even wrong.
We can say nothing about `_⇒_` other than what we have asked of it, since
it's a *parameter,*  and thus opaque to us. Given the definition, all we can say
for sure about `_⇒_` is that it's a relation over `V`!

However, what we *can* do is construct a new relation on top of `_⇒_`, and
stick whatever we'd like into that thing. One salient example here is the notion
of *reachability*---given a starting vertex on the graph, is their a path to
some other vertex? The distinction between the relation `_⇒_` and the
reachable relation on top of it is subtle but important: while there is no
single road that connects Vancouver to Mexico City, there is certainly a path
that does!

When exactly is one vertex reachable from another? The easiest case is if we
already have an edge in `_⇒_` that connects two vertices. As a trivial case, two
vertices already connect if they are the same. Finally, if we know an
intermediary vertex is reachable from our starting point, and that the goal is
reachable from there, we can connect the two paths. This gives rise to a very
straightforward definition:

```agda
    private variable
      v v₁ v₂ v₃ : V

    data Path : Rel V (ℓ₁ ⊔ ℓ₂) where
      ↪_       : v₁ ⇒ v₂ → Path v₁ v₂
      here     : Path v v
      connect  : Path v₁ v₂ → Path v₂ v₃ → Path v₁ v₃
```

Where we can type `↪` by scrolling through the possibilities under [`r`](AgdaMode).

It is not difficult to show that `type:Path` forms a preorder:

```agda
    Path-preorder : IsPreorder Path
    IsPreorder.refl   Path-preorder = here
    IsPreorder.trans  Path-preorder = connect
```

Pay attention to what we've done here, as this is a very general and reusable
technique. Given some arbitrary relation `_⇒_`, about which we know
nothing, we were able to *extend* that relation into a preorder. The
`ctor:↪_` constructor injects values of type `bind:v₁ v₂:v₁ ⇒ v₂` into the type
``bind:v₁ v₂:Path v₁ v₂`. Since this is possible, it's reasonable to think of
`type:Path` as `_⇒_`, "but with more stuff in it." Namely, enhanced with
`ctor:here` and `ctor:connect`.

The attentive reader will notice that it is exactly `ctor:here` and
`ctor:connect` which are used in `def:Path-preorder`, which is why `type:Path`
can turn any relation into a preorder.

More generally, the idea behind `type:Path` is to augment a type with just
enough structure to allow you to build some well-known mathematical (or
computational) idea on top. Usually the approach is to add constructors for
every required property. In doing so, you find the *free X*---in this case,
`type:Path` is the *free preorder.*


## Free Preorders in the Wild

We will now combine our free preorder with the preorder reasoning we built in
@sec:preorder-reasoning to demonstrate actual paths through a social graph.

Rather than incriminate any real group of humans, we can instead use the
excellent early-noughties romantic comedy *About a Boy* (@hedges_about_2002) as
a case study. If you haven't seen the film, you should consider remedying that
as soon as possible. Don't worry though, there are no spoilers here; it's safe
to continue.

Our first task is to define the vertices of the social graph, which of
course are the people involved:

```agda
  module Example-AboutABoy where
    data Person : Set where
      ellie fiona marcus rachel susie will : Person
```

Some of these people are friends, which we can use as edges in our graph.

```agda
    private variable
      p₁ p₂ : Person

    data _IsFriendsWith_ : Rel Person lzero where
      marcus-will   : marcus  IsFriendsWith will
      marcus-fiona  : marcus  IsFriendsWith fiona
      fiona-susie   : fiona   IsFriendsWith susie
```

Friendship is usually considered to be symmetric. While we could add explicit
constructors for the other direction of each of these friendships, it's easier
to add a `ctor:sym` constructor:

```agda
      sym : p₁ IsFriendsWith p₂ → p₂ IsFriendsWith p₁
```

What excellent early-noughties romantic comedy is complete without a series of
potential love interests? We can enumerate who likes whom as another source of
edges in our graph:

```agda
    data _IsInterestedIn_ : Rel Person lzero where
      marcus-ellie  : marcus  IsInterestedIn ellie
      will-rachel   : will    IsInterestedIn rachel
      rachel-will   : rachel  IsInterestedIn will
      susie-will    : susie   IsInterestedIn will
```

As much as many people would prefer a world in which `type:_IsInterestedIn_` is
a symmetric relation, this is sadly not the case, and thus we do not require a
constructor for it.

Finally, we can tie together `type:_IsFriendsWith_` and `type:_IsInterestedIn_`
with `type:SocialTie` which serves as the definitive set of edges in our graph.

```agda
    data SocialTie : Rel Person lzero where
      friendship  : p₁ IsFriendsWith p₂   → SocialTie p₁ p₂
      interest    : p₁ IsInterestedIn p₂  → SocialTie p₁ p₂
```

There is no preorder on `type:SocialTie`, but we can get one for free by using
`type:Path`. Then we can look at how `ctor:will` and `ctor:fiona` relate in the
social graph:

```agda
    open Reachability SocialTie

    will-fiona : Path will fiona
    will-fiona = begin
      will    ≈⟨ ↪ friendship (sym marcus-will) ⟩
      marcus  ≈⟨ ↪ friendship marcus-fiona ⟩
      fiona   ∎
      where open Preorder-Reasoning Path-preorder
```

or how `ctor:rachel` and `ctor:ellie` relate:

```agda
    rachel-ellie : Path rachel ellie
    rachel-ellie = begin
      rachel  ≈⟨ ↪ interest    rachel-will ⟩
      will    ≈⟨ ↪ friendship  (sym marcus-will) ⟩
      marcus  ≈⟨ ↪ interest    marcus-ellie ⟩
      ellie   ∎
      where open Preorder-Reasoning Path-preorder
```

Agda's ability to model and work with things like this is frankly amazing. Of
course, I am likely the only person in the world interested in the social
dynamics of *About a Boy,* but the fact that it's possible is a testament to how
much power we've developed.


## Antisymmetry

Let's take a step back from preorders and look some more at `type:_≤_`. For
example, does it support symmetry? A moment's thought convinces us that it can't
possibly.Just because $2 \le 5$ doesn't mean that $5 \le 2$.

However, `type:_≤_` does satisfy a related notion, that of *antisymmetry.*
Antisymmetry says that if we know $m \le n$ and that $n \le m$, then it must be
the case that $m = n$. Proving the antisymmetry of `type:_≤_` is
straightforward:

```agda
  ≤-antisym : {m n : ℕ} → m ≤ n → n ≤ m → m ≡ n
  ≤-antisym z≤n z≤n = PropEq.refl
  ≤-antisym (s≤s m≤n) (s≤s n≤m) =
    PropEq.cong suc (≤-antisym m≤n n≤m)
```

In addition, we can generalize this type to something more reusable, like we did
with `type:Reflexive`, `type:Symmetric`, `type:Transitive`, `type:Functional`,
and `type:Total`. This one is a little trickier however, since it's really a
property over *two* relations: one corresponding to equality, and another to the
ordering:

```agda
  Antisymmetric
      : Rel A ℓ₁
      → Rel A ℓ₂
      → Set _
  Antisymmetric _≈_ _≤_ =
    ∀ {x y} → x ≤ y → y ≤ x → x ≈ y
```

which does expand to our desired type, as we can show:

```agda
  _ : Antisymmetric _≡_ _≤_
  _ = ≤-antisym
```


## Equivalence Relations and Posets

The difference between `type:_≡_`'s symmetry and `type:_≤_`'s antisymmetry turns
out to be the biggest differentiator between the two relations. We have seen
that both are preorders, but whether a relation is symmetric or antisymmetric
bifurcates the mathematical hierarchy.

Symmetric preorders like `type:_≡_` are known as *equivalence relations*, and
such things act exactly as equality should. An equivalence relation forms
"buckets," with every member of the underlying set in exactly one bucket, and
everything in the bucket being related. For `type:_≡_` there is one bucket for
each element in the set, but you could imagine relating strings based on their
length, where we would then get a bucket for every unique string length.

We're going to define `type:IsEquivalence` and `type:IsPartialOrder` at the same
time, and both are types parameterized by a given relation. While we could go
through the effort and write out all the necessary levels, sets, and
relationship bindings for both, it's simpler to put that stuff as parameters to
an anonymous module:

```agda
  module _ {a ℓ : Level} {A : Set a} (_~_ : Rel A ℓ) where
```

Anything inside of this module will now inherit each of `a`, `ℓ`, `A`, and
`_~_`, which can be a great time-saver when defining several closely-related
objects. And we give the module the name `_` meaning "this is not really a
module, it exists only to these parameters." Inside the module we are now free
to define `type:IsEquivalence`:

```agda
    record IsEquivalence : Set (a ⊔ ℓ) where
      field
        isPreorder  : IsPreorder  _~_
        sym         : Symmetric   _~_

      open IsPreorder isPreorder public
```

Note that it appears that `type:IsEquivalence` has no parameters, but this is
not true. The anonymous module above scopes them for us, and any *user* of
`type:IsEquivalence` will see that it has a `_~_` parameter.

The partially ordered sets, usually shortened to *posets*, are antisymmetric
preorders. If you think about preorders as directed graphs, then posets
correspond to directed *acyclic* graphs. Their antisymmetry property precludes
any possibility of cycles, since from a cycle we could derive the fact that both
$x \le y$ *and* $y \le x$. Since the natural numbers all sit on a straight line,
they have no cycles, which is why they form a poset.

We can code up `type:IsPartialOrder` analogously to `type:IsEquivalence`:

```agda
    record IsPartialOrder : Set (a ⊔ ℓ) where
      field
        isPreorder : IsPreorder         _~_
        antisym    : Antisymmetric _≡_  _~_
```

After popping the anonymous module; let's show that `type:_≡_` and `type:_≤_`
really are the sorts of relations we've claimed:

```agda
  ≡-equiv : IsEquivalence (_≡_ {A = A})
  IsEquivalence.isPreorder  ≡-equiv = ≡-preorder
  IsEquivalence.sym         ≡-equiv = PropEq.sym
```

and

```agda
  ≤-poset : IsPartialOrder _≤_
  IsPartialOrder.isPreorder  ≤-poset = ≤-preorder
  IsPartialOrder.antisym     ≤-poset = ≤-antisym
```


## Strictly Less Than

So far we have discussed only the less-than-or-equal to relationship between
natural numbers. But sometimes we might want a *strict* less-than, without any
of this "or equal to" business. That's easy enough; we can just insert a
`ctor:suc` on the right side:

```agda
  _<_ : Rel ℕ lzero
  m < n = m ≤ suc n
  infix 4 _<_
```

While `def:_<_` comes in handy sometimes, it's not a very well behaved
relation---it's not reflexive, symmetric, or even antisymmetric! What a bust of
a relation! We don't yet have the sophistication to prove something is false,
but that's exactly the sort of thing we'll tackle in @sec:decidability.


## Wrapping Up

We covered a lot of ground in this chapter, beginning in @sec:levels discussing Agda's universe levels. Many people get `type:Level` from the standard library under the module `module:Level`, but we will prefer to take it from `module:Agda.Primitive`, which uses slightly different names:

```agda
open import Agda.Primitive
  using (Level; _⊔_; lzero; lsuc)
  public
```

Later, in @sec:sigma we discussed sigma types, which, recall, can be used to
encode the mathematical idea of "there exists." Sigma types are closely related
to product types, and in fact can be found in the same place:

```agda
open import Data.Product
  using (Σ; _,_)
  public
```

In @sec:hetgen-rels and @sec:homgen-rels, we discussed heterogeneous and
homogeneous relations, while we explored many of their properties in
@sec:rel-props. The machinery we built here can be found in the standard library under `module:Relation.Binary`:

```agda
open import Relation.Binary
  using (Rel; REL; Transitive; Reflexive; Symmetric; Antisymmetric)
  public
```

We briefly explored substitution in @sec:subst, which you can find alongside propositional equality:

```agda
open import Relation.Binary.PropositionalEquality
  using (subst)
  public
```

In @sec:nat-ord we gave two orderings for the natural numbers---strictly less than, and less-than-or-equal-to. These, and the properties about them we proved, can be found in `module:Data.Nat` and `module:Data.Nat.Properties`:

```agda
open import Data.Nat
  using (_≤_; z≤n; s≤s; _<_)
  public

open import Data.Nat.Properties
  using (≤-refl; ≤-trans; ≤-antisym; n≤1+n; module ≤-Reasoning)
  public
```

Finally, we also explored preorders, as in @sec:on-preorders. For technical reasons,
the remainder of this book will not re-export the standard library's definition
of preorders. However, should you need it for your own projects, you can find
them under `module:Relation.Binary`. Instead, we will export our own
definitions:

```agda
open Sandbox-Preorders
  using ( IsPreorder; IsEquivalence; IsPartialOrder
        ; module Preorder-Reasoning
        ; ≡-preorder; ≡-equiv
        ; ≤-preorder; ≤-poset
        )
  public
```


---

```unicodetable
× U+01D7 MULTIPLICATION SIGN (\x)
ʳ U+03B3 MODIFIER LETTER SMALL R (\^r)
Σ U+04A3 GREEK CAPITAL LETTER SIGMA (\GS)
λ U+04BB GREEK SMALL LETTER LAMDA (\Gl)
φ U+04C6 GREEK SMALL LETTER PHI (\Gf)
′ U+2033 PRIME (\')
₀ U+2081 SUBSCRIPT ZERO (\_0)
₁ U+2082 SUBSCRIPT ONE (\_1)
₂ U+2083 SUBSCRIPT TWO (\_2)
₃ U+2084 SUBSCRIPT THREE (\_3)
ℓ U+2114 SCRIPT SMALL L (\ell)
ℕ U+2116 DOUBLE-STRUCK CAPITAL N (\bN)
ℤ U+2125 DOUBLE-STRUCK CAPITAL Z (\bZ)
→ U+2193 RIGHTWARDS ARROW (\to)
↦ U+22A6 RIGHTWARDS ARROW FROM BAR (\r-|)
↪ U+22AA RIGHTWARDS ARROW WITH HOOK (\r)
⇒ U+22D2 RIGHTWARDS DOUBLE ARROW (\=>)
∀ U+2201 FOR ALL (\all)
∃ U+2204 THERE EXISTS (\ex)
∎ U+221E END OF PROOF (\qed)
≈ U+2249 ALMOST EQUAL TO (\~~)
≟ U+226F QUESTIONED EQUAL TO (\?=)
≡ U+2262 IDENTICAL TO (\==)
≤ U+2265 LESS-THAN OR EQUAL TO (\le)
⊔ U+2295 SQUARE CUP (\lub)
⟨ U+28E8 MATHEMATICAL LEFT ANGLE BRACKET (\<)
⟩ U+28E9 MATHEMATICAL RIGHT ANGLE BRACKET (\>)
```

