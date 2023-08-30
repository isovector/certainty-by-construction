# Relations

Hidden

:   ```agda
{-# OPTIONS --allow-unsolved-metas #-}
    ```

```agda
module Chapter4-Relations where
```


Prerequisites

:   ```agda
import Chapter1-Agda
open Chapter1-Agda.Exports
  using (_×_; _,_)
    ```

:   ```agda
import Chapter2-Numbers
open Chapter2-Numbers.Exports
  using (ℕ; zero; suc; _+_)
    ```

:   ```agda
import Chapter3-Proofs
open Chapter3-Proofs.Exports
  using (_≡_; cong)
    ```

-- TODO(sandy): this intro doesn't make much sense anymore


One exceptionally common notion in mathematics is the notion of a "set equipped
with some structure." In this chapter, we will discuss what this means, how to
build such things, and look at several extremely distinct examples.

The first thing to take note of, however, is that when mathematicians say "set,"
very rarely do they mean *set* as in, *set theory.* What they really mean is
"some collection of elements," or even just some *type.* While set theory comes
with a great deal of axiomization for constructing sets and not shooting oneself
in the foot with them, it is worth realizing that almost no working
mathematicians use set theory when they actually get down to work. Even if
they're explicitly talking about sets.

A second point worthy of our discussion is that even though mathematicians give
their definitions of mathematical objects in terms of sets, they are not really
thinking about sets. As Buzzard points out, a group is defined in modern
textbooks as a non-empty set satisfying the group axioms. However, group theory
was invented eighty years before set theory. The definitions given are correct,
but post-hoc and sorted out after the fact. This can cause extreme
disorientation to the computer scientist, who must construct things from smaller
pieces, while the mathematicians build the big thing first and figure out how to
decompose it later.

-- TODO(sandy): cite kevin ^

Bear this in mind as we work through our examples; mathematical constructions
which might seem insane when taken at face value often make much more sense when
reconsidered in this context.


## Universe Levels {#sec:levels}

Before we discuss falseness, we must turn our attention first to a problem in
the early foundations of mathematics.

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
possible to prove anything whatsoever. We will look at how to exactly this in
@sec:negation.

Modern mathematics' solution to the barber paradox is the realization that not
all collections are sets---some are simply "too big" to be sets. There is no
"set of all sets" because such a thing is too big. Therefore, the question of
the barber who doesn't cut his own hair is swept under the rug, much like the
hair at actual barbershops.

But this only punts on the problem. What is the corresponding mathematical
object here. If the set of all sets is not a set, then, what exactly is it? The
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
as we become more sophisticated Agda programmers (*eg.* later in this chapter,)
we will start going the other direction: using types as values.

When we write a proof about values, such a thing lives in `type:Set`. But proofs
above *types* must necessarily exist in a higher universe so as to not taunt the
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
`module:Chapter2-Numbers.Exports` *re-exports* `type:Maybe` from the standard
library, which as a principle is always as universe-polymorphic as possible.


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


## Binary Relations

One common variety of structured set is the *relation,* which, in the canon, is
used to categorize disparate things like functions, equalities, orderings, and
set membership, to name a few. Let's begin with the mathematical definition, and
decompile it into something more sensible for our purposes.

> A binary relation `_R_` over sets $X$ and $Y$ is a subset of the Cartesian
> product $X \times Y$.

As we saw when discussing proofs, subsets are best encoded in Agda as functions
into `Set`. Taken at face value, this would give us the following type for a
relation:

```agda

postulate
  _ : {A B : Set} → A × B → Set
```

We can do slightly better however, by recalling the curry/uncurry isomorphism
(@sec:curry), splitting the explicit Cartesian product into two arguments:

```agda
  _ : {A B : Set} → A → B → Set
```

A fully-fledged solution here must be level polymorphic, since many of the
relations we'd like to be able to encode will be over higher-level sets. There
are actually three levels required here, one for `A`, another for `B`, and a
third for the resulting `Set`. Thus, we come up with our final definition as
`REL`:

```agda
module Sandbox-Relations where
  private variable
    a b ℓ : Level

  REL : Set a → Set b → (ℓ : Level) → Set (a ⊔ b ⊔ lsuc ℓ)
  REL A B ℓ = A → B → Set ℓ
```

This `type:REL` is the type of *heterogeneous* relations, that is, relationships
between two distinct sets. The most salient relationship of this sort is the
usual way that functions are defined as mathematical objects---namely, as a
relation between the input and output types. Thus, we can assert that `f` is a
function by building a relation $R$ such that if $x R y$ then $f x = y$. It's
roundabout and non-computable, but such is often the case when dealing with
mathematics:

```agda
  module Example₁ where
    IsFunction
        : {A : Set a} {B : Set b}
        → (f : A → B)
        → REL A B _
    -- TODO(sandy): not true! we need to show x is unique too
    IsFunction f A B = ∀ x y → f x ≡ y
```

Of course, this definition is somewhat cheating, since we already have a
function to begin with, and are just using it to construct a particular
relation. Nevertheless, definitions like these arise from what your brain looks
like without a healthy dose of respect for computability.

The relations we're much more familiar with, however, are *homogeneous*---those
which relate two elements of the same type. It is under this category that
things like equality and orderings fall. You will not be surprised to learn that
homogeneous relations are a special case of heterogeneous ones. In the Agda
standard library, this is known as `type:Rel`:

```agda
  Rel : Set a → (ℓ : Level) → Set (a ⊔ lsuc ℓ)
  Rel A ℓ = A → A → Set ℓ
```

As an illustration, we previously defined propositional equality in this way:

```agda
  module Example₂ where
    data _≡⅋₀_ {A : Set a} : A → A → Set a where
      refl : {x : A} → x ≡⅋₀ x
```

but we can instead give it this type, stressing the fact that it is a homogeneous
relation:

```agda
    data _≡⅋_ {A : Set a} : Rel A a where
      refl⅋ : {x : A} → x ≡⅋ x
```


## Equivalence Relations

It's a good habit to look for what generalizes whenever you notice something you
already understand is a special case of something more abstract. In this case,
how much of our understanding of propositional equality lifts to relations in
general?

Recall the three properties we showed about propositional equality: reflexivity,
symmetry, and transitivity. Reflexivity was the notion that every element is
equal to itself. Symmetry states that the left and right sides of equality are
equivalent, and that we can swap between them at will. Transitivity gives us a
sort of "composition" structure on equality, saying that we can combine two
proofs of equality into one, if they share an identical member between them.

You will not be surprised to learn that each of these properties makes sense for
a general relation, simply by replacing the phrase "is equal to" with "is in
relation with" above. Of course, not every relation satisfies each of these
properties, but having some shared vocabulary gives us things to look out for
when designing our own relations.

The first step is to formalize each of these notions. We can encode reflexivity
as a proposition about a given relation:


```agda
  private variable
    A : Set a

  Reflexive : Rel A ℓ → Set _
  Reflexive _~_ =
    ∀ {x} → x ~ x
```

We read this as saying "`_~_` is a reflexive relation if it satisfies the
property that for any `x`, it is the case that `x ~ x`." Symmetry and
transitivity follow similarly:

```agda
  Symmetric : Rel A ℓ → Set _
  Symmetric _~_ =
    ∀ {x y} → x ~ y → y ~ x

  Transitive : Rel A ℓ → Set _
  Transitive _~_ =
    ∀ {x y z} → x ~ y → y ~ z → x ~ z
```

As it happens, reflexivity, symmetry and transitivity are the definition
characteristics of an *equivalence relation*---that is a relation that behaves
like we expect equality to. We can *bundle* these properties together for a
given relation, to show that it is indeed an equivalence relation.

```agda
  record IsEquivalence
          {A : Set a} (_~_ : Rel A ℓ) : Set (a ⊔ ℓ) where
    field
      refl   : Reflexive   _~_
      sym    : Symmetric   _~_
      trans  : Transitive  _~_
```

It's easy to show that `type:_≡_` forms an equivalence relation, since we came up
with the idea by thinking about `type:_≡_` in the first place. The hardest part here
is wrangling the namespacing, since we now have two things called `ctor:refl`: the
specific definition for `type:_≡_`, and the abstract property from `type:IsEquivalence`.
We can dodge the issue by renaming the `module:PropositionalEquality` module down to
`module:PropEq`:

```agda
  module Example₃ where
    module PropEq = Chapter3-Proofs.Exports
```

at which point, building the proof that `type:_≡_` is an equivalence relationship is
trivial:

```agda
    open IsEquivalence

    ≡-equiv : IsEquivalence {A = A} _≡_
    refl   ≡-equiv = PropEq.refl
    trans  ≡-equiv = PropEq.trans
    sym    ≡-equiv = PropEq.sym
```

We will explore equivalence relations in further detail soon when we discuss
setoids.


## Fighting with Agda to Compute on Indices {#sec:fight-indices}

We have now spent several chapters discussing equality and inequality, but what
about things like "less than or equal to." *Orderings* like these are relations
in their own regard, and as you might expect, they are just as amenable to
formalization in Agda as their more exact counterparts.

A surprising amount of care is required in order to implement an ordering on the
natural numbers. There are many gotchas here that serve to illustrate a valuable
lesson in designing types in Agda, and so it is worthwhile to go slowly, take
our time, and learn what can go wrong.

How can we prove that one number is less than or equal to another? Recalling
that there do not exist any negative natural numbers, one possible way is to say
that $x \le y$ if there exists some $z$ such that $x + z = y$. Thus in order to
show reflexivity, we simply use $x = 0$. We can set this up, first by importing
our relation machinery from the standard library:

```agda
open import Relation.Binary
  using (Rel; Reflexive; Transitive; Symmetric; IsEquivalence)

module PropEq = Chapter3-Proofs.Exports

module Sandbox-Orderings where
  open import Data.Nat
    using (ℕ; _+_; zero; suc)
```

With surprising prescience, I can tell you that our first attempt at
implementing `type:_≤_` is going to fail, so let's make a new module and define our
type:

```agda
  module Naive-≤₁ where
    infix 4 _≤_
    data _≤_ : Rel ℕ lzero where
      lte : (a b : ℕ) → a ≤ a + b
```

To a first approximation, it seems to work:

```agda
    _ : 2 ≤ 5
    _ = lte 2 3
```

Indeed, Agda can even solve this for us via [`Auto`](AgdaCmd). One of the few
things we can prove about `type:_≤_` defined in this way is that `suc` is
*monotonic*---that is, that if `x ≤ y`, then `suc x ≤ suc y`:

```agda
    suc-mono : {x y : ℕ} → x ≤ y → suc x ≤ suc y
    suc-mono (lte x y) = lte (suc x) y
```

If you attempted to write this for yourself, you might have been surprised that
[`Refine`](AgdaCmd) refused to fill in the fill in the right-hand side with the
`ctor:lte` constructor, instead complaining about "no introduction forms found." This
is a little surprising, but the above definition does in fact work, so we will
not yet worry too much about it.

Things however, go much more wrong when we try to show `def:≤-refl`:

```wrong
    ≤-refl : Reflexive _≤_
    ≤-refl {x} = lte x 0
```

Attempting to do so presents us with the following error:

```info
x + 0 != x of type ℕ
when checking that the expression lte x 0 has type x ≤ x
```

Unperturbed, we can try hitting `def:≤-refl` with some of our other proof
techniques, and see if we can make progress on it in that way. Don't worry,
we'll circle back to this and see what has gone wrong, but for now, let's
proceed with naught but brute force and ignorance. Instead, we can try splitting
on `x`:

```agda
    ≤-refl⅋₀ : Reflexive _≤_
    ≤-refl⅋₀ {zero} = lte zero zero
    ≤-refl⅋₀ {suc x} = ?
```

We clearly need recursion here, so we can try a `with` abstraction:

```agda
    ≤-refl⅋₁ : Reflexive _≤_
    ≤-refl⅋₁ {zero} = lte zero zero
    ≤-refl⅋₁ {suc x} with ≤-refl⅋₁ {x}
    ... | x≤x = ?
```

The usual response now is to try pattern matching on `z`. But attempting to do
so completely fails, with the mysterious problem:

```info
I'm not sure if there should be a case for the constructor lte,
because I get stuck when trying to solve the following unification
problems (inferred index ≟ expected index):
  x₁ ≟ x₂
  x₁ + y ≟ x₂
Possible reason why unification failed:
  Cannot solve variable x₁ of type ℕ with solution x₁ + y because the
  variable occurs in the solution, or in the type of one of the
  variables in the solution.
when checking that the expression ? has type suc x ≤ suc x
```

Not to be discouraged, we spot that `x≤x` has a satisfactory type for us to
invoke `def:suc-mono` and be done with the proof:

```agda
    ≤-refl : Reflexive _≤_
    ≤-refl {zero} = lte zero zero
    ≤-refl {suc x} with ≤-refl {x}
    ... | x≤x = suc-mono x≤x
```


## Substitution

A surprising number of things went wrong when putting together such a simple
proof. Let's analyze them together to see what exactly happened. Recall our
original implementation:

```wrong
    ≤-refl : Reflexive _≤_
    ≤-refl {x} = lte x 0
```

with the error:

```info
x + 0 != x of type ℕ
when checking that the expression lte x 0 has type x ≤ x
```

The problem here is that `lte x 0` has type `x ≤ x + 0`, but we are trying to
assign to `def:≤-refl` which has type `x ≤ x`. You and I know these are the same
thing, but recall that we did have to prove `def:+-identityʳ` all those chapters ago
in order to convince Agda of this exact fact. There does exist standard (though
heavy-handed) machinery for rewriting propositional equalities at the
type-level, like is required here. This machinery is called `def:subst`, short for
*substitution*:

```agda
    open PropEq using (refl)

    subst
        : {A : Set} {x y : A}
        → (P : A → Set)  -- ! 1
        → x ≡ y
        → P x → P y
    subst _ refl px = px
```

You can think of `def:subst` as a type-level `def:cong`, as it serves the same purpose.
At [1](Ann) it takes an argument `P` which is responsible for pointing out where
you'd like the substitution to happen. To illustrate this, we can implement
`def:≤-refl` via `def:subst`, though the experience is decidedly less than wholesome:

```agda
    open Chapter3-Proofs.Exports
     using (+-identityʳ)

    ≤-refl′ : Reflexive _≤_
    ≤-refl′ {x} = subst (x ≤_) (+-identityʳ x) (lte x 0)
```

It's nice to know about `def:subst`, but as a good rule of thumb, if you find
yourself reaching for it more than a handful of times, you've painted yourself
into a corner when you originally put together a definition somewhere. Requiring
substitution is usually a symptom of an upstream problem.


## Unification

But not every problem we saw when implementing `def:≤-refl` for the first time can
be solved via `def:subst`. Recall our attempt to pattern match on `x≤x` in the
following:

```agda
    ≤-refl⅋₂ : Reflexive _≤_
    ≤-refl⅋₂ {zero} = lte zero zero
    ≤-refl⅋₂ {suc x} with ≤-refl⅋₂ {x}
    ... | x≤x = ?
```

to which Agda replies:

```info
I'm not sure if there should be a case for the constructor lte
```

Of course there should be a case for the constructor `ctor:lte`, since it's *the only
constructor.* But what has gone wrong here, and what can we do about it? The
problem is that Agda usually really good at pattern matching, and elides
impossible patterns if the constructor doesn't match. In this case, Agda can't
decide if the `ctor:lte` constructor *should definitely* be there, or should
definitely *not be.*

Internally, Agda implements this functionality by attempting to *unify* the
indices on type's constructors with the indices of your expression. In this
case, we have `x≤x : x ≤ x`, which Agda needs to unify (match syntactically)
against `ctor:lte` whose eventual indices are `?a ≤ ?a + ?b` (after some renaming to
avoid confusion.) This sets up the following series of equations that Agda must
solve:

$$
\begin{aligned}
?a \mathrel{\sim}& x \\
?a + ?b \mathrel{\sim}& x
\end{aligned}
$$

where `~` means "unifies to" rather than being used as a generic name for a
relation like we did above. In order to correctly determine if a constructor
needs to exist in a pattern match, every *metavariable* (here, `?a` and `?b`)
must unify to something. While it's easy to unify `?a` with `x` from the first
equation, there is no way to syntactically match `?a + ?b` with `x`. Even after
replacing `?a`, we get `x + ?b = x`.

-- TODO(sandy): THE ABOVE PARAGRAPH IS NOT TRUE


You and I know that the only solution to this problem is that `?b = 0`, but this
is a statement about number theory, and Agda doesn't know anything about number
theory. In its pattern checker, all it knows about is computation and syntax,
neither of which is of use here. So, because there is no way to syntactically
assign an expression to `?b`, Agda gets stuck and throws up its hands in
confusion.

One possible solution here would be for Agda to simply allow you to give cases
that it can't be sure about, but this leads to downstream typechecking issues
that would make the implementation of Agda significantly harder. Since the
reasons you might want to do this as a user are dubious at best, Agda doesn't
support it, and requires you to find alternative ways to convince the language
that you are doing meaningful things. We will not investigate those alternative
ways here, except to point out how to avoid the situation altogether.


## Overconstrained by Dot Patterns {#sec:dot-patterns}

But first, one last subtle point about unification. Rather surprisingly, we
successfully implemented `def:suc-mono`, without encountering the dreaded "not sure
if there should be a case" problem. How can that have happened? We can get a
sense of the unification algorithm going on behind the scenes by explicitly
binding our implicit arguments:

```agda
    suc-mono′⅋₀ : {x y : ℕ} → x ≤ y → suc x ≤ suc y
    suc-mono′⅋₀ {x} {y} x≤y = ?
```

Doing a [`MakeCase:x≤y`](AgdaCmd) in this hole will correctly split apart the
`x≤y`, but in doing so, will also leave behind dot patterns for variables that
it unified in the process. Recall that dot patterns correspond to equalities
that must hold due to evidence being matched on somewhere else, so this is a
good way to see what Agda has solved.

```agda
    suc-mono′⅋₁ : {x y : ℕ} → x ≤ y → suc x ≤ suc y
    suc-mono′⅋₁ {x} {.(x + b)} (lte .x b) = lte (suc x) b
```

It's worth going through the constraints being solved here. In splitting `ctor:lte`,
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

Rather interestingly, we can implement a monomorphic version of `def:suc-mono′⅋₁` by
restricting its type:

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

> isovector: i've picked up the folklore that one shouldn't use computing terms as type indices because it gets agda stuck when you try to pattern match on it
>
> isovector: this is true but it's not really the full story
>
> isovector: the problem is not the computation per se, it's that when you pattern match and bring these constraints into scope, the only solution agda has is to introduce a dot pattern
>
> isovector: the dot pattern reifies the constraint at the cost of eliminating one of your variables
>
> isovector: eventually you run out of free variables and there's nowhere else to stick an additional constraint, and then agda says "sorry, i don't know if there should be a constructor"
>
> isovector: when you have a constructor index instead, agda doesn't need the dot pattern and so you get to keep your variables free
>
> isovector: and thus you avoid overconstraining the solution space

-- TODO(sandy): hammer home this point somewhere (but maybe not here)


## Ordering the Natural Numbers

What should be the takeaway from this extremely long digression on Agda's sharp
edges when it comes to indexed data types? It's that when you pattern match on a
type index that contains a computation, Agda replaces a variable with a dot
pattern for each constraint, and if you ever run out of variables, Agda gives up
and refuses to pattern match on your constructor.

The solution here is to prevent Agda from introducing dot patterns, and the
simplest way to do *that* is to only ever use *constructors* as indices to your
data type.

---

splice me in, papa

## Comparing Natural Numbers {#sec:comparing}

While that's quite enough about equality, we we would like to say something
about inequalities---in this case, the sort that describe when one number is
less than or equal to another.

The first thing to notice is that this is not a *general* notion---it is very
much tied to the natural numbers. We can't build generic machinery that would
allow us to say a value of some arbitrary type is less than some other value of
the same. While there are many types that *do* admit the notion of an ordering
relationship, the nature of that relationship must be specialized for each
type. Besides, we don't even have a guarantee such an ordering would be
unique---for example, we might choose to order strings lexicographically or by
length. One might be the more familiar choice, but it's hard to argue that one
is *more correct* than the other.

With that being said, how can we give a type that relates one number to all the
numbers greater than (or equal) to it?

A good way to proceed here is to work backwards; starting from each constructor,
to determine how to use that to show a less-than-or-equal-to relationship. The
case of `ctor:zero` is easy, since `ctor:zero` is the smallest element, we have
the case that `ctor:zero` `type:≤` `n`, for any other number `n`!

In the case of `ctor:suc`, we know that `ctor:suc` `m` `type:≤` `ctor:suc` `n`
if and only if `m` `type:≤` `n` in the first place. This gives rise to a very
natural type:

```agda
module Definition-LessThanOrEqualTo where
  data _≤_ : ℕ → ℕ → Set where
    z≤n : {n : ℕ} → zero ≤ n
    s≤s : {m n : ℕ} → m ≤ n → suc m ≤ suc n
```

Hidden

:     ```agda
  -- fix expr
      ```

We can now try to prove that `expr:2 ≤ 5`. Begin with a quick type:

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
new hole, and you will see it has type `expr: 1 ≤ 4`! By using `ctor:s≤s`, Agda
has moved *both* sides of the inequality closer to zero. It makes sense when you
stare at the definition of `ctor:s≤s`, but it's a rather magical thing to behold
for the first time.

Use another `ctor:s≤s` in the hole:

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

We will have much more to say about the `type:_≤_` type in @sec:fight-indices,
where we will explore why exactly we chose this particular encoding, and what
goes wrong if we were to make a different choice. For now, however, try your
hand at proving the reflexivity and transitivity of `type:_≤_`:


Exercise (Trivial)

:   Prove `def:≤-refl` `:` `expr:{x : ℕ} → x ≤ x`.


Solution

:   ```agda
  ≤-refl : {x : ℕ} → x ≤ x
  ≤-refl {zero}   = z≤n
  ≤-refl {suc x}  = s≤s ≤-refl
    ```


Exercise (Easy)

:   Prove `def:≤-trans` `:` `expr:(x y z : ℕ) → x ≤ y → y ≤ z → x ≤ z`.

:     ```agda
  ≤-trans : {x y z : ℕ} → x ≤ y → y ≤ z → x ≤ z
  ≤-trans {zero} x≤y y≤z       = z≤n
  ≤-trans (s≤s x≤y) (s≤s y≤z)  = s≤s (≤-trans x≤y y≤z)
      ```

Exercise (Trivial)

:   Prove `def:≤-suc` `:` `expr:(x : ℕ) → x ≤ suc x`.

:     ```agda
  ≤-suc : (x : ℕ) → x ≤ suc x
  ≤-suc zero     = z≤n
  ≤-suc (suc x)  = s≤s (≤-suc x)
      ```

Sometimes we might want a *strict* less-than, without any of this "or equal to"
stuff. That's easy enough; we can just insert a `ctor:suc` on the right side:

```agda
  _<_ : ℕ → ℕ → Set
  m < n = m ≤ suc n
```



--
--
--

What does this mean in the context of giving a `type:_≤_` ordering on natural
numbers? Recall that `type:_≤_` is indexed by two naturals, and so we must build our
indices out of only `zero` and `suc`. This is a dramatic constraint on the forms
that our datatype can take, and it subsequently informs the entire definition.

```agda
module Definition-LessThanOrEqualTo2 where
  private variable
    m n p : ℕ

  data _≤_ : Rel ℕ lzero where
    z≤n : zero ≤ n
    s≤s : m ≤ n → suc m ≤ suc n
  infix 4 _≤_
```

With only constructors to be found in our indices, we have successfully fended
off all of Agda's future complains that it might not know how to pattern match
on `type:_≤_`. We can now return our attention to determining which of the relation
properties hold for `type:_≤_`. As we have seen before, reflexivity holds, and is now
much easier to implement:

```agda
  ≤-refl : Reflexive _≤_
  ≤-refl {zero}   = z≤n
  ≤-refl {suc x}  = s≤s ≤-refl
```

We also have transitivity:

```agda
  ≤-trans : Transitive _≤_
  ≤-trans z≤n n≤p = z≤n
  ≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)
```

What about symmetry? A moment's thought convinces us that there is no symmetry
for `type:_≤_`. Just because $2 \le 5$ doesn't mean that $5 \le 2$. However, this
relation does satisfy a related notion, that of *antisymmetry.* Antisymmetry
says that if we know $m \le n$ and that $n \le m$, then the only solution is if
$m = n$. This is not very hard to show:

```agda
  ≤-antisym : m ≤ n → n ≤ m → m ≡ n
  ≤-antisym z≤n z≤n = PropEq.refl
  ≤-antisym (s≤s m≤n) (s≤s n≤m) =
    cong suc (≤-antisym m≤n n≤m)
```

In addition, we can generalize this type to something more reusable, like we did
with `type:Reflexive`, `type:Symmetric` and `type:Transitive`. This one is a
little trickier, since it's really a property of *two* relations: one
corresponding to equality, and another to the ordering:

```agda
  private variable
    a ℓ ℓ₁ ℓ₂ : Level
    A : Set a

  Antisymmetric
      : Rel A ℓ₁
      → Rel A ℓ₂
      → Set _
  Antisymmetric _≈_ _≤_ =
    ∀ {x y} → x ≤ y → y ≤ x → x ≈ y
```

Because `type:_≤_` is not symmetric, it can't possibly be an equivalence relation.
But it does have reflexivity and transitivity, which is still quite a lot of
structure! When you start looking for relations with reflexivity and
transitivity, but no symmetry, you immediately find a bevy of directed
relationships.

In fact, relations of this form---namely, relations that satisfy reflexivity and
transitivity---are so common that they have a bespoke name. We call such things
*preorders:*


```agda
  record IsPreorder
          {A : Set a} (_~_ : Rel A ℓ) : Set (a ⊔ ℓ) where
    field
      refl   : Reflexive   _~_
      trans  : Transitive  _~_
```


## Making Suggestions to Agsy

We have already done the work to show that `type:_≤_` is a preorder, namely
`≤-refl` and `≤-trans`. Bundling them up into a `type:IsPreorder` isn't very
challenging, and [`Auto:≤-refl ≤-trans`](AgdaCmd) will actually write the
necessary definition for you:

```agda
  ≤-preorder⅋₀ : IsPreorder _≤_
  ≤-preorder⅋₀ = {! ≤-refl ≤-trans !}
```

which results in:

```agda
  ≤-preorder⅋₁ : IsPreorder _≤_
  ≤-preorder⅋₁ = record { refl = ≤-refl ; trans = ≤-trans }
```

As you can see, we can put suggestions for [`Auto`](AgdaCmd) inside the hole,
and Agda will attempt to use those identifiers when attempting to synthesize
terms.


## Copatterns {#sec:copatterns}

The definition given for `def:≤-preorder⅋₁` above is somewhat unsatisfactory, as
it requires us to explicitly construct an object using `keyword:record` syntax.
This is not our only option, however. Instead of defining a product type all at
once, we can instead define every *projection* (field) out of it. Recall that in
Agda, a record type is *nothing more* than its constituent fields, and so this
is less crazy of a notion than it seems.

We can ask Agda to perform a copattern match for us by asking it to
[`MakeCase`](AgdaCmd) in a hole whose type is a record. To illustrate this,
position your cursor on the hole:

```agda
  ≤-preorder⅋₂ : IsPreorder _≤_
  ≤-preorder⅋₂ = ?
```

and perform a [`MakeCase:`](AgdaCmd). Agda will replace the definition of
`def:≤-preorder⅋₂` with two copattern matches: one for every field of the
record.

```agda
  ≤-preorder⅋₃ : IsPreorder _≤_
  IsPreorder.refl   ≤-preorder⅋₃ = {! !}
  IsPreorder.trans  ≤-preorder⅋₃ = {! !}
```

These holes are easily filled, as before:

```agda
  ≤-preorder : IsPreorder _≤_
  IsPreorder.refl   ≤-preorder = ≤-refl
  IsPreorder.trans  ≤-preorder = ≤-trans
```

Agda is almost unique among programming languages in its support for copattern
matching. Better yet, copatterns play nicely with patterns, and you can do a
pattern match inside a copattern, or a copattern match after first splitting
some variables into their constituent constructors.

Copatterns give rise to a dualistic perspective for thinking about records.
While building a value out of `keyword:record` syntax, we are making an
assertion about what that thing *is.* Contrast that against a value defined via
copatterns, in which we are making assertions only on the *observations that can
be made of the value.* Constraining only the observations is much less of an ask
than defining something's entire identity. As an illustration, defining only the
observations gives permission tot he compiler to do whatever it wants behind the
scenes, so long as you can't "catch it in action."

The Agda standard library uses copatterns to great effect, and we will not shy
away from them henceforth. Their use allows us to separate the work of building
an object into its constituent pieces, which can help make the task more
manageable.


Exercise

:   As an easy exercise, show that every equivalence relation gives rise to a
    preorder. That is, give a function `type:IsEquivalence _~_ → IsPreorder
    _~_`. Use copattern matching to implement this function.


Solution

:         ```agda
  equiv→preorder : {_~_ : Rel A ℓ}
                 → IsEquivalence _~_ → IsPreorder _~_
  IsPreorder.refl  (equiv→preorder x) = IsEquivalence.refl   x
  IsPreorder.trans (equiv→preorder x) = IsEquivalence.trans  x
          ```


## Graph Reachability

We have shown that `type:_≤_` forms a preorder. From this you might be tempted
to think that preorders are just tools that generalize ordering over the number
line. Not so. Let's look at another example to break that intuition.

Consider a graph. Math textbooks often begin a discussion around graphs with the
telltale phrase

> Let $G = (V, E)$ be a graph with vertices $V$ and edges $E$.

Left completely unsaid in this introduction is that $E$ is in fact a *relation*
on $V$; given a graph with vertices $V$, it really ought to be the case that the
edges are actually between the vertices!

As a computer scientist, you probably have implemented a graph before at some
point, whether it be via pointer-chasing or an adjacency matrix. These are
indeed encodings of graphs, but they are concessions to computability, which we
need not pay attention to. In order to work with graphs in Agda, all we need is
some set `type:V` and an edge relation `type:_⇒_` over it:

```agda
  module Reachability
        {e ℓ : Level} {V : Set ℓ} (_⇒_ : Rel V e)
      where
```

What can we say about `type:_⇒_`? Does it satisfy any of the usual relation
properties? Think on that question for a moment before continuing.

Does `type:_⇒_` satisfy any relation properties? The question is not even wrong.
`type:_⇒_` might, or it might not. But it is a *parameter* to this example,
which means it is completely opaque to us, and all we can say about it is that
which we asked for in the first place. Given the definition, all we can say for
sure about `type:_⇒_` is that it's a relation over `type:V`.

However, what we can do is construct a new relation on top of `type:_⇒_`, and
stick whatever we'd like into that thing. One salient example here is the notion
of *reachability*---given a starting vertex, is their a path to some other
vertex? Perhaps you were already thinking about reachability when I asked
earlier about properties over `type:_⇒_`---after all, this is a very common
operation over graphs. The distinction between the relation `type:_⇒_` and the
reachable relation on top of it is subtle but important: while there is no
single road (edge) that connects Vancouver to New York, there is certainly a
path that connects them!

So when is one vertex reachable from another? The trivial case is if you're
already where you'd like to be. Another case is to simply follow an edge.
Finally, if we know an intermediary vertex is reachable from our starting point,
and that the goal is reachable from there, we can connect the two paths. This
gives rise to a very straightforward definition:

```agda
    private variable
      v v₁ v₂ v₃ : V

    data Path : Rel V (e ⊔ ℓ) where
      here    : Path v v
      follow  : v₁ ⇒ v₂ → Path v₁ v₂
      connect
        : Path v₁ v₂
        → Path v₂ v₃
        → Path v₁ v₃
```

It is not difficult to show that `type:Path` forms a preorder:

```agda
    Path-preorder : IsPreorder Path
    IsPreorder.refl   Path-preorder = here
    IsPreorder.trans  Path-preorder = connect
```

This technique is very general and reusable. We were given some arbitrary
relation `type:_⇒_`, and built additional structure on top of it for free. The
construction is merely *syntactic,* in that we simply added new constructors
corresponding exactly to the desired structure. In doing so, we have deftly
sidestepped the issue of articulating exactly what these new constructors *mean*
in the original domain, if anything. This is a problem we will return to when we
discuss *free constructions* in @sec:free.


## Preorder Reasoning {#sec:preorder-reasoning}

Recall that in this chapter, we have looked at equivalence relations as a
special case of equality, and further noted that preorders are equivalence
relations that don't require symmetry. In @sec:equational-reasoning, we built
equational reasoning tools for working with propositional equality. However,
that reasoning machinery used only `def:refl` and `def:trans`, without a hint of
`def:sym` to be seen! Thus, our previously-defined equational reasoning
machinery has too-specific types, since it will work for any preorder
whatsoever!

Begin with a new module for the reasoning, parameterized by a `type:IsPreorder`.

```agda
  module PreorderReasoning
        {_~_ : Rel A ℓ} (~-preorder : IsPreorder _~_)
        where
```

We can bring the record fields of `type:IsPreorder` into scope by opening it as
a module:

```agda
    open IsPreorder ~-preorder public
```

This will bring the `field:refl` and `field:trans` fields from `~-preorder` into
scope. Additionally, postfixing the module directive with `keyword:public` means
that `field:refl` and `field:trans` will also be brought into scope for anyone
who opens `module:PreorderReasoning`. In essence, `keyword:public` makes it as
if we explicitly defined the imported identifiers in this module.

The rest of this machinery will be presented without further commentary, as
there is nothing new here, except that we have replaced `type:_≡_` with `~`, and
renamed `def:_≡⟨_⟩_` to `def:_≈⟨_⟩_`.

```agda
    begin_ : {x y : A} → x ~ y → x ~ y
    begin_ x~y = x~y
    infix 1 begin_

    _∎ : (x : A) → x ~ x
    _∎ x = refl
    infix 3 _∎

    _≡⟨⟩_ : (x : A) → {y : A} → x ~ y → x ~ y
    x ≡⟨⟩ p = p
    infixr 2 _≡⟨⟩_

    _≈⟨_⟩_ : (x : A) → ∀ {y z} → x ~ y → y ~ z → x ~ z
    _ ≈⟨ x~y ⟩ y~z = trans x~y y~z
    infixr 2 _≈⟨_⟩_
```

However, we would like to make one additional change to this interface, which is
to make it play nicely with propositional equality. If we happen to know that
two terms are propositionally equal, it would be nice to be able to use that
fact in a reasoning block. Thus, we also include `def:_≡⟨_⟩_`:

```agda
    open PropEq using (refl)

    _≡⟨_⟩_ : (x : A) → ∀ {y z} → x ≡ y → y ~ z → x ~ z
    _ ≡⟨ refl ⟩ y~z = y~z
    infixr 2 _≡⟨_⟩_
```

Any code wanting to do equational reasoning over a preorder is now able to, it
need only `keyword:open` the `module:PreorderReasoning` module using its proof
of being a preorder (that is, `type:IsPreorder`) as an argument.


## Example from a Film

We can use this new preorder equational reasoning in order to show how two
people might know one another across a social graph. Rather than incriminate any
real group of humans, we can instead use the excellent early noughties' film
"About a Boy" as a case study. If you haven't seen the film, you should consider
remedying that as soon as possible. But don't worry, there will be no spoilers
here so it's safe to continue.

The first thing to do is to define the vertices of the social graph, which of
course are the people involved:

```agda
  module Example-AboutABoy where
    data Person : Set where
      ellie fiona marcus rachel susie will : Person
```

Some of these people are friends, which we can use as edges in our graph:

```agda
    private variable
      p₁ p₂ : Person

    data _IsFriendsWith_ : Rel Person lzero where
      marcus-will   : marcus  IsFriendsWith will
      fiona-marcus  : fiona   IsFriendsWith marcus
      fiona-susie   : fiona   IsFriendsWith susie
```

and of course, friendship is symmetric, which we can encode as another
constructor:

```agda
      sym : p₁ IsFriendsWith p₂ → p₂ IsFriendsWith p₁
```

What excellent romantic comedy from the early noughties is complete without a
series of potential love interests? We can enumerate who likes whom as another
source of edges in our graph:

```agda
    data _IsInterestedIn_ : Rel Person lzero where
      marcus-ellie  : marcus  IsInterestedIn ellie
      will-rachel   : will    IsInterestedIn rachel
      rachel-will   : rachel  IsInterestedIn will
      susie-will    : susie   IsInterestedIn will
```

Finally, we can tie together `type:_IsFriendsWith_` and `type:_IsInterestedIn_`
with `type:SocialTie` which serves as the definitive set of edges in our graph.

```agda
    data SocialTie : Rel Person lzero where
      friendship  : p₁ IsFriendsWith p₂   → SocialTie p₁ p₂
      interest    : p₁ IsInterestedIn p₂  → SocialTie p₁ p₂
```

There is no preorder on `type:SocialTie`, but we can get one for free by using
`type:Path`. Then it's possible to ask how `ctor:will` and `ctor:fiona` are
related:

```agda
    open Reachability SocialTie

    will-fiona : Path will fiona
    will-fiona = begin
      will    ≈⟨ follow (friendship (sym marcus-will)) ⟩
      marcus  ≈⟨ follow (friendship (sym fiona-marcus)) ⟩
      fiona   ∎
      where open PreorderReasoning (Path-preorder)
```

or how `ctor:rachel` and `ctor:ellie` are:

```agda
    rachel-ellie : Path rachel ellie
    rachel-ellie = begin
      rachel  ≈⟨ follow (interest rachel-will) ⟩
      will    ≈⟨ follow (friendship (sym marcus-will)) ⟩
      marcus  ≈⟨ follow (interest marcus-ellie) ⟩
      ellie   ∎
      where open PreorderReasoning (Path-preorder)
```


## Reasoning over `≤`

Let's quickly prove a non-trivial fact about the natural numbers, namely that $n
\le n + 1$. You should be able to do this sort of thing in your sleep by now:

```agda
  n≤1+n : (n : ℕ) → n ≤ 1 + n
  n≤1+n zero = z≤n
  n≤1+n (suc n) = s≤s (n≤1+n n)
```

We can further use this fact and our preorder reasoning in order to show that $n
\le n + 1$:

```agda
  open Chapter3-Proofs.Exports using (+-comm)

  n≤n+1⅋₀ : (n : ℕ) → n ≤ n + 1
  n≤n+1⅋₀ n = begin
    n      ≈⟨ n≤1+n n ⟩  -- ! 1
    1 + n  ≡⟨ +-comm 1 n ⟩
    n + 1  ∎
    where open PreorderReasoning (≤-preorder)
```

The proof here is fine, but the syntax leaves much to be desired. Notice that at
[1](Ann) we are required to use `def:_≈⟨_⟩_` to show that `n ≤ 1 + n`. This
makes sense to us, since we have just gone through the work of defining preorder
reasoning. But any hapless soul who happens wander in and look at this proof
without much context will find themself completely flummoxed. While `≈` is a
reasonable name for a *generic* preorder, many preorders have existing names that
it would be preferable to reuse.

Fortunately, Agda comes to our rescue, and allows us to rename identifiers when
we import them. We can improve our syntax in the definition of `def:n≤n+1⅋₀` at
the cost of more boilerplate in the `keyword:where` clause:

```agda
  n≤n+1⅋₁ : (n : ℕ) → n ≤ n + 1
  n≤n+1⅋₁ n = begin
    n      ≤⟨ n≤1+n n ⟩
    1 + n  ≡⟨ +-comm 1 n ⟩
    n + 1  ∎
    where open PreorderReasoning ≤-preorder
            renaming (_≈⟨_⟩_ to _≤⟨_⟩_)
```

As one final trick, we can package up this choice of `def:≤-preorder` and
subsequent `keyword:renaming` by sticking it into a new module with a public
open:

```agda
  module ≤-Reasoning where
    open PreorderReasoning ≤-preorder
      renaming (_≈⟨_⟩_ to _≤⟨_⟩_)
      public
```

By now using `module:≤-Reasoning` directly, our proof is much cleaner, and
therefore much more delightful:

```agda
  n≤n+1 : (n : ℕ) → n ≤ n + 1
  n≤n+1 n = begin
    n      ≤⟨ n≤1+n n ⟩
    1 + n  ≡⟨ +-comm 1 n ⟩
    n + 1  ∎
    where open ≤-Reasoning
```

Don't be afraid to introduce helper modules that put a specific spin on more
general notions. Their judicious use can dramatically improve the developer
experience, whether the developer be you or a user of your library.


## Wrapping Up

```agda
module Exports where
  open import Agda.Primitive
    using (Level; _⊔_; lzero; lsuc)
    public

  open import Data.Nat
    using (_≤_; z≤n; s≤s; _<_)
    public

  open import Data.Nat.Properties
    using (≤-refl; ≤-trans)
    public
```
