# Structured Sets

Hidden

:   ```agda
{-# OPTIONS --allow-unsolved-metas #-}
    ```

```agda
module 4-setoids-redo where
```

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
open import Data.Product using (_×_)

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
open import Level
  using (Level; _⊔_)
  renaming (zero to lzero; suc to lsuc)

module Sandbox-Relations where
  private variable
    a b ℓ : Level

  REL : Set a → Set b → (ℓ : Level) → Set (a ⊔ b ⊔ lsuc ℓ)
  REL A B ℓ = A → B → Set ℓ
```

This `REL` is the type of *heterogeneous* relations, that is, relationships
between two distinct sets. The most salient relationship of this sort is the
usual way that functions are defined as mathematical objects---namely, as a
relation between the input and output types. Thus, we can assert that `f` is a
function by building a relation $R$ such that if $x R y$ then $f x = y$. It's
roundabout and non-computable, but such is often the case when dealing with
mathematics:

```agda
  module Example₁ where
    open import Relation.Binary.PropositionalEquality
      using (_≡_)

    IsFunction
        : {A : Set a} {B : Set b}
        → (f : A → B)
        → REL A B _
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
standard library, this is known as `Rel`:

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
    data _≡_ {A : Set a} : Rel A a where
      refl : {x : A} → x ≡ x
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
      refl : Reflexive _~_
      sym : Symmetric _~_
      trans : Transitive _~_
```

It's easy to show that `_≡_` forms an equivalence relation, since we came up
with the idea by thinking about `_≡_` in the first place. The hardest part here
is wrangling the namespacing, since we now have two things called `refl`: the
specific definition for `_≡_`, and the abstract property from `IsEquivalence`.
We can dodge the issue by renaming the `PropositionalEquality` module down to
`PropEq`:

```agda
  module Example₃ where
    import Relation.Binary.PropositionalEquality
      as PropEq
    open PropEq using (_≡_)
```

at which point, building the proof that `_≡_` is an equivalence relationship is
trivial:

```agda
    open IsEquivalence

    ≡-equiv : IsEquivalence {A = A} _≡_
    refl  ≡-equiv = PropEq.refl
    trans ≡-equiv = PropEq.trans
    sym   ≡-equiv = PropEq.sym
```

We will explore equivalence relations in further detail soon when we discuss
setoids.


## Fighting with Agda to Compute on Indices

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
module Sandbox-Orderings where
  open import Relation.Binary
    using (Rel; Reflexive; Transitive; Symmetric)

  open import Data.Nat
    using (ℕ; _+_; zero; suc)
```

With surprising prescience, I can tell you that our first attempt at
implementing `_≤_` is going to fail, so let's make a new module and define our
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
things we can prove about `_≤_` defined in this way is that `suc` is
*monotonic*---that is, that if `x ≤ y`, then `suc x ≤ suc y`:

```agda
    suc-mono : {x y : ℕ} → x ≤ y → suc x ≤ suc y
    suc-mono (lte x y) = lte (suc x) y
```

If you attempted to write this for yourself, you might have been surprised that
[`Refine`](AgdaCmd) refused to fill in the fill in the right-hand side with the
`lte` constructor, instead complaining about "no introduction forms found." This
is a little surprising, but the above definition does in fact work, so we will
not yet worry too much about it.

Things however, go much more wrong when we try to show `≤-refl`:

```wrong
    ≤-refl : Reflexive _≤_
    ≤-refl {x} = lte x 0
```

Attempting to do so presents us with the following error:

```info
x + 0 != x of type ℕ
when checking that the expression lte x 0 has type x ≤ x
```

Unperturbed, we can try hitting `≤-refl` with some of our other proof
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
invoke `suc-mono` and be done with the proof:

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
assign to `≤-refl` which has type `x ≤ x`. You and I know these are the same
thing, but recall that we did have to prove `+-identityʳ` all those chapters ago
in order to convince Agda of this exact fact. There does exist standard (though
heavy-handed) machinery for rewriting propositional equalities at the
type-level, like is required here. This machinery is called `subst`, short for
*substitution*:

```agda
    open import Relation.Binary.PropositionalEquality
      using (_≡_; refl)

    subst
        : {A : Set} {x y : A}
        → (P : A → Set)  -- ! 1
        → x ≡ y
        → P x → P y
    subst _ refl px = px
```

You can think of `subst` as a type-level `cong`, as it serves the same purpose.
At [1](Ann) it takes an argument `P` which is responsible for pointing out where
you'd like the substitution to happen. To illustrate this, we can implement
`≤-refl` via `subst`, though the experience is decidedly less than wholesome:

```agda
    open import Data.Nat.Properties
     using (+-identityʳ)

    ≤-refl′ : Reflexive _≤_
    ≤-refl′ {x} = subst (x ≤_) (+-identityʳ x) (lte x 0)
```

It's nice to know about `subst`, but as a good rule of thumb, if you find
yourself reaching for it more than a handful of times, you've painted yourself
into a corner when you originally put together a definition somewhere. Requiring
substitution is usually a symptom of an upstream problem.


## Unification

But not every problem we saw when implementing `≤-refl` for the first time can
be solved via `subst`. Recall our attempt to pattern match on `x≤x` in the
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

Of course there should be a case for the constructor `lte`, since it's *the only
constructor.* But what has gone wrong here, and what can we do about it? The
problem is that Agda usually really good at pattern matching, and elides
impossible patterns if the constructor doesn't match. In this case, Agda can't
decide if the `lte` constructor *should definitely* be there, or should
definitely *not be.*

Internally, Agda implements this functionality by attempting to *unify* the
indices on type's constructors with the indices of your expression. In this
case, we have `x≤x : x ≤ x`, which Agda needs to unify (match syntactically)
against `lte` whose eventual indices are `?a ≤ ?a + ?b` (after some renaming to
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


## Overconstrained by Dot Patterns

But first, one last subtle point about unification. Rather surprisingly, we
successfully implemented `suc-mono`, without encountering the dreaded "not sure
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

It's worth going through the constraints being solved here. In splitting `lte`,
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
`suc-mono′⅋₁` above.

Rather interestingly, we can implement a monomorphic version of `suc-mono′⅋₁` by
restricting its type:

```agda
    suc-mono-mono⅋₁ : {x : ℕ} → x ≤ x → suc x ≤ suc x
    suc-mono-mono⅋₁ = suc-mono′⅋₁
```

but we *cannot* inline the definition of `suc-mono′⅋₁` here, since we will get
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

What does this mean in the context of giving a `_≤_` ordering on natural
numbers? Recall that `_≤_` is indexed by two naturals, and so we must build our
indices out of only `zero` and `suc`. This is a dramatic constraint on the forms
that our datatype can take, and it subsequently informs the entire definition.

A good way to proceed here is to work backwards; starting from each constructor,
to determine how to use that to show a less-than-or-equal-to relationship. The
case of zero is easy, since zero is the smallest element, it must be `_≤_` any
other number. We have already shown the `suc` case earlier, namely `≤-suc` which
states that if `m ≤ n`, then `suc m ≤ suc n`:

```agda
  private variable
    m n p : ℕ

  data _≤_ : Rel ℕ lzero where
    z≤n : zero ≤ n
    s≤s : m ≤ n → suc m ≤ suc n
```

With only constructors to be found in our indices, we have successfully fended
off all of Agda's future complains that it might not know how to pattern match
on `_≤_`. We can now return our attention to determining which of the relation
properties hold for `_≤_`. As we have seen before, reflexivity holds, and is now
much easier to implement:

```agda
  ≤-refl : Reflexive _≤_
  ≤-refl {zero} = z≤n
  ≤-refl {suc x} = s≤s ≤-refl
```

We also have transitivity:

```agda
  ≤-trans : Transitive _≤_
  ≤-trans z≤n n≤p = z≤n
  ≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)
```

What about symmetry? A moment's thought convinces us that there is no symmetry
for `_≤_`. Just because $2 \le 5$ doesn't mean that $5 \le 2$. However, this
relation does satisfy a related notion, that of *antisymmetry.* Antisymmetry
says that if we know $m \le n$ and that $n \le m$, then the only solution is if
$m = n$. This is not very hard to show:

```agda
  import Relation.Binary.PropositionalEquality as PropEq
  open PropEq using (_≡_; cong)

  ≤-antisym : m ≤ n → n ≤ m → m ≡ n
  ≤-antisym z≤n z≤n = PropEq.refl
  ≤-antisym (s≤s m≤n) (s≤s n≤m) =
    cong suc (≤-antisym m≤n n≤m)
```

In addition, we can generalize this type to something more reusable, like we did
with `Reflexive`, `Symmetric` and `Transitive`. This one is a little trickier,
since it's really a property of *two* relations: one corresponding to equality,
and another to the ordering:

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

Because `_≤_` is not symmetric, it can't possibly be an equivalence relation.
But it does have reflexivity and transitivity, which is still quite a lot of
structure!






```agda

  record IsPreorder
          {A : Set a} (_~_ : Rel A ℓ) : Set (a ⊔ ℓ) where
    field
      refl : Reflexive _~_
      trans : Transitive _~_

  record IsEquivalence⅋
          {A : Set a} (_~_ : Rel A ℓ) : Set (a ⊔ ℓ) where
    field
      is-preorder : IsPreorder _~_
      sym : Symmetric _~_

    open IsPreorder is-preorder public

  module Reasoning {_~_ : Rel A ℓ} (~-preorder : IsPreorder _~_) where
    open IsPreorder ~-preorder public

    _∎ : (x : A) → x ~ x
    _∎ x = refl
    infix 3 _∎

    import Relation.Binary.PropositionalEquality
      as PropEq
    open PropEq using (_≡_)

    begin_ : {x y : A} → x ~ y → x ~ y
    begin_ x~y = x~y
    infix 1 begin_

    _≡⟨⟩_ : (x : A) → {y : A} → x ≡ y → x ≡ y
    x ≡⟨⟩ p = p
    infixr 2 _≡⟨⟩_

    _≡⟨_⟩_ : (x : A) → ∀ {y z} → x ≡ y → y ~ z → x ~ z
    _ ≡⟨ PropEq.refl ⟩ y~z = y~z
    infixr 2 _≡⟨_⟩_

    _≈⟨_⟩_ : (x : A) → ∀ {y z} → x ~ y → y ~ z → x ~ z
    _ ≈⟨ x~y ⟩ y~z = trans x~y y~z
    infixr 2 _≈⟨_⟩_

  -- module ≤-Reasoning where
  --   import Data.Nat.Properties as ℕ
  --   ≤-preorder : IsPreorder (_≤_)
  --   IsPreorder.refl ≤-preorder = ℕ.≤-refl
  --   IsPreorder.trans ≤-preorder = ℕ.≤-trans

  --   open Reasoning ≤-preorder
  --     renaming (_≈⟨_⟩_ to _≤⟨_⟩_)
      -- public


open import Data.Nat
import Relation.Binary.PropositionalEquality
  as PropEq
open PropEq using (_≡_; module ≡-Reasoning; cong)

module ModularArithmetic where
  infix 4 _≈_⟨mod_⟩
  data _≈_⟨mod_⟩ (a b n : ℕ) : Set where
    ≈-mod
      : (x y : ℕ)
      → a + x * n ≡ b + y * n  -- ! 1
      → a ≈ b ⟨mod n ⟩

open ModularArithmetic

_ : 11 + 2 ≈ 1 ⟨mod 12 ⟩
_ = ≈-mod 0 1 PropEq.refl

module ℕ/nℕ (n : ℕ) where
  open Sandbox-Relations
  open Sandbox-Orderings

  infix 4 _≈_
  _≈_ : Rel ℕ _
  _≈_ = _≈_⟨mod n ⟩

  private variable
    a b c d : ℕ


  ≈-refl : Reflexive _≈_
  ≈-refl = ≈-mod 0 0 PropEq.refl

  ≈-sym : Symmetric _≈_
  ≈-sym (≈-mod x y p) = ≈-mod y x (PropEq.sym p)

  open import Data.Nat.Solver

  ≈-trans : Transitive _≈_
  ≈-trans {a} {b} {c} (≈-mod x y pxy) (≈-mod z w pzw) =
    ≈-mod (x + z) (w + y) ( begin
      a + (x + z) * n      ≡⟨ lemma₁ ⟩
      (a + x * n) + z * n  ≡⟨ cong (_+ z * n) pxy ⟩
      (b + y * n) + z * n  ≡⟨ lemma₂ ⟩
      (b + z * n) + y * n  ≡⟨ cong (_+ y * n) pzw ⟩
      c + w * n + y * n    ≡⟨ lemma₃ ⟩
      c + (w + y) * n      ∎
    )
    where
      open ≡-Reasoning
      open +-*-Solver

      lemma₁ = solve 4
        (λ a n x z → a :+ (x :+ z) :* n
                  := (a :+ x :* n) :+ z :* n)
        PropEq.refl a n x z

      lemma₂ = solve 4
        (λ b n y z → (b :+ y :* n) :+ z :* n
                  := (b :+ z :* n) :+ y :* n)
        PropEq.refl b n y z

      lemma₃ = solve 4
        (λ c n w y → c :+ w :* n :+ y :* n
                  := c :+ (w :+ y) :* n)
        PropEq.refl c n w y

  ≈-equiv : IsEquivalence _≈_
  IsEquivalence.refl ≈-equiv = ≈-refl
  IsEquivalence.sym ≈-equiv = ≈-sym
  IsEquivalence.trans ≈-equiv = ≈-trans

  module ≈-Reasoning where
    ≈-preorder : IsPreorder _≈_
    IsPreorder.refl ≈-preorder = ≈-refl
    IsPreorder.trans ≈-preorder = ≈-trans

    open IsEquivalence ≈-equiv using (sym) public
    open Reasoning ≈-preorder public


  +-cong₂-mod : a ≈ b → c ≈ d → a + c ≈ b + d
  +-cong₂-mod {zero} {b} {c} {d} a=b c=d =
    begin
      zero + c
    ≡⟨ PropEq.refl ⟩
      c
    ≈⟨ c=d ⟩
      d
    ≈⟨ ? ⟩
      b + d
    ∎
    where open ≈-Reasoning
  +-cong₂-mod {suc a} {b} {c} {d} a=b c=d = {! !}




```
