# Common Properties

```agda
module 5-properties where

open import Agda.Primitive

private variable
  a b c ℓ ℓ₁ ℓ₂ ℓ₃ : Level
  A : Set a
  B : Set b
  C : Set c
```

In this chapter we will explore some common, exceptionally potent and
reoccurring ideas in mathematics. In many ways, these properties are at the
heart of mathematics; regardless of the mathematical objects of study, we will
continue to find relations, reflexivity, symmetry, associativity, transitivity,
commutativity, identities and compositions. This chapter will serve as an
introduction to all of these concepts.


## Relations

A *relation* is a set of pairs of elements from two other sets. We say the
elements that form the pair are said to "relate" in some way. The "two other
sets" are called the *carrier* sets, and serves as the universe of discourse by
selecting for the sorts of things we can consider. Most of the time, the two
carrier sets will be the *same* set, in which case we unambiguously refer to it
as the *carrier*.

Relations as defined are extremely broad mathematical objects, consisting of
everything ranging from equalities (`x = y`) and inequalities (`3 ≤ 4`) and
functions ($f(x) \mapsto x^2$). Mathematicians usually write an abstract
relation as the infix operator `R`, thus our previous examples could plausibly
be written as `x R y`, `3 R 4` or `x R x^2`, though *never at the same time.*
Furthermore, this is not a habit you should adopt; mathematics has path
dependency as being done on paper by pencil, in a context without autocomplete
or find-and-replace. Thus, mathematical symbols are often terse, but this is a
bad habit on the part of mathematicians and you, as an aspiring mathematician,
should strive to do better.

Relations are generalizations of functions, simultaneously relaxing
restrictions. Functions are required to have unique outputs for a given input,
but this is not necessary in a relation. Furthermore, functions are required to
map every element in the domain, but this too is relaxed when discussing
relations.

In the Agda standard library, the definitions for relations are found under
`Relation.Binary.Core`, which provide the following definitions. Agda defines
the type of heterogeneous relations (that is, the variety with distinct carrier
sets) as `REL`:

```agda
REL : Set a → Set b → (ℓ : Level) → Set (a ⊔ b ⊔ lsuc ℓ)  -- ! 1
REL A B ℓ = A → B → Set ℓ  -- ! 2
```

which you can read as saying two things. [1](Ann) is a type annotation on `REL`
stating it is a function[^relfunc] that takes two sets as inputs and produces a
set as an output. Line [2](Ann) gives the definition of how to build such a set;
it's a function that takes sets `A` and `B`, and maps them to a function which
selects a particular element from `A`, a particular element from `B`, and gives
back a new set.

[^relfunc]: Mathematically, relations are the more fundamental idea than
  functions. But computationally, everything is functions, which is why this odd
  discrepancy exists.

It is a common idiom in Agda to use Latin level names for carrier sets, and
saving the cursive `ℓ` for the levels that parameterize relations.

In the common case that `A = B`, Agda provides `Rel`, which is parameterized by
only one carrier set. It is important to remember, however, that just because
`Rel` takes only one carrier, elements of the defined relation are still a pair!

```agda
Rel : Set a → (ℓ : Level) → Set (a ⊔ lsuc ℓ)
Rel A ℓ = REL A A ℓ
```

In Agda, we build *particular* relations via either `record` or `data`
constructors, depending on the details of the object. Propositional equality is
one such relation:

```agda
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x
```

If you squint at this definition, you can see that the type of `_≡_` is actually
`{A : Set} → Rel A ℓ` --- that is, a `Set` parameterized by two elements of `A`.


## Preservation

One of the most important mathematical ideas is the notion of *preservation*,
which is a statement about a function and two relations --- one over its domain
type, and the other over its codomain. Preservation is a statement that, if the
input relation holds, you can map both of its elements by the given function,
and the result holds in the output relation.

Preservation in the Agda standard library is also defined in
`Relation.Binary.Core`, and is given the somewhat unwieldy syntax
`_Preserves_⟶_`:

```agda
_Preserves_⟶_ : (f : A → B) → Rel A ℓ₁ → Rel B ℓ₂ → Set _
f Preserves P ⟶ Q = ∀ {x y} → P x y → Q (f x) (f y)
```

The best known preservation theorem is function congruence; that is, if two
things were propositionally equal before being run through a function, they are
still propositionally equal afterwards.

```agda
cong : (f : A → B) → f Preserves _≡_ ⟶ _≡_
cong f refl = refl
```
However, we also have a relation formed by `_≤_` on the natural numbers:

```agda
open import Data.Nat using (ℕ; _≤_; suc; z≤n; s≤s)
```

in which case we have a different, and more stringent, preservation rule ---
monotonicity. That is, if `x ≤ y`, monotonicity states that `f x ≤ f y`. Of
course, this is not true of all functions, but is certainly true of `suc`:

```agda
suc-mono-≤ : suc Preserves _≤_ ⟶ _≤_
suc-mono-≤ z≤n = s≤s z≤n
suc-mono-≤ (s≤s x) = s≤s (suc-mono-≤ x)
```

Preservation also comes in the form of pointwise binary preservation; that is,
if you have two relations as input, you can compose them pointwise in the
output. Namely:

```agda
_Preserves₂_⟶_⟶_ : (A → B → C) → Rel A ℓ₁ → Rel B ℓ₂ → Rel C ℓ₃ → Set _
_∙_ Preserves₂ P ⟶ Q ⟶ R = ∀ {x y u v} → P x y → Q u v → R (x ∙ u) (y ∙ v)
```


### Reflexivity

For some relation `_~_`, we say `_~_` is reflexive if it has the property that
every `x` is in relation with itself. That is:

```agda
Reflexive : Rel A ℓ → Set _
Reflexive _~_ = ∀ {x} → x ~ x
```

Reflexivity is an important part of many mathematical structures, including
equivalence relations, partially ordered sets, (semi-)lattices, and, in
a slightly different form, categories. We will discuss all of these structures
later in this book.

Reasoning about relations is significantly easier when reflexivity is involved.
You can say much more about `_≤_` (a reflexive relation) than you can about
`_<_` (a non-reflexive relation), and this seems to hold for all humans. For
whatever reason, it appears that humans are hard-wired to reason with respect to
self-identity. Thus, if you find yourself in a position where you are defining
a relation (which happens much more frequently than you might expect), you will
be well-served to fit in reflexivity if at all possible. Sometimes this will
require finagling some of the fine details, but it will pay for itself
immediately when you begin to work with the structure.


### Symmetry

*Symmetry* is a property of relations that if `a` is in relation with `b`, then
`b ` is also in relation with `a`. That is, a relation `_~_` is symmetric if it
is agnostic to its argument order. In Agda, we write `Symmetric` thusly:

```agda
Symmetric : Rel A ℓ → Set _
Symmetric _∼_ = ∀ {x y} → x ∼ y → y ∼ x
```

Equality is a symmetric relation, but `_≤_` is not, since the latter has
explicit "smaller" and "larger" sides.

Symmetry is much like being ambidextrous; it rarely allows you to do things you
wouldn't otherwise be able to, but it sure comes in handy. We're much more
comfortable with asymmetric relations than we are with irreflexive ones as
asymmetry is something we see constantly in everyday life. From one-way streets
to the eventual heat-death of the universe, most things in life do not go both
ways.


### Antisymmetry

We have one other important property regarding the position of a relation's
arguments --- *antisymmetry.* Antisymmetry is a property that transforms one
relation into another; namely, it espouses the notion of *ordering.* That is, if
we know `a ~ b` and `b ~ a` for some relation `_~_`, we learn that `a ≈ b` for
some other relation `_≈_`. The most well-known example of antisymmetry is the
antisymmetry between `_≤_` and `_≡_`. If we know simultaneously that `a ≤ b` and
also that `b ≤ a`, our only possible conclusion is that `a ≡ b`.

In code, we write:

```agda
Antisymmetric : Rel A ℓ₁ → Rel A ℓ₂ → Set _
Antisymmetric _≈_ _≤_ = ∀ {x y} → x ≤ y → y ≤ x → x ≈ y
```

In practice, antisymmetry always results in an equivalence between the two
terms, but this is not strictly necessary given the definition.

Antisymmetry is really a statement about the symmetry of a relation; stating
that the only symmetry that can occur is reflexivity.


### Transitivity

If a relation `_~_` is *transitive*, that means we can glue its ends together
like dominoes, building bigger terms of the relation from smaller ones. In code:

```agda
Transitive : Rel A ℓ → Set _
Transitive _∼_ = ∀ {x y z} → x ∼ y → y ∼ z → x ∼ z
```

> TODO(sandy): omg there is a great idea here; a set of 5 relations that the
> reader is encouraged to work out whether each property holds
>
> dominoes, what else?

Transitivity is the great workhorse of mathematics, allowing practitioners to
subdivide problems into smaller pieces, solve those individually, and then
compose the results together in service of the whole. Transitivity is the rule
you (perhaps unwittingly) invoke when you perform arithmetic:

$$
\begin{aligned}
& 42 * 7 + 15 / 3 \\
&= 42 * 7 + 5 \\
&= 294 + 5 \\
&= 299
\end{aligned}
$$

Each line of this computation is an "obvious" step, performing one step of
reasoning to transform one expression into the next. But transitivity is what
allows us to glue each individual step together, eventually asserting the
conclusion, $299$ from merely the premise $42 * 7 + 15 / 3$, eliminating all of
the intermediary work.

Transitivity and reflexivity are in fact such important concepts that category
theory, a branch of mathematics, uses them as the starting point, and derives an
alternative foundation to math than the usual set-theoretic notions.


### Totality

A relation `_~_` is said to be *total* if and only if we can always derive one
of `a ~ b` or `b ~ a` for any elements `a` and `b`. This is true of the ordering
on numbers, such that we can always determine whether `m ≤ n` or `n ≤ m`, but
not true of family trees, where two members in the same family tree might have
no genetic relation whatsoever.

```agda
open import Data.Sum

Total : Rel A ℓ → Set _
Total _∼_ = ∀ x y → (x ∼ y) ⊎ (y ∼ x)
```

### Trichotomy

### stuff for later

```agda
module Dominos where

  data Face : Set where
    ∙ ⠢ ⋱ ⠭ ⁙ ⠿ : Face

  data Domino : Face → Face → Set where
    _∣_ : (m n : Face) → Domino m n

  dom-refl : Reflexive Domino
  dom-refl {x} = x ∣ x

  dom-sym : Symmetric Domino
  dom-sym (m ∣ n) = n ∣ m

  dom-trans : Transitive Domino
  dom-trans (m ∣ n) (.n ∣ o) = m ∣ o

  open import 8-iso

  instance
    face-equiv : Equivalent lzero Face
    Equivalent._≋_ face-equiv = Domino
    IsEquivalence.refl (Equivalent.equiv face-equiv) = dom-refl
    IsEquivalence.sym (Equivalent.equiv face-equiv) = dom-sym
    IsEquivalence.trans (Equivalent.equiv face-equiv) = dom-trans

  open ≋-Reasoning

  _ : Domino ⠢ ⠿
  _ = begin
      ⠢  ≈⟨ ⠢ ∣ ⠢ ⟩
      _  ≈⟨ ⠢ ∣ ∙ ⟩
      _  ≈⟨ ∙ ∣ ⋱ ⟩
      _  ≈⟨ ⋱ ∣ ⠿ ⟩
      ⠿  ∎
```

