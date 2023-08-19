# Common Properties

```agda
module Chapter5-properties where

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


### Dominoes

To illustrate some of the above properties, let's build our own relation, and
see what we can discover about it. We'll take a particularly simple domain:
domino tiles. If you're unfamiliar, dominoes are rectangular tiles with markings
on either end of their long side. The markings are a number of dots, between
zero and six, inclusive. Each end may have a different number of dots.

We can model this in Agda rather cutely. First we define the markings that can
be on a domino tile, that is some number of dots between zero and six. Because
Agda has unicode support, we can dig deep for adequate symbols to properly
capture the domain, coming up with the following:

```agda
module Dominoes where

  data Marking : Set where
    □ ∙ ⠢ ⋱ ⠭ ⁙ ⠿ : Marking
```

The `Marking` set is the carrier of our relation. The relation itself is
a `Chain` (for reasons we will articulate later), indexed by two `Marking`s

```agda
  data Chain : Rel Marking lzero where
```

the constructor for which is to put two markings on either end of a "tile,"
indicated in our domain-syntax as a vertical bar:

```agda
    _∣_ : (m n : Marking) → Chain m n
```

Such a notation is amazingly close to how real dominoes look. Unicode has
codepoints for every possible domino tile, which means we can give more
canonical names to our tiles if we'd like, for example:

```agda
  🁐 : Chain ⠭ ⋱
  🁐 = ⠭ ∣ ⋱
```

We will not pursue this idea any further, as the unicode codepoints are not
particularly composable, and operating over these symbols will require a great
deal of work on our part. Instead we will be content with the `_∣_` syntax for
building domino tiles.

The question now is, what properties does our `Chain` relation admit? This is
a meaningless question without knowledge of the game of dominoes. The first rule
we need to know is that every possible combination of `Marking`s exists as
a domino tile. The markings on opposite ends of the tile do not need to be
distinct, therefore we are justified in saying `Path`s are reflexive; for any
desired marking, we can find a tile with that marking on either end.

```agda
  dom-refl : Reflexive Chain
  dom-refl {x} = x ∣ x
```

Furthermore, note that domino tiles are, in real life, actual physical objects,
which can be rotated arbitrarily in three-dimensional space. The two ends of the
tile are not differentiated in any way, and therefore, we have no justification
to say that one end is definitely on the left and the other definitely on the
right. Therefore, we can swap which end is where, and thus `Path`s are symmetric:

```agda
  dom-sym : Symmetric Chain
  dom-sym (m ∣ n) = n ∣ m
```

These last two "rules" have been more facts about the physical dominoes
themselves, rather than any rules about the game. Playing the game however,
players take turn putting down tiles according to certain constraints. The
constraint in question is that you must play a domino on the end of a chain,
ensuring your played domino has the same marking as the one on the table. That
is, if the chain of dominoes currently on the table is `Chain ⁙ ∙`, you can play
any domino that has one end as a `⁙`, or any domino that has a `∙` on one side.
Any domino which has neither a `⁙` nor a `∙` may not be played. When playing the
domino, you must ensure the matching end is played beside the end of the chain.
That is, dominoes must be aligned, therefore if the chain is `⁙ ∣ ∙`, you can
extend it by playing your `⋱ ∣ ∙` domino as `⁙ ∣ ∙ ∙ ∣ ⋱`, such that the two
`∙`-sides are adjacent to one another.

Therefore, we have a notion of transitivity for dominoes; if we have two chains
whose ends line up, we can glue the two together like so:

```agda
  dom-trans : Transitive Chain
  dom-trans (m ∣ n) (.n ∣ o) = m ∣ o
```

It is for this reason that we called our relation `Chain` rather than `Tile`; of
course, it might be more proper to explicitly model the series of tiles existing
in a chain, and the motivated reader is encouraged to flesh out such
a definition of `Chain`.

Pulling in a bit of machinery from other chapters, we can construct some
compelling syntax for showing chains of dominoes. After a bit of ceremony,

```agda
  open import Chapter8-iso

  instance
    face-equiv : Equivalent lzero Marking
    Equivalent._≋_ face-equiv = Chain
    IsEquivalence.refl (Equivalent.equiv face-equiv) = dom-refl
    IsEquivalence.sym (Equivalent.equiv face-equiv) = dom-sym
    IsEquivalence.trans (Equivalent.equiv face-equiv) = dom-trans
```

we can construct chains of dominoes by showing which tiles were glued together,
and what the intermediate game state looked like:

```agda
  _ : Chain ⠢ ⠿
  _ = begin
      ⠢  ≈⟨ ⠢ ∣ ⠢ ⟩
      ⠢  ≈⟨ ⠢ ∣ ∙ ⟩
      ∙  ≈⟨ ∙ ∣ ⋱ ⟩
      ⋱  ≈⟨ ⋱ ∣ ⠿ ⟩
      ⠿  ∎
    where open ≋-Reasoning
```

