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





```agda
_Preserves₂_⟶_⟶_ : (A → B → C) → Rel A ℓ₁ → Rel B ℓ₂ → Rel C ℓ₃ → Set _
_∙_ Preserves₂ P ⟶ Q ⟶ R = ∀ {x y u v} → P x y → Q u v → R (x ∙ u) (y ∙ v)

Reflexive : Rel A ℓ → Set _
Reflexive {A = A} _≈_ = ∀ {x} → x ≈ x
```


In fact, we have a `cong` like rule for every possible output relation:

```agda
kong : {_≈_ : Rel B ℓ} → (f : A → B) → f Preserves _≡_ ⟶ _≈_
kong f refl = {! !}
```



