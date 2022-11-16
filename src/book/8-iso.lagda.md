# Isomorphism

```agda
module 8-iso where

open import Relation.Binary using (Setoid; _Preserves_⟶_)

open import Relation.Binary.Structures public

open import Function using (_∘_; id; const)
open import Agda.Primitive

open Setoid using (Carrier)
```

Consider the types `Bool` and `⊤ ⊎ ⊤`. Both contain exactly one bit of
information, and so in some sense, are "the same thing" even if they are, on the
other hand, completely different types. But given that they are at least
equivalent, if not *the same,* is there some way we can formalize that notion?

In fact, we can. The trick comes from combinatorics, where we would like to know
the size of two sets. If we know the size of one of them, and we can transform
each set into the other, without losing anything in the process, the two sets
must be the same size. Why must that be true? Well, if one were smaller than the
other, we would have to map some elements in the bigger set to the same element
in the smaller set, and thus, when we returned to the bigger set, we wouldn't
end up where we started from.

This idea is known as a *bijection,* or an *isomorphism.* More formally, a
bijection is, either an *injective* and *surjective* function, or alternatively,
a pair of functions that are inverses of one another. We will use the latter
approach here in this presentation.

Let's work an example together. We would like to show `Bool` is isomorphic to `⊤
⊎ ⊤`. Recall that `true`, `false`, `inj₁ tt`, and `inj₂ tt` are all just
arbitrary identifiers, half of which we assign to be type `Bool` and the other
half to `⊤ ⊎ ⊤`, but at the end of the day, the symbols are meaningless and it
is we humans who foist meaning upon them.

By this reasoning, so long as we can give a consistent mapping between the two
sets, we have shown that they are the same thing, modulo choice of arbitrary,
meaningless symbol.

Thus, we need a mapping from `Bool`s to `⊤ ⊎ ⊤`:

```agda
module Example where
  open import Data.Bool
  open import Data.Sum
  open import Data.Unit
  open import Function
  open import Relation.Binary.PropositionalEquality

  to : Bool → ⊤ ⊎ ⊤
  to false = inj₁ tt
  to true = inj₂ tt
```

We also need a function to map the other direction. Crucially, this mapping must
be self-consistent, requiring us to pick *the same elements* that got us here.
Under this constraint, there is only one possibility.

```agda
  from : ⊤ ⊎ ⊤ → Bool
  from (inj₁ tt) = false
  from (inj₂ tt) = true
```

While you and I are thus convinced that `Bool` and `⊤ ⊎ ⊤` are the "same", we
should also give a proof of this. In this case, a suitable proof is an equality
between the functions `from ∘ to = id` and, vice versa, `to ∘ from = id`.

```agda
  from∘to≡id : from ∘ to ≗ id
  from∘to≡id false = refl
  from∘to≡id true = refl

  to∘from≡id : to ∘ from ≗ id
  to∘from≡id (inj₁ tt) = refl
  to∘from≡id (inj₂ tt) = refl
```

These four pieces, `to`, `from`, `from∘to≡id`, and `to∘from≡id`, make up a proof
that `Bool` and `⊤ ⊎ ⊤` are indeed isomorphic to one another. In general, we
will need to package these four pieces of evidence together.


## More Setoids

Did you notice earlier that we smuggled in an equality, without defining exactly
what its details were? The elision in question is in the proofs of `from∘to≡id`,
and `to∘from≡id`, where we say going forward and back again "is the same thing"
as not going anywhere. But what sort of equality do we require here? Need it be
propositional? This is a good question to ask yourself whenever you see an
equality --- "but what does it mean?"

In this case we will be using general setoid equality. Unfortunately, setoids
are notoriously difficult things to work with, causing a condition colloquially
known as *setoid hell.* Before we can get into the meat of defining
isomorphisms, we will first need some machinery to make dealing with setoids
much easier.

Agda supports a feature known as "instance arguments," which are capable of
performing automatic proof search. Rather than deal directly with setoids
everywhere, we would instead like to deal with types and have Agda work out the
setoid formalizations for us automatically. For technical reasons, we can't do
this directly with the `Setoid` record, but instead, we can build an equivalent
type, and equip it with a means of being transformed into a `Setoid`.

Enter the `Equivalent` record, which we use for automatically passing around
setoids. The only difference between `Equivalent` and `Setoid` is that we pass
the carrier type directly as a type index, rather than as a record field.

```agda
private variable
  ℓ ℓ₁ ℓ₂ c c₁ c₂ : Level

record Equivalent (ℓ : Level) (A : Set c) : Set (lsuc ℓ ⊔ c) where
  infix 4 _≋_
  field
    _≋_ : A → A → Set ℓ
    equiv : IsEquivalence (_≋_)
```

Agda's automatic instance resolution is type-driven, so we need to make this
change in order to connect up the wiring later. We will also equip `Equivalent`
with the setoid we actually want:

```agda
  ≋setoid : Setoid c ℓ
  ≋setoid = record { isEquivalence = equiv }
```

Finally, we will add a few record-scoped modules, to allow downstream callers
access to the internal machinery if they'd like it, merely by opening the
relevant record:

```agda
  module Equiv where
    open IsEquivalence equiv public

  module ≋-Reasoning where
    open import Relation.Binary.Reasoning.Setoid ≋setoid public
```

The final step is to open our `Equivalent` module with the special `⦃ ... ⦄`
syntax, connecting `Equivalent` to the automatic instance resolution machinery.

```agda
open Equivalent ⦃ ... ⦄ public
```

Now, whenever we refer to `_≋_`, Agda will look for whatever `Equivalent` is in
scope, and use its `_≈_` relation. As we will see soon, Agda does quite a lot of
work to resolve the `Equivalent`s in scope, and can write a significant amount
of code for us. In addition, this gives us a convenient syntax for overloading
operators. No longer do we need to rename our operations to `_≈₁_` in order for
them to not conflict; we just overload everything and let Agda elaborate what it
is we meant in the first place.


## Formalizing Isomorphisms

Finally we're ready to build an isomorphism. As usual, start with the type and
its indices:

```agda
record _↔_
      (A : Set c₁)
      (B : Set c₂)
```

However, were not ready to just slap `: Set` on yet. We also need to bind our
`Equivalent` witnesses, which we can do by adding them as *instance* arguments
to the record:

```agda
      ⦃ equiv-A : Equivalent ℓ₁ A ⦄
      ⦃ equiv-B : Equivalent ℓ₂ B ⦄
      : Set (lsuc ℓ₁ ⊔ lsuc ℓ₂ ⊔ c₁ ⊔ c₂) where
```

We now put in our four pieces that we identified as

```agda
  constructor inverse
  field
    to   : A → B
    from : B → A
    left-inverse-of  : (x : A) → from (to x) ≋ x
    right-inverse-of : (x : B) → to (from x) ≋ x
```

While this was enough when we were dealing with propositional equality, in the
land of setoids we need two additional properties, namely `cong`s for both `to`
and `from`:

```agda
    to-cong   : to   Preserves _≋_ ⟶ _≋_
    from-cong : from Preserves _≋_ ⟶ _≋_
```

It's interesting to note that `_↔_` forms an equivalence relationship, which we
should expect. We can show this by giving definitions for `refl`, `sym` and
`trans`. First, a little setup:

```agda
module _ where
  open _↔_
  open Equiv
  open ≋-Reasoning

  private variable
    A : Set c₁
    B : Set c₂

    c₃ ℓ₃ : Level
    C : Set c₃
```

Showing `refl` is trivial, as always:

```agda
  ↔-refl : ⦃ _ : Equivalent ℓ₁ A ⦄ → A ↔ A
  ↔-refl = inverse id id (λ x → refl) (λ x → refl) id id
```

Witnessing `sym` is likewise trivial; we need only swap around which arguments
are which:

```agda
  ↔-sym : ⦃ _ : Equivalent ℓ₁ A ⦄ ⦃ _ : Equivalent ℓ₂ B ⦄ → A ↔ B → B ↔ A
  ↔-sym (inverse to from left-inverse-of right-inverse-of to-cong from-cong) =
    inverse from to right-inverse-of left-inverse-of from-cong to-cong
```

And then we come to `trans`, which isn't challenging, but is certainly a lot of
work. The trick is to compose our functions correctly, but besides that,
everything else falls into place. You will see why we need our additional `cong`
laws here:

```agda
  ↔-trans : ⦃ _ : Equivalent ℓ₁ A ⦄
            ⦃ _ : Equivalent ℓ₂ B ⦄
            ⦃ _ : Equivalent ℓ₃ C ⦄
          → A ↔ B
          → B ↔ C
          → A ↔ C
  ↔-trans (inverse to₁ from₁ left-inverse-of₁ right-inverse-of₁ to-cong₁ from-cong₁)
          (inverse to₂ from₂ left-inverse-of₂ right-inverse-of₂ to-cong₂ from-cong₂) =
    inverse
      (to₂ ∘ to₁)
      (from₁ ∘ from₂)
      (λ x → begin
        from₁ (from₂ (to₂ (to₁ x)))  ≈⟨ from-cong₁ (left-inverse-of₂ (to₁ x)) ⟩
        from₁ (to₁ x)                ≈⟨ left-inverse-of₁ x ⟩
        x                            ∎
      )
      (λ x → begin
        to₂ (to₁ (from₁ (from₂ x)))  ≈⟨ to-cong₂ (right-inverse-of₁ (from₂ x)) ⟩
        to₂ (from₂ x)                ≈⟨ right-inverse-of₂ x ⟩
        x                            ∎
      )
      (to-cong₂   ∘ to-cong₁)
      (from-cong₁ ∘ from-cong₂)
```
