# Isomorphism

```agda
{-# OPTIONS --allow-unsolved-metas #-}

module Chapter8-iso where

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
    left-inv-of  : (x : A) → from (to x) ≋ x
    right-inv-of : (x : B) → to (from x) ≋ x
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
  ↔-sym (inverse to from left-inv-of right-inv-of to-cong from-cong) =
    inverse from to right-inv-of left-inv-of from-cong to-cong
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
  ↔-trans (inverse to₁ from₁ left-inv-of₁ right-inv-of₁ to-cong₁ from-cong₁)
          (inverse to₂ from₂ left-inv-of₂ right-inv-of₂ to-cong₂ from-cong₂) =
    inverse
      (to₂ ∘ to₁)
      (from₁ ∘ from₂)
      (λ x → begin
        from₁ (from₂ (to₂ (to₁ x)))  ≈⟨ from-cong₁ (left-inv-of₂ (to₁ x)) ⟩
        from₁ (to₁ x)                ≈⟨ left-inv-of₁ x ⟩
        x                            ∎
      )
      (λ x → begin
        to₂ (to₁ (from₁ (from₂ x)))  ≈⟨ to-cong₂ (right-inv-of₁ (from₂ x)) ⟩
        to₂ (from₂ x)                ≈⟨ right-inv-of₂ x ⟩
        x                            ∎
      )
      (to-cong₂   ∘ to-cong₁)
      (from-cong₁ ∘ from-cong₂)
```


### Injectivity

We made the claim earlier that mathematicians define bijections as functions
which are both injective and surjective. Let's take some time to investigate
what exactly this means, why it's so, and what it means for programmers.

An *injective* function is one which maps every input to a unique output. That
means, at least in principle, if you know where values end up after a function
call, you can determine where they came from. Alternatively, and more usefully
to us, it means if you know that two values are equal in the range of the
function, you can show that they must have been equal in the domain.

After a little bit of ritual setup, binding two types and equivalence relations
on them, and opening some modules to get everything in scope:

```agda
module _ {A : Set c₁}
         {B : Set c₂}
         ⦃ _ : Equivalent ℓ₁ A ⦄
         ⦃ _ : Equivalent ℓ₂ B ⦄ where

  open Equiv
  open ≋-Reasoning
  open _↔_
  open import Data.Nat hiding (_⊔_)
```

we can define the property of injectiveness exactly as this "reverse `cong`":

```agda
  Injective : (f : A → B) → Set (ℓ₁ ⊔ c₁ ⊔ ℓ₂)
  Injective f = (x y : A) → f x ≋ f y → x ≋ y
```

As a little trial run, we can show that `suc` over naturals is injective:

```not-agda-truly-i-swear
  suc-injective : Injective suc
  suc-injective x .x refl = refl
```

Why is this so? Well, there's only one way to propositionally get `suc n`, via
applying `suc` to `n`. It sounds a bit stupid when written out this way, but
that's because `suc` is so injective there is no syntax available to even state
the problem in a non-injective way.

A more interesting observation is that we can extract an `Injective` proof from
a `_↔_`. There are two functions inside of the bijection, `to` and `from`, so we
will need to pick one to show is injective. Without loss of generality, we
arbitrarily pick `to`:

```agda
  ↔-inj : (bij : A ↔ B) → Injective (bij .to)
```

The proof of injectivity is a bit roundabout, and is a good opportunity for
fiddling with proofs if you're amenable. Try it now!

We have a proof that `to x ≋ to y`, but need to somehow coerce that into a proof
that `x ≋ y`. The trick is to use the fact that `x ≋ from (to x)`, and then
`cong` our given proof into the right shape.

```agda
  ↔-inj (inverse to from left-inv-of _ _ from-cong) x y p =
    begin
      x            ≈⟨ sym (left-inv-of x) ⟩
      from (to x)  ≈⟨ from-cong p ⟩
      from (to y)  ≈⟨ left-inv-of y ⟩
      y            ∎
```

Injectivity is a sort of "algebraic" property over functions, giving us the
ability to "cancel out" function application. We often play fast and loose with
injectivity when doing mathematics informally and in school. For example, you
will probably get the marks if you write:

$$
\begin{aligned}
x^2 &= 16 \\
x^2 &= 4^2 \\
x &= 4
\end{aligned}
$$

While $x = 4$ is a valid solution to this problem, it's not the unique solution.
Of course, we also have $x = -4$. This plurality of results is an immediate
consequence of the fact that $\text{--}^2$ is not an injective function. As all
grade-schoolers discover when they learn about square roots, non-injectivity
makes algebra significantly more difficult.


### Surjectivity

The other half of a bijection is the property of *surjectivity* --- that is,
that every value in the codomain gets "hit" by the function. If a function is
surjective, we know that its range is equal to its codomain. Surjectivity is
good for showing that wherever you are in the codomain, you are guaranteed to
have a preimage in the function.

Why is that important? You certainly can't have an inverse if you have nowhere
to go to!

We can therefore encode surjectivity as a mapping from elements in the codomain
to elements in the domain, plus a proof that applying the function gets you back
to where you started.

```agda
  open import Data.Product

  Surjective : (f : A → B) → Set (ℓ₂ ⊔ c₁ ⊔ c₂)
  Surjective f = (b : B) → Σ A λ a → f a ≋ b
```

Showing that any bijection is surjective is trivial, since we have everything we
need at our fingertips:

```agda
  ↔-sur : (bij : A ↔ B) → Surjective (bij .to)
  proj₁ (↔-sur bij b) = bij .from b
  proj₂ (↔-sur bij b) = bij .right-inv-of b
```

Easy peasy.


### Showing the Bijection

Actually, I don't think we can show this bijection! As it happens, the argument
for an injection and surjection making a bijection is:

1. the surjection shows that everything in the codomain is hit
2. the injection shows that everything in the domain goes to a unique value in
   the codomain
3. therefore, everything in the domain goes to a unique place in the codomain,
   and everywhere in the codomain is hit, so the two sets must have the same
   cardinality and thus we must have a bijection

As you can see, this shows the two sets have the same cardinality, and thus
there *must exist* a bijection, but we don't know exactly how to construct it.
For example, there are *two* bijections between `Bool` and `Bool`, and our
argument about cardinalities above says only that we have a bijection, not that
we know which one it is.

Therefore, having an injection and a surjection is sufficient to show there must
exist an isomorphism, but it doesn't give us any clues as to how to actually
build such a thing. This is our first taste of how mathematics as it's practiced
doesn't line up with what we'd desire in a more rigorous setting, like the
necessity of actual computation.

```agda
  inj-sur-↔ : {f : A → B} → Injective f → Surjective f → A ↔ B
  to           (inj-sur-↔ {f} inj sur) = f
  from         (inj-sur-↔ {f} inj sur) x = proj₁ (sur x)
  left-inv-of  (inj-sur-↔ {f} inj sur) x =
    begin
      ?
    ≡⟨ ? ⟩
      ?
    ∎
  right-inv-of (inj-sur-↔ {f} inj sur) x = proj₂ (sur x)
  to-cong      (inj-sur-↔ {f} inj sur) {x} {y} p =
    begin
      f x
    ≈⟨ ? ⟩
      f y
    ∎
  from-cong    (inj-sur-↔ {f} inj sur) {x} {y} p =
    begin
      proj₁ (sur x)
    ≈⟨ ? ⟩
      proj₁ (sur y)
    ∎


module _ where
  open import Data.Nat hiding (_⊔_)
  open import Data.Bool
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)
  open import Relation.Binary.PropositionalEquality.Properties

  ≡-equiv : (A : Set) → Equivalent lzero A
  ≡-equiv _ = record { equiv = isEquivalence }

  instance
    ℕ-equiv = ≡-equiv ℕ
    Bool-equiv = ≡-equiv Bool

  suc-injective : Injective suc
  suc-injective x .x refl = refl
```


## Moving Forwards

Despite our failures to replicate the mathematical ideal existence proof of an
isomorphism, we still have a perfectly good computational version. It just
requires more constraints than the mathematical ideal does. But nevertheless, we
can continue to work with this isomorphism type, using it to show the
equivalence of other mathematical ideas. For example, it will be extremely
helpful when we begin to talk about free constructions, and would like to show
the so-called "universal properties" of these objects.

In addition, under the Curry--Howard interpretation, equality in mathematics
corresponds with isomorphism in types. We have been using setoids thus far, but
setoids only allow us to show equality between members of the same type.
However, isomorphism is a more useful notion of equality when dealing with
disparate types. To illustrate this, we can transform a setoid into a bijection
extremely trivially:

```agda
module _ where
  open Equiv

  setoid-to-↔ : (A : Set c) → ⦃ _ : Equivalent ℓ A ⦄ → A ↔ A
  _↔_.to (setoid-to-↔ A) = id
  _↔_.from (setoid-to-↔ A) = id
  _↔_.left-inv-of (setoid-to-↔ A) a = refl
  _↔_.right-inv-of (setoid-to-↔ A) a = refl
  _↔_.to-cong (setoid-to-↔ A) p = p
  _↔_.from-cong (setoid-to-↔ A) p = p
```

However, it simply doesn't typecheck to build the reverse transformation in its
full generality (that is, with disparate types on either side of the
isomorphism.) Since we have an injection (but not *injectivity*) into
isomorphisms from setoids, but not vice versa, the former are more general.

However, because isomorphisms are more general than setoids, they allow us to
say less than we can say about setoids. The old adage that "liberties constrain,
and constraints liberate" applies here more than ever. The less an object can do
*in theory,* the better we can guess about what it does *in actuality.*

