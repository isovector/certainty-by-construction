
which is one half of the famous "De Morgan's laws." Can we show the other
direction, namely

$$
\neg (a \vee b) = \neg a \wedge \neg b
$$

In order to do this, we'll need to swap the direction of our monoid
homomorphism. Before we were looking for a homomorphism from `true-and-monoid`
to `false-or-monoid`, but now we need to go the other way around. Thus we can
start a new module and instantiate `IsMonoidHom` in the desired direction:


Exercise

:   Show the other half of De Morgan's law.


Solution

:   ```agda
  not-hom₂ : IsMonoidHom  (mkMonoid false-or-monoid)
                          (mkMonoid true-and-monoid)
                          not
  preserves-ε  not-hom₂ = refl
  preserves-∙  not-hom₂ false  b = refl
  preserves-∙  not-hom₂ true   b = refl
  f-cong       not-hom₂ refl = refl
    ```

Armed with some understanding of the importance of monoid homomorphisms, let's
now attempt to develop an intuition as to what they *are.* If a function `f` is
a monoid homomorphism it means we can play fast-and-loose about when we want to
apply `f`. Maybe `f` is expensive, so we'd like to batch all of our combining
work first, and only ever call `f` once. Alternatively, maybe `_∙₁_` is
expensive, in which case we might prefer to map every `A` term into a `B` before
accumulating them together.

Consider the case of list appending; each call to `_++_` is $O(n)$ time, and
thus we run in quadratic time when we have a linear number of lists to append.
(TODO check the details of this big O stuff) If all we'd like to do is count the
number of elements in the resulting list, we have two options: concatenate the
lists and take its length, or take the lengths individually and add them.
Therefore, in some sense, list concatenation "is the same thing as" addition of
numbers, at least with respect to the `length` function.

Whenever you can compute the answer in two ways, on either side of a function
call, it's time to start looking for a monoid homomorphism. In this case, we'd
like one between `[]-++-monoid` and `0-+-monoid`:

```agda
-- module _ {A : Set} where
  -- open monoid-hom ([]-++-monoid {A}) 0-+-monoid
  -- open IsMonoidHom
```

As previously identified, `length` forms a homomorphism between these two
monoids. All we have left to do is to show it:

```agda
  length-hom
      : {c : Level} {A : Set c}
      → IsMonoidHom  (mkMonoid ([]-++-monoid {A = A}))
                     (mkMonoid 0-+-monoid)
                     length
  preserves-ε  length-hom = refl
  preserves-∙  length-hom []       b = refl
  preserves-∙  length-hom (x ∷ a)  b =
    cong suc (preserves-∙ length-hom a b)
  f-cong length-hom refl = refl
```

Monoid homomorphisms allow us to reify this idea that there are two ways to get
to the same place, and therefore that the two ways must be equivalent. I like to
think about homomorphisms as "preserving metaphors"---that is to say, anything
I believe to be true before the function call is also true after the function
call, at least with respect to the operations on hand.

Of course, it can be rather fun to attempt to "collect" homomorphisms, but this is
often missing the forest for the trees. Instead, a better technique is to look
for homomorphisms whenever you are designing new programs or mathematics. Often
it will be the case that your first idea of how to solve a problem doesn't quite
admit any homomorphisms. In cases like those, it's worth playing around with
your formalization; is there some minor tweak that can be made to make a salient
homomorphism work out?

For example, consider some function-like data structure, maybe we'll call it
`Map`. We can give it the following abstract interface:

```agda
module Example where
  -- open monoid
  -- postulate
  --   Map Key Val : Set

  --   get : Key → Map → Val
  --   set : Map → Key → Val → Map
```

and two monoids, one over `Map`s and one over `Val`s:

```agda
    -- map-monoid : Monoid (setoid Map)
    -- val-monoid : Monoid (setoid Val)
```

With this infrastructure in place, we can assert a huge amount of "does what
you'd expect" on the implementations of `get` and `set` by showing the following
two monoid homomorphisms:

```agda
  -- open monoid-hom

  -- postulate
  --   get-hom
  --     : (k : Key)
  --     → IsMonoidHom map-monoid val-monoid (get k)
```

You'll notice here that we haven't instantiated the `homs` module with any
arguments, and therefore those arguments get distributed onto every use of
`IsMonoidHom`, which is why it now takes three arguments when it used to take
only one.

Anyway, returning to doing-what-you'd-expect, we can think of the conditions
from `get-hom` as these:

```mathstuff
forall k.
  get k e1 = e2
```

which is to say, if we attempt to pull a key out of an empty container, we get
back an empty result. At a higher level, this means that "empty" containers
really are empty.

Our other constraint from `get-hom` is the following:

```mathstuff
forall k m1 m2.
  get k (m1 .1 m2) = get k m1 .2 get k m2
```

which states that getting a key out of a merged map is the same as merging the
values obtained by getting that key in either map. At a higher level, we're
saying "merging really does do merging---and doesn't do anything else!"

A `get`-based monoid homomorphism seems like it correctly classifies the
behavior we'd like. Is the same true for `set-hom`?

```agda
    -- set-hom
    --   : (m : Map)
    --   → (k : Key)
    --   → IsMonoidHom val-monoid map-monoid (set m k)
```

What laws fall out of this? The first is that we have a distribution of `_∙_`
over `set`:

```mathstuff
forall m k v1 v2.
  set m k (v1 .1 v2) = set m k v1 .2 set m k v2
```

All told, this law looks good. Merging two maps with the same key is the same as
just merging the values at those keys. Note that this is probably surprising
behavior if you haven't seen it before. Most data structures will simply
*replace* the value at a key with another if it overlaps. Perhaps that's an
indication that this is the wrong law? I would argue no; we can get the
"replacement"-style implementation by choosing the "last value wins" monoid:

```agda
-- module _ {A : Set} where
  -- open monoid (setoid (Maybe A))
  open IsMonoid

  last : {A : Set} → Maybe A → Maybe A → Maybe A
  last a (just x) = just x
  last a nothing = a

  last-monoid
      : {A : Set}
      → IsMonoid (setoid (Maybe A)) last nothing
  ∙-assoc last-monoid a b (just x)  = refl
  ∙-assoc last-monoid a b nothing   = refl
  ε-unitˡ last-monoid (just x)  = refl
  ε-unitˡ last-monoid nothing   = refl
  ε-unitʳ last-monoid a         = refl
  ∙-cong₂ last-monoid refl refl = refl
```

The `last-wins` gives us the traditional behavior of data structures: that
writes are destructive to the value previously there. We need to do a little
lifting however, since for an arbitrary type `A` we don't have a suitable unit
value. So instead of using `A` directly we use `Maybe A`, which extends `A` with
`nothing`, and we use this value as our unit.

By parameterizing our data container over its monoidal structure, we can pull
extra behavior out of it. Users now have more options as to how it should
behave, and this customizability comes without any cost; in fact, it gives us a
more elegant specification of how the container should behave.

Unfortunately, as we push through with this monoid homomorphism for `set`, we
realize that this might not be the best choice. Our next required law indicates
why:

```mathstuff
forall m k.
  set m k e1 = e2
```

This states that inserting an empty value into the map should *delete* the rest
of the contents of the map! Egads! Surely this is a step too far, and suggests
that we did not in fact want a *monoid* homomorphism for `set`. But since the
`_∙_` law is desirable, is there something weaker we can require of `set`?


## Semigroups

As a matter of fact, there is. We can weaken the `Monoid` structure by dropping
the `ε` element and relevant laws. We're left with just the associative binary
operation, in an algebraic structure known as a *semigroup:*

```agda
module semigroup {c l : Level} (eq : Setoid c l)  where
  -- open Setoid eq renaming (_≈_ to _≈_; Carrier to A)
  -- record Semigroup : Set (lsuc (c ⊔l l)) where
  --   constructor semigroup
  --   infixr 5 _∙_
  --   field
  --     _∙_ : A → A → A
  --     ∙-assoc : (a b c : A) → (a ∙ b) ∙ c ≈ a ∙ (b ∙ c)
```

Exercise

:   Show that every monoid is a semigroup.


Solution

:   ```agda
module _ {c l : Level} (eq : Setoid c l) where
  -- open monoid eq
  -- open semigroup eq
  -- open Semigroup
  -- open Monoid
  --   ```

  --   ```agda
  -- monoid→semigroup : Monoid → Semigroup
  -- _∙_ (monoid→semigroup x) = x ._∙_
  -- ∙-assoc (monoid→semigroup x) = x .∙-assoc
    ```


Because semigroups are weaker notions that monoids, there are strictly more
semigroups than monoids. For example, while there's a `max` monoid over
naturals:

```agda
module _ where
  -- open monoid (setoid ℕ)
  -- open Monoid
  -- open import Data.Nat.Properties

  -- max-monoid : Monoid
  -- _∙_ max-monoid = _⊔_
  -- ε max-monoid = 0
  -- ∙-assoc max-monoid = ⊔-assoc
  -- ε-unitˡ max-monoid = ⊔-identityˡ
  -- ε-unitʳ max-monoid = ⊔-identityʳ
  -- ∙-cong₂ max-monoid refl refl = refl
```

which uses 0 as the identity element, since it's the smallest possible natural
number, we don't have a corresponding `min` monoid---because we don't have an
identity element! In this case, we have two options: extend the naturals with a
"top" element `+∞` that is guaranteed to be bigger than every other number, or
settle for building a semigroup. We will do the latter here.

```agda
module _ where
  -- open semigroup (setoid ℕ)
  -- open Semigroup
  -- open import Data.Nat.Properties

  -- min-semigroup : Semigroup
  -- _∙_ min-semigroup = _⊓_
  -- ∙-assoc min-semigroup = ⊓-assoc
```

We can follow the same pattern as when we defined monoid homomorphisms to build
semigroup homomorphisms:

```agda
-- module semigroup-hom {c l : Level}
--             {s1 s2 : Setoid c l}
--             (m1 : semigroup.Semigroup s1)
--             (m2 : semigroup.Semigroup s2) where
--   open semigroup
--   open Setoid s1 renaming (Carrier to A; _≈_ to _≈₁_)
--   open Setoid s2 renaming (Carrier to B; _≈_ to _≈₂_)
--   open Semigroup m1 renaming (_∙_ to _∙₁_)
--   open Semigroup m2 renaming (_∙_ to _∙₂_)

  -- record IsSemigroupHom (f : A → B) : Set (lsuc (c ⊔l l)) where
  --   field
  --     preserves-∙ : (a b : A) → f (a ∙₁ b) ≈₂ f a ∙₂ f b
  --     f-cong : (a b : A) → a ≈₁ b → f a ≈₂ f b
```

Exercise

:   Show that every monoid homomorphism gives rise to a semigroup homomorphism.


Solution

:   ```agda
-- module _ {c l : Level} {s1 s2 : Setoid c l}
--     (m1 : monoid.Monoid s1)
--     (m2 : monoid.Monoid s2) where
--   open Setoid s1 renaming (Carrier to A)
--   open Setoid s2 renaming (Carrier to B)
--   open monoid-hom m1 m2
--   open semigroup-hom (monoid→semigroup s1 m1) (monoid→semigroup s2 m2)
--   open IsMonoidHom
--   open IsSemigroupHom
    ```

```agda
  -- monoid-hom→semigroup-hom : {f : A → B} → IsMonoidHom f → IsSemigroupHom f
  -- preserves-∙ (monoid-hom→semigroup-hom x) = x .preserves-∙
  -- f-cong (monoid-hom→semigroup-hom x) = x .f-cong
```

