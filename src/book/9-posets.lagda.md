# Partially Ordered Sets

```agda
module 9-posets where

open import Agda.Primitive
open import 8-iso
```


*Partially ordered sets* generalize our everyday notion of comparison --- that
is, to ask, "is this thing less than that other thing?" We are most familiar
with orderings in the context of the number line, which is a helpful starting
point, but doesn't cover the whole story.

Orderings over numbers have a property that you might take for granted, that is,
they are *total.* For any two numbers $a$ and $b$, you can decide whether $a <
b$, $a = b$ or $a > b$. This is an extremely strong property, and requiring it
would filter out many things we'd otherwise like to order. For example, consider
a family tree where we can say person $a$ is less than person $b$ if $a$ is
below $b$ (or if $a$ *is* $b$) in the family tree. Such a thing certainly feels
like an ordering, but it isn't total; for example, my neither my wife's parents
are neither above nor below my parents, since they exist in an unrelated
branches of the family tree.

The opposite of a total relation is a partial one, and since we don't require
totality, our ordering is thus a partial one. Therefore, "partially ordered
sets."

What properties would we expect of an ordering? Like equivalence relationships,
we will require reflexivity and transitivity. However, symmetry doesn't hold in
an ordering, and this is in fact the defining characteristic of an ordering.
Instead, we'd prefer a different, though similar, property, namely
*antisymmetry*. Antisymmetry is the property that if we know `a ≤ b` and that `b
≤ a`, then we know $a ≈ b$. That is to say, the only sort of cycles that are
allowed in a poset are those from an element to itself.

We can formalize this notion of `Antisymmetry` in Agda as a function of two
relations:

```agda
Antisymmetric
  : {c ℓ₁ ℓ₂ : Level} {A : Set c}
  → (A → A → Set ℓ₁)
  → (A → A → Set ℓ₂)
  → Set (c ⊔ ℓ₁ ⊔ ℓ₂)
Antisymmetric {A = A} _≈_ _≤_ = {i j : A} → i ≤ j → j ≤ i → i ≈ j
```

This definition comes directly from `Relation.Binary.Definitions` if you need it
in the future and don't want to define it yourself.

```agda
open import Relation.Binary.Definitions hiding (Antisymmetric)
```

We can now dive into giving the definition of a poset: a record parameterized by
the `_≤_` relationship we are asserting is a poset. Like everything we do, we
require an equivalence relation on the underlying carrier `A` to having a
meaningful notion of "equality" when discussing antisymmetry.

```agda
private variable
  c ℓ : Level

module _ {A : Set c} ⦃ _ : Equivalent ℓ A ⦄ (_≤_ : A → A → Set ℓ) where
  record Poset : Set (c ⊔ ℓ) where
    field
      refl : Reflexive _≤_
      antisym : Antisymmetric _≋_ _≤_
      trans : Transitive _≤_

```

In addition, we will introduce the notions of *top* and *bottom* elements. These
are elements in the set which are greater than and less than every other element
in the set. Not ever poset has top and bottom elements, but some do, and we will
keep an eye out for them as we go forwards.

```agda
  Top : A → Set (c ⊔ ℓ)
  Top top = (a : A) → a ≤ top

  Bottom : A → Set (c ⊔ ℓ)
  Bottom bot = (a : A) → bot ≤ a
```

Rather interestingly, top (and bottom p elements are guaranteed to be unique, if
they exist. This is an easy thing to prove; given two top elements, they most
both be bigger than the other, and thus be equal by antisymmetry.

```agda
  Top-unique : {x y : A} → Poset → Top x → Top y → x ≋ y
  Top-unique {x} {y} pos e≤x e≤y =
    pos .Poset.antisym (e≤y x) (e≤x y)
```

The dual fact holds for bottom elements, for exactly the same reasons:

```agda
  Bottom-unique : {x y : A} → Poset → Bottom x → Bottom y → x ≋ y
  Bottom-unique {x} {y} pos x≤e y≤e =
    pos .Poset.antisym (x≤e y) (y≤e x)
```

Let's close out the module, and then do a little ritual to get the Agda
environment into the right state for the remainder of the chapter.

```agda
open Poset

import Relation.Binary.PropositionalEquality as PropEq
open PropEq using (cong)
```

## Examples of Posets

Look around you. There are partial orderings everywhere you look. But we can
start slowly, and show that there is a partial ordering on booleans in the way
you'd expect, namely that `false ≤ true`. We need to define a data type that
witnesses this fact, beginning with a constructor that shows that false is a
bottom element:

```agda
module _ where
  open import Data.Bool

  data _≤B_ : Bool → Bool → Set where
    f≤b : {b : Bool} → false ≤B b
```

Dually, we could give a constructor `b≤t : {b : Bool} → b ≤B true`, but doing so
means we would have two ways of proving `false ≤ true` --- via `f≤b {true}` and
via `b≤t {false}`. Your life in Agda and mathematics will be easier if you try
to avoid situations in which there are different representations of the same
proof. Of course, it's often not possible to avoid, but when you, you will be
rewarded with less of a proving burden.

Instead, recognizing that the only thing we're unable to prove is that `true ≤
true`, we can add a constructor that witnesses only that fact:

```agda
    t≤t : true ≤B true
```

It's trivial to show that `false` is a bottom element, and that `true` is the
top element:

```agda
  false-bottom : Bottom _≤B_ false
  false-bottom a = f≤b

  true-top : Top _≤B_ true
  true-top false = f≤b
  true-top true = t≤t
```

Showing that `_≤B_` forms a poset is nothing more than running the maze; all
that's required is to match on the constructors and use the only thing that can
possibly type check to fill the holes. The poset is presented without further
comment.

```
  ≤B-poset : Poset _≤B_
  refl ≤B-poset {false} = f≤b
  refl ≤B-poset {true} = t≤t
  antisym ≤B-poset f≤b f≤b = PropEq.refl
  antisym ≤B-poset t≤t b≤a = PropEq.refl
  trans ≤B-poset f≤b b≤c = f≤b
  trans ≤B-poset t≤t t≤t = t≤t
```

Another poset is the usual ordering over the natural numbers. We can construct
it in a similar fashion to the poset over booleans; namely, by observing that 0
is the bottom element, and then seeing what other case we have to prove. We
begin:

```agda
module _ where
  open import Data.Nat

  data _≤ℕ_ : ℕ → ℕ → Set where
    z≤n : {n : ℕ} → zero ≤ℕ n
```

We can now show a `zero` on the left side, but what about a `suc`? Well, a `suc`
is never less than a `zero`, so we must have `suc` on both cases. The only time
`suc m ≤ suc n` is if `m ≤ n`, which completes our reasoning and leads directly
to our only other means of constructing a natural order on the natural numbers:

```agda
    s≤s : {m n : ℕ} → m ≤ℕ n → suc m ≤ℕ suc n
```

Once again we can show that 0 is a bottom element, but observe that since there
is no biggest natural number, there is therefore no top element.

```agda
  0-bottom : Bottom _≤ℕ_ 0
  0-bottom a = z≤n
```

Showing that `_≤ℕ_` forms a poset is only slightly more involved than `_≤B_`;
the only difference is the requirement of a `cong` to show antisymmetry in the
`suc/suc` case. But otherwise it's just business as usual.

```agda
  ≤ℕ-poset : Poset _≤ℕ_
  refl ≤ℕ-poset {zero} = z≤n
  refl ≤ℕ-poset {suc x} = s≤s (refl ≤ℕ-poset)
  antisym ≤ℕ-poset {.zero} {.zero} z≤n z≤n = PropEq.refl
  antisym ≤ℕ-poset {.(suc _)} {.(suc _)} (s≤s a≤b) (s≤s b≤a) =
    cong suc (antisym ≤ℕ-poset a≤b b≤a)
  trans ≤ℕ-poset z≤n b≤c = z≤n
  trans ≤ℕ-poset (s≤s a≤b) (s≤s b≤c) =
    s≤s (trans ≤ℕ-poset a≤b b≤c)
```

## The Poset of Substrings

Perhaps the examples we've shown thus far have lulled you into a false sense of
security. They frankly are not particularly interesting cases of posets, for two
reasons. One, these examples correspond with your mental intuition as to what an
ordering should be. And two, these examples are both *total* orders, and so we
don't have any funny business in which things we can compare. But let's take
this as an opportunity to look into a much more interesting poset:
*non-consecutive substrings.*

We can define a poset over lists, such that list $a$ is less than list $b$ if
there is some series of insertions into $a$ that produce $b$. That is, `"cat"`
is less than `"cast"`, but there is no ordering between `"foo"` and `"bar"`.
This operation probably doesn't seem like any ordering you've ever seen before,
but it does indeed form a poset.

But before we can show that substrings form a poset, we must first define a type
that constructs the relationship we'd like. For simplicity, we'll just define
this over lists of `Set` using propositional equality as our notion of
equivalence, but that is just to not unnecessarily muddy the waters.

We begin with a module to parameterize the contents of our lists, assert an
`Equivalent` instance for those lists, and create a few variables to refer to
later.

```agda
module _ (A : Set) where
  open import Data.List

  private instance
    ListA-equiv = ≡-equiv (List A)


  private variable
    a : A
    l l₁ l₂ : List A
```

So what are the ways we can show one string is a substring of another? As in our
earlier examples, there's a trivial case, namely that the empty list is a
substring of all lists:


```agda
  data _SubstrOf_ : List A → List A → Set where
    []≤ : [] SubstrOf l
```

Furthermore, we know that if one list is a substring of another, then that
invariant is not broken if we cons the same element on front of either list.
Therefore, we can build a `_SubstrOf_` via `match`:

```agda
    match : l₁ SubstrOf l₂ → (a ∷ l₁) SubstrOf (a ∷ l₂)
```

And for our final case, we know that if one list is a substring of another, then
we can always cons an element onto the bigger element without breaking our
invariant. And thus our last case is `insert`:

```agda
    insert : l₁ SubstrOf l₂ → l₁ SubstrOf (a ∷ l₂)
```

As it happens, we didn't need to define `_≤ℕ_` ourselves. It turns out that we
were not the first people to think of defining a less-than ordering on the
natural numbers, and we can instead find this (and much more machinery) in
`Data.Nat`, alongside with properties of the less-than relationship in
`Data.Nat.Properties`.

```agda
  open import Data.Nat
  open import Data.Nat.Properties
```

Before showing our poset, let's first define a little lemma, namely that
`length` is a homomorphism from `_SubstrOf_` to `_≤_` (the ordering on the
natural numbers.) We can show this via `_Preserves_⟶_`, and it's a good exercise
to cut our teeth on.

```agda
  open import Relation.Binary using (_Preserves_⟶_)
```


Exercise

:   Show
    ```agda
  substr-cong-length : length Preserves _SubstrOf_ ⟶ _≤_
    ```


Solution

:   ```agda
  substr-cong-length []≤ = z≤n
  substr-cong-length (match x) =
    s≤s (substr-cong-length x)
  substr-cong-length {[]} (insert x) =
    z≤n
  substr-cong-length {x₁ ∷ l₁} (insert {l₂ = l₂} {a = a} a≤b) = begin
    length (x₁ ∷ l₁)  ≤⟨ substr-cong-length a≤b ⟩
    length l₂         ≤⟨ ≤-step ≤-refl ⟩
    1 + length l₂     ≡⟨⟩
    length (a ∷ l₂)   ∎
    where open ≤-Reasoning
    ```

We will need two more lemmas in order to show our poset on substrings. The first
is that it is not the case that $1 + n ≤ 1$. It's easy to show by a simple
recursion:

```agda
  open import Relation.Nullary

  lies : {n : ℕ} → ¬ (1 + n ≤ n)
  lies (s≤s x) = lies x
```

Our other lemma states that if $1 + m ≤ n$ then it is not the case that $1 + n ≤
m$, and is also an easy, single step of recursion.

```agda
  lies₂ : {m n : ℕ} → 1 + m ≤ n → ¬ (1 + n ≤ m)
  lies₂ (s≤s m≤n) (s≤s n≤m) = lies₂ m≤n n≤m
```

Showing reflexivity is never hard, and subsets are no exception:

```agda
  substr-pos : Poset _SubstrOf_
  refl substr-pos {[]} = []≤
  refl substr-pos {x ∷ xs} = match (refl substr-pos)
```

Transitivity is also straightforward in the case of subsets. We need to split on
every case of both proofs, and then find something that typechecks to fill the
solution, but there is little of interest here.

```agda
  trans substr-pos []≤ b≤c = []≤
  trans substr-pos (match a≤b) (match b≤c)
    = match (trans substr-pos a≤b b≤c)
  trans substr-pos (match a≤b) (insert b≤c)
    = insert (trans substr-pos (match a≤b) b≤c)
  trans substr-pos (insert a≤b) (match b≤c)
    = insert (trans substr-pos a≤b b≤c)
  trans substr-pos (insert a≤b) (insert b≤c)
    = insert (trans substr-pos (insert a≤b) b≤c)
```

Having saved the most interesting bits for last, we turn our attention to the
last remaining property: antisymmetry. Showing antisymmetry for the `[]≤` and
`match/match` cases come naturally:


```agda
  antisym substr-pos []≤ []≤ = PropEq.refl
  antisym substr-pos (match a≤b) (match b≤a) =
    cong (_ ∷_) (antisym substr-pos a≤b b≤a)
```

but challenges immediately pop up as soon as we have an `insert` proof. When we
look at `match/insert` for example

```agda
  antisym substr-pos (match a≤b) (insert b≤a)
```

our goal becomes to show `a ∷ l₁ ≡ a ∷ l₂`, given the following two proofs:

```info
a≤b : l₁ SubstrOf l₂
b≤a : (a ∷ l₂) SubstrOf l₁
```

Something looks horribly wrong here. We're being asked to show that `l₁` is
equal to `l₂`, but this is unlikely to be the case, because the `insert`
constructor we're matching on states that `l₁` *couldn't* have matched `l₂`.
What can we do? Thankfully, our proofs of `a≤b` and `b≤a` shed some light on the
situation. If we interpret these proofs as statements about the lengths of their
lists, we have the following set of inequalities:

```info
length l₁ ≤ length l₂
1 + length l₂ ≤ length l₁
```

Doing some light syntactic replacement, and we see the above is equivalent to:

```info
        x ≤ y
1 + y ≤ x
```

which you will notice is an impossible state of affairs. What we can infer from
this little proof is that it *can never be the case* that we are asked to show
antisymmetry of a `match` constructor with an `insert` constructor. It simply
can't happen based on how we set up the problem. Unfortunately, Agda isn't smart
enough to figure this out on its own, and so we must help it understand.

Recall the lemmas we wrote before starting to show the poset. The lemma of
importance right now is `lies : {n : ℕ} → ¬ (1 + n ≤ n)`. Letting `n = length
l₂`, we can push our `a≤b` and `b≤a` proofs through `substr-cong-length` to get
equivalent statements about the lengths of the corresponding lists. Then,
`≤-trans` can glue them together, and finally `lies` will show the
contradiction.

```agda
    with lies (≤-trans (substr-cong-length b≤a) (substr-cong-length a≤b))
```

Once we've shown a contradiction, Agda is smart enough to realize there is no
more work to be done, so all we need to do is pattern match on the resulting
proof from `lies` and we're home free:


```agda
  ... | ()
```

A similar story holds for the other two cases of `antisym`; they are both
impossible, but in different ways and requiring us to show different
contradictions.

```agda
  antisym substr-pos (insert a≤b) (match b≤a)
    with lies (≤-trans (substr-cong-length a≤b) (substr-cong-length b≤a))
  ... | ()
  antisym substr-pos (insert {a = a} a≤b) (insert {a = b} b≤a)
    with lies₂ (substr-cong-length a≤b) (substr-cong-length b≤a)
  ... | ()
```


## Meets and Joins

Some, but not all, posets have *joins,* also known as a *least upper bound.*
That is, given elements `x` and `y` in the poset, can we find a unique element
`z` which is the smallest element that's "at least as big" as `x` and `y`? In
the family tree, two cousin's join is their grandparent (assuming they have only
one --- if they have two grandparents, the join is not unique and thus doesn't
exist!)

A *meet* is the exact same idea, except it reverses the directions of all the
`≤` signs! A meet is the *greatest lower bound.* In the family tree, a couple's
meet is their single child.

Doing some module rites to set up the problem again:

```agda

module _ {A : Set c}
         ⦃ _ : Equivalent ℓ A ⦄
         (_≤_ : A → A → Set ℓ)
         (poset : Poset _≤_)
         where

  open import Data.Product
```

We can formalize the notion of a join with a record to hold all of the necessary
proofs together. `IsJoin x y a` is a proof that the join of `x` and `y` is `a`:

```agda
  record IsJoin (x y : A) (a : A) : Set (c ⊔ ℓ) where
    field
```

Our definition requires us to show that `a` is bigger than both `x` and `y`:

```agda
      x≤a : x ≤ a
      y≤a : y ≤ a
```

and also that `a` is the least it can be. That is, for any other element `z`
which is also less than `x` and `y`, we also have `a ≤ z`.

```agda
      a-is-least : (z : A) → x ≤ z → y ≤ z → a ≤ z
```

`IsJoin` is a proof that a join exists for any particular pair of elements. For
a poset at large, we might want to say it *has all joins*, which is to say, that
for any pair of elements, they have a join:

```agda
  HasJoins : Set (c ⊔ ℓ)
  HasJoins = (x y : A) → Σ A (IsJoin x y)
```

To wet our whistle

