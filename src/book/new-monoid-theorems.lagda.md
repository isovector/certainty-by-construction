## Theorems about Monoids

```agda
module new-monoid-theorems where

open import 8-structures
```

It's time to get a feel for proving things about abstract algebraic structures.
That means we'll need to be working with arbitrary monoids, and need to show
what holds over them. We can begin with a little bit of Agda module management
to help wrangle our monoids into a more usable format:

```agda
open import Agda.Primitive using (Level)
open import Relation.Binary using (Setoid)
open import Data.Product

open Setoid using (Carrier)
open monoid

module use-monoid {c l} {s : Setoid c l} (m : Monoid s) where
  open Setoid s public renaming (Carrier to A)
  open monoid.Monoid m public
```

Now, given some monoid `m`, we can use `open use-monoid m` to unpack all of the
relevant pieces we'll need --- things like getting its carrier set into scope
(named `A `), as well as its `ε` and `_∙_`, and associated laws. It's a small
touch, but it saves on a lot of typing in the long run.

As our first theorem, we can show that there is only one unit for any given
monoid. There is a common trick for showing uniqueness, which is to show that if
you have some other object that behaves in the same way, to then provide a proof
that the two things are in fact equal. That is to say, if we have some other
element `ε'` that acts like exactly like a `ε`, then it must be the case that `ε
≈ ε'`!

Notice that our setup here made no mention of the *particular* monoid under
consideration, therefore, we'd like to show the uniqueness of units for all
monoids. The trick to doing this is to setup a new `module` parameterized by a
given monoid:

```agda
module _ {c l} {s : Setoid c l} (m : monoid.Monoid s) where
```

which we can then open via `use-monoid`, as well as enable module-wide setoid
reasoning for `s`:

```agda
  open use-monoid m
  open import Relation.Binary.Reasoning.Setoid s
```

We're now ready to prove generic properties about all monoids. So let's show the
uniqueness of `ε`. First, we take some other element `ε'`:

```agda
  uniqueness-of-ε
    : (ε' : A)
```

which has the two identity properties with respect to `_∙_`. We encode this as a
single argument whose type is a *pair* of the left and right identities, to cut
down on typing. This is not of importance; you could instead pass two identity
laws.

```agda
    → ((a : A) → ε' ∙ a ≈ a × a ∙ ε' ≈ a)
```

And finally, we need to show `ε'` was in fact our unit all along:

```agda
    → ε' ≈ ε
```

The proof of this theorem is rather delightful. Since `ε` is an identity, it
means we can reintroduce it on the left without changing the expression. And
then since `ε'` is also an identity, we can remove it from the right.

```agda
  uniqueness-of-ε ε' x = begin
    ε'      ≈⟨ sym (ε-unitˡ ε') ⟩
    ε ∙ ε'  ≈⟨ proj₂ (x ε) ⟩
    ε       ∎
```

Tada! Like magic, we have transformed `ε'`  into `ε`, and therefore shown `ε`
must be unique.

TODO(sandy): what else do we have in this area?


## Free Constructions

A *free X* (where $X$ is an algebraic structure, for example, the free monoid)
is a structure that satisfies all of the requirements of $X$ without any extra
baggage.


```agda

module _ where
  open Relation.Binary.IsEquivalence
  open Setoid

  _⇨_ : {c l : Level} → Set → Setoid c l → Setoid c l
  Carrier (A ⇨ x) = A → Carrier x
  _≈_ (A ⇨ x) f g = (a : A) → (_≈_ x) (f a) (g a)
  refl (isEquivalence (A ⇨ x)) a = refl x
  sym (isEquivalence (A ⇨ x)) p a = sym x (p a)
  trans (isEquivalence (A ⇨ x)) p1 p2 a = trans x (p1 a) (p2 a)

module _ {X : Set} {s : Setoid _ _} (m : Monoid s) where
  open monoid-hom ([]-++-monoid {X}) m
  open use-monoid m
  open import Relation.Binary.Reasoning.Setoid s
  open import Data.List
  import Relation.Binary.PropositionalEquality as PropEq

  fold : (X → A) → List X → A
  fold f [] = ε
  fold f (x ∷ xs) = f x ∙ fold f xs

  open IsMonoidHom

  list-is-free : (f : X → A) → IsMonoidHom (fold f)
  preserves-ε (list-is-free f) = begin
    fold f (Monoid.ε []-++-monoid)  ≡⟨⟩
    fold f []                       ≡⟨⟩
    ε                             ∎
  preserves-∙ (list-is-free f) [] y = begin
    fold f ([] ++ y)  ≡⟨⟩
    fold f y          ≈⟨ sym (ε-unitˡ (fold f y)) ⟩
    ε ∙ fold f y      ∎
  preserves-∙ (list-is-free f) (x ∷ xs) ys = begin
    fold f (x ∷ xs ++ ys)          ≡⟨⟩
    f x ∙ fold f (xs ++ ys)
          ≈⟨ ∙-cong₂ refl (preserves-∙ (list-is-free f) xs ys) ⟩
    f x ∙ (fold f xs ∙ fold f ys)
          ≈⟨ sym (∙-assoc (f x) (fold f xs) (fold f ys)) ⟩
    (f x ∙ fold f xs) ∙ fold f ys  ≡⟨⟩
    fold f (x ∷ xs) ∙ fold f ys    ∎
  f-cong (list-is-free f) a b x = begin
    fold f a  ≡⟨ PropEq.cong (fold f) x ⟩
    fold f b  ∎

  open import iso
  open _↔_

  Really-free : (X ⇨ s) ↔ PropEq.setoid (Σ (List X → A) IsMonoidHom)
  to Really-free f = fold f , list-is-free f
  from Really-free (f , hom) x = f [ x ]
  left-inverse-of Really-free f x = begin
    f x ∙ ε  ≈⟨ ε-unitʳ (f x) ⟩
    f x      ∎
  right-inverse-of Really-free = {! !}



```
