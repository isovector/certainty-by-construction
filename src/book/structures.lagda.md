## Algebraic Structures

```agda
open import Relation.Binary using (Setoid)
open import Agda.Primitive using (Level; lsuc; _⊔_)

module structures where

postulate
  todo : {A : Set} → A

open import Data.Bool
open import Data.List hiding (merge)
open import Data.Nat hiding (_⊔_)
open import Data.Unit

module monoid {c l : Level} (eq : Setoid c l)  where
  open Setoid eq renaming (_≈_ to _≡_; Carrier to A)
```

Now that we have a passing familiarity with our language and tools, it's time to
start grappling with mathematical ideas in earnest. We will begin with a
structure called a *monoid* which is a general interface with vast applications
in everyday programming.

To develop our ability to parse mathematical language, let's look at the
Wikipedia definition of a monoid:

> A monoid is a set equipped with an associative binary operation and an
> identity element.

That sounds pretty straightforward. We can introduce a new type `A`,
corresponding to the "set." The phrase "equipped with" means "these things
always go together," which is to say, we should bundle them up in a record:

```agda
  record Monoid : Set (lsuc (c ⊔ l)) where
    constructor monoid
    infixr 5 _∙_
```

We are equipped with "an associative binary operation." The definition gives no
canonical name, so we must come up with one; because it's a binary operator, it
requires two arguments. Perhaps `_∙_` will do fine for a name. Associativity is
a law regarding how the operation behaves, so we will pass the buck on that for
now.

```agda
    field
      _∙_ : A → A → A
```

We are also equipped with an identity element. An element is just a value of the
type, so all we require is an `A`. Although the passage above doesn't say so,
this element is canonically known as `ε` ("epsilon".)

```agda
      ε : A
```

Returning to the associativity of our binary operation, associativity always
means that we can reassemble parentheses as we please. You should be reminded of
our old `+-assoc` proof in the following definition:

```agda
      ∙-assoc : (a b c : A) → (a ∙ b) ∙ c ≡ a ∙ (b ∙ c)
```

We are also told that `ε` is an identity. Without any more context we are
forced to elaborate on the meaning here. An "identity" means something doesn't
change when the identity is an argument; the only suspect around is `_∙_`. And
since we're not told if `ε` is a left- or a right- unit, we must conclude it's
both. Thus, we also add the following laws to our `Monoid` record:

```agda
      ε-unitˡ : (a : A) → ε ∙ a ≡ a
      ε-unitʳ : (a : A) → a ∙ ε ≡ a
```

The first step to building intuition as to what a mathematical idea *is* is to
start by looking for some examples. We need to pick a set; what happens if we
pick the one-element set `⊤`?

```agda
open import Relation.Binary.PropositionalEquality hiding ([_])
module _ where
  open monoid (setoid ⊤)
  open Monoid
```

Well we'd need to pick a binary operation of type `⊤ → ⊤ → ⊤` of which there is
exactly one: the function that only ever returns `tt`. Likewise, we need an
identity element, which must be `tt : ⊤` since we have no other options.

```agda
  ⊤-monoid : Monoid
  _∙_ ⊤-monoid _ _ = tt
  ε ⊤-monoid = tt
```

As you might expect, this thing follows the laws, but in a very trivial manner:

```agda
  ∙-assoc ⊤-monoid a b c = refl
  ε-unitˡ ⊤-monoid a = refl
  ε-unitʳ ⊤-monoid a = refl
```

Well, we managed to create a trivial monoid. But it wasn't very informative as
to what exactly this thing is. Let's try the next simplest type we know, `Bool`.
Are there any monoids over `Bool`s? Perhaps it's easiest to think about our
binary operation first --- boolean AND is a good candidate of the right shape.
In Agda, this function is called `_∧_`.

We need now to find an identity for `_∧_`, which is `true` if and only if both
of its inputs are `true`. Therefore, if we fill one of its arguments with
`true`, the result of `true ∧_` must be just the second argument, and therefore
`true` is indeed an identity:

```agda
module _ where
  open monoid (setoid Bool)
  open Monoid
  open import Data.Bool.Properties

  true-and-monoid : Monoid
  _∙_ true-and-monoid = _∧_
  ε true-and-monoid = true
  ∙-assoc true-and-monoid = ∧-assoc
  ε-unitˡ true-and-monoid = ∧-identityˡ
  ε-unitʳ true-and-monoid = ∧-identityʳ
```

Exercise

:   Find two other monoid over the booleans.


Solution

:   ```agda
  false-or-monoid : Monoid
  _∙_ false-or-monoid = _∨_
  ε false-or-monoid = false
  ∙-assoc false-or-monoid = ∨-assoc
  ε-unitˡ false-or-monoid = ∨-identityˡ
  ε-unitʳ false-or-monoid = ∨-identityʳ

  false-xor-monoid : Monoid
  _∙_ false-xor-monoid = _xor_
  ε false-xor-monoid = false
  ∙-assoc false-xor-monoid false b c = refl
  ∙-assoc false-xor-monoid true false c = refl
  ∙-assoc false-xor-monoid true true false = refl
  ∙-assoc false-xor-monoid true true true = refl
  ε-unitˡ false-xor-monoid a = refl
  ε-unitʳ false-xor-monoid false = refl
  ε-unitʳ false-xor-monoid true = refl
    ```

Let's now turn our attention to the natural numbers. Do any monoids exist there?


Exercise

:   Find two monoids over the natural numbers. Hint: what associative binary
    operations can you think of?


Solution

:   ```agda
module _ where
  open monoid (setoid ℕ)
  open Monoid
  open import Data.Nat.Properties

  0-+-monoid : Monoid
  _∙_ 0-+-monoid = _+_
  ε 0-+-monoid = 0
  ∙-assoc 0-+-monoid = +-assoc
  ε-unitˡ 0-+-monoid = +-identityˡ
  ε-unitʳ 0-+-monoid = +-identityʳ

  1-*-monoid : Monoid
  _∙_ 1-*-monoid = _*_
  ε 1-*-monoid = 1
  ∙-assoc 1-*-monoid = *-assoc
  ε-unitˡ 1-*-monoid = *-identityˡ
  ε-unitʳ 1-*-monoid = *-identityʳ
    ```

Exercise

:   Show that list concatenation forms a monoid.


Solution

:   ```agda
module _ {A : Set} where
  open monoid (setoid (List A))
  open Monoid
  open import Data.List.Properties

  []-++-monoid : Monoid
  _∙_ []-++-monoid = _++_
  ε []-++-monoid = []
  ∙-assoc []-++-monoid = ++-assoc
  ε-unitˡ []-++-monoid = ++-identityˡ
  ε-unitʳ []-++-monoid = ++-identityʳ
    ```

Armed with a few examples of monoids, we can now take some time to analyze the
situation and try to make sense of the structure. Somehow we need to make sense
of an abstraction that relates addition, multiplication, boolean AND, OR, XOR,
list concatenation, union, intersection, branch insertion and function
composition. At face value, these are very disparate operations; why do they
belong together? What do they have in common?

TODO(sandy): Fill in these other examples

Perhaps things will become clearer if we look at what we can *do* with a monoid.
Consider the following function `summarize`, which takes a `Monoid` record
proving that `M : Set` is a monoid, a function `A → M`, and then transforms a
`BinTree A` into an `M`. We will first implement this function, and then discuss
its importance. We begin as always with the type:

```agda
open import types using (BinTree; branch; empty)

module _ {A : Set} {M : Set} where
  open monoid (setoid M)

  summarize : Monoid → (A → M) → BinTree A → M
```

We have two cases. The first is in which the tree is `empty`. Here we have no
`A` to play with, but we still need to return an `M`. What can we do? Our only
possible way to get our hands on an `M` is to use `ε`:

```agda
  summarize m f empty = ε
    where open Monoid m
```

Our other case is a `branch`, in which case we have left and right subtrees, as
well as a node of type `A`. We can transform each subtree into an `M`
via recursion, and we can turn the node into one via `f`:

```agda
  summarize m f (branch l n r) =
    let l-sum = summarize m f l
        r-sum = summarize m f r
        n-sum = f n
```

and finally we can combine all of these `M`s together generically via `_∙_`:

```agda
     in l-sum ∙ n-sum ∙ r-sum
    where open Monoid m
```

Congratulations! We have just written every possible query (TODO: is this true?)
over binary trees. Let's take a quick example of a tree:

```agda
open import Data.String using (String)

example : BinTree String
example =
  branch
    (branch empty "Glass" empty)
    "Teflon"
    (branch empty "Argon" empty)
```

We can query the number of nodes in the tree by using the `0-+-monoid` and
letting `f = const 1`:

```agda
size : ℕ
size = summarize 0-+-monoid (λ { x → 1 }) example

-- size = 3
```

We can instead flatten the tree into a list (with the query: what are the
elements of the list?) by using the `[]-++-monoid` and letting `f = [_]` (the
singleton list injection):

```agda
elements : List String
elements = summarize []-++-monoid [_] example

-- elements = "Glass" ∷ "Teflon" ∷ "Argon" ∷ []
```

Or we can query whether `"Sandwich"` is in the tree by using `false-or-monoid`:

```agda
has-sandwich : Bool
has-sandwich =
  summarize
    false-or-monoid
      (λ { "sandwich" → true
         ; x          → false
         }
      ) example

-- has-sandwich = false
```

These results are remarkable; all we did was write one function that takes a
monoid and a tree, and gives back some result. The function itself is extremely
general, but can be instantiated to great effect.

The `summarize` function lets us use a function to transform a single value
contained by the tree, uses `_∙_` to combine all the results in a meaningful
way, and fills in empty spaces with `ε` --- a value guaranteed not to change the
answer. In essence, monoids allow for a generalization of the common programming
idiom:

```c
let result = ε
for (var x in c) {
  result = result ∙ f x
}
```

Amazingly, every strictly-positive data structure admits an analogous
`summarize` function.

So, one intuition for what monoids *are* is that they are things that can be
meaningfully combined, and come with a suitable default value. Mathematicians
also like to think of monoids as generalized multiplication; for that reason you
will sometimes hear `_∙_` pronounced as "multiplication" or "times", and `ε`
called the "unit."


### More Monoids

There are infinitely many monoids out there than the ones we've seen. In fact,
most data structures admit at least one monoid; often many. Whenever you design
a new type, you should ask yourself where it admits a monoid, and if so,
provide it!

TODO(sandy): awful. talk about writing your own instances and what not


### Monoid Homomorphisms

Where things start getting interesting, however, is when we have several
different monoids in play simultaneously. It's fun to think about the monoidal
structure with respect to functions. If we have two monoids, one over set $A$
and another over set $B$, is it always the case that a function `f : A → B` will
preserve the monoidal structure? That is to say, will it satisfy the following
equations:

$$
f(\varepsilon) = \varepsilon
$$

and

$$
f(a \cdot b) = f(a) \cdot f(b)
$$

At first glance, these two equations might not appear to typecheck. This is an
unfortunate but common situation in math, arising from its history having been
done by pen and paper. The necessary mental process is that of *elaboration:*
a fancy word for "fiddling with the equation as written, filling in details
until it makes sense." In this case, remember that we have two monoids in play,
and thus two units `ε` and two binary operators `_∙_`. Let's say the `A`-side
monoid is the first one, and the `B`-side is the second. Rewriting our equations
above with this new elaboration, we get:

$$
f(\varepsilon_1) =_2 \varepsilon_2
$$

and

$$
f(a \cdot_1 b) =_2 f(a) \cdot_2 f(b)
$$

where we have been careful to add a subscript even to the equality since we
could have *different* notions of equality on either side of the function.

TODO(sandy): point out that the lhs is just syntax but it's not a thing you can
OBSERVE< so this is actually much harder to implement than it seems

With the definition in front of us, it's clear that not all functions preserve
monoids. Consider some a monoid over some set $A$, with distinct values $a$ and
$\varepsilon$. We can then trivially construct a function $A → A$ which does not
preserve the monoidal structure:

$$
f(x) = a
$$

which clearly doesn't satisfy the `preserves-ε` property, since

$$
f(\varepsilon) \mapsto a
$$

In fact, there is even a simpler proof. We have seen that there are at least two
monoids over the booleans, one for AND and one for OR. But these two monoids
have different units. Therefore, no function that maps into `Bool` can possibly
preserve both units at once!

Since we have now shown in two ways that monoid-preserving-ness is not a trivial
property of functions, it is an interesting exercise to consider which functions
*do indeed* satisfy our laws above. Any such function is known as a *monoid
homomorphism,* and are our first introduction to homomorphisms which will play a
great deal of importance in later chapters.

Before we get into the weeds of finding monoid homomorphisms, let's first define
what it means to be a monoid homomorphism, in more rigor than we have done thus
far. That is to say, let's code it up in Agda.

A monoid homomorphism is a relationship between three things, two monoids, and a
function that maps between the *carriers* (underlying sets) of those monoids.
Because we'll need the two monoids in scope first, we can parameterize our
module over them:

```agda
open monoid
module homs {c l : Level}
            {s1 s2 : Setoid c l}
            (m1 : Monoid s1)
            (m2 : Monoid s2) where
```

Our next step is to get the types `A` and `B` into scope by renaming the
underlying carriers of our monoids:

```agda
  open Setoid s1 renaming (Carrier to A; _≈_ to _≈₁_)
  open Setoid s2 renaming (Carrier to B; _≈_ to _≈₂_)
```

Next, we will unpack the two monoids, renaming their units and operations so we
can differentiate between the two like above with subscripts:

```agda
  open Monoid m1 renaming (_∙_ to _∙₁_; ε to ε₁)
  open Monoid m2 renaming (_∙_ to _∙₂_; ε to ε₂)
```

Finally we're ready to get to the meat of our monoid homomorphism. Whenever you
think about packing laws together, you should immediately jump for a record
type. We still have to tie the homomorphic function into the mix, so we can
parameterize the record by the function in question:

```agda
  record IsMonoidHom (f : A → B) : Set (lsuc (c ⊔ l)) where
```

And then we can write our desired laws down verbatim:

```agda
    field
      preserves-ε : f ε₁ ≈₂ ε₂
      preserves-∙ : (a b : A) → f (a ∙₁ b) ≈₂ f a ∙₂ f b
```

Now that we have the machinery in place to prove we're not fooling ourselves,
let's begin hunting for a monoid homomorphism. The `⊤` type seems too simple, so
let's instead think about functions between booleans. We know two monoid
homomorphisms, AND and OR, so maybe we could find a homomorphism between those
monoids.

```agda
module _ where
  open homs true-and-monoid false-or-monoid
  open IsMonoidHom
```

Given the constraints of the problem, we are looking for a function `f : Bool →
Bool`, with the property that `f true = false`. There are only two such
functions, `const false` and `not`. The latter seems more promising, so let's
try that:

```agda
  not-hom₁ : IsMonoidHom not
```

The proofs, as it happen, are trivial:

```agda
  preserves-ε not-hom₁ = refl
  preserves-∙ not-hom₁ false b = refl
  preserves-∙ not-hom₁ true b  = refl
```

which works like a charm.


Exercise

:   Show that there is also a homomorphism between these two monoids for `const false`.


Solution

:   ```agda
  open import Function
  dumb : IsMonoidHom (const false)
  preserves-ε dumb = refl
  preserves-∙ dumb false b = refl
  preserves-∙ dumb true b  = refl
    ```

Returning to `not-hom₁`, we have shown (via `preserves-∙`):

$$
\neg (a \wedge b) = \neg a \vee \neg b
$$

which is one half of the famous "De Morgan's laws." Can we show the other
direction, namely

$$
\neg (a \vee b) = \neg a \wedge \neg b
$$

In order to do this, we'll need to swap the direction of our monoid
homomorphism. Before we were looking for a homomorphism from `true-and-monoid`
to `false-or-monoid`, but now we need to go the other way around. Thus we can
start a new module and instantiate `IsMonoidHom` in the desired direction:

```agda
module _ where
  open homs false-or-monoid true-and-monoid
  open IsMonoidHom
```


Exercise

:   Show the other half of De Morgan's law.


Solution

:   ```agda
  not-hom₂ : IsMonoidHom not
  preserves-ε not-hom₂ = refl
  preserves-∙ not-hom₂ false b = refl
  preserves-∙ not-hom₂ true b  = refl
    ```

Perhaps you're beginning to see, if not yet the use, at least the importance of
monoid homomorphisms. We managed to rediscover an important mathematical fact
simply by looking for an example! By looking for monoid homomorphisms, we have
seemingly found a good means of pruning the mathematical search space of good
ideas.

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
module _ {A : Set} where
  open homs ([]-++-monoid {A}) 0-+-monoid
  open IsMonoidHom
```

As previously identified, `length` forms a homomorphism between these two
monoids. All we have left to do is to show it:

```agda
  length-hom : IsMonoidHom length
  preserves-ε length-hom = refl
  preserves-∙ length-hom [] b = refl
  preserves-∙ length-hom (x ∷ a) b =
    cong suc (preserves-∙ length-hom a b)
```

Monoid homomorphisms allow us to reify this idea that there are two ways to get
to the same place, and therefore that the two ways must be equivalent. I like to
think about homomorphisms as "preserving metaphors" --- that is to say, anything
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
  postulate
    Map Key Val : Set

    get : Key → Map → Val
    set : Map → Key → Val → Map
```

and two monoids, one over `Map`s and one over `Val`s:

```agda
    map-monoid : Monoid (setoid Map)
    val-monoid : Monoid (setoid Val)
```

With this infrastructure in place, we can assert a huge amount of "does what
you'd expect" on the implementations of `get` and `set` by showing the following
two monoid homomorphisms:

```agda
  open homs

  postulate
    get-hom
      : (k : Key)
      → IsMonoidHom map-monoid val-monoid (get k)

    -- TODO(sandy) this can't be a monoid hom, it should only be a semi hom
    set-hom
      : (m : Map)
      → (k : Key)
      → IsMonoidHom val-monoid map-monoid (set m k)
```

You'll notice here that we haven't instantiated the `homs` module with any
arguments, and therefore those arguments get distributed onto every use of
`IsMonoidHom`, which is why it now takes three arguments when it used to take
only one.

Anyway, returning to doing-what-you'd-expect, we can think of the conditions
from `get-hom` as these:

```math
forall k.
  get k ε₁ = ε₂
```

which is to say, if we attempt to pull a key out of an empty container, we get
back an empty result. At a higher level, this means that "empty" containers
really are empty.

Our other constraint from `get-hom` is the following:

```math
forall k m1 m2.
  get k (m1 ∙₁ m2) = get k m1 ∙₂ get k m2
```

which states that getting a key out of a merged map is the same as merging the
values obtained by getting that key in either map. At a higher level, we're
saying "merging really does do merging!"









