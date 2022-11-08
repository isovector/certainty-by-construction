## Algebraic Structures

```agda
open import Relation.Binary using (Setoid)
open import Agda.Primitive using (Level; lsuc; _⊔_)

module structures where

open import Data.Bool
open import Data.List
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

