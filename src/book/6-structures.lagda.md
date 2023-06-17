# Structured Sets

Hidden

:   ```agda
{-# OPTIONS --allow-unsolved-metas #-}
    ```

```agda
module 6-structures where

open import Level
  using (Level)
  renaming (zero to lzero; suc to lsuc; _⊔_ to _⊔l_)
```

-- TODO(sandy): removeme

```agda
postulate
  leave-me-as-a-hole : {a : Level} {A : Set a} → A
```



A huge amount of mathematical objects are the *structured sets*---that is,
objects defined by the following template:

> A [widget]{.underline} is a [variety of set]{.underline} equipped with [some
> operations]{.underline} and [some elements]{.underline}, subject to
> [laws]{.underline}.

This is a concise definition of a mathematical widget, and being able to quickly
parse definitions like these is essential to getting real work done. Of course,
having the definition is only the first hurdle; what's much more important is
gaining the related intuition behind what this widget is and why we should care
about it.


## Monoids

The first structured sets we'll look at are the *monoids,* because of their
relative mathematical simplicity, and their extreme relevance in programming.
The definition of a monoid is given as:

> A monoid is a set equipped with an associative binary operation `field:_∙_`
> and an identity element `field:ε`.

Left implicit, but not unsaid, in this definition are the laws to which monoids
are subject. We are told that `field:_∙_` is associative, which means the
construction is subject to the law

$$
a \cdot (b \cdot c) = (a \cdot b) \cdot c
$$

and furthermore, we are told that `field:ε` is an identity element. Since
identity elements are always identities *with respect to an operation,* and
there is only one operation mentioned, we are to assume that `field:ε` is an
identity for `field:_∙_`. Thus, a monoid must also be subject to the laws:

$$
\begin{aligned}
\epsilon \cdot x &= x \\
x \cdot \epsilon &= x
\end{aligned}
$$

As a note on terminology, the `field:_∙_` operator is often called
*multiplication*, and `field:ε` is often called the *unit.* These are historical
artifacts from the early days, but the usage is widespread and we will continue
in that tradition here unless the use would be confusing in context.

Let's see what happens when we code up all of this structure. There are some
subtleties here that we don't yet have the experience to appreciate, so we'll
sandbox our definition into a "naive" module:

```agda
module Sandbox-Naive-Monoids where
```

As preparation for later, we can give a definition for `type:Op₂`, which is the
type of binary operations:

```agda
  Op₂ : ∀ {ℓ} → Set ℓ → Set ℓ
  Op₂ A = A → A → A
```

We will also need propositional equality in scope, and use it to instantiate all
of the relevant algebraic definitions, like those of associativity and
identities. The syntax here is a little roundabout, due to us wanting to keep
everything polymorphic, but you should be able to follow along with the
following, even without necessarily knowing why:

```agda
  open import Relation.Binary.PropositionalEquality
  import Algebra.Definitions

  -- TODO(sandy): just define assoc / identity for ourselves?
  open module Def {ℓ} {A : Set ℓ}
    = Algebra.Definitions {A = A} _≡_
```

-- TODO(sandy): rewrite this paragraph

The module `module:Algebra.Definitions` is parameterized by an equality
relationship, which we must fill in before we can use its definitions. We'd like
to fill it in with a polymorphic version of `type:_≡_`, but Agda is quick to
monomorphize things. Thus, we must tell Agda to use a polymorphic variable `A`,
but we don't have one in scope, thus we must do the new module song and dance.
This module exists only to bring `A : Set ℓ` into scope so that we can pass it
to the instantiation of `type:_≡_` at [1](Ann). Finally, since this import is
happening inside a module, we add `keyword:public` to the import statement at
[2](Ann) in order to say that we'd like to also *export* any definitions that we
import. The end result is that the containing scope has now managed to import
`module:Algebra.Definitions` with a polymorphic version of `type:_≡_`.

Like I said, it's roundabout, but this is one of the few warts in Agda, and so
we can accept it gracefully.

Returning to monoids, we now have all of the machinery in scope necessary to
define monoids and their associated laws:

```agda
  record Monoid {c : Level} (Carrier : Set c) : Set (lsuc c)
      where
    infixl 7 _∙_
    field
      _∙_      : Op₂ Carrier
      ε        : Carrier
      assoc      : Associative       _∙_
      identityˡ  : LeftIdentity   ε  _∙_
      identityʳ  : RightIdentity  ε  _∙_
```

As an important aside, this definition of `type:Monoid` diverges rather
dramatically from the one in Agda's standard library. The two types are, of
course, equivalent, but the standard version puts the carrier set *inside* the
record, rather than being an index on the type. I prefer the version presented
here for its pedagogical clarity, and in that it will dramatically simplify some
of the types we'd like to define in a later section.


## Examples of Monoids

A definition without an intuition is worthless. So what *are* these monoid
things? I like to think of monoids as *generalized queries* (in the database
sense of "query") that we can ask. Under this guise, the carrier set corresponds
to the possible answers of the query, while `field:_∙_` is a means of combining
sub-queries together, and `field:ε` is the "default," or "uninteresting"
response.

One possible query we might ask, and thus one monoid we might define, is "are
there any?" This is clearly a yes/no question, and therefore corresponds to a
monoid over the booleans. Our combining operator returns `ctor:true` *iff*
either sub-queries did. And the default response is "no, there are not any," ie.
`ctor:false`.

Thus, assuming all the necessary laws hold, we can say there exists a monoid
`def:_∨_`, `ctor:false` over the booleans:

```agda
  open import Data.Bool using (Bool; true; false; _∨_)
  open import Data.Bool.Properties
    using (∨-assoc; ∨-identityˡ; ∨-identityʳ)

  ∨-false : Monoid Bool
  Monoid._∙_  ∨-false = _∨_
  Monoid.ε    ∨-false = false
```

The laws do in fact happen to hold:

```agda
  Monoid.assoc      ∨-false = ∨-assoc
  Monoid.identityˡ  ∨-false = ∨-identityˡ
  Monoid.identityʳ  ∨-false = ∨-identityʳ
```

Monoids give us a convenient means of summarizing a lot of data. As a silly
example, we can write a couple of little functions that takes a `type: Monoid Bool` and
combines a few randomly chosen booleans:

```agda
  ex₁ : Monoid Bool → Bool
  ex₁ m = false ∙ true ∙ false ∙ false
    where open Monoid m

  ex₂ : Monoid Bool → Bool
  ex₂ m = true ∙ true ∙ true
    where open Monoid m

  ex₃ : Monoid Bool → Bool
  ex₃ m = false  -- ! 1
```

Note that at [1](Ann) we don't use `field:_∙_` whatsoever. This is intentional,
since `field:_∙_` corresponds to *combining* sub-queries. Its absence is thus
just a single sub-query.

We can ask whether any of these booleans were `ctor:true` by passing
`def:∨-false` to `def:ex₁`, `def:ex₂`, and `def:ex₃`:

```agda
  _ : ex₁ ∨-false ≡ true
  _ = refl

  _ : ex₂ ∨-false ≡ true
  _ = refl

  _ : ex₃ ∨-false ≡ false
  _ = refl
```

Perhaps your spider-sense is tingling; if we can use `def:∨-false` to ask "is
there any?" maybe there is another monoid for "do they all?" And indeed, there
is such a monoid over `def:_∧_` and `ctor:true`.


Exercise

:   Show the monoid over `def:_∧_` and `ctor:true`.


Solution

:   ```agda
  open Data.Bool using (_∧_)
  open import Data.Bool.Properties
    using (∧-assoc; ∧-identityˡ; ∧-identityʳ)
    ```

:   ```agda
  ∧-true : Monoid Bool
  Monoid._∙_  ∧-true = _∧_
  Monoid.ε    ∧-true = true
  Monoid.assoc      ∧-true = ∧-assoc
  Monoid.identityˡ  ∧-true = ∧-identityˡ
  Monoid.identityʳ  ∧-true = ∧-identityʳ
    ```

Using `def:∧-true` to summarize our examples asks whether each is made up of
*only* `ctor:true` values:

```agda
  _ : ex₁ ∧-true ≡ false
  _ = refl

  _ : ex₂ ∧-true ≡ true
  _ = refl

  _ : ex₃ ∧-true ≡ false
  _ = refl
```

These are extremely contrived examples, of course. As two slightly more real
world applications, you can imagine taking a data set of people, and running a
battery of tests over them. For example, you could map every data point to the
person's age, and then check if that age is above 18. Combining the resultant
booleans together via `def:∨-false` is a good means of determining if everyone
in the data set is an adult. Alternatively, we could map people to their
surnames, and then check if the resultant is "Maguire". Combining these bools
together with `def:∧-true` might tell you whether you're at my family reunion.

We will return to examples of these nature after we discuss monoids over
functions, which makes queries of this sort feel much more natural.


## A Few Monoids More

Booleans are not remotely the only set which admits monoids. Another common
example is the additive monoid over the natural numbers, namely:

```agda
  open import Data.Nat using (ℕ; _+_)
  open import Data.Nat.Properties
    using (+-assoc; +-identityˡ; +-identityʳ)

  +-0 : Monoid ℕ
  Monoid._∙_  +-0 = _+_
  Monoid.ε    +-0 = 0
  Monoid.assoc      +-0 = +-assoc
  Monoid.identityˡ  +-0 = +-identityˡ
  Monoid.identityʳ  +-0 = +-identityʳ
```

Considered as a query, `def:+-0` asks "what's the total sum?" In the special
case where every `type:ℕ` considered is 1, `def:+-0` instead asks "how many are
there?"

Monoids over a given type are not unique, as we saw with `def:∨-false` and
`def:∧-true`. Likewise, there is another monoid over the natural numbers, which
is where the terminology of "multiplication" for `field:_∙_` comes from:

```agda
  open Data.Nat using (_*_)
  open Data.Nat.Properties
    using (*-assoc; *-identityˡ; *-identityʳ)

  *-1 : Monoid ℕ
  Monoid._∙_  *-1 = _*_
  Monoid.ε    *-1 = 1
  Monoid.assoc      *-1 = *-assoc
  Monoid.identityˡ  *-1 = *-identityˡ
  Monoid.identityʳ  *-1 = *-identityʳ
```

There are infinitely many monoids. A good habit to get into is to look for a
monoid whenever you see a binary operation. For example, concatenation of lists
is a binary operation, and correspondingly has a monoid using `ctor:[]` as its
identity:

```agda
  open import Data.List using (List; _∷_; []; _++_)
  open import Data.List.Properties
    using (++-assoc; ++-identityˡ; ++-identityʳ)

  private variable
    a b c : Level
    A : Set a
    B : Set b
    C : Set c

  ++-[] : Monoid (List A)
  Monoid._∙_ ++-[] = _++_
  Monoid.ε ++-[] = []
  Monoid.assoc ++-[] = ++-assoc
  Monoid.identityˡ ++-[] = ++-identityˡ
  Monoid.identityʳ ++-[] = ++-identityʳ
```

Interestingly, we can often derive monoids from other monoids. Consider as an
example, `def:dual`, which reverses the order in which multiplication occurs:

```agda
  flip : (A → B → C) → B → A → C
  flip f b a = f a b

  module _ (m : Monoid A) where
    open Monoid m

    dual : Monoid A
    Monoid._∙_  dual = flip _∙_
    Monoid.ε    dual = ε
    Monoid.assoc      dual x y z  = sym (assoc z y x)
    Monoid.identityˡ  dual        = identityʳ
    Monoid.identityʳ  dual        = identityˡ
```


## Summarizing Data Structures

We now have sufficient examples under our belt to show off just how cool monoids
are. Monoids give us a convenient means of querying data structures like lists,
trees, and other containers. To illustrate this, we can write
`def:summarizeList` which transforms every contained element by some function,
and then uses a monoid to combine everything together:

```agda
  summarizeList : Monoid B → (A → B) → List A → B
  summarizeList m f [] = ε  -- ! 1
    where open Monoid m
  summarizeList m f (x ∷ l) = f x ∙ summarizeList m f l
    where open Monoid m
```

At [1](Ann), you'll notice for the first time, why we need `field:ε`. The
identity element is used to return a result when there is no data to summarize.
Furthermore, thanks to `field:identityˡ` and `field:identityʳ`, we know that
adding the identity element in the empty case can't change the summary. In
essence, we're able to add in the identity element as often as we want without
getting a different answer.

I like to think of `def:summarizeList`'s function parameter as "what data do I
want to collect about this data structure," and its monoid parameter as "and how
should I combine that information?"

Given `def:summarizeList` and our handful of monoids from earlier, we can
succinctly implement a great deal of common algorithms over lists. To make our
example from earlier clearer, we can determine whether any or all elements in a
list satisfy a given predicate:

```agda
  any? : (A → Bool) → List A → Bool
  any? = summarizeList ∨-false

  all? : (A → Bool) → List A → Bool
  all? = summarizeList ∧-true
```

Furthermore, by using the identity function which maps a value to itself:

```agda
  id : A → A
  id a = a
```

we can specialize `def:summarizeList` in order to add its elements:

```agda
  sum : List ℕ → ℕ
  sum = summarizeList +-0 id

  _ : sum (1 ∷ 10 ∷ 100 ∷ []) ≡ 111
  _ = refl
```

or to flatten nested lists:


```agda
  flatten : List (List A) → List A
  flatten = summarizeList ++-[] id

  _ : flatten  ( (1 ∷ 2 ∷ 3 ∷ [])
               ∷ (4 ∷ 5 ∷ []) ∷ []
               )
        ≡ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []
  _ = refl
```

By mapping every element of a list into a singleton list, and using `def:dual`,
we can even use `def:summarize` to *reverse* a list:

```agda
  reverse : List A → List A
  reverse = summarizeList (dual ++-[]) (_∷ [])

  _ : reverse (1 ∷ 2 ∷ 3 ∷ []) ≡ 3 ∷ 2 ∷ 1 ∷ []
  _ = refl
```

But that's not all! We can also use `def:summarizeList` to query information
about the container structure itself, by using a function that ignores its
argument:

```agda
  const : A → B → A
  const a _ = a
```

Thus, we can determine the length of the list by mapping every element to 1 and
then accumulating via `def:+-0`:

```agda
  size : List A → ℕ
  size = summarizeList +-0 (const 1)

  _ : size (true ∷ false ∷ []) ≡ 2
  _ = refl
```

Similarly, we can determine if a list is empty by checking if it has any
elements:

```agda
  empty? : List A → Bool
  empty? = summarizeList ∧-true (const false)
```

In `def:empty?`, we map every element to `ctor:false`, and then combine
via `def:∧-true`. Therefore, if there are any elements, the query will return
`ctor:false`. The only case in which the identity element is used is if the
list is empty in the first place.

This approach of summarizing data structures via a monoid is in no way limited
to lists. In fact, for any inductively defined data type, it's possible to write
a function analogous to `def:summarizeList`. The definition of such a thing gets
a bit gnarly:

```agda
  Foldable
      : {ℓa ℓb : Level}
      → (ℓf : Level)
      → (Set ℓa → Set ℓf)
      → Set (lsuc ℓa ⊔l ℓf ⊔l lsuc ℓb)
  Foldable {ℓb = ℓb} _ F =
    ∀ {A} {B : Set ℓb} → Monoid B → (A → B) → F A → B

  private variable
    ℓ₁ ℓ₂ : Level

  foldableList : Foldable {ℓ₁} {ℓ₂} _ List
  foldableList = summarizeList
```

Of course, `def:foldableList` is not the only inhabitant of `type:Foldable`.
`type:BinTree`s, for example, are also foldable:

```agda
  import  4-decidability
  open 4-decidability.BinaryTrees
    using (BinTree; leaf; branch; empty)

  foldableBinTree : Foldable {lzero} {ℓ₁} lzero BinTree
  foldableBinTree m f empty = ε
    where open Monoid m
  foldableBinTree m f (branch l x r) =
    foldableBinTree m f l ∙ f x ∙ foldableBinTree m f r
    where open Monoid m
```

Coming up with `type:Foldable`s for other types is done in a similar manner.
Pattern match on the data constructors, and use `field:ε` for any which don't
contain the type parameter. If there is a raw occurrence of the parameter,
apply the function to it, and otherwise use recursion to eliminate inductive
cases.

Given `type:Foldable`, we can write amazing things like `def:size′`, which are
capable of counting every element in any data structure you throw at it:

```agda
  size′ : ∀ {ℓ F} → Foldable ℓ F → F A → ℕ
  size′ fold = fold +-0 (const 1)

  _ : size′ foldableList
        (1 ∷ 1 ∷ 2 ∷ 3 ∷ []) ≡ 4
  _ = refl

  _ : size′ foldableBinTree
        (branch (leaf true) false (leaf true)) ≡ 3
  _ = refl
```

In this more general domain, there is an interesting summarization, which turns
any `type:Foldable` into a list:

```agda
  toList : ∀ {ℓ F} → Foldable ℓ F → F A → List A
  toList fold = fold ++-[] (_∷ [])
```

In fact, every function we defined over lists is amenable to this treatment;
meaning that for the price of thinking through a few monoids, we managed to
write summarizing functions over every possible data structure. This amazing
feat is possible because we *factored* the algorithms into three pieces:

1. Traversing the data structure (`type:Foldable`)
2. Summarizing the data (the function)
3. Combining the results (the `type:Monoid`)


## Instance Arguments

Not only can we build monoids out of binary operations, but we can also compose
monoids to build bigger ones. For example, given monoids on `type:A` and
`type:B`, we can build one on `type:A × B` by treating each projection
separately.

When we have more than one monoid in scope at a time, it can be tedious to keep
track of exactly which monoid operation we're talking about. Rather than try to
open the `type:Monoid` modules and rename everything to a unique identifier, we
can instead fall back on Agda's *instance arguments.*

```agda
  module _ (ma : Monoid A) (mb : Monoid B) where
    open Monoid ⦃ ... ⦄  -- ! 1
```

Here we've bound our two monoids, and then at [1](Ann) we've opened the
`module:Monoid` module with this funny `⦃ ... ⦄` syntax. When you open a record
module this way, Agda brings all of the fields into scope, with the module
parameter itself left as an instance argument. We can get a better sense for
what's happening here by invoking [Normalize:ε](AgdaCmd), which responds with:

```info
λ ⦃ r ⦄ → Monoid.ε r
```

You'll notice the `r` parameter is wrapped in the same `⦃⦄` braces that we used
to open the `module:Monoid` record in the first place. Whenever you see a
term wrapped in `⦃⦄`, it means that Agda will automatically try to fill in this
parameter for you, using *instance search.* In practice, this all works out to
"Agda will figure out what you mean from context."

We can make suggestions to Agda's instance search by way of the
`keyword:instance` keyword. This creates a new layout block in which definitions
are allowed to occur, and anything defined in the `keyword:instance` block will
be available for Agda to use during instance search:

```agda
    instance
      _ : Monoid A
      _ = ma

      _ : Monoid B
      _ = mb
```

Since `def:ma` and `def:mb` are already in scope, we don't actually need to give
the type annotations here, and can write the above more tersely as:

```agda
    instance
      _ = ma
      _ = mb
```

What has all this instance search stuff bought us? It means Agda can now figure
out which `type:Monoid` we'd like to use, based only on the desired type:

```agda
    ex₄ : A
    ex₄ = ε

    ex₅ : B → B
    ex₅ b = b ∙ b ∙ b
```

With instance arguments under our belt, we can now proceed to creating a monoid
for a pair of out a pair of monoids:

```agda
    open import Data.Product
      using (_×_; _,_)

    ×-monoid : Monoid (A × B)
    Monoid._∙_  ×-monoid (a₁ , b₁) (a₂ , b₂) = a₁ ∙ a₂ , b₁ ∙ b₂
    Monoid.ε    ×-monoid = ε , ε
    Monoid.assoc ×-monoid  (a₁ , b₁) (a₂ , b₂) (a₃ , b₃)
      rewrite assoc a₁ a₂ a₃
      rewrite assoc b₁ b₂ b₃
        = refl
    Monoid.identityˡ ×-monoid (a , b)
      rewrite identityˡ a
      rewrite identityˡ b
        = refl
    Monoid.identityʳ ×-monoid (a , b)
      rewrite identityʳ a
      rewrite identityʳ b
        = refl
```

Note that in the above, not only are `field:_∙_` and `field:ε` available to us
via instance search, but so too are `field:assoc`, `field:identityˡ`, and
`field:identityʳ`.


## Monoids over Functions

All of the monoids we have looked at thus far have been over regular, everyday
sorts of data types. But there are also monoids over more interesting
mathematical objects, like functions. One example of this is the *monoid of
endomorphisms,* which is the monoid whose binary operation is function
composition. In order for such a thing to type check, it must be the case that
the domain and codomain of each function are the same.

First, we can define function composition:

```agda
  _∘_ : (B → C) → (A → B) → (A → C)
  (g ∘ f) x = g (f x)
```

and then give the monoid over it:

```agda
  ∘-id : Monoid (A → A)
  Monoid._∙_  ∘-id = _∘_
  Monoid.ε    ∘-id = id
  Monoid.assoc      ∘-id x y z = refl
  Monoid.identityˡ  ∘-id x = refl
  Monoid.identityʳ  ∘-id x = refl
```

I personally use `def:∘-id` extremely often. This monoid is useful for
accumulating small changes over big data structures. For example, when writing a
program with message passing, you might want every message to have an observable
effect. You can transform each message into an endomorphism of type
`type:AppState → AppState`, and then use `def:∘-id` to apply all of the
accumulated changes to `type:AppState` at once.

There is another interesting monoid over functions. This one, given a monoid on
`B`, constructs a monoid on *functions* whose codomain is `B`. The binary
operator here is a `type:Op₂ (A → B)`, which runs both functions at the same
input, and combines their results. That is:

```agda
  ⊙ : Monoid B → Op₂ (A → B)
  ⊙ m f g = λ x → f x ∙ g x
    where open Monoid m
```

We can construct a trivial identity element for these functions simply by always
returning the identity element from the monoid:

```agda
  →ε : Monoid B → (A → B)
  →ε m = λ _ → ε
    where open Monoid m
```

The claim is that `def:⊙` and `def:→ε` form a monoid over functions `A → B`,
whenever we know `type:Monoid B`. Showing this fact should be straightforward,
since it's clear that `type:Monoid B` is the one doing all the work here.
Unfortunately, proving this is harder than we might expect:

```agda
  pointwise : Monoid B → Monoid (A → B)
  Monoid._∙_  (pointwise m) = ⊙   m
  Monoid.ε    (pointwise m) = →ε  m
  -- TODO(sandy): leave me as a hole!
  Monoid.assoc      (pointwise m) x y z = leave-me-as-a-hole
  Monoid.identityˡ  (pointwise m) = leave-me-as-a-hole
  Monoid.identityʳ  (pointwise m) = leave-me-as-a-hole
```

We can look at the type of the first goal here, and see:

```info
Goal: ⊙ m (⊙ m x y) z ≡ ⊙ m x (⊙ m y z)
———————————————————————————————————————
m : Monoid B
x y z : A → B
```

This looks plausible, but things become more worrisome when we use
[TypeContext/Normalised](AgdaCmd) in order to fully evaluate the types involved.
Ther resulting goal looks like this:

```info
Goal: (λ x₁ → (m Monoid.∙ (m Monoid.∙ x x₁) (y x₁)) (z x₁))
    ≡ (λ x₁ → (m Monoid.∙ x x₁) ((m Monoid.∙ y x₁) (z x₁)))
———————————————————————————————————————
m : Monoid B
x y z : A → B
```


This was the point of subtlety I mentioned earlier.

The problem here is that we are being asked to show propositional equality of
two *functions.* While we have everything we need from `type:Monoid B` in order
to prove this fact for *any specific* `x₁`, we are unable to do it in general.
Why not? Because we need to show `(λ x₁ → lhs) ≡ (λ x₁ → rhs)`, but given our
current tools, all we can show is `λ x₁ → lhs ≡ rhs`. What's gone wrong is that
the variable we need to prove things about *only* exists inside of the proof
term, not outside of it. Thus, try as we might, there is just no way to use our
propositional equality machinery in order to finagle a proof that shows these
two terms are equal.


## Intentional vs Extensional Equality

This brings up a foundationally interesting question: when are two functions
equal? The answer is not very cut and dry. This is a hard problem. Consider
functions `def:ex₁`, `def:ex₂` and `def:ex₃`:

```agda
module Sandbox-IntensionalExtensional where
  open import Data.Nat
    using (ℕ; _+_;  _*_)
  open ℕ

  ex₁ : ℕ → ℕ
  ex₁ x = x + 2

  ex₂ : ℕ → ℕ
  ex₂ x = 2 * x

  ex₃ : ℕ → ℕ
  ex₃ x = suc (suc x)
```

Clearly functions `def:ex₁` and `def:ex₂` are *not* equal. But the answer is less
clear as to whether `def:ex₁` and `def:ex₃` are. The two functions are syntactically
entirely different, but compute the same output given the same input. If you
were to draw the plots of these two functions, they'd look identical.

But this isn't necessarily the whole story; are bubble sort and merge sort
the same function? They both return the same outputs given the same inputs,
however, they do so in entirely different ways, and with entirely different
computational behaviors. What a mess we find ourselves in.

Many programming languages sidestep the problem by comparing functions by their
pointer equality. In these cases, two functions are the same if they occur at
the same place in memory. But this is unsatisfying on many levels. First and
foremost, it is an abstraction leak. Functions are mathematical ideas,
completely separate from the hardware they run on. There exist models of
computation that don't have memory, and thus such a decision allows you to
deduce properties of the hardware you're running on---which ought to be a
no-no. Mathematics doesn't run on any hardware; it just *is.* Equally abhorrent
in pointer equality of functions is that it means two identical, syntactically
byte-for-byte source identical functions might not compare equal, due to
unpredictable quirks of how the runtime has decided to lay out memory. This
means that a program which might work today could fail tomorrow based only on a
differing mood of the runtime. There are many ways to describe this behavior,
but neither "sane" nor "mathematical" nor even "good programming practice" are
one.

The solution to this problem is to split equality of function types into two
camps. The mathematicians take a stand and say that yes, bubble sort and merge
sort *are* the same function. The computer scientists argue that no, they are
not. In the first world, we care only that the functions map equal inputs to
equal outputs. In the latter, we require the two functions to be defined in
exactly the same way. These two approaches to equality are known as
*extensional* and *intensional* equality, respectively.

Intensionality continues to be a challenge to define. Do variable names matter?
What about no-ops? The entire question is a quagmire, and we will not delve
deeper into this idea here.

Instead, we will worry only about extensional equality. Two functions are thus
equal if they map inputs to equal outputs. That is to say, given two functions
`f` and `g`, we'd like the following property to hold:

```agda
  open import Relation.Binary.PropositionalEquality
    using (_≡_; refl; cong; sym; trans)
  open import Relation.Binary using (Rel)

  _≗_
      : {a b : Level} {A : Set a} {B : A → Set b}  -- ! 1
      → Rel ((x : A) → B x) _ -- ! 2
  _≗_ f g = ∀ x → f x ≡ g x
```

The type here is rather involved, where we have made `B` a type dependent on `A`
at [1](Ann), and then made both `f` and `g` pass their argument to `B` for their
output at [2](Ann). A more intuitive type for `def:_≗_` is:

```type
_≗_ : {A B : Set} → Rel (A → B) _
```

but the extra generality means we can use `def:_≗_` with indexed types and
dependent functions as well. This doesn't matter most of the time, but will lead
to obscure problems if you are not mindful of it.

Given the definition of `def:_≗_`, we can show that `def:ex₁` and `def:ex₃` are
indeed extensionally equal:

```agda
  open import Data.Nat.Properties
    using (+-comm)

  ex₁≗ex₃ : ex₁ ≗ ex₃
  ex₁≗ex₃ zero = refl
  ex₁≗ex₃ (suc x) = cong suc (+-comm x 2)
```

The curious reader might wonder whether `def:_≗_` forms a preorder or an
equivalence relation. In fact it does, given simply by fanning out the argument
to both functions and then using the underling equivalence on `type:_≡_`. Once
you know the trick, it's not very difficult to show on paper, but doing it in
Agda requires jumping through a couple of hoops.

We'd like to bind `A` and `B` once and for all as implicit variables, and then
show that `def:_≗_` is `type:Reflexive`, `type:Symmetric` and `type:Transitive`.
Unfortunately, `def:_≗_` has too many implicit variables for Agda to figure out
the types involved on its own. Thus in order to avoid unsolved metas, we must
explicitly give some types to `type:Reflexive` et al.,

Due to a technical quirk with how Agda handles implicits defined via
`keyword:variable`, it's rather more verbose to do our usual thing here. So
rather than defining our implicits in a `keyword:variable` block, we will
instead construct a private module and add the implicits as parameters to that.
The exact details aren't of importance here, but the dedicated student is
encouraged to repeat this section on their own using a `keyword:variable` block
and see for themself what goes wrong.

```agda
  module _ {a b : Level} {A : Set a} {B : A → Set b} where
```

With our implicits now in scope, we can define an alias for dependent functions:

```agda
    private
      Fn : Set _
      Fn = (x : A) → B x
```

and now show that `def:_≗_` is `type:Reflexive` when its `A` parameter is
instantiated at `type:Fn`:

```agda
    open import Relation.Binary
      using (Reflexive; Symmetric; Transitive; IsEquivalence)

    ≗-refl : Reflexive {A = Fn} _≗_
    ≗-refl x = refl
```

With the `type:Fn` trick sorted out, it's not very hard to define symmetry or
transitivity---just apply the extensional equality, and perform the underlying
operation on the result:

```agda
    ≗-sym : Symmetric {A = Fn} _≗_
    ≗-sym f≗g a = sym (f≗g a)

    ≗-trans : Transitive {A = Fn} _≗_
    ≗-trans f≗g g≗h a = trans (f≗g a) (g≗h a)
```

Therefore `def:_≗_` is an equivalence relation:

```agda
    ≗-equiv : IsEquivalence {A = Fn} _≗_
    IsEquivalence.refl   ≗-equiv = ≗-refl
    IsEquivalence.sym    ≗-equiv = ≗-sym
    IsEquivalence.trans  ≗-equiv = ≗-trans
```


## Function Extensionality

If you are working in more of a mathematical domain (as opposed to a
computational one), you might want to postulate *function extensionality*: the
notion that extensionally equal functions are in fact *propositionally equal.*
As we have seen, this doesn't make sense when computation is your main goal, but
if you are simply modeling the world, it's an extremely convenient thing to have
around. We can postulate `def:fun-ext` as follows:

```agda
  postulate
    fun-ext
        : {a b : Level} {A : Set a} {B : A → Set b}
        → {f g : (x : A) → B x}
        → f ≗ g → f ≡ g
```

Function extensionality doesn't exist in the standard library; while Agda is
compatible with the idea, function extensionality can be neither proven nor
disproven in Agda. Therefore, it's up to you to decide whether or not it holds.

Given `def:fun-ext`, we can trivially lift our proof `def:ex₁≗ex₃` into a proof
that the two functions are propositionally equal:

```agda
  ex₁≡ex₃ : ex₁ ≡ ex₃
  ex₁≡ex₃ = fun-ext ex₁≗ex₃
```

Of course, you don't need to postulate `def:fun-ext`; you can always work
directly with extensional equality itself, instantiating it to get whatever
proof of equality you actually need. But the ergonomics around `def:fun-ext` can
dramatically improve the story, if you're willing to give up on computability
for it.

Returning to our `def:pointwise` monoid, if we were willing to postulate
function extensionality all of our problems would go away. But, are we really
willing to add such a strong axiom as function extensionality merely to define a
particular monoid? Funext is a big pill to swallow. Postulating it makes sense
when we're in a *particular domain* in which we'd like it to hold, but do we
really want this particular monoid to exist only in case funext holds?

Rather than fire off at full speed down that path, let's instead rephrase the
definition of a monoid so as to not require full funext.


## Setoids

Returning to our definition of `type:Monoid`, it's rather unclear where exactly
things have gone wrong. Nowhere in the definition do we seem to use
propositional equality! No, the problem is in fact earlier, when we imported
`module:Algebra.Definitions` in this manner:

```agda
  open import Relation.Binary.PropositionalEquality
  import Algebra.Definitions

  open module Def {ℓ} {A : Set ℓ}
    = Algebra.Definitions {A = A} _≡_
```

As it happens, we are not the first people to run into the problem that
sometimes we need a weaker notion of equality than the propositional variety.
Thus, you'll notice that the `module:Algebra.Definitions` module itself is
parameterized by an equivalence relation, which we chose to be `type:_≡_`.

The solution to all of our problems is simply to make this dependency explicit.
We must choose a particular equivalence relation that we will use when proving
the monoid laws hold, and pack this relation into the definition of the
`type:Monoid` itself.

Our second attempt at the problem looks like this:

```agda
module Sandbox-Monoids where
  open import Algebra
    using (Op₂; Associative; LeftIdentity; RightIdentity)
  open import Relation.Binary
    using (Rel; IsEquivalence; _Preserves₂_⟶_⟶_)

  record Monoid₂ {a} (Carrier : Set a) (ℓ : Level)
        : Set (a ⊔l lsuc ℓ) where
    infix   4 _≈_
    infixl  7 _∙_
    field
      _∙_      : Op₂ Carrier
      ε        : Carrier
      _≈_      : Rel Carrier ℓ  -- ! 1
      isEquivalence : IsEquivalence _≈_  -- ! 2
      assoc      : Associative    _≈_ _∙_
      identityˡ  : LeftIdentity   _≈_ ε  _∙_
      identityʳ  : RightIdentity  _≈_ ε  _∙_
      ∙-cong     : _∙_ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_  -- ! 3
```

You will notice three additions to this version of `type:Monoid₂`, indicated by
markers. At [1](Ann) we have a new `field:_≈_`, which we assert is an
equivalence relation at [2](Ann). This part is expected, but what is rather more
surprising is the addition of `field:∙-cong` at [3](Ann), which witnesses the
important fact that `field:_∙_` preserves the `field:_≈_` relation. The mere
existence of `field:∙-cong` is a taste of the difficulties that lay down this
path.

Imagine reassembling each of our old monoid example anew as a `type:Monoid₂`.
There would be a dramatic amount of overhead and shared code, where we'd need to
show `field:isEquivalence` every time, even though we were merely using
`type:_≡_` for our equivalence relation.

Thus, this is not exactly the formation we will use going forwards. Instead, we
will factor out the equivalence relation, into an object known as a *setoid.*
Setoids are a common proof assistant idiom for dealing with abstract notions of
equality, in that they package up the `field:Carrier` set, and the equivalence
relation all into one object:

```agda
  module Sandbox-Setoids where
    record Setoid (c ℓ : Level) : Set (lsuc (c ⊔l ℓ)) where
      field
        Carrier        : Set c
        _≈_            : Rel Carrier ℓ
        isEquivalence  : IsEquivalence _≈_

      open IsEquivalence isEquivalence public  -- ! 1
```

Notice at [1](Ann) we open the `field:isEquivalence` record, which brings
`field:refl`, `field:sym`, and `refl:trans` into scope. In practice, these
appear as properties of the `type:Setoid` itself, and mean we can reference
these common operations without needing to go through the `type:IsEquivalence`
interface every time.

For every type, we also have a canonical setoid given by propositional equality:

```agda
    open import Relation.Binary.PropositionalEquality as PropEq
      using (_≡_)

    open Setoid

    setoid : Set → Setoid _ _
    Carrier (setoid A) = A
    _≈_ (setoid A) = PropEq._≡_
    IsEquivalence.refl   (isEquivalence (setoid A)) = PropEq.refl
    IsEquivalence.sym    (isEquivalence (setoid A)) = PropEq.sym
    IsEquivalence.trans  (isEquivalence (setoid A)) = PropEq.trans
```

Because setoids are extremely common objects in the Agda standard library, we
will prefer to import their definition from the library, so that we can
interoperate between the things we build and the functionality provided to us.

```agda
  open import Relation.Binary
    using (Setoid)
  open import Relation.Binary.PropositionalEquality
    using ()
    renaming (setoid to prop-setoid)
```

We can now define `type:Monoid` for the third and final time. On this attempt,
we will use a `type:Setoid` to wrangle as much of the complexity for us as
possible.

```agda
  record Monoid (c ℓ : Level) : Set (lsuc (c ⊔l ℓ)) where
    field
      setoid : Setoid c ℓ

    open Setoid setoid  -- ! 1
      renaming (_≈_ to infix 4 _≈_)   -- ! 2
      public

    infixl  7 _∙_
    field
      _∙_      : Op₂ Carrier
      ε        : Carrier
      assoc      : Associative    _≈_ _∙_
      identityˡ  : LeftIdentity   _≈_ ε  _∙_
      identityʳ  : RightIdentity  _≈_ ε  _∙_
      ∙-cong     : _∙_ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_

    module Reasoning where
      open import Relation.Binary.Reasoning.Setoid setoid public
```

One cool thing about Agda records is that you don't need to define all of your
`keyword:field`s at once. At [1](Ann), we open up the `field:setoid`, and at
[2](Ann) we use a `keyword:renaming` modifier in order to attach an otherwise
missing `keyword:infix` declaration.

Given our new definition, it's possible to mechnically translate every "naive"
`type:Monoid` into this type, as given by `def:recover`.

```agda
  private variable
    a b c ℓ : Level
    A : Set a

  module Naive = Sandbox-Naive-Monoids
  import Relation.Binary.PropositionalEquality as PropEq

  recover : {A : Set a} → Naive.Monoid A → Monoid a a
  recover {A = A} x = record
    { setoid     = prop-setoid A
    ; _∙_        = _∙_
    ; ε          = ε
    ; assoc      = assoc
    ; identityˡ  = identityˡ
    ; identityʳ  = identityʳ
    ; ∙-cong     = λ { PropEq.refl PropEq.refl → PropEq.refl }
    }
    where open Naive.Monoid x
```

After all of this labor, we are now ready to finally implement the
`def:pointwise` monoid. First, we can show that `type:_≗_` forms a
`type:Setoid`:

```agda

  module _ (A : Set a) (setoid : Setoid c ℓ) where
    open Setoid renaming (isEquivalence to eq)
    open IsEquivalence
    open Setoid setoid
      using ()
      renaming ( Carrier to B
               ; _≈_ to _≈ᵇ_
               )

    _≗_ : Rel (A → B) _
    f ≗ g = (a : A) → f a ≈ᵇ g a

    ≗-setoid : Setoid _ _
    Carrier  ≗-setoid = A → B
    _≈_      ≗-setoid = _≗_
    refl   (eq ≗-setoid)          a  = refl   setoid
    sym    (eq ≗-setoid) f≗g      a  = sym    setoid (f≗g a)
    trans  (eq ≗-setoid) f≗g g≗h  a  = trans  setoid (f≗g a) (g≗h a)
```

and then use this fact to construct `def:pointwise` proper:

```agda
  module _ (A : Set a) (mb : Monoid c ℓ) where
    -- open ≗-Def {A = A}
    open Monoid mb
      using ()
      renaming ( _∙_  to _∙ᵇ_
               ; ε    to εᵇ
               )
```

Our hard work is rewarded, in that the definition of `def:pointwise` is as
straightforward as it feels like it ought to be.

```agda
    open Monoid

    pointwise : Monoid _ _
    setoid pointwise      = ≗-setoid A (Monoid.setoid mb)
    _∙_    pointwise f g  = λ x → f x ∙ᵇ g x
    ε      pointwise      = λ _ → εᵇ
    assoc      pointwise f g h a    = assoc      mb _ _ _
    identityˡ  pointwise f a        = identityˡ  mb _
    identityʳ  pointwise f a        = identityʳ  mb _
    ∙-cong     pointwise f≗g h≗i a  = ∙-cong     mb (f≗g a) (h≗i a)
```


## Monoid Homomorphisms

One particularly fruitful area of using mathematics for real problems is to
investigate functions which *preserve* structured sets. That is, given two
`type:Monoid`s, one on `A` and another on `B`, which are the functions `A → B`
that are *well-behaved* with respect to the monoids? A well behaved function, in
this context, is one which preserves the monoid structure. In equations, that
means:

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
and thus two units `field:ε` and two binary operators `field:_∙_`. Let's say the
`A`-side monoid is the first one, and the `B`-side is the second. Rewriting our
equations above with this new elaboration, we get:

$$
f(\varepsilon_1) =_2 \varepsilon_2
$$

and

$$
f(a \cdot_1 b) =_2 f(a) \cdot_2 f(b)
$$

where we have been careful to add a subscript even to the equality---since we
might have *different* notions of equality on either side of the function!

It's important to point out that while these equations look simple, they are
much harder to get right than they seem at first blush. The reason is that the
notation $f(a \cdot_1 b)$ is just *syntax.* Assuming a potential monoid
homomorphism between `def:+-0` and `def:*-1`, in the wild these equations might
look like any of the following:

$$
\begin{aligned}
f(13) &= f(10) \cdot f(3) \\
f(13) &= f(13) \cdot f(0) \\
f(13) &= 1 \cdot f(13) \\
f(13) &= 30
\end{aligned}
$$

depending on exactly how much normalization occurred before we got a chance to
look at it. As you can see, being a homomorphism is an extremely stringent
requirement of a function, due to the astronomical number of equations that it
must satisfy.

Nevertheless, we can set up the type `type:MonHom`, which witnesses that a given
function is a homomorphism between two monoids. Due to the two monoids we have
in scope, we go through the instance argument song and dance again, which makes
this definition a little more of a mouthful:

```agda
module Sandbox-MonoidHomomorphisms where
  open Sandbox-Monoids

  private variable
    c c₁ c₂ ℓ ℓ₁ ℓ₂ : Level

  module _ (m₁ : Monoid c₁ ℓ₁) (m₂ : Monoid c₂ ℓ₂) where
    open import Relation.Binary using (_Preserves_⟶_)
    open Monoid m₁ using () renaming (Carrier to A)
    open Monoid m₂ using () renaming (Carrier to B)
    open Monoid ⦃ ... ⦄

    instance
      _ = m₁
      _ = m₂

    record MonHom (f : A → B)
         : Set (c₁ ⊔l c₂ ⊔l ℓ₁ ⊔l ℓ₂) where
      field
        preserves-ε  : f ε ≈ ε
        preserves-∙  : (x y : A) → f (x ∙ y) ≈ f x ∙ f y
        f-cong       : f Preserves _≈_ ⟶ _≈_
```

With the definition in front of us, it's clear that not all functions preserve
monoids. In fact, there is even a simple proof. We have seen that there are at
least two monoids over the booleans, `def:∧-true` and `def:-∨-false`. But these
two monoids have different units. Therefore, no function that maps into
`type:Bool` can possibly preserve both units at once.

We can now `def:recover` some of our simple monoids back into scope, in order to
show some homomorphisms between them.

```agda
  ∧-true   = recover Naive.∧-true
  ∨-false  = recover Naive.∨-false
  +-0      = recover Naive.+-0
  *-1      = recover Naive.*-1

  private variable
    a : Level
    A : Set a

  ++-[] : (A : Set a) → Monoid _ _
  ++-[] A = recover (Naive.++-[] {A = A})

--   ∘-id : (A : Set a) → Monoid _ _
--   ∘-id A = recover (Naive.∘-id {A = A})

  open import Function using (flip)

  dual : (m : Monoid c ℓ) → Monoid c ℓ
  dual m = record
    { setoid     = setoid
    ; _∙_        = flip _∙_
    ; ε          = ε
    ; assoc      = λ _ _ _ → sym (assoc _ _ _)
    ; identityˡ  = identityʳ
    ; identityʳ  = identityˡ
    ; ∙-cong     = flip ∙-cong
    }
    where open Monoid m
```

Now that we have the machinery in place to prove we're not fooling ourselves,
let's begin our hunt for a monoid homomorphism. The simplest monoids we have are
those over the booleans, so let's try to find a homomorphism between
`def:∧-true` and `def:∨-false`. Given the constraints of the problem, we thus
are looking for a function `f : Bool → Bool`, with the property that `f true ≡
false`. There are only two such functions, `const false` and `def:not`. The
latter seems more promising, so let's try that:

```agda
  open import Data.Bool
    using (true; false; not)

  open MonHom
  module _ where
    open import Relation.Binary.PropositionalEquality

    not-hom₁ : MonHom ∧-true ∨-false not
    preserves-ε  not-hom₁           = refl
    preserves-∙  not-hom₁ false  y  = refl
    preserves-∙  not-hom₁ true   y  = refl
    f-cong       not-hom₁ refl      = refl
```

However, interestingly, `const false` is *also* a homomorphism between these two
monoids, albeit not a very interesting one:

```agda
    open import Function using (const)

    false-hom : MonHom ∧-true ∨-false (const false)
    preserves-ε  false-hom       = refl
    preserves-∙  false-hom x y   = refl
    f-cong       false-hom refl  = refl
```

Returning to `def:not-hom₁`, expanding out the definition of `field:preserves-∙`
gives us the following equation:

$$
\neg (a \wedge b) = \neg a \vee \neg b
$$

which is an exceptionally famous mathematical theorem, known as one half of *De
Morgan's laws.* Believe it or not, I did not plan on this result; it simply fell
out when I was looking for simple examples of monoid homomorphisms to illustrate
this section. The other direction of De Morgan's laws is the fact that

$$
\neg (a \vee b) = \neg a \wedge \neg b
$$

This law also looks suspiciously like a monoid homomorphism, albeit this time
from `def:∨-false` to `def:∧-true`. As it happens, it's not any harder to show
`def:not-hom₂`:

```agda
    not-hom₂ : MonHom ∨-false ∧-true not
    preserves-ε  not-hom₂           = refl
    preserves-∙  not-hom₂ false  y  = refl
    preserves-∙  not-hom₂ true   y  = refl
    f-cong       not-hom₂ refl      = refl
```

Perhaps you're beginning to see the importance of---if maybe not yet the use
of---monoid homomorphisms. We managed to rediscover an important mathematical
fact simply by looking for an example! By looking for monoid homomorphisms, we
have seemingly stumbled across a good strategy for pruning the mathematical
search space.

Hot off the success of deriving `def:not-hom₂` from looking only at
`def:not-hom₁`, can we switch around the monoids in `def:false-hom` to find a
homomorphism going the other direction for `const false`? A little investigation
shows that no, we cannot find such a homomorphism. Its existence would violate
the law that `false = const false ε` `= f ε` `= ε = true`. We can show that
there is no such homomorphism by deriving exactly this contradiction:

```agda
    open import Relation.Nullary

    not-false-hom₂ : ¬ MonHom ∨-false ∧-true (const false)
    not-false-hom₂ x with preserves-ε x
    ... | ()
```


## Finding Equivalent Computations

Armed with some understanding of the importance of monoid homomorphisms, let's
now attempt to develop an intuition as to what they *are.* If a function `f` is
a monoid homomorphism it means we can play fast-and-loose about when we want to
apply `f`. Maybe `f` is expensive, so we'd like to batch all of our combining
work first, and only ever call `f` once. Alternatively, maybe `field:_∙₁_` is
expensive, in which case we might prefer to map every `A` term into a `B` before
accumulating them together.

Consider the case of list appending; each call to `def:_++_` is $O(n)$ time, and
thus we run in quadratic time when we have a linear number of lists to append.
If all we'd like to do is count the number of elements in the resulting list, we
have two options: concatenate the lists and subsequently take the length of the
result, or take the lengths individually and add them. Because addition runs in
$O(1)$ time, it is asymptotically faster to add the lengths rather than taking
the length of the concatenation. And it is the existence of the `def:length-hom`
monoid homomorphism that ensures these two algorithms compute the same result.

```agda
  open import Data.Nat using (ℕ)
  open import Data.List
    using (List; []; _∷_)

  open import Relation.Binary.PropositionalEquality
    using ()
    renaming (setoid to prop-setoid)

  module _ where
    open import Relation.Binary.PropositionalEquality

    length : List A → ℕ
    length = Naive.size

    length-hom : (A : Set a) → MonHom (++-[] A) +-0 length
    preserves-ε (length-hom A) = refl
    preserves-∙ (length-hom A) [] y = refl
    preserves-∙ (length-hom A) (x ∷ xs) y
      rewrite preserves-∙ (length-hom A) xs y
        = refl
    f-cong (length-hom A) refl = refl
```

It's interesting to note that list concatenation is not *intrinsically* slow;
merely that `x ++ y` has linear runtime in the length of `x`. Therefore, it's
much more efficient to compute `x ++ (y ++ (z ++ w))` than it is to compute `((x
++ y) ++ z) ++ w`.

-- TODO(sandy): quick point about how this is unfortunate, because we almost
-- always build the first things first, and thus the association is wrong

This is the key insight behind *string builders,* which are
types that, as expected, efficiently build big strings. String builders are
cleverly implemented to ensure that all the strings they combine are
right-associated, and thus take advantage of this linear runtime.

By this point in the chapter, you will not be surprised to learn that string
builders---also known as *difference lists*, or *dlists* for short---take
advantage of a monoid homomorphism.

```agda
    open Function using (_∘_; id)

    ∘-id : Set a → Monoid _ _
    Monoid.setoid  (∘-id A)      = ≗-setoid A (prop-setoid A)
    Monoid._∙_     (∘-id A) g f  = g ∘ f
    Monoid.ε       (∘-id A)      = id
    Monoid.assoc      (∘-id A) x y z a  = refl
    Monoid.identityˡ  (∘-id A) x a      = refl
    Monoid.identityʳ  (∘-id A) x a      = refl
    Monoid.∙-cong     (∘-id A) x≗y u≗v a
      rewrite u≗v a = x≗y _
```

We can construct dlists by first making the relevant monoid, and then extracting
its carrier to get the definition of a `type:DList`:

```agda
    module DList where
      open Data.List using (_++_)
      open import Data.List.Properties
        using (++-identityʳ; ++-assoc)

      dlist-mon : Set a → Monoid _ _
      dlist-mon A = ∘-id (List A)

      DList : Set a → Set a
      DList A = Monoid.Carrier (dlist-mon A)
```

There is an isomorphism between `type:List` and `type:DList`, given by:

```agda
      toDList : List A → DList A
      toDList = _++_

      fromDList : DList A → List A
      fromDList dl = dl []
```

although the proof of this fact is left as an exercise to the reader. Finally,
we can show that `def:toDList` is a monoid homomorphism between lists under
concatenation and `def:dlist-mon`:

```agda
      dlist-hom : MonHom (++-[] A) (dlist-mon A) toDList
      preserves-ε  dlist-hom a = refl
      preserves-∙  dlist-hom = ++-assoc
      f-cong       dlist-hom refl a = refl
```

While `def:dlist-hom` is in fact a proof that `type:DList` and `type:List`
behave identically under their relevant monoid multiplications, it can be hard
to *feel* this fact. Thus, even though it is completely unnecessary, we can
write a little test with a concrete example:

```agda
      ex-dlist
        = fromDList
          ( toDList (1 ∷ 2 ∷ [])
          ∙ toDList (3 ∷ 4 ∷ [])
          ∙ toDList (5 ∷ [])
          )
        where
          open Monoid (dlist-mon ℕ)

      _ : ex-dlist  ≡ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []
      _ = refl
```

We're left with only one question---why exactly does all of this work? Our
`field:preserves-∙` law gets instantiated as:

```type
  toDList (x ++ y) = toDList x ∘ toDList y
```

which when we expand out the definition of `def:_∘_` gives us:

```type
  toDList (x ++ y) = λ z → toDList x (toDList y z)
```

and then the definition of `def:toDList`:

```type
  λ z → (x ++ y) ++ z = λ z → x ++ (y ++ z)
```

After an invocation of function extensionality for pedagogical reasons, we can
drop the lambdas:

```type
  (x ++ y) ++ z = x ++ (y ++ z)
```

which shows that using the `def:DList` multiplication ensures that all uses of
`def:_++_` are right-associative, and therefore provide exactly the asymptotic
speedup we were looking for.

This trick---using a function encoding of an object in order to reassociate
expressions into an optimal form---is general and widely applicable. The more
general theorem here is known as *Yoneda's lemma,* which we will explore in
@sec:yoneda.

To hammer home the point; to a computer scientist, the only salient pieces
here are the definitions `type:DList`, `def:toDList`, `def:fromDList`, and
the dlist `field:_∙_`. This is the entirety of the interface that users of your
library need be aware of. But it is `def:dlist-hom` which proves that our dlist
optimization does exactly what it promises to. The monoids do the actual work,
while the homomorphism proves that there are no bugs in either the
implementation or the conceptual model.


## Homomorphisms in Software Design

```agda
  open import Data.Maybe
  open import Data.Maybe.Properties
    using ( <∣>-assoc
          ; <∣>-identityˡ
          ; <∣>-identityʳ
          )


  module _ where
    open import Relation.Binary.PropositionalEquality

    first : (A : Set a) → Monoid _ _
    Monoid.setoid  (first A) = prop-setoid (Maybe A)
    Monoid._∙_     (first A) = _<∣>_
    Monoid.ε       (first A) = nothing
    Monoid.assoc      (first A) = <∣>-assoc
    Monoid.identityˡ  (first A) = <∣>-identityˡ
    Monoid.identityʳ  (first A) = <∣>-identityʳ
    Monoid.∙-cong     (first A) refl refl = refl

    last : (A : Set a) → Monoid _ _
    last A = dual (first A)
```

```agda
  module KeyValStore (Key : Set c₁) (val-monoid : Monoid c₂ ℓ₂) where
    open Monoid val-monoid using () renaming (Carrier to Val)

    KVStore : Set (c₁ ⊔l c₂)
    KVStore = Key → Val

    _[_] : KVStore → Key → Val
    kv [ ix ] = kv ix

```



## Theorems about Monoids

For a given `type:Monoid`, there are always at least two monoid homomorphisms:
the trivial one, which maps elements to themselves; and the degenerate one,
which maps every element in some other monoid to `field:ε`:

```agda
  open import Function using (const; id)

  trivial : (m : Monoid c₂ ℓ₂) → MonHom m m id
  trivial m = record
    { preserves-ε  = refl
    ; preserves-∙  = λ  x y → refl
    ; f-cong       = λ  x → x
    }
    where open Monoid m

  degenerate
      : {m₁ : Monoid c₁ ℓ₁}
      → (m : Monoid c₂ ℓ₂)
      → MonHom m₁ m (const (Monoid.ε m))
  degenerate m = record
    { preserves-ε  = refl
    ; preserves-∙  = λ  x y → sym (identityʳ _)
    ; f-cong       = λ  x → refl
    }
    where open Monoid m

  -- identities are unique
  -- homs are not invertible in general
```

-- TODO(sandy): other examples?


