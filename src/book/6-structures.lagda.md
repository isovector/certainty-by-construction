# Structured Sets

```agda
module 6-structures where

open import Level
  using (Level)
  renaming (zero to lzero; suc to lsuc; _⊔_ to _⊔l_)
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
and an > identity element `field:ε`.

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

  -- TODO(sandy): just define assoc / identity for ourselves?
  module _ {ℓ : Level} {A : Set ℓ} where
    open import Algebra.Definitions (_≡_ {A = A})  -- ! 1
      public  -- ! 2
```

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

There are infinitely many monoids. A good habit to get into is to look for a
monoid whenever you see a binary operation. For example, concatenation of lists
is a binary operation, and correspondingly has a monoid using `ctor:[]` as its
identity:

```agda
  open import Data.List using (List; _∷_; []; _++_)
  open import Data.List.Properties
    using (++-assoc; ++-identityˡ; ++-identityʳ)

  private variable
    a b : Level
    A : Set a
    B : Set b

  ++-[] : Monoid (List A)
  Monoid._∙_ ++-[] = _++_
  Monoid.ε ++-[] = []
  Monoid.assoc ++-[] = ++-assoc
  Monoid.identityˡ ++-[] = ++-identityˡ
  Monoid.identityʳ ++-[] = ++-identityʳ
```

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

we can specialize `def:summarizeList` in order to add its elements, and to
flatten nested lists:

```agda
  sum : List ℕ → ℕ
  sum = summarizeList +-0 id

  flatten : List (List A) → List A
  flatten = summarizeList ++-[] id
```

We can also use `def:summarizeList` to query information about the container
structure itself, by using a function that ignores its argument:

```agda
  const : A → B → A
  const a _ = a
```

Thus, we can determine the length of the list by mapping every element to 1 and
then accumulating via `def:+-0`:

```agda
  length : List A → ℕ
  length = summarizeList +-0 (const 1)
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
```

but, given `type:Foldable`, we can write amazing things like `def:length′`,
which are capable of counting every element in any data structure you throw at
it:

```agda
  length′ : ∀ {ℓ F} → Foldable ℓ F → F A → ℕ
  length′ fold = fold +-0 (const 1)
```

In fact, every function we defined over lists is amenable to this treatment;
meaning that for the price of thinking through a few monoids, we managed to
write summarizing functions over every possible data structure. This amazing
feat is possible because we *factored* the algorithms into three pieces:

1. Traversing the data structure (`fold`)
2. Summarizing the data (the function)
3. Combining the results (the `type:Monoid`)


## Monoids over Functions

