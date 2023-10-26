# Program Optimization

Hidden

:   ```agda
{-# OPTIONS --allow-unsolved-metas #-}
    ```

```agda
module Chapter9-ProgramOptimization where
```

The purpose of theory is not satisfying idle curiosities; instead it is to make
short work of otherwise difficult problems. In this final chapter, we will turn
our gaze towards a difficult problem in computing---dynamic programming---and
see how our new theoretical understanding completely eliminates the challenges.
Since dynamic programming often improves algorithmic complexity asymptotically,
solving it is therefore equivalent to program optimization, and doing it
automatically demonstrates a total understanding of the problem space. This is
by no means a new idea, having first been done by @hinze_memo_2000, but we now
have enough comprehension to be able to understand (and prove!) where exactly
good ideas like this come from.

As is fitting for a capstone, this chapter has a great number of dependencies in
concepts:

Prerequisites

:   ```agda
open import Chapter1-Agda
  using (_×_; _,_; proj₁; proj₂; _⊎_; inj₁; inj₂)
    ```

:   ```agda
open import Chapter2-Numbers
  using (ℕ; zero; suc; _+_; _*_)
    ```

:   ```agda
open import Chapter3-Proofs
  using (_≡_; case_of_; module PropEq; module ≡-Reasoning)
open PropEq
  using (refl; sym; trans; cong)
    ```

:   ```agda
open import Chapter4-Relations
  using (Level; _⊔_; lsuc; Σ)
    ```

:   ```agda
open import Chapter6-Decidability
  using (Dec; yes; no; map-dec)
    ```

:   ```agda
open import Chapter7-Structures
  using ( id; _∘_; const; _≗_; prop-setoid; Setoid; ⊎-setoid
        ; ×-setoid)
    ```

:   ```agda
open import Chapter8-Isomorphisms
  using ( Iso; _≅_; ≅-refl; ≅-sym; ≅-trans; ⊎-fin; fin-iso
        ; ×-fin; Vec; []; _∷_; lookup; Fin; zero; suc; toℕ
        ; _Has_Elements; ⊎-prop-homo; ×-prop-homo)
    ```


## Why Can This Be Done?

Computing is a practical means to an end. One of the greatest tragedies in our
field is the muddled thinking that arises from conflating "what do we want to do"
from "how should we do it." But confusion exists only in our minds, and never in
reality. Because dynamic programming is an often-confusing solution to a class
of problems, we will likely learn more by studying the class of problems than we
will the offered solution.

Dynamic programming is helpful for problems with a great deal of overlapping
subproblems. This notion of subproblems arises from the algorithmic concept of
*divide and conquer,* which you will note is also muddled thinking---it too
confuses the question with a means of answering it.

At the end of the day, all computing reduces down to sampling functions at
finitely many points. Seen through this lens, dynamic programming is a technique
which makes functions less expensive to repeatedly sample, by caching their
results somewhere convenient.

This is the true nature of dynamic programming---as a technique, it is nothing
more than thinking about problems inductively, and memoizing that induction. By
virtue of being the sort of person who would read this book, you are clearly
already capable of thinking compositionally, and so all we have left is to
tackle the problem of memoization.

Why should we expect to be able to make progress on this problem? As seen in
@sec:exponents, we proved an isomorphism between functions on finite domains and
vectors. Indeed, it is exactly this vector which is most-often used as a caching
data structure when doing dynamic programming by hand. Figuring out exactly how
to index such a structure is often less clear and requires much fiddling in the
absence of explicit isomorphisms.

Note however that an effective memoization strategy is dependent on the problem.
This "one big vector" isn't necessarily always the best choice. If you know that
you need to sample the entire function space, you might as well just sample the
whole function into a table. But if sampling the function is sufficiently
expensive and you have no guarantee you'll need all of its image, you might
prefer to memoize the function at only those points necessary.

For functions with large input spaces, it would be quite wasteful to allocate a
table large enough to memoize the whole function, and proceed to only cache a
handful of points in it. Therefore, we conclude that different memoization
strategies must result in different caching data structures. And in fact, this
class of memoization strategies grows *fast*---corresponding to every possible
way of splitting the input space into contiguous chunks.

There is no one-size-fits-all memoization strategy, so our eventual solution to
this problem must be polymorphic over all possible strategies.

It certainly feels like we have our work cut out for us, doesn't it? Thankfully,
the task is less monumental than it seems. The hardest part is simply organizing
the problem, and our theory will guide us the rest of the way.


## Shaping the Cache

Our first order of business is to find a means of describing our desired
memoization strategy, which in turn means to find a way of describing the data
type we will use to cache results.[^cite-conal] The data structures we end up
building will all turn out to generalize *tries,* which is more commonly
thought-of as a structure for representing collections of strings. We will leave
the formal connection to tries unexplored in this text, but use the terminology
interchangeably.

[^cite-conal]: Generating classes of algorithms giving a "factoring" of the
  shape of the problem is a trick I learned from @elliott_generic_2017.

Note that while there are many variations on the theme, we are looking for the
*building blocks* of these cache shapes. It is undeniable that we must be able to
support a flat vector of contiguous results. Another means of building tries is
to combine two *differently-shaped* tries together. And our final means is
direct composition---that is, we'd like to nest one trie inside another. In
essence, this composition means we are no longer caching values, but instead
caching *caches of values.*

Rather surprisingly, these are all the shape combinators we need in order to
describe any trie we'd like. We'll see some examples momentarily, but in the
meantime, we can write `type:Shape` in Agda:

```agda
data Shape : Set where
  num     : ℕ → Shape
  beside  : Shape → Shape → Shape
  inside  : Shape → Shape → Shape
```


Hidden

:     ```agda
-- FIX
      ```


The names of these constructors are pleasingly straightforward. We have
`bind:n:num n`, which corresponds to a table of `n` elements, while
`ctor:beside` combines two caches "side by side", and `ctor:inside` composing
one cache inside of another. To get a feel for how `type:Shape` describes data
structures, let's look at a few examples.

As we have seen, the simplest trie imaginable is just a vector, which we will
represent via `ctor:num`. An 8-celled cache described by this constructor is
illustrated in @fig:t8; note that the filled squares represent places to cache
results.

~~~~ {design=code/Languages/Tree.hs label="The trie described by `expr:num 8`" #fig:t8}
asTrie $ Table 8 0
~~~~

The semantics of the trie built by `ctor:num` is that if any value in the table
is required, the entire table will be populated. Sometimes this is not desirable,
like when snappy startup times are expected, or when the function we'd like to
memoize is prohibitively expensive. Thus, the `ctor:num` shape by itself gives
us per-table caching. At the other end of the spectrum, we can get *per-element*
caching semantics by nesting one table inside of another, as in @fig:t8by1.

~~~~ {design=code/Languages/Tree.hs label="The trie described by `expr:inside (num 8) (num 1)`" #fig:t8by1}
asTrie $ And $ Table 8 $ Table 1 0
~~~~

The `ctor:inside` constructor allows us to compose caches; in the case of
@fig:t8by1, we have nested a table of 1 inside a table of 8. The data structure
described by this `type:Shape` is a vector of pointers to elements, where we have
a convention that a pointer doesn't point anywhere until an element in its
subtree has been cached.

As another example of how flexible the tries defined by our `type:Shape`
machinery are, we can look at using `ctor:beside`. This `type:Shape` lays out two
tries side by side, which we can use to define a binary tree by subsequently
nesting layers:

```agda
bintrie : ℕ → Shape
bintrie zero     = num 1
bintrie (suc n)  = beside (bintrie n) (bintrie n)
```

The result of this is illustrated in @fig:2x2x2:

~~~~ {design=code/Languages/Tree.hs label="The trie described by `expr:bintrie 3`" #fig:2x2x2}
asTrie $ let two = Or (Table 1 0) (Table 1 0) in Or (Or two two) (Or two two)
~~~~

Of course, nothing says we can't go off the rails and define arbitrarily weird
tries:

```agda
weird : Shape
weird = beside  (beside  (num 3)
                         (inside (num 2) (num 1)))
                (inside (num 3) (num 1))
```

which is illustrated in @fig:weird.

~~~~ {design=code/Languages/Tree.hs label="The trie described by `def:weird`" #fig:weird}
asTrie $ Or (Or (Table 3 0) (And (Table 2 (Table 1 0)))) (And (Table 3 (Table 1 0)))
~~~~

Hopefully you agree that the tries describable by `type:Shape` are indeed rich
in variation. Of course, we haven't actually built any of this yet, merely given
a type and its intended semantics. In the next section, we turn our attention
towards building these tries.


## Building the Tries

Whenever we'd like to build a data structure whose cases correspond to some
other type, our immediate reaction should be to use an indexed data type. This
is no exception; we can build a `type:Trie` data structure *parameterized* by the
values we'd like to store it in, and *indexed* by its shape:

```agda
private variable
  ℓ ℓ₁ ℓ₂ : Level

data Trie (B : Set ℓ) : Shape → Set ℓ where
  empty  : {sh : Shape}                          → Trie B sh            -- ! 1
  table  : {n : ℕ}        → Vec B n              → Trie B (num n)
  both   : {m n : Shape}  → Trie B m → Trie B n  → Trie B (beside m n)
  nest   : {m n : Shape}  → Trie (Trie B n) m    → Trie B (inside m n)  -- ! 2
```


Hidden

:     ```agda
-- FIX
      ```


Alongside constructors corresponding to the three for `type:Shape`, we have
added a fourth constructor at [1](Ann), corresponding to an empty, unpopulated
trie. A trie of any shape can be empty, thus `ctor:empty` makes no demands on
the index of `type:Trie`.

At [2](Ann), notice the non-regular recursion; our trie parameter no longer
contains `B`, but instead `bind:B n:Trie B n`.

From the `type:Shape` of a trie, we can also compute an appropriate type for
indexing it, given by `type:Ix`:

```agda
Ix : Shape → Set
Ix (num n)       = Fin n
Ix (beside m n)  = Ix m ⊎ Ix n
Ix (inside m n)  = Ix m × Ix n
```

This `bind:sh:Ix sh` type acts as a lookup key in a corresponding `bind:B
sh:Trie B sh`. If we ignore the `ctor:empty` case, a `ctor:num`-shaped trie is a
vector, which we can index via a `type:Fin`. In the `ctor:beside` case, we have
two sub-tries we'd like to differentiate between; a key is therefore the
coproduct of the sub-trie keys. Similarly, for `ctor:inside` we have nested one
trie inside another, meaning we need a key for each trie in order to
successfully find a `B`.

The number of keys possible in a `type:Shape` is given by `def:∣_∣`:

```agda
∣_∣ : Shape → ℕ
∣ num     m    ∣ = m
∣ beside  m n  ∣ = ∣ m  ∣ +  ∣ n ∣
∣ inside  m n  ∣ = ∣ m  ∣ *  ∣ n ∣
```

which we can prove by way of `def:shape-fin`:

```agda
shape-fin : (sh : Shape) → prop-setoid (Ix sh) Has ∣ sh ∣ Elements
shape-fin (num x)       = ≅-refl
shape-fin (beside m n)  = ≅-trans  (≅-sym ⊎-prop-homo)
                                   (⊎-fin (shape-fin m) (shape-fin n))
shape-fin (inside m n)  = ≅-trans  (≅-sym ×-prop-homo)
                                   (×-fin (shape-fin m) (shape-fin n))
```

We will also require decidability of propositional equality over two indices,
which we could write by hand, but will instead get by transporting across
`def:shape-fin` and using our decidable equality over `type:Fin`.

```agda
open import Data.Fin using (_≟_)
open Iso using (to; from; from∘to)

Ix-dec : {sh : Shape} → (ix₁ ix₂ : Ix sh) → Dec (ix₁ ≡ ix₂)
Ix-dec {sh = sh} ix₁ ix₂
  = let s = shape-fin sh
    in  map-dec
          (λ toix₁=toix₂ → begin
            ix₁                ≡⟨ sym (from∘to s ix₁) ⟩
            from s (to s ix₁)  ≡⟨ cong (from s) toix₁=toix₂ ⟩
            from s (to s ix₂)  ≡⟨ from∘to s ix₂ ⟩
            ix₂                ∎)
          (cong (to s))
          (to s ix₁ ≟ to s ix₂)
  where open ≡-Reasoning
```

We'll need a few other miscellaneous helper functions and proofs as well. First,
often we can infer the first argument of a `type:Σ` type, in which case we can
omit it using `def:-,_`:

```agda
-,_ : {A : Set ℓ₁} {a : A} {B : A → Set ℓ₂} → B a → Σ A B
-,_ {a = a} b = a , b
```

Also, given a function out of `type:Fin`, we can use it to build a `type:Vec`,
as in `def:tabulate`:

```agda
tabulate : {n : ℕ} {A : Set ℓ} → (Fin n → A) → Vec A n
tabulate {n = zero}   f = []
tabulate {n = suc n}  f = f zero ∷ tabulate (f ∘ suc)
```

Finally, we know that calling `def:lookup` on `def:tabulate` is the same as
sampling the function we used to build the table:

```agda
lookup∘tabulate
  : {n : ℕ} {A : Set ℓ}
  → (f : Fin n → A)
  → (i : Fin n)
  → lookup (tabulate f) i ≡ f i
lookup∘tabulate f zero    = refl
lookup∘tabulate f (suc i) = lookup∘tabulate (f ∘ suc) i
```


## Memoizing Functions

An obvious way to go about implementing our memoizing tries is to jump into just
that, the implementation, and prove separately that the implementation is
correct. But take it from someone who went down that path and got stumped for a
week, doing so is much less trivial than it seems. Not only did I manage to get
the implementation wrong at first, proving the fixed version correct is also a
huge ordeal.

Better than jumping in immediately is to take a moment and think about what
exactly a memoized trie looks like. Having done that work, we will then
immortalize this thinking in a new type, which indexes a `type:Trie`, proving
that trie does indeed memoize the particular function.[^cite-trick] Only after
all of this work is done will we jump into implementation, using our types to
guarantee correctness *by construction.*

[^cite-trick]: This is a trick I learned from @scholz_parsing_2011, where you
  show correctness with respect to an indexed type that provides semantics.

First, we'll need some variables in scope:

```agda
private variable
  B : Set ℓ
  sh m n : Shape
  t₁ : Trie B m
  t₂ : Trie B n
  f : Ix sh → B
```

We now have three definitions that need to be defined simultaneously, which we
can do by way of Agda's `keyword:mutual` keyword. Mutual blocks introduce a new
scope in which definitions can refer to one another, without the top-down
order that Agda usually enforces. We'll define it momentarily, but for the time
being, assume that we have a data type `type:Memoizes` `f` `tr` which proves
that trie `tr` is filled only with values produced by function `f`. Then, a
`def:MemoTrie` is a `type:Trie` alongside with a proof that it does indeed
memoize a function:

```agda
mutual
  MemoTrie : {B : Set ℓ} {sh : Shape} → (Ix sh → B) → Set ℓ
  MemoTrie {B = B} {sh = sh} f = Σ (Trie B sh) (Memoizes f)
```

Getting the definition of `type:Memoizes` right is rather finicky, so we will
proceed by case. First, its type:

```agda
  data Memoizes {B : Set ℓ}
      : {sh : Shape}
      → (f : Ix sh → B)
      → Trie B sh
      → Set ℓ where
```

Of particular interest here is the sheer number of indices we have for
`type:Memoizes`. We might expect that `sh` and `f` could be *parameters*
instead of indices, but each constructor of `type:Memoizes` makes different
demands of the shape, on which the function is dependent. Thus they must both be
indices.

For our first case, we note that an `ctor:empty` trie is vacuously memoized, for
any function at all---as witnessed by the `ctor:emptyM` (for "memoized")
constructor:

```agda
    emptyM : {f : Ix sh → B} → Memoizes f empty
```

A `ctor:table` trie is memoized if the vector it contains was built via
`def:tabulate`:

```agda
    tableM
      : {n : ℕ} {f : Ix (num n) → B}
      → Memoizes f (table (tabulate f))
```

We can show that a `ctor:both` trie is correctly memoized if its constituent
tries split the function space in half, memoizing the `ctor:inj₁` and
`ctor:inj₂` halves, respectively:

```agda
    bothM
      : {f : Ix (beside m n) → B}
      → Memoizes (f ∘ inj₁) t₁
      → Memoizes (f ∘ inj₂) t₂
      → Memoizes f (both t₁ t₂)
```

And now we come to the hard part---determining exactly when a `ctor:nest` trie
correctly memoizes a function. Spiritually this should be the same as in
`ctor:bothM`, except that we now need to split the function into an arbitrary
number of smaller functions, show that each sub-trie correctly memoizes one, and
use all of this information to actually *build* a `ctor:nest` trie.

We will accomplish splitting the function and showing each sub-trie correctly
memoizes its cut by way of a function, transforming the index of each sub-trie
into a `type:MemoTrie`. We will use a helper function, `def:to-trie`, to
transform this function-of-sub-tries into the necessary nested `type:Trie`.

```agda
    nestM
      : {f : Ix (inside m n) → B}
      → (subf : (ix : Ix m) → MemoTrie (f ∘ (ix ,_)))
      → Memoizes f (nest (proj₁ (to-trie {f = f} subf)))
```

All that's left is to write `def:to-trie`, which, despite the tricky-looking
implementation, actually comes for free given the types.

```agda
  to-trie
      : {m n : Shape}
      → {f : Ix (inside m n) → B}
      → (subf : (ix : Ix m) → Σ (Trie B n) (Memoizes (f ∘ (ix ,_))))
      → MemoTrie (proj₁ ∘ subf)
  to-trie {m = num _} _
    = -, tableM
  to-trie {m = beside _ _} subf
    with proj₂ (to-trie (subf ∘ inj₁)) , proj₂ (to-trie (subf ∘ inj₂))
  ...  |  mt₁ , mt₂ =  -, bothM mt₁ mt₂
  to-trie {m = inside _ _} f2
    = -, nestM (λ i → to-trie λ j → f2 (i , j))
```


## Inspecting Memoized Tries

Before we go through the work of actually getting values *out* of
`type:MemoTrie`s, let's take a moment to see how far our current machinery can
go. We'll write a dummy function to memoize, which simply turns its desired
index into a `type:ℕ`:

```agda
dummy : (sh : Shape) → Ix sh → ℕ
dummy sh ix = toℕ (to (shape-fin sh) ix)
```

Now, for any arbitrary `type:Shape`, we can give a proof of memoization to Agda,
and ask it to *build* us the relevant trie. For example, let's look again at the
`type:Shape` for @fig:weird above:

```agda
weird⅋ : Shape
weird⅋ = beside  (beside  (num 3)
                          (inside (num 2) (num 1)))
                 (inside (num 3) (num 1))
```

For `def:dummy weird`, let's now give a `type:Memoizes`, which chooses some
sub-tries to be `ctor:emptyM`, and others to be full:

```agda
_ : Memoizes
      (dummy weird)
      ?
_ = bothM (bothM tableM emptyM)
          (nestM λ { zero              → -, emptyM
                   ; (suc zero)        → -, tableM
                   ; (suc (suc zero))  → -, emptyM
                   })
```

Recall that [Solve](AgdaCmd) fills in values that can be unambiguously
inferred. If we invoke solve in the hole above, Agda will *synthesize* the only
valid `type:Trie` which can possibly satisfy the given `type:Memoizes` proof. In
this case, it responds with:


Hidden

:   ```agda
_ : Memoizes (dummy weird)
    ```


```agda
      (both  (both  (table  (0 ∷ 1 ∷ 2 ∷ []))
                    empty)
             (nest (table  ( empty
                           ∷ table (6 ∷ [])
                           ∷ empty
                           ∷ []))))
```

which we can visualize as in @fig:amazing, where `∙` corresponds to an
`ctor:empty` trie.


Hidden

:                     ```agda
_ = bothM (bothM tableM emptyM)
          (nestM λ { zero              → -, emptyM
                   ; (suc zero)        → -, tableM
                   ; (suc (suc zero))  → -, emptyM
                   })
                      ```

~~~~ {design=code/Languages/Tree.hs label="A memoized `type:Trie`, synthesized by Agda" #fig:amazing}
asTrie $ Or (Or (Tabled [0, 1, 2]) Null) (And (Tabled [Null, Tabled [6], Null]))
~~~~

In an incredible show, Agda managed to find the memoized `type:Trie` which
corresponds to our proof! Take a moment or two to marvel at this result; our
type `type:Memoizes` is precise enough that it *completely* constrains *all*
valid `type:Trie`s. Truly remarkable.


## Updating the Trie

We are only a few steps away from a working, self-updating trie. Having
successfully constrained what a memoized `type:Trie` must look like, we need
only define the function which looks up a value in this `type:Trie`, possibly
filling in more fields if they are not yet present. And then we will tie a
little bow around the whole thing, wrapping all the machinery in a pleasant
interface.

For now, we will need a lemma, `def:replace`, which replaces a single
branch of a `ctor:nestM`'s `subf` function. The idea here is to create a new
`subf` which compares any looked-up index with the one we'd like to replace; if
they match, return the new `type:Memoizes`, otherwise, look up this index in the
old `subf`.

```agda
replace
  : {fst : Trie B n}
  → (x : Ix m)
  → Memoizes (f ∘ (x ,_)) fst
  → ((ix : Ix m) → MemoTrie (f ∘ (ix ,_)))
  → MemoTrie f
replace x sub-mem subf = -, nestM (λ ix →
  case Ix-dec ix x of λ
    { (yes refl)  → -, sub-mem
    ; (no z)      → subf ix
    }
  )
```

We are now ready for the main event, implementing `def:get′`, which looks up an
index in a `type:Memoizes`[^why-not-trie]. If the index is already present in
the trie, `def:get′` simply returns the associated value. If it's not,
`def:get′` will build just enough of the trie so that it can get the correct
value.

[^why-not-trie]: Why don't we look up an index in a `type:Trie`, you might be
  wondering? It's because every `type:Memoizes` *uniquely* describes a
  memoized `type:Trie`, and we're only interested in the case where we're
  looking something up in a `type:Trie` that is *guaranteed* to memoize the
  given function.

Note that we don't have mutation in Agda, so we can't *update* the trie
directly. Instead, we will return a new `type:MemoTrie` alongside, corresponding
to what the trie would be if we *could* update it. This is purely a concession
in Agda, and if you wanted to implement the same algorithm in another language,
you could certainly perform the mutation. Hence the type of `def:get′`:

```agda
get′
  : {t : Trie B sh}
  → Memoizes f t
  → Ix sh
  → B × MemoTrie f
```

There are eight cases we need to consider, so we will look at them in bunches.
In general, we must first branch on the `type:Memoizes` proof, and, in the case
of `ctor:emptyM`, subsequently branch on the `type:Shape` `sh` in order to
determine how we must fill in the trie.

The first case is when we've encountered an empty `ctor:table`, which we must
`def:tabulate`, being careful to look up the desired `B` in the resulting table,
rather than evaluating `f` any more than we have to:

```agda
get′ {sh = num x} {f = f} emptyM a =
  let t = tabulate f
   in lookup t a , table t , tableM
```

Note, as you look through the remainder of the cases, that this is the only case
in which we evaluate `f`.

If instead we'd like to lookup a value in an empty `ctor:both` trie, we can
branch on which sub-trie we're looking at. This sub-trie is also empty, but will
recursively find the right answer, returning us a minimally-filled in trie,
which we can insert into the proper branch, leaving `ctor:emptyM` in the other
branch:

```agda
get′ {sh = beside m n} emptyM (inj₁ x)
  with get′ emptyM x
... | b , t₁  , memo = b , both t₁ empty  , bothM memo emptyM
get′ {sh = beside m n} emptyM (inj₂ y)
  with get′ emptyM y
... | b , t₂  , memo = b , both empty t₂  , bothM emptyM memo
```

The only other case in which we might be looking at a `ctor:emptyM` is when we
are looking to build a `ctor:nest` trie. This is the same as replacing a branch
of the empty-everywhere `subf`:

```agda
get′ {sh = inside m n} {f = f} emptyM (x , y)
  with get′ { f = f ∘ (x ,_) } emptyM y
... | b , _ , sub-mem
    = b , replace x sub-mem λ ix → -, emptyM
```

In all other cases, the trie we'd like to index already exists. If it's a table,
we know it must already be filled in, and so we can just lookup the answer in
the vector:

```agda
get′ {sh = num _} {t = table t} tableM a
    = lookup t a , table t , tableM
```

Otherwise, we need only call `def:get′` recursively, and replace the branch we
looked at with the updated sub-trie:

```agda
get′ {sh = beside m n} (bothM l r) (inj₁ x)
  with get′ l x
... | b , t₁ , memo = b , both t₁ _ , bothM memo r
get′ {sh = beside m n} (bothM l r) (inj₂ y)
  with get′ r y
... | b , t₂ , memo = b , both _ t₂ , bothM l memo
```

In the last case, we need to look inside an existent `ctor:nestM` trie, which
means looking at its `subf` function, and then recursively calling `def:get′` on
what we find. Care must be taken to subsequently `def:replace` the sub-trie we
found:[^wont-typecheck]

[^wont-typecheck]: Although, rather amazingly, failing to call `def:replace`
  will prevent the program from typechecking!

```agda
get′ {sh = inside m n} (nestM subf) (x , y)
  with subf x
... | _ , sub-mem
  with get′ sub-mem y
... | b , _ , _ = b , replace x sub-mem subf
```

And we're done! We've got a satisfactory implementation of `def:get′` that
certainly seems to work! While we have good guarantees by the fact that
`def:get′` operates over `type:MemoTrie`s, an outside observer might not be as
impressed with our handiwork as we are. To convince any potential naysayers, we
can also show `def:get′-is-fn`, which shows that `def:get′` and the
function-being-memoized are extensionally equal:

```agda
get′-is-fn
    : {sh : Shape} {t : Trie B sh} {f : Ix sh → B}
    → (mt : Memoizes f t)
    → proj₁ ∘ get′ mt ≗ f
get′-is-fn {sh = num _}       emptyM x          = lookup∘tabulate _ x
get′-is-fn {sh = beside _ _}  emptyM (inj₁  x)  = get′-is-fn emptyM x
get′-is-fn {sh = beside _ _}  emptyM (inj₂  y)  = get′-is-fn emptyM y
get′-is-fn {sh = inside _ _}  emptyM (x , y)    = get′-is-fn emptyM y
get′-is-fn {sh = num _}       tableM x          = lookup∘tabulate _ x
get′-is-fn {sh = beside _ _}  (bothM t₁ _) (inj₁  x) = get′-is-fn t₁  x
get′-is-fn {sh = beside _ _}  (bothM _ t₂) (inj₂  y) = get′-is-fn t₂  y
get′-is-fn {sh = inside _ _}  (nestM subf) (x , y)
  = get′-is-fn (proj₂ (subf x)) y
```


## Wrapping It All Up

Our machinery so far has all operated over this weird function out of indices of
our `type:Shape`---but that's a poor interface for anyone who has a real
function they'd like to memoize. All that remains is for us to package up our
memoization code into something more readily usable.

The trick is we'll take a `type:Shape`, the function we'd like to memoize, and
a proof that its domain has the same size as the `type:Shape`. From there, we
can run the isomorphism gauntlet to define a function more amenable to operating
with our memoization machinery:

```agda
module _ {A : Set} {B : Set ℓ} (sh : Shape)
         (f : A → B)
         (sized : prop-setoid A Has ∣ sh ∣ Elements)
         where

  private
    A≅Ix : prop-setoid A ≅ prop-setoid (Ix sh)
    A≅Ix = fin-iso sized (shape-fin sh)

    f′ : Ix sh → B
    f′ = f ∘ Iso.from A≅Ix
```

And finally, we can give an implementation of `def:get` with a much nicer
signature:

```agda
  Memoized : Set ℓ
  Memoized = MemoTrie f′

  get : Memoized → A → B × Memoized
  get (_ , memo) = get′ memo ∘ (Iso.to A≅Ix)
```

-- TODO(sandy): some wrapping up ?





## Unicode {.unlisted}

```unicodetable
× U+00D7 MULTIPLICATION SIGN (\x)
Σ U+03A3 GREEK CAPITAL LETTER SIGMA (\GS)
λ U+03BB GREEK SMALL LETTER LAMDA (\Gl)
′ U+2032 PRIME (\')
₁ U+2081 SUBSCRIPT ONE (\_1)
₂ U+2082 SUBSCRIPT TWO (\_2)
ℓ U+2113 SCRIPT SMALL L (\ell)
ℕ U+2115 DOUBLE-STRUCK CAPITAL N (\bN)
→ U+2192 RIGHTWARDS ARROW (\to)
∎ U+220E END OF PROOF (\qed)
∘ U+2218 RING OPERATOR (\o)
∙ U+2219 BULLET OPERATOR (\.)
∣ U+2223 DIVIDES (\|)
∷ U+2237 PROPORTION (\::)
≅ U+2245 APPROXIMATELY EQUAL TO (\~=)
≗ U+2257 RING EQUAL TO (\o=)
≟ U+225F QUESTIONED EQUAL TO (\?=)
≡ U+2261 IDENTICAL TO (\==)
⊎ U+228E MULTISET UNION (\u+)
⊔ U+2294 SQUARE CUP (\lub)
⟨ U+27E8 MATHEMATICAL LEFT ANGLE BRACKET (\<)
⟩ U+27E9 MATHEMATICAL RIGHT ANGLE BRACKET (\>)
```

