# Constructivism and Computation

It is worth noting that the mathematics we will be doing in this book are not
the "whole story" of mathematics. You see, there are two big camps in the
mathematics worlds: the *classicists* and the *constructivists.* Much like
many religious sects, these two groups have much more in common than they have
distinct. In fact, the only distinction between these two groups of
truth-seekers is their opinion on the nature of falsities.

The classicists believe all mathematical statements are divided into the ones
which are *true* and the ones which are *false.* There is no middle ground, and
thus the ones which are not true must certainly be false, and vice versa. It is
very probable that you, gentle reader, fall into this camp, likely without
knowing it. Most of the world does.

Contrasting with the classicists are the constructivists, who trust their nose
more than they trust logical arguments. Constructivists aren't happy knowing
something merely *doesn't not exist;* they'd like to see that thing with their
own eyes.

In general, there are two ways to mathematically show something exists. The
first way is to just build the thing, in sense "proof by doing." The other is to
show that a world without the thing would be meaningless, and thus show its
existence --- in some sense --- by sheer force of will, because we really
*don't* want to believe our world is meaningless.

To illustrate this difference, suppose we'd like to prove the existence of a
number that is divisible by 2, and 5. Under a classical worldview, a perfectly
acceptable (although silly) proof would go something like this:

-- TODO(sandy): gross

* Suppose there does not exist a number $n$ that is divisible by 2 and 5.
* The factorial function $m!$ has divisors for every $x \le m$.
* $2 \le 5$
* The factorial function is monotonically increasing.
* Therefore, there exists some number $k$ such that $k!$ has divisors 2 and 5.
* But we said there is no such number. This is a contradiction.
* Therefore there does exist a number $n$ that is divisible by 2 and 5.

The constructivists instead, are required to just give you some multiple of 10.

This perspective suggests that the difference between the two camps is one more
of philosophy than it is necessarily of technique. In fact, the classical proof
above gives a hint as to what this philosophical difference really is. The
classicists view contradiction as anathema, and thus that anything which leads
to it must be false. The constructivists, on the other hand, *define refutation
of a claim* as being a proof that it would result in contradiction.

Symbolically, we write the refutation of a proposition `P` as `¬ P`, and the
entire disagreement descends into a question of whether the following function
should exist:

```notagda
¬-elim : ¬ (¬ P) → P
```

that is, do two negations cancel one another? In essence, this really boils down
to a question of "what type does `P` have?" The classicists say `P : Bool`,
while the constructivists say `P : Set`. Under `P : Bool`, it's clear that `¬ =
not`, and thus, that `¬-elim` is inhabited.

However, this is less clearly true under the constructivist perspective that `P
: Set`. Instead, we begin by defining the `Set` of falsity. Since both camps
agree that there should never be a proof of false, this `Set` is defined by
having no inhabitants:

```agda
{-# OPTIONS --allow-unsolved-metas #-}

module constructivism where

module introduction where
  data ⊥ : Set where
    -- intentionally left empty
```

Mathematicians hate the idea of having a proof of false, because of the
principle of *reductio ad absurdum* --- that is, from false, you can prove
anything. We can show this in Agda:

```agda
  private variable
    P : Set

  ⊥-elim : ⊥ → P
  ⊥-elim ()
```

This funny `()` pattern is Agda's acknowledgment that this function is vacuously
true. That is, it's a bit of a bluff: `⊥-elim` can return any `A` you want
because you can't actually call it in the first place ---- there are no `⊥`s
around to use as an argument to call the thing!

And this is the necessary trick the constructivists use to encode a false
statement; from it, you could conclude anything, including `⊥` which we have
intentionally constructed as something un-concludable. That is, we can define
the refutation of `P` as a function that, given a `P`, would result in `⊥`:

```agda
  ¬ : Set → Set
  ¬ P = P → ⊥
```

We can use `¬` to construct more traditional sorts of "negative propositions",
like the fact that two things are *not* equal:

```agda
  open import Relation.Binary.PropositionalEquality using (_≡_)

  _≢_ : P → P → Set
  x ≢ y = ¬ (x ≡ y)
```

Returning to the idea of `¬-elim : {A : Set} → ¬ (¬ A) → A`, it's clear that
this simply isn't true given our encoding of `¬`. We would like to produce an
`A`, but all we have is a function `(A → ⊥) → ⊥`. There's nowhere to get an `A`
from, but maybe we could cheat and try `⊥-elim` on the result of our function.

Following this line of thought through, we can get as far as the following:

```agda
  ¬-elim : ¬ (¬ P) → P
  ¬-elim ¬p→⊥ = ⊥-elim (¬p→⊥ (λ p → {! !}))
```

where we now have `a : A` in scope, but simply have no way to exfiltrate it.
Alas.

You might have heard of the *law of the excluded middle,* or LEM for short,
which is exactly the classical claim that any proposition is either true or it
is false. That is, `lem : {P : Set} → P ⊎ ¬ P`. Traditionally, it is the
existence of LEM which differentiates classical from constructive mathematics,
so why are we talking about `¬-elim` instead? As it happens, the LEM is
equivalent to `¬-elim`, which we can prove by implementing one in terms of the
other.

Assuming we have `¬-elim`, we can use it to provide the law of excluded middle,
as per `¬-elim→lem`. The trick is to use `¬-elim` to get into scope a proof that
the LEM doesn't hold, with the intention to derive a contradiction from this
fact:

```agda
  open import Data.Sum

  ¬-elim→lem : P ⊎ ¬ P
  ¬-elim→lem = ¬-elim λ ¬lem →
    ¬lem ?
```

In order to show the contradiction, we must fill the hole with a `P ⊎ ¬ P`. But
that was our original goal, which you might think means we haven't accomplished
anything. But in fact, we have. We've gained the ability to bluff. Now, we can
say "no, `P` certainly isn't true:"

```agda
  ¬-elim→lem⅋ : P ⊎ ¬ P
  ¬-elim→lem⅋ = ¬-elim λ ¬lem →
    ¬lem (inj₂ λ p → ?)
```

In order to show `P` isn't so, we must be able to turn a proof of `P` into `⊥`,
which we can do by reneging on our early promise that `P` wasn't true, since we
now have evidence that it is!

```agda
  ¬-elim→lem⅋⅋ : P ⊎ ¬ P
  ¬-elim→lem⅋⅋ = ¬-elim λ ¬lem →
    ¬lem (inj₂ λ p →
      ¬lem (inj₁ p))
```

What a weaselly sort of way to something --- pretend it isn't, and change your
mind if someone calls your bluff. Nevertheless, the typechecker is happy, and
therefore, we are too.

Recall that Agda is a programming language, and thus that there must be some
sort of computational intepretation of the programs we can write in it. The
computational interpretation of the LEM is to say "no," but if anyone ever
refutes that, you just rewind back to where you said "no" and say "yes" instead,
using your new evidence. In this light, `¬-elim` captures the current
continuation of the remainder of the program, and calling that function will
rewind all of your progress, jumping back to whatever instruction was next when
you called `¬-elim`.

The harm here is the existence of this non-determinism. You can go your whole
life, proving things that transitively depend on `¬ P`. But then, two hundred
years later, it turns out `P` was true all along, which means that none of your
life's work still holds! Better to be safe, and admit our ignorance that we
simply don't know which of `P` or `¬ P` is true, rather than pretending and
hoping we got it right.

Returning to the problem at hand, it's thankfully much simplier to go the other
direction, from the LEM to `¬`-elimination. We just ask which one is true. If
it's `P`, then we're already done. Otherwise, we can use `¬ P` to get a `⊥` and
then `⊥`-eliminate it away.

```agda
  lem→¬-elim : ¬ (¬ P) → P
  lem→¬-elim ¬p→⊥ with ¬-elim→lem
  ... | inj₁ p = p
  ... | inj₂ ¬p = ⊥-elim (¬p→⊥ ¬p)
```

For the remainder of this book, we will ignore the possibility of the existence
of the law of the excluded middle, and by equivalence, the possibility of
`¬-elim`. We will focus our efforts henceforth entirely on constructivist
mathematics, but that is not to say that classical mathematics can't be done in
Agda! You can merely `postulate` the LEM and be on your merry way.


## Decidability

Of course, just because the law of excluded middle isn't constructively true
*in general* doesn't mean it's *never true.* For example, I can show that any
natural number is, or is not, 0:

```agda
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_)
open import Data.Sum

is-zero?⅋ : (n : ℕ) → (n ≡ 0) ⊎ (¬ (n ≡ 0))
is-zero?⅋ zero    = inj₁ refl
is-zero?⅋ (suc n) = inj₂ λ ()   -- ! 1
```

The first case here is easy enough to understand, but the second might require a
little explanation. At [1](Ann), we have pattern matched on the argument and
know that it is a `suc`, not a `zero`. Thus, we are required to show `suc n ≡
zero`, which is clearly not the case, because in Agda, data constructors are
always apart. In order to show this is false, we must provide a function `(suc n
≡ zero) → ⊥`. Simply pattern matching on the argument is enough for Agda to
figure out we're clearly talking nonsense, and it replaces our lambda pattern
with `()` showing there is no such proof.

So, what differentiates our ability to determine whether `n ≡ 0`, but not some
arbitrary proposition `P`? We call the difference *decidability* --- a property
`P` is decidable if and only if it's possible to determine whether `P` or `¬ P`
holds. Rather than overload poor `_⊎_` to satisfy this property for us, we will
instead define a new type:

```agda
module Hypothetical where
  data Dec (P : Set) : Set where
    yes :  P → Dec P
    no : ¬ P → Dec P
```

Rather than use the clumsy names `inj₁` and `inj₂`, we instead say `yes` if the
proposition holds, and `no` if it doesn't. We can rewrite `is-zero?` in terms of
our new machinery:

```agda
  is-zero? : (n : ℕ) → Dec (n ≡ 0)
  is-zero? zero    = yes refl
  is-zero? (suc n) = no λ ()
```

Besides the simplified type and the new constructor names, nothing has changed
here. But what does decidability really mean? It means there is a *decision
procedure* (an algorithm) which we can run to tell us the answer. For example,
there's a decision procedure that will tell us if two natural numbers are equal
--- namely, keep making them smaller and see if they both get to `zero` at the
time:

```agda
  _≟_ : (x y : ℕ) → Dec (x ≡ y)
  zero  ≟ zero  = yes refl
  zero  ≟ suc y = no λ ()
  suc x ≟ zero  = no λ ()
```

This definition of `_≟_` is not quite complete; we still need to show the
`suc`/`suc` case is decidable. But the trick, as always, is to recurse,
using the decidability of if the smaller numbers are equal, and if so, lifting
the proof to one of the successed numbers.

```agda
  suc x ≟ suc y
    with x ≟ y
  ... | yes x=y = yes (cong suc x=y)  -- ! 1
  ... | no  x≠y = no λ sx=sy → x≠y (suc-injective sx=sy)  -- ! 2
    where
      open import Data.Nat.Properties using (suc-injective)
```

In the `yes` case at [1](Ann), we are required to turn a proof of `x ≡ y` into a
proof that `suc x ≡ suc y`, which is an obvious application of `cong suc`.
However, due to the way we've constructed propositional refutation, at
[2](Ann) we need to go the other direction --- turning a proof of `suc x ≡ suc
y` into a proof that `x ≡ y` (that is, so we can refute that fact via `x≠y`.)
There is clearly some sort of "backwardness" going on here in the `no` case. We
will explore this further in a moment.

Maybe you are wondering why decidability is an important property to have.
Perhaps its most salient feature is that it is helpful in connecting the messy
outside world to the crisp, inner logic of a dependently typed programming
language. Data that comes from the outside world is subject to the whims of
users, and is unlikely to be well-typed, let alone *dependently-typed.*

The notion of decidability generalizes to any sort of decision procedure which
results in a proof one way or another. One common form of decidability you're
likely familiar with is the *trichotomy* of `_<_`; that is, the fact that for
any `x y : ℕ`, exactly one of the following propositions holds: `x < y`, `x ≡
y`, or `x > y`. We can define trichotomy:

```agda
open import Data.Nat using (_<_; _>_; _≤_; z≤n; s≤s)

data <-Trichotomy (x y : ℕ) : Set where
  tri< : x < y → <-Trichotomy x y
  tri≈ : x ≡ y → <-Trichotomy x y
  tri> : x > y → <-Trichotomy x y
```

and then witness the trichotomy of `_<_` via `<-cmp`:

```agda
<-cmp : (x y : ℕ) → <-Trichotomy x y
<-cmp zero zero = tri≈ refl
<-cmp zero (suc y) = tri< (s≤s z≤n)
<-cmp (suc x) zero = tri> (s≤s z≤n)
<-cmp (suc x) (suc y) with <-cmp x y
... | tri< x<y = tri< (s≤s x<y)
... | tri≈ x≈y = tri≈ (cong suc x≈y)
... | tri> x>y = tri> (s≤s x>y)
```

The `<-cmp` is a decision procedure fully capable of not only determining which
of two numbers is bigger, but also of *proving* why it's so. We will use this
trichotomy immediately in our next example of decidability.

Let's consider the case of a *binary search tree* (BST) of natural numbers. A
BST has the property that every value in the left sub-tree of a branch is
smaller than the node at the branch, and likewise, every value on the right is
larger. We can encode such a thing in Agda by tracking the smallest and largest
elements in the tree as indices on the type.

Under this framing, a BST is either empty with arbitrary bounds (albeit with the
constraint that the lower bound is smaller than the higher bound):

```agda
open Data.Nat using (_≤_; z≤n; s≤s)

data BST : ℕ → ℕ → Set where
  ⊘ : {lo hi : ℕ} → ⦃ lo ≤ hi ⦄ → BST lo hi
```

or alternatively, that we have a branch that satisfies the BST invariant stating
sub-trees are well-organized with respect to the root node:

```agda
  branch' : {lo hi : ℕ}
         → (n : ℕ)
         → (l : BST lo n)
         → (r : BST n hi)
         → BST lo hi
```

When we visualize binary search trees, we prefer to put the left sub-tree on the
left of the root node, but `branch'` doesn't allow us to do this, since `l`
depends on `n`. We can use a little syntactic sugar in the form of a pattern to
alleviate this problem:


```agda
pattern _◁_▷_ l n r = branch' n l r
```

Furthermore, it's tedious to need to write `⊘ ◁ n ▷ ⊘` whenever we want a leaf,
so we can add a pattern for that too.

```agda
pattern leaf n = ⊘ ◁ n ▷ ⊘
```

The goal is now that we'd like to insert a value guaranteed to be in bounds
into an existing `BST`. This latter constraint simplifies the problem, meaning
we don't need to determine new bounds for the `BST`, which would be an exercise
in patience. We begin with the type of `insert`:

```agda
open import Data.Nat.Properties using (≤-trans; n≤1+n)

insert
    : {lo hi : ℕ} → (n : ℕ)
    → ⦃ lo ≤ n ⦄ → ⦃ n≤h : n ≤ hi ⦄
    → BST lo hi
    → BST lo hi
```

If we are trying to insert into the empty tree, we can just leave a `leaf`
behind:

```agda
insert n ⊘ = leaf n
```

However, the branch case is much more interesting. We will need to recursively
insert our value into the sub-trees, but doing so requires us to have a proof
that our value is inside the bounds of the sub-tree. All we know, however, is
that the value is contained by the bounds of the entire tree. It's clear that
for an arbitrary value, this is going to require a runtime check, which is to
say, a decidable test of how `n` relates to `i`. The attentive reader will
notice that this is a perfect use-case for `<-cmp`.

By inspecting how `n` relates to `i`, we can refine our proofs of how `n` sits
in the bounds of the sub-trees.

```agda
insert n (l ◁ i ▷ r)
  with <-cmp n i
... | tri≈ n=i = l ◁ i ▷ r
... | tri< n<i =
  insert n ⦃ n≤h = ≤-trans (n≤1+n n) n<i ⦄ l ◁ i ▷ r
... | tri> i<n =
  l ◁ i ▷ insert n ⦃ (≤-trans (n≤1+n i) i<n) ⦄ r
```

You might be puzzled by the instance arguments used by `⊘` and `insert`; these
exist so that we can ask Agda to automatically solve the necessary bounds
proofs. By giving instances for both constructors of the irrelevant `_≤_`, Agda
will happily construct `x ≤ y` proofs whenever `x` and `y` are known statically:

```agda
private instance
  z≤ : {n : ℕ} → 0 ≤ n
  z≤ = z≤n

  s≤ : {a b : ℕ} → ⦃ a ≤ b ⦄ → suc a ≤ suc b
  s≤ ⦃ a≤b ⦄ = s≤s a≤b
```

We can now test our handiwork. By constructing an empty `BST` with explicit
bounds:

```agda
b : BST 0 100
b = ⊘
```

we are able to `insert` several values into it, and inspect the resulting value
in all of its glory:

```agda
_ : insert 3
      (insert 5
        (insert 10
          (insert 12
            (insert 5
              (insert 42 b)))))
    ≡ (leaf 3 ◁ 5 ▷ (leaf 10 ◁ 12 ▷ ⊘)) ◁ 42 ▷ ⊘
_ = refl
```

Inspecting the results, you can see that, read left-to-right, all numbers are in
ascending order. Furthermore, the duplicated `5` element only made it into the
resultant tree once.

Decidability (and its related forms, like trichotomy) is an important feature of
*computation,* and is the primary means of differentiating mathematics from
computation. Math requires no decidability, computation is useless without it.

