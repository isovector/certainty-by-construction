# Quotients

```agda
module 4-setoids where
open import Data.Nat
open import Data.Nat.Properties
```

Let's return to the perennial issue: when are two things equal to one another?
We've discussed *propositional equality,* that is, that two things are equal
when they are defined in exactly the same way. We've also looked at
*constructions over equality,* which allow us to derive new notions of equality
out of others, like we did with function extensionality. But in this chapter we
will discuss the notion of *quotients* --- that is, asserting by fiat that two
non-propositionally-equal things are in fact, equal.

A favorite example of quotienting for mathematicians are the so-called "ring of
natural numbers modulo $n$," more tersely written as $\mathbb{N}/n\mathbb{N}$.
But what is this ring? This ring is the mathematical way of saying "clock
addition" --- that is, we pick some $n$, maybe $n = 12$ for an example, and say
that whenever our arithmetic gets to $n$ it overflows back to 0. This is the
peculiar fact that, on an analog clock, we have the fact that $11 + 2 = 1
(\text{mod} 12)$.

How can we formalize this idea? Well, if we'd like to show $a = b (\text{mod}
n)$, we would like to find two multiples of $n$ that we can use to equate the
two. That is to say, we need to find $x, y : ℕ$ such that $a + xn = b + yn$.

The definition almost rolls off the tongue:

```agda
module mod-def where
  open import Relation.Binary.PropositionalEquality

  infix 4 _≈_⟨mod_⟩
  data _≈_⟨mod_⟩ (a b n : ℕ) : Set where
    ≈-mod
      : (x y : ℕ)
      → a + x * n ≡ b + y * n  -- ! 1
      → a ≈ b ⟨mod n ⟩
```

Notice that we use propositional equality at [1](Ann) to assert that we're
witnessing the fact that these two expressions *really are the same!* But that's
merely an implementation detail.

We can now show that our clock example works as expected:

```agda
  _ : 11 + 2 ≈ 1 ⟨mod 12 ⟩
  _ = ≈-mod 0 1 refl
```

Pretty nice, if you ask me.

My claim is that our use of the `≈` in `_≈_⟨mod_⟩` is valid; this relationship
truly is an equivalence relation --- that is to say, it's interchangeable with
equality, and behaves in an identical manner, mathematically speaking. Recall
that to show an equivalence relationship, we need to show the relation satisfies
reflexivity, symmetry, and transitivity. As usual, we can reify these
constraints into a record, parameterized by a relation:

```agda
module _ where
  private variable
    A : Set
    a b c : A

  record IsEquivalence (_≈_ : A → A → Set) : Set where
    field
      refl : a ≈ a
      sym : a ≈ b → b ≈ a
      trans : a ≈ b → b ≈ c → a ≈ c
```

Let's now show that `_≈_⟨mod_⟩` forms an equivalence relation. We begin by
binding a few helper variables:

```agda
module mod-base (n : ℕ) where
  open mod-def public
  open import Relation.Binary.PropositionalEquality

  private
    variable
      a b c d : ℕ
```

Show `refl` is trivial --- the two numbers are already equal:

```agda
  mod-refl : a ≈ a ⟨mod n ⟩
  mod-refl = ≈-mod 0 0 refl
```

Symmetry is also simple; we just need to swap around which multiples are which,
and fiddle the equality proof correspondingly:

```agda
  mod-sym : a ≈ b ⟨mod n ⟩ → b ≈ a ⟨mod n ⟩
  mod-sym (≈-mod x y p) = ≈-mod y x (sym p)
```

Transitivity, however, is significantly more involved. Before diving into the
implementation, let's work out the solution "on paper" first, where we can more
more quickly and require less formality in justifying our steps.

We can set up the problem as given $a, b, c, x, y, z, w : ℕ$, we have a series
of simultaneous equations:

$$
a + xn = b + yn \\
b + zn = c + wn
$$

We'd like to eliminate the $b$ term, so we can solve both sides for $b$:

$$
a + xn - yn = b = c + wn - zn
$$

Recall, however, that we're working over the natural numbers, which do not have
a satisfactory implementation of subtraction. So we'd prefer to phrase the
problem only in addition, which we can do by moving the negative terms to the
other side:

$$
a + xn + zn = c + wn + yn
$$

and all that's left to do is to factor out the $n$:

$$
a + (x + z)n = c + (w + y)n
$$

This gives us our desired multiples of $n$ for implementing transitivity:

```agda
  mod-trans : a ≈ b ⟨mod n ⟩ → b ≈ c ⟨mod n ⟩ → a ≈ c ⟨mod n ⟩
  mod-trans {a} {b} {c} (≈-mod x y pxy)  (≈-mod z w pzw) =
    ≈-mod (x + z) (w + y) ( begin
```

And all that's left is to carry out the proof we performed above. This is not
hard, but requires a good amount of symbolic manipulation:

```agda
      a + (x + z) * n      ≡⟨ lemma₁ ⟩
      (a + x * n) + z * n  ≡⟨ cong (_+ z * n) pxy ⟩
      (b + y * n) + z * n  ≡⟨ lemma₂ ⟩
      (b + z * n) + y * n  ≡⟨ cong (_+ y * n) pzw ⟩
      c + w * n + y * n    ≡⟨ lemma₃ ⟩
      c + (w + y) * n      ∎
    )
```

The lemmas here are an annoying amount of work simply to move the equation into
the right shape such that we can apply `pxy` and `pzw`. Rather than write them
by hand, we can turn to our trusty friend, the ring solver:

```agda
    where
      open ≡-Reasoning
      open import Data.Nat.Solver
      open +-*-Solver

      lemma₁ = solve 4
        (λ a n x z → a :+ (x :+ z) :* n
                  := (a :+ x :* n) :+ z :* n)
        refl a n x z

      lemma₂ = solve 4
        (λ b n y z → (b :+ y :* n) :+ z :* n
                  := (b :+ z :* n) :+ y :* n)
        refl b n y z

      lemma₃ = solve 4
        (λ c n w y → c :+ w :* n :+ y :* n
                  := c :+ (w :+ y) :* n)
        refl c n w y
```

We are now satisfied that `_≈_⟨mod_⟩` is indeed an equivalence relationship.
All that's left is to bundle everything together into an `IsEquivalence`:

```agda
  mod-equiv : IsEquivalence (_≈_⟨mod n ⟩)
  IsEquivalence.refl mod-equiv = mod-refl
  IsEquivalence.sym mod-equiv = mod-sym
  IsEquivalence.trans mod-equiv = mod-trans
```

As you've seen, it's quite a lot of work to prove anything about `_≈_⟨mod_⟩`;
whenever we'd like to do anything, we need to construct two numbers `x` and `y`,
and then prove the underlying equality holds. While this is OK for trivial
propositions, things like `mod-trans` are nearly overwhelming. You can imagine
how much effort it would be to prove anything of actual *substance* in this
domain. Mathematicians hate number crunching as much, if not more, than anyone
else, so surely they are not doing all this work by hand, are they? How can we
simplify our workload?

The answer, is setoids.


## Setoids

While it may seem like we've taken a long detour from our original goal of
talking about equality, we are now ready to tackle *setoids* in their full
glory. A setoid is a bundled binary relation alongside a proof that it's an
equivalence relationship. By putting all of these things together, we're
rewarded by the Agda standard library with setoid reasoning: syntax for doing
"equational" reasoning over our objects. This reasoning lets us operate at a
much higher level than we could when we were constructing pairs of numbers and
proofs between them.

```agda
  private
    open import Relation.Binary
    mod-setoid : Setoid _ _
    Setoid.Carrier mod-setoid = ℕ
    Setoid._≈_ mod-setoid = _≈_⟨mod n ⟩
    IsEquivalence.refl (Setoid.isEquivalence mod-setoid) = mod-refl
    IsEquivalence.sym (Setoid.isEquivalence mod-setoid) = mod-sym
    IsEquivalence.trans (Setoid.isEquivalence mod-setoid) = mod-trans

  module mod-reasoning where
    open import Relation.Binary.Reasoning.Setoid mod-setoid public
```

Our `Setoid` record merely needs to bundle the underlying set with its
equivalence relation (and a proof that that relation is in fact an equivalence
relation!)

```agda
record Setoid : Set₁ where
  infix 4 _≈_
  field
    Carrier : Set
    _≈_ : Carrier → Carrier → Set
    isEquivalence : IsEquivalence _≈_
open Setoid
```

Given this, it's trivial to show now that `_≈_⟨mod_⟩` forms a setoid:

```agda
mod-setoid : ℕ → Setoid
Carrier       (mod-setoid n) = ℕ
_≈_           (mod-setoid n) = _≈_⟨mod n ⟩
  where open mod-def
isEquivalence (mod-setoid n) = mod-equiv
  where open mod-base n
```

We're almost ready to build some interesting proofs; but we're going to need to
define a few more trivial ones first. But let's start proving some properties
about `_≈_⟨mod_⟩` in a new module:

```agda
module mod-properties (n : ℕ) where
```

We'll still need propositional equality for a few things, but the setoid
infrastructure is meant to be a mostly drop-in replacement for propositional
equality, and so we will import it qualified:

```agda
  import Relation.Binary.PropositionalEquality as PropEq
```

We also need our base types and equivalence in scope:

```agda
  open mod-base n
  open IsEquivalence mod-equiv public
```

Let's prove two more fact "by hand", the fact that $0 = n (\text{mod} n)$:

```agda
  0≈n : 0 ≈ n ⟨mod n ⟩
  0≈n = ≈-mod 1 0 PropEq.refl
```

and the fact that we can `cong suc` onto proofs about `_≈_⟨mod_⟩`. While this
sounds obvious, it doesn't hold for most functions! Most functions do not
preserve setoid equality, so it's very exciting to find ones that do. To
illustrate this point, consider the function `4 *_`, which doesn't preserve
equality whenever, for example, $n = 5$.

```agda
  mod-suc-cong : {a b : ℕ} → a ≈ b ⟨mod n ⟩ → suc a ≈ suc b ⟨mod n ⟩
  mod-suc-cong (≈-mod x y p) = ≈-mod x y (PropEq.cong suc p)
```

Now that our setoid infrastructure is bought and paid for, and also that we have
a few primitive lemmas to work with, we're ready to begin proving things about
modular arithmetic in earnest. We can open the `mod-reasoning` module to enable
setoid reasoning throughout the rest of the current module.

```agda
  open mod-reasoning
```

Let's begin by proving the following theorem:

```agda
  +-zero-mod : (a b : ℕ) → a ≈ 0 ⟨mod n ⟩ → a + b ≈ b ⟨mod n ⟩
```

We can proceed in two cases, by splitting on `b`. In the zero case, we need to
show `a + zero ≈ zero ⟨mod n⟩`. Like when we did reasoning over propositional
equality, we `begin`:

```agda
  +-zero-mod a zero a≈0 =
    begin
      a + zero
```

and we still have access to propositional equality rewriting:

```agda
    ≡⟨ +-identityʳ a ⟩
      a
```

However, now that we have setoid reasoning enable, we can also do *setoid
rewriting* via the `≈⟨_⟩` operator. We have an `a` and want `zero`, and
conveniently, already have a proof that `a ≈ 0 ⟨mod n⟩`, so we can just apply it:

```agda
    ≈⟨ a≈0 ⟩
      zero
    ∎
```

You can see already how much nicer this style of reasoning is, compared with our
old method of building the `_≈_⟨mod_⟩` term directly.

We also need to show the `suc b` case, presented without further commentary.

```agda
  +-zero-mod a (suc b) a≈0 = begin
    a + suc b    ≡⟨ +-suc a b ⟩
    suc a + b    ≡⟨⟩
    suc (a + b)  ≈⟨ mod-suc-cong (+-zero-mod a b a≈0) ⟩
    suc b        ∎

```

Let's hoist another theorem about natural numbers that will come in handy: the
fact that `suc` is injective.

```agda
  mod-suc-injective
    : {a b : ℕ} → suc a ≈ suc b ⟨mod n ⟩ → a ≈ b ⟨mod n ⟩
  mod-suc-injective (≈-mod x y p) =
    ≈-mod x y (suc-injective p)
```

We're now ready to show a major result, the fact that `_≈_⟨mod_⟩` preserves
addition. Congruence proofs like this are the real workhorses of getting real
mathematics done, so it's exciting that we're able to build it.

```agda
  +-cong₂-mod
      : {a b c d : ℕ}
      → a ≈ b ⟨mod n ⟩
      → c ≈ d ⟨mod n ⟩
      → a + c ≈ b + d ⟨mod n ⟩
```

We can begin by case splitting on `a`. The zero case is straightforward, making
use of our previous lemma `+-zero-mod`:

```agda
  +-cong₂-mod {zero} {b} {c} {d} pab pcd = begin
    c         ≈⟨ pcd ⟩
    d         ≈⟨ sym (+-zero-mod b d (sym pab)) ⟩
    b + d     ∎
```

In the `suc a` case, we can now case split on `b`. The zero case is equally
straightforward:

```agda
  +-cong₂-mod {suc a} {zero} {c} {d} pab pcd = begin
    suc a + c  ≈⟨ +-zero-mod (suc a) c pab ⟩
    c          ≈⟨ pcd ⟩
    d          ∎
```

And all that's left is the non-zero cases, in which we can hand the problem over
to induction, using `mod-suc-cong` and `mod-suc-injective` to manipulate our
proofs back into the right shape.

```agda
  +-cong₂-mod {suc a} {suc b} {c} {d} pab pcd =
      mod-suc-cong (+-cong₂-mod (mod-suc-injective pab) pcd)
```

`+-cong₂-mod` is quite a marvel of a theorem, especially when you consider
needing to build this proof term by hand. Let's take a moment to appreciate what
we've accomplished here, by reasoning our way through how we would have solved
the problem naively.

Our parameters to `+-cong₂-mod` work out to two equations:

$$
a + xn = b + yn \\
c + zn = d + wn
$$

and we are tasked with finding $p$ and $q$ such that the following holds:

$$
(a + c) + pn = (b + d) + qn
$$

The solution is to add the two original equations together, point-wise:

$$
a + xn + c + zn = b + yn + d + wn
$$

and then group like terms:

$$
(a + c) + xn + zn = (b + d) + yn + wn
$$

of which we can then factor out an $n$ term:

$$
(a + c) + (x + z)n = (b + d) + (y + w)n
$$

giving us the solutions $p = x + z$ and $q = y + w$. So far so good, but now we
are tasked with building this equality term given the original equations. It's
not hard, but it's a consider amount of work. But the worst part is that this
reasoning is at a lower level than we'd like to be operating; we want to be
thinking about modular arithmetic, not juggling equations!

We'll prove two more facts about modular arithmetic, one in service of the
other. We can show that modular multiplication by zero results in zero:

```agda
  *-zero-mod : (a b : ℕ) → b ≈ 0 ⟨mod n ⟩ → a * b ≈ 0 ⟨mod n ⟩
  *-zero-mod zero b x = refl
  *-zero-mod (suc a) b x = begin
    suc a * b  ≡⟨⟩
    b + a * b  ≈⟨ +-cong₂-mod x (*-zero-mod a b x) ⟩
    0          ∎
```

And at long last, we can show that modular arithmetic is also congruent over
multiplication, via `*-cong₂-mod`:

```agda
  *-cong₂-mod
      : {a b c d : ℕ}
      → a ≈ b ⟨mod n ⟩
      → c ≈ d ⟨mod n ⟩
      → a * c ≈ b * d ⟨mod n ⟩
  *-cong₂-mod {zero} {b} {c} {d} a=b c=d = begin
    zero * c  ≡⟨⟩
    zero      ≈⟨ sym (*-zero-mod d b (sym a=b)) ⟩
    d * b     ≡⟨ *-comm d b ⟩
    b * d     ∎
  *-cong₂-mod {suc a} {zero} {c} {d} a=b c=d = begin
    suc a * c  ≡⟨ *-comm (suc a) c ⟩
    c * suc a  ≈⟨ *-zero-mod c (suc a) a=b ⟩
    zero       ≡⟨⟩
    zero * d   ∎
  *-cong₂-mod {suc a} {suc b} {c} {d} a=b c=d = begin
    suc a * c  ≡⟨⟩
    c + a * c
      ≈⟨ +-cong₂-mod c=d (*-cong₂-mod (mod-suc-injective a=b) c=d) ⟩
    d + b * d  ≡⟨⟩
    suc b * d  ∎
```

While the proof of `*-cong₂-mod` is still quite involved, again, it's worth
considering the problem in its more "raw" form. Given:

$$
a + xn = b + yn \\
c + zn = d + wn
$$

we are looking for $p$ and $q$ such that the following holds:

$$
ac + pn = bd + qn
$$

The solution again is analogous to solving for `+-cong₂-mod`, except in this
case we must multiply the two sides of our equations, resulting in the hairy
solutions:

$$
p = cx + az + xzn \\
q = dy + bw + ywn
$$

Convincing Agda of the equality of these terms is on the order of 50 algebraic
manipulations; most of it being gentle massaging of the expression into
something you can `cong` one proof over, and then massaging it into a form on
which you can `cong` the other.

All in all, setoids have bought us a great deal of algebraic power. We've used
them to manage working over an equivalence relation, showing how we can quotient
over values that are not *literally* equal to one another, but still operate in
a context that allows us to work as if they were. The only real loss here is
that `cong` no longer holds for all functions, and that we must prove it holds
whenever we'd like to use that fact. This is a limitation more of Agda's type
theory than it is of mathematics; in the latter, it's perfectly acceptable to
define a quotient relationship that holds by fiat. It is only in our
computational context that we are required to *show* that functions cannot
observe the difference between quotiented values.

On the other hand, the rigor afforded to us by doing mathematics in a rich type
theory is what has driven so much of the recent study of equality. When you're
doing mathematics by pen and paper, it's easy to be sloppy about what equality
actually *means.* The setoid approach can be paraphrased as "whenever you define
a set, you must also define what equality means over it."


## Constructions on Setoids

By virtue of being first-class objects, setoids are *values* that we can pass
as parameters, and return from functions. That means there's an entire set of
combinators we can use for building setoids out of other things. For example,
given a type, we can trivially construct a setoid using propositional equality:

```agda
module _ where
  import Relation.Binary.PropositionalEquality as PropEq

  setoid : Set → Setoid
  Carrier (setoid A) = A
  _≈_ (setoid A) = PropEq._≡_
  IsEquivalence.refl (isEquivalence (setoid A)) = PropEq.refl
  IsEquivalence.sym (isEquivalence (setoid A)) = PropEq.sym
  IsEquivalence.trans (isEquivalence (setoid A)) = PropEq.trans
```

We can also lift setoids over functions to get a setoid-extensional version of
function equality. By ensuring two functions are equal for every possible input,
we can show two functions are equal:

```agda
  hom-setoid : Set → Setoid → Setoid
  Carrier (hom-setoid A s) = A → Carrier s
  _≈_ (hom-setoid A s) f g = (a : A) → (_≈_ s) (f a) (g a)  -- ! 1
  isEquivalence (hom-setoid A s) = equiv
    where
    open IsEquivalence (s .isEquivalence)

    equiv : IsEquivalence _
    IsEquivalence.refl equiv a = refl
    IsEquivalence.sym equiv f a = sym (f a)
    IsEquivalence.trans equiv f g a = trans (f a) (g a)
```

Notice at [1](Ann) we are unable to write the more natural `f a ≈ g a`, because
as we've set up the problem, `_≈_` is a field of the `s` record, and is thus a
*ternary* function with binary operator syntax. We solve this problem by
writing the function in head-normal form. Left to its own devices, Agda will
attempt to rewrite this in cursed form as `(s ≈ f a) (g a)`, which we go through
great lengths to avoid.


