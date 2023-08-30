# Modular Arithmetic

```agda
module Chapter6-Modular-Arithmetic where
```

All of the equivalences we have looked at thus far have been combinators on
existing equivalences. And of course, we have also seen propositional equality,
but it's reasonable to wonder whether any of this actually "cashes out" in the
real world. In this section, we will look into a familiar way of quotienting the
natural numbers, and see just how much leg work this common vocabulary can do
for us.

A favorite example of quotienting for mathematicians are the so-called "ring of
natural numbers modulo $n$," more tersely written as $\mathbb{N}/n\mathbb{N}$.
But what is this ring? This ring is the mathematical way of saying "clock
addition"---that is, we pick some $n$, maybe $n = 12$ for an example, and say
that whenever our arithmetic gets to $n$ it overflows back to 0. This is the
peculiar fact that, on an analog clock, we have the fact that $11 + 2 = 1$. Of
course, this is a blatant misuse of the equals symbol, so instead we write
$11 + 2 = 1 \text{(mod 12)}$.

How can we formalize this idea of modular arithmetic? Well, if we'd like to show
$a = b \text{(mod }n\text{)}$, we would like to find two multiples of $n$ that we can
use to equate the two. That is to say, we need to find $x, y : ℕ$ such that $a +
xn = b + yn$.


```agda
open import Data.Nat using (ℕ; _+_; _*_)

module ModularArithmetic where
  open import Relation.Binary.PropositionalEquality
    using (_≡_; refl)

  infix 4 _≈_⟨mod_⟩
  data _≈_⟨mod_⟩ (a b n : ℕ) : Set where
    ≈-mod
      : (x y : ℕ)
      → a + x * n ≡ b + y * n  -- ! 1
      → a ≈ b ⟨mod n ⟩
```

Notice that we use propositional equality at [1](Ann) to assert that we're
witnessing the fact that these two expressions *really are the same!*

We can now show that our clock example works as expected:

```agda
  _ : 11 + 2 ≈ 1 ⟨mod 12 ⟩
  _ = ≈-mod 0 1 refl
```

Of course, it's quite a mouthful to stick in the `⟨mod_⟩` part every time, so we
can make a new module and subsequent relation in which we hold the modulus
constant:

```agda
module ℕ/nℕ (n : ℕ) where
  open ModularArithmetic public
  open import Relation.Binary
    using (Rel)

  infix 4 _≈_
  _≈_ : Rel ℕ _
  _≈_ = _≈_⟨mod n ⟩
```

As it happens, `type:_≈_` forms an equivalence relation. Showing reflexivity and
symmetry is simple enough:

```agda
  open Relation.Binary
    using (Reflexive; Symmetric; Transitive; IsEquivalence)

  module _ where
    open import Relation.Binary.PropositionalEquality

    ≈-refl : Reflexive _≈_
    ≈-refl = ≈-mod 0 0 refl

    ≈-sym : Symmetric _≈_
    ≈-sym (≈-mod x y p) = ≈-mod y x (sym p)
```

However, the transitivity of `type:_≈_` is a significantly harder thing to
demonstrate. Before diving into the implementation, let's work out the solution
"on paper" first, where we can more more quickly and require less formality in
justifying our steps. To set up the problem, given `a ≈ b` and `b ≈ c`, and
would like to show `a ≈ c`. This looks simple enough, but the short types
involved here pack quite a punch. Recall that what `a ≈ b` really means is that
we have two numbers `x y : ℕ`, such that

$$
a + xn = b + yn
$$

Similarly for `b ≈ c` we have two more numbers `z w : ℕ` such that

$$
b + zn = c + wn
$$

In order to show `type:Transitive _≈_`, we therefore must find two more numbers
`i j : ℕ` such that the following equation holds:

$$
a + in = c + jn
$$

Solving this requires some simultaneous manipulation of the first two equations:

$$
\begin{aligned}
a + xn &= b + yn \\
b + zn &= c + wn
\end{aligned}
$$

We'd like to eliminate the $b$ term, so we can solve both equations for $b$:

$$
\begin{aligned}
a + xn - yn &= b + yn \\
b &= c + wn - zn
\end{aligned}
$$

which then allows us to combine the two equations:

$$
a + xn - yn = b = c + wn - zn
$$

and therefore we have:

$$
a + xn - yn = c + wn - zn
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

This gives us our desired numbers `i j : ℕ` for transivity, namely $i = x + z$
and $j = w + y$.

```agda
    ≈-trans : Transitive _≈_
    ≈-trans {a} {b} {c} (≈-mod x y pxy) (≈-mod z w pzw) =
      ≈-mod (x + z) (w + y)
```

And now for the hard part---we must give a *proof* that these are in fact the
right numbers. Most of the work involved is algebraic manipulation, shuffling
the terms around such that we can apply `pxy` and then `pzw`. Inlining the
algebraic manipulation is a huge amount of effort, so instead we will use two
as-of-yet-undefined lemmas that do the heavy lifting.

```agda
      ( begin
        a + (x + z) * n      ≡⟨ lemma₁ a n x z ⟩
        (a + x * n) + z * n  ≡⟨ cong (_+ z * n) pxy ⟩
        (b + y * n) + z * n  ≡⟨ lemma₂ b (y * n) (z * n) ⟩
        (b + z * n) + y * n  ≡⟨ cong (_+ y * n) pzw ⟩
        c + w * n + y * n    ≡⟨ sym (lemma₁ c n w y) ⟩
        c + (w + y) * n      ∎
      )
      where
        open ≡-Reasoning
```

Here, `def:lemma₁` distributes `* n` over the addition, and reassociate everything
so it's in the right shape for `pxy`. Meanwhile, `def:lemma₂` applies the
commutativity of addition across a pair of parentheses.

Rather than go through the effort of proving these lemmas for ourselves, we can
turn to the ring solver, and ask it to do the heavy lifting on our behalf.
First, we must bring the ring solver into scope:

```agda
        open import Data.Nat.Solver
        open +-*-Solver
```

and then we can get our two lemmas by invoking `def:solve` with the number of
variables in the expression, and a syntactic representation of the problem we'd
like solved:

```agda
        lemma₁ = solve 4
          (λ a n x z → a :+ (x :+ z) :* n := (a :+ x :* n) :+ z :* n)
          refl

        lemma₂ = solve 3
          (λ b i j → (b :+ i) :+ j := (b :+ j) :+ i)
          refl
```

The ring solver is a fantastic tool for automating away tedious, symbolic proofs
of this form. Of course, we could have proven these lemmas by hand, but they are
uninteresting and error-prone. And, after all, why do something by hand when
it's automateable? What's amazing is that the ring solver is just standard Agda
library code; it's nothing you couldn't have written for yourself. And indeed,
we will drill into exactly this problem in @sec:ringsolving.

Anyway, now that we have reflexivity, symmetry, and transitivity, we now know
that `type:_≈_` is an equivalence relation.

```agda
  ≈-equiv : IsEquivalence _≈_
  IsEquivalence.refl   ≈-equiv = ≈-refl
  IsEquivalence.sym    ≈-equiv = ≈-sym
  IsEquivalence.trans  ≈-equiv = ≈-trans
```

Additionally, we can use this fact to get equational reasoning syntax for free,
via our `module:PreorderReasoning` module from @sec:preorderreasoning.

```agda
  module ≈-Reasoning where
    open import Chapter4-Relations
    open Definition-LessThanOrEqualTo2

    ≈-preorder : IsPreorder _≈_
    IsPreorder.refl   ≈-preorder = ≈-refl
    IsPreorder.trans  ≈-preorder = ≈-trans

    open IsEquivalence ≈-equiv using (sym) public
    open PreorderReasoning ≈-preorder public
```

We're almost ready to build some interesting proofs; but we're going to need to
define a few more trivial ones first. But let's start proving some properties
about `type:_≈_` in a new module:

```agda
module mod-properties (n : ℕ) where
  open ℕ/nℕ n
```

We'll still need propositional equality for a few things, but the preorder
reasoning infrastructure is meant to be a mostly drop-in replacement for
propositional equality.

-- TODO(sandy): sloppy; needs some reordering

Let's prove two more fact "by hand", the fact that $0 = n\text{ (mod
}n\text{)}$:

```agda
  import Relation.Binary.PropositionalEquality as PropEq
  open import Data.Nat
  open import Data.Nat.Properties

  0≈n : 0 ≈ n
  0≈n = ≈-mod 1 0 PropEq.refl
```

and the fact that we can `cong suc` onto proofs about `type:_≈_`. While this
sounds obvious, it doesn't hold for most functions! Most functions do not
preserve setoid equality, so it's very exciting to find ones that do. To
illustrate this point, consider the function `4 *_`, which doesn't preserve
equality whenever, for example, $n = 5$.

```agda
  mod-suc-cong : {a b : ℕ} → a ≈ b → suc a ≈ suc b
  mod-suc-cong (≈-mod x y p) = ≈-mod x y (PropEq.cong suc p)
```

Now that our setoid infrastructure is bought and paid for, and also that we have
a few primitive lemmas to work with, we're ready to begin proving things about
modular arithmetic in earnest. We can open the `mod-reasoning` module to enable
setoid reasoning throughout the rest of the current module.

```agda
  open ≈-Reasoning
```

Let's begin by proving the following theorem:

```agda
  +-zero-mod : (a b : ℕ) → a ≈ 0 → a + b ≈ b
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
old method of building the `type:_≈_` term directly.

We also need to show the `ctor:suc` case, presented without further commentary.

```agda
  +-zero-mod a (suc b) a≈0 = begin
    a + suc b    ≡⟨ +-suc a b ⟩
    suc a + b    ≡⟨⟩
    suc (a + b)  ≈⟨ mod-suc-cong (+-zero-mod a b a≈0) ⟩
    suc b        ∎
```

Let's hoist another theorem about natural numbers that will come in handy: the
fact that `ctor:suc` is injective.

```agda
  mod-suc-injective
    : {a b : ℕ} → suc a ≈ suc b → a ≈ b
  mod-suc-injective (≈-mod x y p) =
    ≈-mod x y (suc-injective p)
```

We're now ready to show a major result, the fact that `type:_≈_` preserves
addition. Congruence proofs like this are the real workhorses of getting real
mathematics done, so it's exciting that we're able to build it.

```agda
  +-cong₂-mod
      : {a b c d : ℕ}
      → a ≈ b
      → c ≈ d
      → a + c ≈ b + d
```

We can begin by case splitting on `a`. The zero case is straightforward, making
use of our previous lemma `def:+-zero-mod`:

```agda
  +-cong₂-mod {zero} {b} {c} {d} pab pcd = begin
    c         ≈⟨ pcd ⟩
    d         ≈⟨ sym (+-zero-mod b d (sym pab)) ⟩
    b + d     ∎
```

In the `ctor:suc` case, we can now case split on `b`. The zero case is equally
straightforward:

```agda
  +-cong₂-mod {suc a} {zero} {c} {d} pab pcd = begin
    suc a + c  ≈⟨ +-zero-mod (suc a) c pab ⟩
    c          ≈⟨ pcd ⟩
    d          ∎
```

And all that's left is the non-zero cases, in which we can hand the problem over
to induction, using `def:mod-suc-cong` and `def:mod-suc-injective` to manipulate our
proofs back into the right shape.

```agda
  +-cong₂-mod {suc a} {suc b} {c} {d} pab pcd =
      mod-suc-cong (+-cong₂-mod (mod-suc-injective pab) pcd)
```

`def:+-cong₂-mod` is quite a marvel of a theorem, especially when you consider
needing to build this proof term by hand. Let's take a moment to appreciate what
we've accomplished here, by reasoning our way through how we would have solved
the problem naively.

Our parameters to `def:+-cong₂-mod` work out to two equations:

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
  *-zero-mod : (a b : ℕ) → b ≈ 0 → a * b ≈ 0
  *-zero-mod zero b x = refl
  *-zero-mod (suc a) b x = begin
    suc a * b  ≡⟨⟩
    b + a * b  ≈⟨ +-cong₂-mod x (*-zero-mod a b x) ⟩
    0          ∎
```

And at long last, we can show that modular arithmetic is also congruent over
multiplication, via `def:*-cong₂-mod`:

```agda
  *-cong₂-mod
      : {a b c d : ℕ}
      → a ≈ b
      → c ≈ d
      → a * c ≈ b * d
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
    c + a * c  ≈⟨ +-cong₂-mod c=d
                    (*-cong₂-mod (mod-suc-injective a=b) c=d)⟩
    d + b * d  ≡⟨⟩
    suc b * d  ∎
```

While the proof of `def:*-cong₂-mod` is still quite involved, again, it's worth
considering the problem in its more "raw" form. Given:

$$
a + xn = b + yn \\
c + zn = d + wn
$$

we are looking for $p$ and $q$ such that the following holds:

$$
ac + pn = bd + qn
$$

The solution again is analogous to solving for `def:+-cong₂-mod`, except in this
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

