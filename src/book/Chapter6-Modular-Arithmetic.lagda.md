# Modular Arithmetic

```agda
module Chapter6-Modular-Arithmetic where
```

In the last several chapters, we have constructed the natural numbers, proven
many facts about them, learned about proof in the meanwhile, and most recently
have tried our hands at building equivalence relations.

Presented in the abstract, it can be easy to miss the forest for the trees, and
think that all this *stuff* is good only for padding a resume. Not so! In my
first year being an undergraduate, I was forced to battle with modular
arithmetic, and it was one of the worst grades in my academic career. A decade
later, I'm ready to fight back, and thought it would be fun to put together this
chapter to prove to myself that Agda really can help me learn difficult topics.

For anyone who doesn't have a personal vendetta against modular arithmetic, this
chapter will serve as a quick interlude in which we turn down the learning dial,
and apply everything we know to a "real problem."


Prerequisites

:   ```agda
open import Chapter1-Agda
    ```

:   ```agda
open import Chapter2-Numbers
    ```

:   ```agda
open import Chapter3-Proofs
  using (_≡_; cong; module ≡-Reasoning; suc-injective)
    ```

:   ```agda
open import Chapter4-Relations
    ```


There is one feature of Agda I'd like to cover before we get started in earnest
on modular arithmetic. That feature is Agda's programmable, automatic proof
search.


## Instance Arguments

In @sec:preorders, we had to do some gymnastics with modules in order to
differentiate between the `ctor:refl` constructor of `type:_≡_`, and the
`field:refl` field of `type:IsPreorder`. As we begin to juggle more and more
notions of equality, it will quickly become burdensome to need to unambiguously
refer to each.

You'll note that this shouldn't be a real problem; `ctor:refl` and `field:refl`
have completely different types, and it seems like if Agda were smarter, it
should be able to differentiate from context alone. As it happens, this is
exactly what Agda can do for us, but we must opt-in and explicitly ask it to do
so.

The mechanism we need here is Agda's support for *instance arguments,* which are
much like implicit arguments (#sec:implicits), except that we can control how
Agda searches for them. There are two sides to instance arguments---the
arguments themselves, and the tools for controlling the search.

```agda
module Playground-Instances where
  open Chapter3-Proofs
    using (refl)
```

As the name suggests, instance arguments are special arguments to functions that
Agda will fill in on behalf of the caller. They are defined and matched on with
special syntax, using either the Unicode double braces `⦃` and `⦄`
(input via [`{{`](AgdaMode) and [`}}`](AgdaMode)), or by just typing double
braces, as in `{{` and `}}`.

For an example, we can use instance arguments to implement a function
`def:default` which gives back a default value for any type you ask for:

```agda
  default : {ℓ : Level} {A : Set ℓ} → ⦃ a : A ⦄ → A
  default ⦃ val ⦄ = val
```

That's all fine and good, but we haven't yet said what default values there are.
How should Agda know what to give back when `A =` `type:ℕ`, or when `A =`
`type:Bool`? Easy: we tell it by way of an `keyword:instance` block:

```agda
  private instance
    default-ℕ : ℕ
    default-ℕ = 0

    default-Bool : Bool
    default-Bool = false
```

Rather amazingly, that's all we need. Now whenever Agda sees `def:default` and
determines its type should be `type:ℕ`, Agda will look at all of the
`keyword:instance`s it knows about, and if there is a unique definition whose
type is `type:ℕ`, it will return that:

```agda
  _ : default ≡ 0
  _ = refl
```

Likewise for `type:Bool`:

```agda
  _ : default ≡ false
  _ = refl
```

Agda truly is looking into all of the `keyword:instance` blocks to look these
up. We can convince ourselves by checking `def:default` against another value:

```illegal
  _ : default ≡ 1
  _ = refl
```

which produces an error, as we'd expect:

```info
0 != 1 of type ℕ
when checking that the expression refl has type
default ≡ 1
```

If that were all we could do with instance arguments, it would be pretty
underwhelming. More interestingly, instances can use implicit arguments, as
well as *instance* arguments themselves. We can exploit these two features to
give two `keyword:instance`s for `type:_≤_` corresponding to its two
constructors `ctor:z≤n` and `ctor:s≤s`:

```agda
  private instance
    find-z≤n : {n : ℕ} → 0 ≤ n
    find-z≤n = z≤n

    find-s≤n
        : {m n : ℕ}
        → ⦃ m ≤ n ⦄  -- ! 1
        → suc m ≤ suc n
    find-s≤n ⦃ m≤n ⦄ = s≤s m≤n
```


Hidden

:   ```agda
  -- fix bind
    ```

The `def:find-z≤n` isn't particularly interesting, but `def:find-s≤s` has a lot
going on. At [1](Ann) we ask Agda to automatically find us a proof of `bind:m
n:m ≤ n` by instance search, and then we turn around and give it back as our
instance. The result is a marvelous thing: Agda can now automatically derive a
proof of `bind:m n:m ≤ n` whenever `m` and `n` are concrete numbers:


Hidden

:   ```agda
  module _ where
    -- fix indent
    ```


```agda
  _ : 10 ≤ 20
  _ = default
```

Notice how we used `def:default` again here, as all `def:default` does is
return whatever it can find via instance search. As you can see, instance lookup
is *global* in the sense that we can't "namespace" between the values we'd like
to default (like 0 and `ctor:false`), from the values we'd like to derive (like
`expr:10 ≤ 20`.)

This is indicative of sloppiness on our part. It's a good idea to be rather
principled with what you put into an `keyword:instance`. Instances are scoped to
the current module, so we can try again by dropping out of
`module:Playground-Instances` and starting a new module:

```agda
module Playground-Instances₂ where
```

Rather than just dumping everything directly into an `keyword:instance` block,
it's better to define a new record:

```agda
  record HasDefault {ℓ : Level} (A : Set ℓ) : Set ℓ where
    constructor default-of
    field
      the-default : A
```

and then use instance search to look directly for this record:

```agda
  default : {ℓ : Level} {A : Set ℓ} → ⦃ HasDefault A ⦄ → A
  default ⦃ default-of val ⦄ = val
```

We are not required to give names or types for anything in an `keyword:instance`
block, so the follow is fine:

```agda
  private instance
    _ = default-of 0
    _ = default-of false
```


Hidden

:   ```agda
  -- fix bind
    ```


Because `def:default` only looks for records of type `type:HasDefault`, we are
now free to stick other values into the instance environment, which won't get
accidentally picked up as being default values:

```agda
  data Color : Set where
    red green blue : Color

  private instance
    _ = green
```

Attempting to use `def:default` on `type:Color` now will produce a helpful error:

```illegal
  _ : Color
  _ = default
```

```info
No instance of type HasDefault Color was found in scope.
when checking that the expression default has type Color
```

Using parameterized data types like this is an excellent way to enforce
namespacing inside the otherwise global instance environment. To demonstrate one
final feature, we don't need to write `def:default` by hand---Agda supports
an automatic conversion from record fields to instance search. The trick is to
open the module using the instance brace syntax above:

```agda
  open HasDefault ⦃ ... ⦄
```

which will bring into scope the following definition:

```agda
  the-default⅋ : {ℓ : Level} {A : Set ℓ} → ⦃ HasDefault A ⦄ → A
  the-default⅋ ⦃ x ⦄ = x .HasDefault.the-default
```

This is exactly the trick we will end up using to solve our problem of having
too many `refl`s to count:

```agda
open IsPreorder     ⦃ ... ⦄
open IsEquivalence  ⦃ ... ⦄
```

which brings into scope `field:refl` and `field:trans` from `module:IsPreorder`,
as well as `field:isPreorder` and `field:sym` from `module:IsEquivalence`. The
final rabbit in our hat is to give an `keyword:instance` search strategy which
turns an instance of `type:IsEquivalence` into an instance of `type:IsPreorder`
by way of `field:isPreorder`:

```agda
private instance
  equiv-to-preorder
      : {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} {_~_ : Rel A ℓ₂}
      → ⦃ IsEquivalence _~_ ⦄
      → IsPreorder _~_
  equiv-to-preorder = isPreorder
```

Additionally, let's add `def:≡-equiv` as an instance, so our overloaded terms
will find propositional equality immediately:

```agda
  _ = ≡-equiv
```

We'll add more instances as we discover more equivalence relations throughout
this chapter.


## The Ring of Natural Numbers Modulo N

Having concluded that pedagogical soliloquy, let's return to the problem at hand.

What exactly is modular arithmetic, you might wonder. It's the idea of doing
math with number overflows, much like on an analog clock. Modular arithmetic is
the reason that 1pm comes three hours after 10am, and the reason that turning
360 degrees gets you back to where you started.

The math people call this doing work over the "ring of natural numbers modulo
$n$", where $n$ is the point at which we overflow back to zero. On a clock we
have $n = 12$. And when talking about rotation in degrees, $n = 360$.

Of course, it's a blatant misuse of the equals symbol to say $10 + 3 = 1$, so
instead we write $10 + 3 = 1 \pmod{12}$. As a point of subtlety, such a thing
must be parsed as a three-way relationship; that is, the $=$ and $\pmod{n}$
should be considered part of the same symbol.

Speaking of bad notation, the mathematicians write this so-called ring of
natural numbers modulo $n$ as `ℕ/nℕ`. No wonder I had such a hard time with this
back in my undergraduate.


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


Notice that we use propositional equality at [1](Ann) to assert that we're
witnessing the fact that these two expressions *really are the same!*

We can now show that our clock example works as expected:

```agda
  -- _ : 11 + 2 ≈ 1 ⟨mod 12 ⟩
  -- _ = ≈-mod 0 1 PropEq.refl
```

Of course, it's quite a mouthful to stick in the `⟨mod_⟩` part every time, so we
can make a new module and subsequent relation in which we hold the modulus
constant:

```agda
module ℕ/nℕ (n : ℕ) where
  record _≈_ (a b : ℕ) : Set where
    constructor ≈-mod
    field
      x y : ℕ
      is-mod : a + x * n ≡ b + y * n  -- ! 1

  infix 4 _≈_
```

As it happens, `type:_≈_` forms an equivalence relation. Showing reflexivity and
symmetry is simple enough:

```agda
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

And now for the hard part---we must give a *proof* that these are in fact the
right numbers. Most of the work involved is algebraic manipulation, shuffling
the terms around such that we can apply `pxy` and then `pzw`. Inlining the
algebraic manipulation is a huge amount of effort, so instead we will use two
as-of-yet-undefined lemmas that do the heavy lifting.

Here, `def:lemma₁` distributes `* n` over the addition, and reassociate everything
so it's in the right shape for `pxy`. Meanwhile, `def:lemma₂` applies the
commutativity of addition across a pair of parentheses.

```agda
  ≈-trans : Transitive _≈_
  ≈-trans {a} {b} {c} (≈-mod x y pxy) (≈-mod z w pzw) =
    ≈-mod (x + z) (w + y)
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
      open import Data.Nat.Solver
      open +-*-Solver

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
  ≈-preorder : IsPreorder _≈_
  IsPreorder.refl   ≈-preorder = ≈-refl
  IsPreorder.trans  ≈-preorder = ≈-trans

  ≈-equiv : IsEquivalence _≈_
  IsEquivalence.isPreorder  ≈-equiv = ≈-preorder
  IsEquivalence.sym         ≈-equiv = ≈-sym

```

Additionally, we can use this fact to get equational reasoning syntax for free,
via our `module:PreorderReasoning` module from @sec:preorderreasoning.

```agda
  module Mod-Reasoning = Preorder-Reasoning ≈-preorder
```

We're almost ready to build some interesting proofs; but we're going to need to
define a few more trivial ones first. But let's start proving some properties
about `type:_≈_` in a new module:

```agda

module mod-properties (n : ℕ) where
  open ℕ/nℕ n

  private instance
    _ = ≈-equiv
```

We'll still need propositional equality for a few things, but the preorder
reasoning infrastructure is meant to be a mostly drop-in replacement for
propositional equality.

-- TODO(sandy): sloppy; needs some reordering

Let's prove two more fact "by hand", the fact that $0 = n\text{ (mod
}n\text{)}$:

```agda
  open Chapter3-Proofs
    hiding (refl; sym)

  0≈n : 0 ≈ n
  0≈n = ≈-mod 1 0 refl
```

and the fact that we can `cong suc` onto proofs about `type:_≈_`. While this
sounds obvious, it doesn't hold for most functions! Most functions do not
preserve setoid equality, so it's very exciting to find ones that do. To
illustrate this point, consider the function `4 *_`, which doesn't preserve
equality whenever, for example, $n = 5$.

```agda
  mod-suc-cong : {a b : ℕ} → a ≈ b → suc a ≈ suc b
  mod-suc-cong (≈-mod x y p) = ≈-mod x y (cong suc p)
```

Now that our setoid infrastructure is bought and paid for, and also that we have
a few primitive lemmas to work with, we're ready to begin proving things about
modular arithmetic in earnest. We can open the `mod-reasoning` module to enable
setoid reasoning throughout the rest of the current module.

Let's begin by proving the following theorem:

```agda
  +-zero-mod : (a b : ℕ) → a ≈ 0 → a + b ≈ b
```

We can proceed in two cases, by splitting on `b`. In the zero case, we need to
show `a + zero ≈ zero ⟨mod n⟩`. Like when we did reasoning over propositional
equality, we `begin`:

```agda
  +-zero-mod a zero a≈0 = begin
    a + zero  ≡⟨ +-identityʳ a ⟩
    a         ≈⟨ a≈0 ⟩
    zero      ∎
    where open Mod-Reasoning
```

We also need to show the `ctor:suc` case, presented without further commentary.

```agda
  +-zero-mod a (suc b) a≈0 = begin
    a + suc b    ≡⟨ +-suc a b ⟩
    suc a + b    ≡⟨⟩
    suc (a + b)  ≈⟨ mod-suc-cong (+-zero-mod a b a≈0) ⟩
    suc b        ∎
    where open Mod-Reasoning
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
    where open Mod-Reasoning
```

In the `ctor:suc` case, we can now case split on `b`. The zero case is equally
straightforward:

```agda
  +-cong₂-mod {suc a} {zero} {c} {d} pab pcd = begin
    suc a + c  ≈⟨ +-zero-mod (suc a) c pab ⟩
    c          ≈⟨ pcd ⟩
    d          ∎
    where open Mod-Reasoning
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
    where open Mod-Reasoning
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
    where open Mod-Reasoning
  *-cong₂-mod {suc a} {zero} {c} {d} a=b c=d = begin
    suc a * c  ≡⟨ *-comm (suc a) c ⟩
    c * suc a  ≈⟨ *-zero-mod c (suc a) a=b ⟩
    zero       ≡⟨⟩
    zero * d   ∎
    where open Mod-Reasoning
  *-cong₂-mod {suc a} {suc b} {c} {d} a=b c=d = begin
    suc a * c  ≡⟨⟩
    c + a * c  ≈⟨ +-cong₂-mod c=d
                    (*-cong₂-mod (mod-suc-injective a=b) c=d)⟩
    d + b * d  ≡⟨⟩
    suc b * d  ∎
    where open Mod-Reasoning
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
\begin{aligned}
p &= cx + az + xzn \\
q &= dy + bw + ywn
\end{aligned}
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

