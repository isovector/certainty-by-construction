# Modular Arithmetic

```agda
module Chapter5-Modular-Arithmetic where
```

In the last several chapters, we have constructed the natural numbers, proven
many facts about them, learned about proof in the meanwhile, and most recently
have tried our hands at building equivalence relations.

Presented in the abstract, it can be easy to miss the forest for the trees, and
think that all this *stuff* is good only for padding a resume. Not so! In my
first year being an undergraduate, p was forced to battle with modular
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
open PropEq using (cong)
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
  open PropEq
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
  _ = PropEq.refl
```

Likewise for `type:Bool`:

```agda
  _ : default ≡ false
  _ = PropEq.refl
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
too many `def:refl`s to count:

```agda
open IsEquivalence  ⦃ ... ⦄ public
```

which brings into scope `field:refl` and `field:trans` from `module:IsPreorder`,
as well as `field:isPreorder` and `field:sym` from `module:IsEquivalence`. The
final rabbit in our hat is to give an `keyword:instance` search strategy which
turns an instance of `type:IsEquivalence` into an instance of `type:IsPreorder`
by way of `field:isPreorder`:

```agda
instance
  equiv-to-preorder
      : {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} {_~_ : Rel A ℓ₂}
      → ⦃ IsEquivalence _~_ ⦄
      → IsPreorder _~_
  equiv-to-preorder = isPreorder
```

Additionally, let's add `def:≡-equiv` as an instance, so our overloaded terms
will find propositional equality immediately:

```agda
  ≡-is-equivalence = ≡-equiv
```


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
natural numbers modulo `n` as `ℕ/nℕ`. No wonder p had such a hard time with this
back in my undergraduate. We can parameterize the entire module over `n :`
`ℕ`---in essence, holding it constant for the remainder of our definition:

```agda
module ℕ/nℕ (n : ℕ) where
```

So what does it actually mean if $a = b \pmod{n}$? It means that these two
numbers have the same remainder when divided by `n`. But since we're dealing
with the natural numbers, we don't have any notion of division at hand. Instead,
we can phrase the problem as "if we subtract $a$ from $b$, the result should be
an integer multiple of `n`"  That is, there should exist some `k : ` `type:ℤ`
such that:

$$
a - b = kn
$$

But again, we are dealing with the natural numbers, so we also don't have any
notion of subtraction. From here we can just bonk the problem with our algebra
hammer. Split $k$ into $y - x$, and then:

$$
\begin{aligned}
a - b &= (y - x)n \\
&= yn - xn \\
\therefore \quad a + xn &= b + yn
\end{aligned}
$$

This final phrasing of the problem is now something we can represent in the
natural numbers, and gives rise to our definition of equality modulo `n`:

```agda
  record _≈_ (a b : ℕ) : Set where
    constructor ≈-mod
    field
      x y : ℕ
      is-mod : a + x * n ≡ b + y * n

  infix 4 _≈_
```

Note that `type:_≈_` is *parameterized* by `a` and `b`, but *contains* `field:x`
and `field:y`---this is what we mean above when we say "there exist `field:x`
and `field:y`, such that..."

Equivalence modulo `n` is really just a particular class of propositional
equalities, and so we should not be surprised that `type:_≈_` is reflexive---we
merely pick $x = y$, and the simplest solution here is $x = y = 0$:

```agda
  ≈-refl : Reflexive _≈_
  ≈-refl = ≈-mod 0 0 refl
```

Likewise, `type:_≡_` is symmetric, so we should be able to implement the same
over `type:_≈_`. Just swap the proof around, and rename which variable is
`field:x` and which is `field:y`:

```agda
  ≈-sym : Symmetric _≈_
  ≈-sym (≈-mod x y p) = ≈-mod y x (sym p)
```


## Deriving Transitivity

Showing the transitivity of `type:_≈_` is unfortunately much more involved than
these two cases. The issue stems from the fact that transitivity requires us to
glue together two values of `type:_≈_`, each of which, recall, is an equation in
four variables. Thus, transitivity gives us two equations:

$$
\begin{aligned}
a + xn &= b + yn \\
b + zn &= c + wn
\end{aligned}
$$

and requires us to find `p q :` `type:ℕ` such that $a + pn = c + qn$. Not only
do we need to solve for `p` and `q`, we must also *prove to Agda* that this is a
solution. Let's do it on paper first, to get a lower bound for how painful this
is going to be. We can solve the first equation for $b$:

$$
\begin{aligned}
a + xn &= b + yn \\
a + xn - yn &= b
\end{aligned}
$$

and the second:

$$
\begin{aligned}
b + zn &= c + wn \\
b &= c + wn - zn
\end{aligned}
$$

Since we have separate $b$ on each side, we can combine these two equations into
one:

$$
\begin{aligned}
a + xn - yn &= b = c + wn - zn \\
a + xn - yn &= c + wn - zn \\
\end{aligned}
$$

and after a little simplification we get our solution:

$$
\begin{aligned}
a + xn - yn &= c + wn - zn \\
a + xn + zn &= c + wn + yn \\
a + (x + z)n &= c + (w + y)n
\end{aligned}
$$

namely,

$$
\begin{aligned}
p &= x + z \\
q &= w + y
\end{aligned}
$$

The proof is certainly no cake walk, but it does appear to be tractable. Let's
see if we can convince Agda. What exactly are we going to need? When we get
started, we'll get two proof terms as arguments, these have type `bind:a b x
y n:a + x * n ≡ b + y * n` and `bind:b c z w n:b + z * n ≡ c + w * n`
respectively. Therefore, in order to actually apply those proofs, we're going to
need some lemmas---the first will need to separate out a `bind:a x n:a + x * n`
term from `bind:a x z n:a + (x + z) * n`:

```agda
  lemma₁ : (a x z : ℕ) → a + (x + z) * n ≡ (a + x * n) + z * n
  lemma₁ a x z = begin
    a + (x + z) * n      ≡⟨ cong (a +_) (*-distribʳ-+ n x z) ⟩
    a + (x * n + z * n)  ≡⟨ sym (+-assoc a _ _) ⟩
    (a + x * n) + z * n  ∎
    where open ≡-Reasoning
```

The other lemma we'll need just swaps two terms in a sum:

```agda
  lemma₂ : (i j k : ℕ) → (i + j) + k ≡ (i + k) + j
  lemma₂ i j k = begin
    (i + j) + k  ≡⟨ +-assoc i j k ⟩
    i + (j + k)  ≡⟨ cong (i +_) (+-comm j k) ⟩
    i + (k + j)  ≡⟨ sym (+-assoc i k j) ⟩
    (i + k) + j  ∎
    where open ≡-Reasoning
```

We're now ready to show `def:≈-trans`:

```agda
  ≈-trans : Transitive _≈_
  ≈-trans {a} {b} {c} (≈-mod x y pxy) (≈-mod z w pzw) =
    ≈-mod (x + z) (w + y)
    ( begin
      a + (x + z) * n      ≡⟨ lemma₁ a x z ⟩
      (a + x * n) + z * n  ≡⟨ cong (_+ z * n) pxy ⟩
      (b + y * n) + z * n  ≡⟨ lemma₂ b (y * n) (z * n) ⟩
      (b + z * n) + y * n  ≡⟨ cong (_+ y * n) pzw ⟩
      c + w * n + y * n    ≡⟨ sym (lemma₁ c w y) ⟩
      c + (w + y) * n      ∎
    )
    where open ≡-Reasoning
```

Haven now shown reflexivity, symmetry, and transitivity, it's clear that
`type:_≈_` is an equivalence relation:

```agda
  ≈-preorder : IsPreorder _≈_
  IsPreorder.refl   ≈-preorder = ≈-refl
  IsPreorder.trans  ≈-preorder = ≈-trans

  ≈-equiv : IsEquivalence _≈_
  IsEquivalence.isPreorder  ≈-equiv = ≈-preorder
  IsEquivalence.sym         ≈-equiv = ≈-sym
```

Let's drop this fact into the `keyword:instance` environment:

```agda
  instance
    _ = ≈-equiv
```

and specialize `module:Preorder-Reasoning` so we get reasoning syntax for our
new preorder:

```agda
  module Mod-Reasoning where
    open Preorder-Reasoning ≈-preorder
      hiding (refl; trans)
      public
```


## Congruence of Addition

We're almost ready to build some interesting proofs; but we're going to need to
define a few more trivial ones first. Let's prove two more fact "by hand", the
fact that $0 = n \pmod{n}$:

```agda
  0≈n : 0 ≈ n
  0≈n = ≈-mod 1 0 refl
```

and the fact that the `ctor:suc` function preserves the `type:_≈_` relationship:

```agda
  suc-cong-mod : {a b : ℕ} → a ≈ b → suc a ≈ suc b
  suc-cong-mod (≈-mod x y p) = ≈-mod x y (cong suc p)
```

While this sounds like it should be a freebie, observe that we don't have
a general `def:cong`-like machine for `type:_≈_`! To convince yourself of this
claim, consider the function `expr:_∸ 1`, which recall subtracts one from all
numbers *except zero.* If we had `def:cong` for `type:_≈_`, we could hoist
`expr:_∸ 1` over $0 = 5 \pmod{5}$ (a true statement), which would give us back
$0 = 5 \pmod{5}$ (patently false.) Therefore, there can be no `def:cong` for
`type:_≈_` that allows for arbitrary functions, and so we are forced to prove
lemmas like `def:suc-cong-mod` as if we were plebs.

With these two hand-proven facts out of the way, we can now show that if
`bind:a:a ≈ 0`, then `bind:a b:a + b ≈ b`:

```agda
  +-zero-mod : (a b : ℕ) → a ≈ 0 → a + b ≈ b
  +-zero-mod a zero a≈0 = begin
    a + zero  ≡⟨ +-identityʳ a ⟩
    a         ≈⟨ a≈0 ⟩
    zero      ∎
    where open Mod-Reasoning
  +-zero-mod a (suc b) a≈0 = begin
    a + suc b    ≡⟨ +-suc a b ⟩
    suc a + b    ≡⟨⟩
    suc (a + b)  ≈⟨ suc-cong-mod (+-zero-mod a b a≈0) ⟩
    suc b        ∎
    where open Mod-Reasoning
```

Let's hoist another function about the naturals, namely that `ctor:suc` is
injective:

```agda
  suc-injective-mod : {a b : ℕ} → suc a ≈ suc b → a ≈ b
  suc-injective-mod (≈-mod x y p) = ≈-mod x y (suc-injective p)
```

Give everything we've built, we can now show a major result, namely that
`def:_+_` also preserves `type:_≈_`:

```agda
  +-cong₂-mod : {a b c d : ℕ}
      → a ≈ b → c ≈ d
      → a + c ≈ b + d
  +-cong₂-mod {zero} {b} {c} {d} pab pcd = begin
    c      ≈⟨ pcd ⟩
    d      ≈⟨ sym (+-zero-mod b d (sym pab)) ⟩
    b + d  ∎
    where open Mod-Reasoning
  +-cong₂-mod {suc a} {zero} {c} {d} pab pcd = begin
    suc a + c  ≈⟨ +-zero-mod (suc a) c pab ⟩
    c          ≈⟨ pcd ⟩
    d          ∎
    where open Mod-Reasoning
  +-cong₂-mod {suc _} {suc _} pab pcd =
    suc-cong-mod (+-cong₂-mod (suc-injective-mod pab) pcd)
```

While nobody will argue that `def:+-cong₂-mod` is the prettiest function around,
it's instructive to compare it to the work we had to do in order to prove
transitivity. There we had to work out---by hand---exactly what `field:x` and
`field:y` should be, and then write a big `def:_≡_` term to convince Agda that
we were right. But now that we have transitivity under our collective belt, we
can just throw smaller lemmas around and let Agda do all the work computing
`field:x` and `field:y`.

Proving these things without our equivalence relation isn't necessarily hard,
each one is non-trivial amount of work. Worse, however, is that such a proof is
at a lower level than we'd prefer---we want to be thinking about modular
arithmetic, not juggling equations!


## Congruence of Multiplication {#sec:cong-mod}

Let's prove prove two more facts about modular arithmetic, the first in service
of the second. We can show that modular multiplication by zero results in zero:

```agda
  *-zero-mod : (a b : ℕ) → b ≈ 0 → a * b ≈ 0
  *-zero-mod zero     b x = refl
  *-zero-mod (suc a)  b x = begin
    suc a * b  ≡⟨⟩
    b + a * b  ≈⟨ +-cong₂-mod x (*-zero-mod a b x) ⟩
    0          ∎
    where open Mod-Reasoning
```

and use that as a lemma to show that `def:_*_` preserves `type:_≈_`, via
`def:*-cong₂-mod`:

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
                    (*-cong₂-mod (suc-injective-mod a=b) c=d)⟩
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

Proving the equality of these terms in Agda is on the order of 50 algebraic
manipulations; most of it being gentle massaging of the expression into
something over which you can continually `def:cong` one proof after another.

All in all, showing `def:_≈_` is an equivalence relation has bought us a great
deal of algebraic power. We're now able to work with values which are not equal
*on the nose,* but rather "equal enough" in the circumstances. The only real
loss here is that `def:cong` no longer holds for all functions, and that we must
prove it holds on a function-by-function basis. There do exist extensions to
Agda's type theory which allow us to upgrade equivalence to real,
honest-to-goodness equality, but they are beyond the scope of this book, and are
a major driving force in modern type theory research.


## Automating Proofs

-- TODO(sandy): maybe add a note in the proof about numbers chapter


## Wrapping Up

-- TODO(sandy): finalize wrapping up

