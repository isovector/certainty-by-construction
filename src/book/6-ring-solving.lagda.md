# Ring Solving

```agda
module 6-ring-solving where

open import Data.Nat using (ℕ)
```

With a good deal of practice under our belt by this point, you might have
noticed a frustrating fact about doing proofs in Agda: the most obvious proofs
can be the ones which are tryingly tedious. These are the proofs that involve
reasoning about arithmetic---which is a feat that we humans take for granted,
having so much experience doing it. Agda's mechanical insistence that we spell
out every step of the tedious process by hand is indeed a barrier to its
adoption, but thankfully, we have workarounds.

Recall that when we were implementing `def:*-cong₂-mod`, that is, `def:cong` for
modular arithmetic, we built a lot of setoid machinery and reasoning to avoid
needing to solve these large proofs by hand.

The problem if you recall, is that we're trying to solve the following:

$$
ac + (cx + az + xzn) \times n = bd + (dy + bw + ywn) \times n
$$

subject to the additional facts

$$
a + xn ≡ b + yn \\
c + zn ≡ d + wn
$$

In order to get a sense of the actual effort required to solve this problem, we
can solve the equation in pen and paper:

$$
\begin{aligned}
  ac + (cx + az + xzn) * n \\
&= ac + cxn + azn + xznn \\
&= c * (a + xn) + azn + xznn \\
&= c * (a + xn) + zn * (a + xn) \\
&= c * (b + yn) + zn * (b + yn) \\
&= cb + cyn + zn * (b + yn) \\
&= cb + cyn + znb + zynn \\
&= cb + znb + cyn + zynn \\
&= b * (c + zn) + cyn + zynn \\
&= b * (c + zn) + yn * (c + zn) \\
&= b * (d + wn) + yn * (d + wn) \\
&= bd + bwn + yn * (d + wn) \\
&= bd + bwn + dyn + ywnn \\
&= bd + dyn + bwn + ywnn \\
&= bd + (dyn + bwn + ywnn) \\
&= bd + (dy + bw + ywn) * n
\end{aligned}
$$

This proof is already 15 lines long, and that's including the inherent shortcuts
that we take as humans, such as automatically reasoning over the associativity
and commutativity of addition and multiplication---imagine how much longer
this proof would be if we had to spell out every single time we wanted to move a
term around, and if we kept track of all the parentheses required to multiply
out $z * (y * (n * n))$.

Yeesh. As you can imagine, the cost of writing expensive proofs for simple
lemmas can be prohibitive, and get in our way of actually wanting to use Agda.
Thankfully, this is not a cost we often need to pay, thanks to Agda's *ring
solver.*

The ring solver is a general purpose tool for automatically reasoning about
rings. Rings are algebraic structures which generalize the relationships between
addition and multiplication. A ring has an associative, commutative binary
operation called "addition" and an associative, commutative binary operation
called "multiplication." We also have
distinguished elements 0 and 1 that behave like you'd expect with respect to 0
and 1, namely that we have the following pile of equalities: `def:+-identityˡ`,
`def:+-identityʳ`, `def:*-identityˡ`, `def:*-identityʳ`, `def:*-zeroˡ`,
`def:*-zeroʳ`, `def:+-comm`, `def:*-comm`, `def:+-assocˡ`, `def:+-assocʳ`,
`def:*-assocˡ`, `def:*-assocʳ`, `def:*-distribˡ-+`, and `def:*-distribʳ-+`. As
you can see, there is a great deal of structure inherent here!

But, this is just the structure required of a *semiring*. In order to get the
full *ring*, we require an additive inverse operation analogous to
unary negation, with the property that for any $a$ we have $a + -a = 0$.

By virtue of generalizing addition and multiplication, addition and
multiplication themselves had better form a ring! And
indeed they do. Note that however, the natural numbers don't have any additive
inverses, and so they can at best be semirings. Integers, however, weaken this
constraint, and are fully realizable as rings.

Agda's standard library comes with a *ring solver*, which is a series of tools
for automatically solving equalities over rings. Of course, calling it a *ring*
solver is a bit of a misnomer, since the ring solver works over semirings as
well, due to a subtle weakening of required ring structure. However, these
details are irrelevant to today's discussion; all you need to keep in mind is
that the ring solver works over any commutative semiring in addition to rings
themselves.

, meaning we can use the ring solver to tackle problems of this
form. Let's set up the necessary machinery again to describe the problem:

```agda
-- module _ (n : ℕ) where
--   open import Relation.Binary.PropositionalEquality
--   open import Data.Nat
--   open import 4-setoids
--   open mod-def


--   *-cong₂-mod'
--       : {a b c d : ℕ}
--       → a ≈ b ⟨mod n ⟩
--       → c ≈ d ⟨mod n ⟩
--       → a * c ≈ b * d ⟨mod n ⟩
--   *-cong₂-mod' {a} {b} {c} {d} (≈-mod x y pxy) (≈-mod z w pzw) =
```

Recall, in order to show congruence over `_*_` for modular arithmetic, we are
required to discover $p$ and $q$ such that $ac + pn = bd + qn$. The solutions
for $p$ and $q$ are given as:

```agda
    -- ≈-mod (c * x + a * z + x * z * n)
    --       (d * y + b * w + y * w * n)
    --       (begin
```

and all that's left is to give the proof. Thankfully, we did most of the work
earlier by hand when we gave our informal proof of this fact. The ring solver
can't do all of the work for us, but it can dramatically improve the situation.
The left side of our equality is `a * c + (c * x + a * z + x * z * n) * n`,
which we need to show is equal to `b * d + (d * y + b * w + y * w * n) * n`. The
technique is to massage the left side into a form that we an easily `cong` our
`pxy` proof, then massage the reuslt into a form we can easily `cong` our `pzw`
proof, and then massage *that* result into the final form.

The shape we need for an easy `cong` is the step immediately before the `cong`
in our informal reasoning. That is:

```arithmetic
  -- a * c + (c * x + a * z + x * z * n) * n
-- = ...
-- = c * (a + x * n) + z * n * (a + x * n)
```

We can set up the problem by beginning our reasoning block:

```agda
      -- a * c + (c * x + a * z + x * z * n) * n
      --   ≡⟨
```

The ring solver is invoked via a call to `solve` with its first argument being
the number of free variables flying around needing to be solved for. In this
case we have 5 (a, c, n, x, z):

```agda
            -- solve 5
```

Our next step is to construct a *syntax tree* corresponding to the expression
we'd like to solve. Our goal is to show `a * c + (c * x + a * z + x * z * n) * n
= c * (a + x * n) + z * n * (a + x * n)`, so this is almost our syntax tree; all
that's required is to put a colon before each of `_+_`, `_*_` and `_=_`. We
put this tree inside of a lambda that bounds each of the free variables:

```agda
    -- (λ a c n x z →
    --     a :* c :+ (c :* x :+ a :* z :+ x :* z :* n) :* n
    --  := (a :+ x :* n) :* c :+ (a :+ x :* n) :* z :* n
    -- )
```

This syntax tree is an annoying thing to write, but is necessary to help the
ring solver know what it's trying to solve. Remember, just because we've written
out this expression with full syntax here doesn't mean this is the term Agda is
working on! Agda is free to expand definitional equalities, meaning it might
have already reduced some of these additions and multiplications away!

Finally, all that's left is to finish calling `solve` with `refl`, and then each
of the variables we mentioned in the lambda, in the same order, thus:

```agda
      -- refl a c n x z ⟩
```

Agda will happily accept the resulting proof, meaning we are now in a position
to `cong` `pxy` into the right place:

```agda
      -- (a + x * n) * c + (a + x * n) * z * n
    -- ≡⟨ cong (λ φ → φ * c + φ * z * n) pxy ⟩
      -- (b + y * n) * c + (b + y * n) * z * n
```

We'll do the next step more quickly. We need to get the expression to a place in
which we can apply `pzw`. Following our earlier reasoning again, the
intermediate proof we need is:

```arithmetic
= (b + y * n) * c + (b + y * n) * z * n
= ...
= b * (c + zn) + yn * (c + zn)
```

which is easy enough to do with our ring solver. We identify the variables in
play, build a lambda to create the syntax tree, and apply it:

```agda
    -- ≡⟨ solve 5 (λ b c n y z →
    --       (b :+ y :* n) :* c :+ (b :+ y :* n) :* z :* n
    --     := b :* (c :+ z :* n) :+ y :* n :* (c :+ z :* n)
    --            )
    --      refl b c n y z
    --  ⟩
    --   b * (c + z * n) + y * n * (c + z * n)
```

We're now back in a place we can `cong`. Rather than walk through the rest of
the example, we will present it in its completeness:

```agda
      -- ≡⟨ cong (λ φ → b * φ + y * n * φ) pzw ⟩
      --   b * (d + w * n) + y * n * (d + w * n)
      -- ≡⟨ solve 5 (λ b d n w y →
      --       b :* (d :+ w :* n) :+ y :* n :* (d :+ w :* n)
      --    := b :* d :+ (d :* y :+ b :* w :+ y :* w :* n) :* n
      --            )
      --      refl b d n w y
      --   ⟩
      --   b * d + (d * y + b * w + y * w * n) * n
      -- ∎ )
```

All that's left is to get our solver in scope, by importing it from
`Data.Nat.Solver` and opening the resulting `+-*-Solver` module:

```agda
    -- where
    --   open ≡-Reasoning
    -- open import Data.Nat.Solver
    --   open +-*-Solver
```

It's almost as if by magic, but we've managed to turn a 50 line proof into two
`cong`s and three applications of the ring solver. It doesn't do all the work
for you, but it sure does most. And even better, this machinery works for any
sort of numbers you can throw at it, as well as many of your own types that
happen to be rings.

But the question is --- how does any of this work? Is it built-in to the
compiler, or is it something we could have written for ourselves?
Fascinatingly, the answer is the latter. It's the sort of thing we can build for
ourselves, which we will explore now.


## Canonical Forms

An interesting insight into how to solve this problem is to use the analogy of
solving a maze. Not not the corn-maze sort, but the variety that comes on the
back of cereal boxes. Solving a maze is often a two-sided approach; you explore
from the beginning of the maze, and you simultaneously explore from the end. The
goal is to meet somewhere in the middle. If you can get to the same place from
both sides, you can compose the two half-solutions into a final path to escape
the maze.

Why does this work? In some sense, it's because the first moves you can take
from either direction are relatively constrained. The number of possibilities
are few, and there is an obvious decision procedure in the form of "is this
going roughly the right direction?" As you move further from your starting
point, the number of possibilities increase exponentially; after all, there's
always the chance that you took the wrong direction on your first step.

By exploring from both sides at once, we are minimizing the effects of these
exponential blow-ups. Furthermore, your notion of "the right direction to head"
increases as you have more familiarity with the other side of the maze. Now that
you have a path, you don't need necessarily to find the *end* of the path, you
just need to intersect it. As a result, we have more "targets" to aim our search
at.

All of this applies to proofs as well. We have well-defined starting and
stopping points, and are tasked with bridging the distance between them. Here
too we have exponential blow-ups in complexity, so we can cover the most space
by searching from the top and bottom at the same time.

Of course, this heuristic doesn't always work. But what if we had a well-defined
"middle" to path find to? The reason the ring solver is a *ring* solver, as
opposed to just a *solver*, is that rings give us a healthy balance between
expressiveness and solvability. Why is that?

Rings admit a *normal*, or *canonical,* form. That is to say, we have a
well-defined, unique notion of what terms in a ring should look like. That
means, two terms are equal if they have the same normal form, the proverbial
"middle" of the maze.

Polynomials are the best examples of the canonical form of rings. While we can
express polynomials in any number of ways, by far the most common is in the "sum
of descending powers." To jog your memory, most polynomials look like the
following:

$$
x^3 + 3x^2 - 9x - 17
$$

It's perfectly acceptable, if weird, to write the above as:

$$
(x - 9 + x^2 + 2x)x - 17
$$

which is equivalent, but the mere fact that it doesn't "look like a polynomial"
is a strong indication that you have internalized the polynomial canonical form
whether or not you were aware of it.

Given the existence of canonical forms, we can now reduce the problem of proving
ring equality to be:

1. Prove both terms are equal to their canonical form.
2. Compare the canonical forms.
3. If the canonical forms match, compose the earlier proofs.

This is a powerful, widely-useful technique, and you would do well to add it to
your toolbox.

The notion of polynomial generalizes to arbitrary rings. Why is that? We have
addition and multiplication, both are associative and commutative, and
multiplication distributes over addition. Because of the distributivity, we can
always produce a *sum of products* structure, that is, to distribute all
multiplications over every addition. That is, we can always reduce expressions
of the form:

$$
x(5 + y)
$$

with

$$
5x + xy
$$

which is to say, moving the additions to be the outermost nodes in the
expression tree.

Because multiplication is commutative, we can freely group together all of the
same elements of the group. So, we can happily combine the two $x$s in

$$
xyx = xxy = x^2y
$$

Finally, the commutativity of addition means we can reorder the addition nodes.
For a single variable, we'd like to sort it into decreasing powers of that
variable. For the multi-variable case, we can instead use a "list of
lists"-style approach, and treat other variables as coefficients of another
variable. That is, if we'd like to group the terms

$$
x^2y + x^2y^2 + xy^3 + 3xy^2 - 7yx + 10
$$

we can first group it by descending powers of $x$, and then by powers of $y$,
thus:

$$
(y^2 + y)x^2 + (y^3)x + (3y^2 - 7y)x + 10
$$

This approach clearly generalizes to an arbitrary number of variables, and thus,
given any ordering of variables (perhaps "order mentioned in the call to the
solver"), we can find a canonical form for any expression over rings.

Describing this canonical form also gives us an insight into why we have ring
solvers but not semigroup solvers. Semigroups, having only a single, associative
binary operator, simply don't have enough algebraic structure to require
interesting proofs. If your semigroup is commutative ("Abelian," in the jargon)
then you can simply reorder all the terms so they appear in a row. It's exactly
the interplay between addition and multiplication that makes the problem at all
interesting.


## Sketching Out a Ring Solver

While we will not implement a ring solver in this book, we can certainly explore
the high-level ideas necessary to implement one, and give enough of a sketch for
the motivated reader to follow through on. We will take our inspiration from the
ring solver presented in the introduction to this chapter, looking for a similar
interface.

To simplify the problem, our sketch will only solve over one variable. If
you're curious about generalizing the approach, the standard library is full of
insightful approaches to this problem.

We begin with a little ceremony. We will use the standard library's
`CommutativeSemiring`, which is a record containing `_+_`, `_*_`, `0#` and `1#`.
We then parameterize a new module over a commutative semiring:

```agda
open import Level using (Level)
open import Algebra.Bundles using (CommutativeSemiring)

module RingSolver {c ℓ : Level} (ring : CommutativeSemiring c ℓ) where
```

By opening the `CommutativeSemiring` record, we can pull the semigroup
operations into scope.

```agda
  open CommutativeSemiring ring renaming (Carrier to A)
```

Next we will define the syntax for dealing with rings:

```agda
  infixr 5 _:+_
  infixr 6 _:*_

  data Syn : Set c where
    var : Syn
    con : A → Syn
    _:+_ : Syn → Syn → Syn
    _:*_ : Syn → Syn → Syn
```

And, just to show that this really is the syntax for our language, we can give
it semantics via `⟦_⟧`, which simply interprets the syntax as the actual ring
operations:

```agda
  ⟦_⟧ : Syn → A → A
  ⟦ var ⟧    v = v
  ⟦ con c ⟧  v = c
  ⟦ x :+ y ⟧ v = ⟦ x ⟧ v + ⟦ y ⟧ v
  ⟦ x :* y ⟧ v = ⟦ x ⟧ v * ⟦ y ⟧ v
```

So that covers the syntax. But now we'd like to be able to build a normal form.
The most obvious way of constructing such a thing is via *Horner normal form*,
which is unlike our standard polynomial notation, but instead encodes
polynomials out of the following building blocks:

```agda
  data HNF : Set c where
    ⊘ : HNF
    _*x+_ : HNF → A → HNF
```

You might have encountered HNF in an algorithms class at some point. The
observation comes from the fact that computing the value of a polynomial in
standard form requires $O(n^2)$ multiplications in the largest degree of the
polynomial. Instead if we make the following transformation:

$$
x^2 + 5x + 6 = ((0 + 1)x + 5)x + 6
$$

we require only $O(n)$ multiplications, which is a significant improvement in
asymptotics. Horner normal form doesn't buy us any asymptotic improvements in
this case, but it saves us needing to reshuffle everything around.

Our next step is simply to give the semantics for `HNF`, completely analogously
to what we did for `Syn`:

```agda
  ⟦_⟧H : HNF → A → A
  ⟦ ⊘ ⟧H _ = 0#
  ⟦ a *x+ b ⟧H x = ⟦ a ⟧H x * x + b
```

We'd like to define a transformation from `Syn` into `HNF`, but that is going to
require addition and multiplication over `HNF`. Addition is straightforward:

```agda
  _+H_ : HNF → HNF → HNF
  ⊘ +H y = y
  (a *x+ b) +H ⊘ = a *x+ b
  (a *x+ b) +H (c *x+ d) = (a +H c) *x+ (b + d)

  infixl 5 _+H_
```

and multiplication isn't much more work, after we take advantage of the
algebraic fact that:

$$
(ax + b)(cx + d) = acx^2 + (bc + ad)x + bd
$$

```agda
  _*S_ : A → HNF → HNF
  k *S ⊘ = ⊘
  k *S (hnf *x+ x) = (k *S hnf) *x+ (k * x)
  infixl 6 _*S_

  _*H_ : HNF → HNF → HNF
  ⊘ *H _ = ⊘
  (a *x+ b) *H ⊘ = ⊘
  (a *x+ b) *H (c *x+ d) = (((a *H c) *x+ 0#) +H (b *S c) +H (d *S a)) *x+ (b * d)
  infixl 6 _*H_
```

With all of this machinery out of the way, we can implement `normalize`, which
transforms a `Syn` into an `HNF`:

```agda
  normalize : Syn → HNF
  normalize var = (⊘ *x+ 1#) *x+ 0#
  normalize (con x) = ⊘ *x+ x
  normalize (x :+ y) = normalize x +H normalize y
  normalize (x :* y) = normalize x *H normalize y
```

Believe it or not, that's most of the work to write a ring solver. We have one
more function to write, showing that evaluating the syntactic term is equal to
evaluating its normal form --- that is, that the normal form truly is a merely a
different representation of the same expression. This function has type:

```agda
  open import Relation.Binary.Reasoning.Setoid setoid

  postulate
    …algebra… : {x y : A} → x ≈ y
    …via… : {ℓ : Level} {B : Set ℓ} {x y : A} → B → x ≈ y



  +H-+-hom : ∀ x y v → ⟦ x +H y ⟧H v ≈ ⟦ x ⟧H v + ⟦ y ⟧H v
  +H-+-hom ⊘ ⊘ v = sym (+-identityʳ 0#)
  +H-+-hom (x *x+ x₁) ⊘ v =
    begin
      ⟦ x ⟧H v * v + x₁
    ≈⟨ …algebra… ⟩
      ⟦ x ⟧H v * v + x₁ + 0#
    ∎
  +H-+-hom ⊘ (y *x+ x₁) v = sym (+-identityˡ _)
  +H-+-hom (x *x+ x₂) (y *x+ x₁) v =
    begin
      ⟦ x +H y ⟧H v * v + (x₂ + x₁)
    ≈⟨ +-cong (*-cong (+H-+-hom x y v) refl) refl ⟩
      (⟦ x ⟧H v + ⟦ y ⟧H v) * v + (x₂ + x₁)
    ≈⟨ …algebra… ⟩
      ⟦ x ⟧H v * v + x₂ + (⟦ y ⟧H v * v + x₁)
    ∎

  *S-*-hom : ∀ k x v → ⟦ k *S x ⟧H v ≈ k * ⟦ x ⟧H v
  *S-*-hom k ⊘ v = sym (zeroʳ _)
  *S-*-hom k (x *x+ x₁) v =
    begin
      ⟦ k *S x ⟧H v * v + k * x₁
    ≈⟨ +-congʳ (*-congʳ (*S-*-hom k x v)) ⟩
      k * ⟦ x ⟧H v * v + k * x₁
    ≈⟨ …algebra… ⟩
      k * (⟦ x ⟧H v * v + x₁)
    ∎

  foil : ∀ a b c d → (a + b) * (c + d) ≈ (a * c) + (b * c) + (a * d) + (b * d)
  foil a b c d = …algebra…

  *H-*-hom : ∀ x y v → ⟦ x *H y ⟧H v ≈ ⟦ x ⟧H v * ⟦ y ⟧H v
  *H-*-hom ⊘ y v = sym (zeroˡ _)
  *H-*-hom (x *x+ x₁) ⊘ v = sym (zeroʳ _)
  *H-*-hom (a *x+ b) (c *x+ d) x =
    let ⌊_⌋ a = ⟦ a ⟧H x in
    begin
      ⟦ ((a *H c) *x+ 0#) +H b *S c +H d *S a ⟧H x * x + b * d
    ≈⟨ +-congʳ (*-congʳ (+H-+-hom (((a *H c) *x+ 0#) +H b *S c) (d *S a) x)) ⟩
      (⟦ ((a *H c) *x+ 0#) +H b *S c ⟧H x + ⟦ d *S a ⟧H x) * x + b * d
    ≈⟨ +-congʳ (*-congʳ (+-congʳ (+H-+-hom ((a *H c) *x+ 0#) (b *S c) x))) ⟩
      (⌊ a *H c ⌋ * x + 0# + ⌊ b *S c ⌋ + ⌊ d *S a ⌋) * x + b * d
    ≈⟨ …via… *S-*-hom ⟩
      (⌊ a *H c ⌋ * x + (b * ⌊ c ⌋) + (d * ⌊ a ⌋)) * x + (b * d)
    ≈⟨ +-congʳ (*-congʳ (+-congʳ (+-congʳ (*-congʳ (*H-*-hom a c x))))) ⟩
      (⌊ a ⌋ * ⌊ c ⌋ * x + b * ⌊ c ⌋ + d * ⌊ a ⌋) * x + (b * d)
    ≈⟨ …via… distribʳ ⟩
      (⌊ a ⌋ * ⌊ c ⌋ * x * x) + (b * ⌊ c ⌋ * x) + (d * ⌊ a ⌋ * x) + (b * d)
    ≈⟨ …algebra… ⟩
      (⌊ a ⌋ * x * (⌊ c ⌋ * x)) + (b * (⌊ c ⌋ * x)) + (⌊ a ⌋ * x * d) + (b * d)
    ≈⟨ sym (foil (⌊ a ⌋ * x) b (⌊ c ⌋ * x) d) ⟩
      (⌊ a ⌋ * x + b) * (⌊ c ⌋ * x + d)
    ∎

  _≈nested_>_<_ : A → {f : A → A} → (cong : {x y : A} → x ≈ y → f x ≈ f y) → {x y z : A} → x IsRelatedTo y → f y IsRelatedTo z → f x IsRelatedTo z
  _ ≈nested cong > relTo x=y < (relTo fy=z) = relTo (trans (cong x=y) fy=z)
  infixr 2 _≈nested_>_<_

  _□ : (x : A) → x IsRelatedTo x
  _□ = _∎

  infix  3 _□



  open import Function using (_∘_)

  *H-*-hom' : ∀ x y v → ⟦ x *H y ⟧H v ≈ ⟦ x ⟧H v * ⟦ y ⟧H v
  *H-*-hom' ⊘ y v = sym (zeroˡ _)
  *H-*-hom' (x *x+ x₁) ⊘ v = sym (zeroʳ _)
  *H-*-hom' (a *x+ b) (c *x+ d) x =
    let ⌊_⌋ a = ⟦ a ⟧H x in
    begin
      ⟦ ((a *H c) *x+ 0#) +H b *S c +H d *S a ⟧H x * x + b * d
    ≈nested (+-congʳ ∘ *-congʳ)
      >
        ⌊ ((a *H c) *x+ 0#) +H b *S c +H d *S a ⌋
      ≈⟨ +H-+-hom (((a *H c) *x+ 0#) +H b *S c) (d *S a) x ⟩
        ⌊((a *H c) *x+ 0#) +H b *S c ⌋ + ⌊ d *S a ⌋
      ≈⟨ +-congʳ (+H-+-hom ((a *H c) *x+ 0#) (b *S c) x) ⟩
        ⌊ a *H c ⌋ * x + 0# + ⌊ b *S c ⌋ + ⌊ d *S a ⌋
      ≈⟨ …via… *S-*-hom ⟩
        ⌊ a *H c ⌋ * x + (b * ⌊ c ⌋) + (d * ⌊ a ⌋)
      ≈⟨ +-congʳ (+-congʳ (*-congʳ (*H-*-hom a c x))) ⟩
        ⌊ a ⌋ * ⌊ c ⌋ * x + b * ⌊ c ⌋ + d * ⌊ a ⌋
    □ <
      (⌊ a ⌋ * ⌊ c ⌋ * x + b * ⌊ c ⌋ + d * ⌊ a ⌋) * x + (b * d)
    ≈⟨ …via… distribʳ ⟩
      (⌊ a ⌋ * ⌊ c ⌋ * x * x) + (b * ⌊ c ⌋ * x) + (d * ⌊ a ⌋ * x) + (b * d)
    ≈⟨ …algebra… ⟩
      (⌊ a ⌋ * x * (⌊ c ⌋ * x)) + (b * (⌊ c ⌋ * x)) + (⌊ a ⌋ * x * d) + (b * d)
    ≈⟨ sym (foil (⌊ a ⌋ * x) b (⌊ c ⌋ * x) d) ⟩
      (⌊ a ⌋ * x + b) * (⌊ c ⌋ * x + d)
    ∎

  sems : (s : Syn) → (v : A) → ⟦ s ⟧ v ≈ ⟦ normalize s ⟧H v
```

and is sketched out:

```agda
  sems var v = begin
    v                       ≈⟨ …algebra… ⟩
    (0# * v + 1#) * v + 0#  ∎
  sems (con c) v = begin
    c           ≈⟨ sym (+-identityˡ _) ⟩
    0# + c      ≈⟨ sym (+-congʳ (zeroˡ _)) ⟩
    0# * v + c  ∎
  sems (x :+ y) v = begin
    ⟦ x ⟧ v + ⟦ y ⟧ v                        ≈⟨ +-cong (sems x v) (sems y v) ⟩
    ⟦ normalize x ⟧H v + ⟦ normalize y ⟧H v  ≈⟨ sym (+H-+-hom (normalize x) (normalize y) v) ⟩
    ⟦ normalize x +H normalize y ⟧H v        ∎
  sems (x :* y) v = begin
    ⟦ x ⟧ v * ⟦ y ⟧ v                        ≈⟨ *-cong (sems x v) (sems y v) ⟩
    ⟦ normalize x ⟧H v * ⟦ normalize y ⟧H v  ≈⟨ sym (*H-*-hom (normalize x) (normalize y) v) ⟩
    ⟦ normalize x *H normalize y ⟧H v        ∎
```

Implementing `sems` will probably be the most work if you attempt this at home;
showing the homomorphisms between `_+H_` and `_+_` are not trivial, nor are
those for multiplication.

Finally, we can put everything together, solving proofs of the evaluation of two
pieces of syntax given a proof of their normalized forms:

```agda
  solve
      : (s t : Syn)
      → (v : A)
      → ⟦ normalize s ⟧H v ≈ ⟦ normalize t ⟧H v
      → ⟦ s ⟧ v ≈ ⟦ t ⟧ v
  solve s t v x = begin
    ⟦ s ⟧ v             ≈⟨ sems s v ⟩
    ⟦ normalize s ⟧H v  ≈⟨ x ⟩
    ⟦ normalize t ⟧H v  ≈⟨ sym (sems t v) ⟩
    ⟦ t ⟧ v             ∎
```

The proof argument required by this function is an informative clue as to why we
always needed to pass `refl` to the official ring solver `solve` function.

```agda

module solver2 where

module Solver {𝔸 : Set}
    (0# 1# : 𝔸)
    (_+_ _*_ : 𝔸 → 𝔸 → 𝔸)
    (let infixr 5 _+_; _+_ = _+_) (let infixr 6 _*_; _*_ = _*_) where
  open import Relation.Binary.PropositionalEquality

  module _ {A : Set} where
    open import Algebra.Definitions {A = A} _≡_ public

  postulate
    -- +-identityˡ : LeftIdentity 0# _+_
    +-identityʳ : RightIdentity 0# _+_
    -- *-identityˡ : LeftIdentity 1# _*_
    *-identityʳ : RightIdentity 1# _*_
    -- *-zeroˡ : LeftZero 0# _*_
    -- *-zeroʳ : RightZero 0# _*_
    -- +-comm : Commutative _+_
    -- *-comm : Commutative _*_
    +-assoc : Associative _+_
    -- *-assoc : Associative _*_
    *-distribˡ-+ : _*_ DistributesOverˡ _+_
    *-distribʳ-+ : _*_ DistributesOverʳ _+_

  open import Data.Nat
    using (ℕ; zero; suc)

  private variable
    n : ℕ

  data HNF : ℕ → Set where
    const : 𝔸 → HNF zero
    coeff : HNF n → HNF (suc n)
    _*x+_ : HNF (suc n) → HNF n → HNF (suc n)

  _⊕_ : HNF n → HNF n → HNF n
  const a ⊕ const b = const (a + b)
  coeff a ⊕ coeff b = coeff (a ⊕ b)
  coeff a ⊕ (b *x+ c) = b *x+ (a ⊕ c)
  (a *x+ b) ⊕ coeff c = a *x+ (b ⊕ c)
  (a *x+ b) ⊕ (c *x+ d) = (a ⊕ c) *x+ (b ⊕ d)
  infixr 5 _⊕_

  ↪ : 𝔸 → HNF n
  ↪ {zero} a = const a
  ↪ {suc n} a = coeff (↪ a)

  0H : HNF n
  0H = ↪ 0#

  1H : HNF n
  1H = ↪ 1#

  x* : HNF (suc n) → HNF (suc n)
  x* a = a *x+ 0H

  _⊗_ : HNF n → HNF n → HNF n
  const a ⊗ const b = const (a * b)
  coeff a ⊗ coeff b = coeff (a ⊗ b)
  coeff a ⊗ (b *x+ c) = (coeff a ⊗ b) *x+ (a ⊗ c)
  (a *x+ b) ⊗ coeff c = (a ⊗ coeff c) *x+ (b ⊗ c)
  (a *x+ b) ⊗ (c *x+ d)
      = x* (x* (a ⊗ c))
     ⊕ x* ((a ⊗ coeff d)
     ⊕ (c ⊗ coeff b))
     ⊕ coeff (b ⊗ d)
  infixr 6 _⊗_


  open import Data.Fin
    using (Fin; suc; zero)

  data Syn (n : ℕ) : Set where
    var : Fin n → Syn n
    con : 𝔸 → Syn n
    _:+_ : Syn n → Syn n → Syn n
    _:*_ : Syn n → Syn n → Syn n
  infixr 5 _:+_
  infixr 6 _:*_

  ⟦_⟧ : Syn n → (Fin n → 𝔸) → 𝔸
  ⟦ var v ⟧  vs = vs v
  ⟦ con c ⟧  vs = c
  ⟦ x :+ y ⟧ vs = ⟦ x ⟧ vs + ⟦ y ⟧ vs
  ⟦ x :* y ⟧ vs = ⟦ x ⟧ vs * ⟦ y ⟧ vs

  open import Function using (_∘_)

  to-var : Fin n → HNF n
  to-var zero = x* 1H
  to-var (suc x) = coeff (to-var x)

  normalize : Syn n → HNF n
  normalize (var x) = to-var x
  normalize (con x) = ↪ x
  normalize (x :+ b) = normalize x ⊕ normalize b
  normalize (x :* b) = normalize x ⊗ normalize b

  eval : (Fin n → 𝔸) → HNF n → 𝔸
  eval v (const a) = a
  eval v (coeff a) = eval (v ∘ suc) a
  eval v (a *x+ b) = v zero * eval v a + eval (v ∘ suc) b

  eval-↪ : (f : Fin n → 𝔸) → (a : 𝔸) → eval f (↪ a) ≡ a
  eval-↪ {zero} f a = refl
  eval-↪ {suc n} f a = eval-↪ (f ∘ suc) a

  eval-to-var : (f : Fin n → 𝔸) → (x : Fin n) → eval f (to-var x) ≡ f x
  eval-to-var f zero
    rewrite eval-↪ (f ∘ suc) 0#
    rewrite eval-↪ (f ∘ suc) 1#
    rewrite *-identityʳ (f zero)
      = +-identityʳ (f zero)
  eval-to-var f (suc x) = eval-to-var (f ∘ suc) x

  postulate
    …algebra… : {x y : 𝔸} → x ≡ y
    …via… : {B : Set} {x y : 𝔸} → B → x ≡ y

  open ≡-Reasoning

  eval-coeff : (f : Fin (suc n) → 𝔸) → (h : HNF n) → eval f (coeff h) ≡ eval (f ∘ suc) h
  eval-coeff f a = refl

  eval-⊕ : (f : Fin n → 𝔸) → (a b : HNF n) → eval f (a ⊕ b) ≡ eval f a + eval f b
  eval-⊕ f (const a) (const b) = refl
  eval-⊕ f (coeff a) (coeff b) = eval-⊕ (f ∘ suc) a b
  eval-⊕ f (coeff a) (b *x+ c)
    rewrite eval-⊕ (f ∘ suc) a c = begin
      f zero * eval f b + eval f' a + eval f' c
    ≡⟨ …algebra… ⟩
      eval f' a + f zero * eval f b + eval f' c
    ∎
    where f' = f ∘ suc
  eval-⊕ f (a *x+ b) (coeff c)
    rewrite eval-⊕ (f ∘ suc) b c = sym (+-assoc _ _ _)
  eval-⊕ f (a *x+ b) (c *x+ d)
    rewrite eval-⊕ f a c
    rewrite eval-⊕ (f ∘ suc) b d = begin
      f zero * (eval f a + eval f c)
        + (eval f' b + eval f' d)
    ≡⟨ …algebra… ⟩
      (f zero * eval f a + eval f' b)
        + f zero * eval f c + eval f' d
    ∎
    where f' = f ∘ suc

  eval-x* : (f : Fin (suc n) → 𝔸) → (h : HNF (suc n)) → eval f (x* h) ≡ f zero * eval f h
  eval-x* f (coeff a) =
    begin
      f zero * eval f' a + eval f' (↪ 0#)
    ≡⟨ cong ((f zero * eval f' a) +_) (eval-↪ f' 0#) ⟩
      f zero * eval f' a + 0#
    ≡⟨ +-identityʳ _ ⟩
      f zero * eval f' a
    ∎
    where
      f' = f ∘ suc
  eval-x* f (a *x+ b) =
    begin
      f zero * (f zero * eval f a + eval f' b) + eval f' (↪ 0#)
    ≡⟨ cong (f zero * (f zero * eval f a + eval f' b) +_) (eval-↪ f' 0#) ⟩
      f zero * (f zero * eval f a + eval f' b) + 0#
    ≡⟨ +-identityʳ _ ⟩
      f zero * (f zero * eval f a + eval f' b)
    ∎
    where
      f' = f ∘ suc

  eval-⊗ : (f : Fin n → 𝔸) → (b c : HNF n) → eval f (b ⊗ c) ≡ eval f b * eval f c
  eval-⊗ f (const a) (const b) = refl
  eval-⊗ f (coeff a) (coeff b) = eval-⊗ (f ∘ suc) a b
  eval-⊗ f (coeff a) (b *x+ c)
    rewrite eval-⊗ f (coeff a) b
    rewrite eval-⊗ (f ∘ suc) a c =
      begin
        f zero * eval f' a * eval f b + eval f' a * eval f' c
      ≡⟨ …algebra… ⟩
        eval f' a * f zero * eval f b + eval f' a * eval f' c
      ≡⟨ sym (*-distribˡ-+ _ _ _) ⟩
        eval f' a * (f zero * eval f b + eval f' c)
      ∎
    where
      f' = f ∘ suc
      open ≡-Reasoning
  eval-⊗ f (a *x+ b) (coeff c)
    rewrite eval-⊗ (f ∘ suc) b c
    rewrite eval-⊗ f a (coeff c) =
      begin
        f zero * eval f a * eval f' c + eval f' b * eval f' c
      ≡⟨ …algebra… ⟩
        (f zero * eval f a) * eval f' c + eval f' b * eval f' c
      ≡⟨ sym (*-distribʳ-+ _ _ _) ⟩
        (f zero * eval f a + eval f' b) * eval f' c
      ∎
    where
      f' = f ∘ suc
      open ≡-Reasoning
  eval-⊗ f (a *x+ b) (c *x+ d) =
    begin
      v * (↓ (x* (a ⊗ c) ⊕ a ⊗ coeff d ⊕ c ⊗ coeff b)) + ↓' (↪ 0# ⊕ ↪ 0# ⊕ b ⊗ d)
    ≡⟨ …algebra… ⟩
      v * (↓ (x* (a ⊗ c) ⊕ a ⊗ coeff d ⊕ c ⊗ coeff b)) + ↓' (b ⊗ d)
    ≡⟨ …via… (eval-⊕ f) ⟩
      v * (↓ (x* (a ⊗ c)) + ↓ (a ⊗ coeff d ⊕ c ⊗ coeff b)) + ↓' (b ⊗ d)
    ≡⟨ …via… (eval-⊕ f) ⟩
      v * (↓ (x* (a ⊗ c)) + ↓ (a ⊗ coeff d) + ↓ (c ⊗ coeff b)) + ↓' (b ⊗ d)
    ≡⟨ …via… (eval-⊗ f a (coeff d)) ⟩
      v * (↓ (x* (a ⊗ c)) + ↓ a * ↓ (coeff d) + ↓ (c ⊗ coeff b)) + ↓' (b ⊗ d)
    ≡⟨ …via… (eval-coeff f d) ⟩
      v * (↓ (x* (a ⊗ c)) + ↓ a * ↓' d + ↓ (c ⊗ coeff b)) + ↓' (b ⊗ d)
    ≡⟨ …algebra… ⟩ -- …via… (eval-⊗ f c (coeff b)) ⟩
      v * (↓ (x* (a ⊗ c)) + ↓ a * ↓' d + ↓ c * ↓ (coeff b)) + ↓' (b ⊗ d)
    ≡⟨ …via… (eval-coeff f b) ⟩
      v * (↓ (x* (a ⊗ c)) + ↓ a * ↓' d + ↓ c * ↓' b) + ↓' (b ⊗ d)
    ≡⟨ …via… (eval-⊗ f' b d) ⟩
      v * (↓ (x* (a ⊗ c)) + ↓ a * ↓' d + ↓ c * ↓' b) + ↓' b * ↓' d
    ≡⟨ …via… (eval-x* f (a ⊗ c)) ⟩
      v * (v * ↓ (a ⊗ c) + ↓ a * ↓' d + ↓ c * ↓' b) + ↓' b * ↓' d
    ≡⟨ …via… (eval-⊗ f a c) ⟩
      v * (v * ↓ a * ↓ c + ↓ a * ↓' d + ↓ c * ↓' b) + ↓' b * ↓' d
    ≡⟨ …algebra… ⟩
      v * v * ↓ a * ↓ c + v * ↓ a * ↓' d + v * ↓ c * ↓' b + ↓' b * ↓' d
    ≡⟨ …algebra… ⟩
      (v * ↓ a) * (v * ↓ c) + v * ↓ a * ↓' d +  v * ↓ c * ↓' b + ↓' b * ↓' d
    ≡⟨ …algebra… ⟩
      (v * ↓ a) * (v * ↓ c)  + ↓' b * v * ↓ c   + v * ↓ a * ↓' d + ↓' b * ↓' d
    ≡⟨ …algebra… ⟩
      ((v * ↓ a) * (v * ↓ c) + ↓' b * (v * ↓ c)) + v * ↓ a * ↓' d + ↓' b * ↓' d
    ≡⟨ …algebra… ⟩
      ((v * ↓ a) * (v * ↓ c) + ↓' b * (v * ↓ c)) + (v * ↓ a * ↓' d + ↓' b * ↓' d)
    ≡⟨ …via… *-distribʳ-+ ⟩
      ((v * ↓ a) * (v * ↓ c) + ↓' b * (v * ↓ c)) + (v * ↓ a + ↓' b) * ↓' d
    ≡⟨ cong (_+ ((v * ↓ a + ↓' b) * ↓' d)) (sym (*-distribʳ-+ _ _ _)) ⟩
      (v * ↓ a + ↓' b) * (v * ↓ c) + (v * ↓ a + ↓' b) * ↓' d
    ≡⟨ sym (*-distribˡ-+ _ _ _) ⟩
      (v * ↓ a + ↓' b) * (v * ↓ c + ↓' d)
    ∎
    where
      f' = f ∘ suc
      ↓ = eval f
      ↓' = eval f'
      v = f zero


  eval-normalize : (f : Fin n → 𝔸) → (s : Syn n) → eval f (normalize s) ≡ ⟦ s ⟧ f
  eval-normalize f (var a) = eval-to-var f a
  eval-normalize f (con a) = eval-↪ f a
  eval-normalize f (s :+ s₁)
    rewrite eval-⊕ f (normalize s) (normalize s₁)
    rewrite eval-normalize f s
    rewrite eval-normalize f s₁ = refl
  eval-normalize f (s :* s₁)
    rewrite eval-⊗ f (normalize s) (normalize s₁)
    rewrite eval-normalize f s
    rewrite eval-normalize f s₁ = refl


  open import Data.Vec using (Vec; []; _∷_; map; lookup)

  fins : Vec (Fin n) n
  fins {zero} = []
  fins {suc n} = zero ∷ map suc fins

  vars : Vec (Syn n) n
  vars = map var fins

  solve₀
      : (n : ℕ)
      → (x y : Vec (Syn n) n → Syn n)
      → normalize (x vars) ≡ normalize (y vars)
      → (v : Vec 𝔸 n)
      → ⟦ x vars ⟧ (lookup v) ≡ ⟦ y vars ⟧ (lookup v)
  solve₀ n x y x=y v = begin
    ⟦ x vars ⟧ f                 ≡⟨ sym (eval-normalize f (x vars)) ⟩
    eval f (normalize (x vars))  ≡⟨ cong (eval f) x=y ⟩
    eval f (normalize (y vars))  ≡⟨ eval-normalize f (y vars) ⟩
    ⟦ y vars ⟧ f                 ∎
    where
      f = lookup v

  open import Data.Product
    using (_×_)
    renaming ( proj₁ to lhs
             ; proj₂ to rhs
             ; _,_ to _:=_
             ) public

  N-ary : (n : ℕ) → (A : Set) → (Vec A n → Set) → Set
  N-ary zero A B = B []
  N-ary (suc n) A B = (a : A) → N-ary n A (B ∘ (a ∷_))

  N-ary′ : ℕ → Set → Set → Set
  N-ary′ n A B = N-ary n A (λ _ → B)

  _$ⁿ_ : {n : ℕ} → {A : Set} → {B : Vec A n → Set} → N-ary n A B → ((v : Vec A n) → B v)
  _$ⁿ_ {zero} f [] = f
  _$ⁿ_ {suc n} f (x ∷ v) = _$ⁿ_ (f x) v

  curryⁿ : {n : ℕ} → {A : Set} → {B : Vec A n → Set} → ((v : Vec A n) → B v) → N-ary n A B
  curryⁿ {zero} x = x []
  curryⁿ {suc n} x a = curryⁿ (x ∘ (a ∷_))

  solve
      : (n : ℕ)
      → (eq : N-ary′ n (Syn n) (Syn n × Syn n))
      → (let x := y = eq $ⁿ vars {n})
      → normalize x ≡ normalize y
      → N-ary n 𝔸 (λ v → ⟦ x ⟧ (lookup v) ≡ ⟦ y ⟧ (lookup v))
  solve n eq x=y =
    let x := y = eq $ⁿ vars {n}
     in curryⁿ (solve₀ n (λ _ → x) (λ _ → y) x=y)

open import Data.Nat

open import Data.Vec using ([]; _∷_)

open Solver 0 1 _+_ _*_
open import Relation.Binary.PropositionalEquality



test : (a b : ℕ) → a * (5 * a + b) + b * b ≡ b * b + (a * 5 * a + a * b)
test a b =
  solve 2 (λ x y → x :* ((con 5 :* x) :+ y) :+ (y :* y)
                := y :* y :+ (x :* con 5) :* x :+ x :* y )
    refl a b
```



