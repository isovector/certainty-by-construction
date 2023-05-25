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
adoption, but thankfully, there are workarounds for those willing to plumb
deeper into the depths of the theory.

Recall that when we were implementing `def:*-cong₂-mod`, that is, `def:cong` for
modular arithmetic, we built a lot of setoid machinery and reasoning to avoid
needing to solve these large proofs by hand. The particular problem here was
attempting to solve the following equation:

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
 & ac + (cx + az + xzn) * n \\
=& ac + cxn + azn + xznn \\
=& c * (a + xn) + azn + xznn \\
=& c * (a + xn) + zn * (a + xn) \\
=& c * (b + yn) + zn * (b + yn) \\
=& cb + cyn + zn * (b + yn) \\
=& cb + cyn + znb + zynn \\
=& cb + znb + cyn + zynn \\
=& b * (c + zn) + cyn + zynn \\
=& b * (c + zn) + yn * (c + zn) \\
=& b * (d + wn) + yn * (d + wn) \\
=& bd + bwn + yn * (d + wn) \\
=& bd + bwn + dyn + ywnn \\
=& bd + dyn + bwn + ywnn \\
=& bd + (dyn + bwn + ywnn) \\
=& bd + (dy + bw + ywn) * n
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


## Rings

The ring solver is a general purpose tool for automatically reasoning about
rings. *Rings* are algebraic structures which generalize the relationships
between addition and multiplication. A ring has an associative, commutative
binary operation called "addition" and an associative, commutative binary
operation called "multiplication." These operations need not correspond in any
semantic way to the things we think of as being addition and multiplication,
merely it's just they need to properly fit into the "ecosystem niche" that
regular addition and multiplication do.

What does this mean? A ring must also have distinguished elements 0 and 1 that
behave like you'd expect with respect to addition and multiplication, namely
that we have the following pile of equalities: `def:+-identityˡ`,
`def:+-identityʳ`, `def:*-identityˡ`, `def:*-identityʳ`, `def:*-zeroˡ`,
`def:*-zeroʳ`, `def:+-comm`, `def:*-comm`, `def:+-assocˡ`, `def:+-assocʳ`,
`def:*-assocˡ`, `def:*-assocʳ`, `def:*-distribˡ-+`, and `def:*-distribʳ-+`. As
you can see, there is a great deal of structure inherent in a ring!

But, this is just the structure required of a *semiring*. In order to get the
full *ring*, we require an additive inverse operation analogous to
unary negation, with the property that for any $a$ we have $a + -a = 0$.

By virtue of generalizing addition and multiplication, addition and
multiplication themselves had better form a ring! And indeed they do. Note that
however, the natural numbers don't have any additive inverses, and so they can
at best be semirings. Integers, however, weaken this constraint, and are fully
realizable as rings.

Rings occupy an excellent space in the mathematical hierarchy, corresponding to
the sort of algebraic reasoning that is required in grade-school, at least,
that subset before fractions are introduced. Given our extreme familiarity with
arithmetic over rings, it is the sort of reasoning that comes up everywhere in
mathematics. And what's better is that, given we expect children to be able to
solve it, there exists an algorithm for determining the equivalence of two
expressions over the same ring.

In this chapter, we will get a feel for using Agda's ring solver to tackle
problems, and then dive in more deeply to see exactly how it works by
implementing our own version.


## Agda's Ring Solver

Agda's standard library comes with a *ring solver*, which is a series of tools
for automatically solving equalities over rings. Of course, calling it a *ring*
solver is a bit of a misnomer, since the ring solver works over semirings as
well, due to a subtle weakening of required ring structure. However, these
details are irrelevant to today's discussion; all you need to keep in mind is
that the ring solver works over any commutative semiring in addition to rings
themselves.

The ring solver machinery exists in the standard library under
`module:Algebra.Solver.Ring.Simple`, but many specialized versions are present.
For example, the (semi)ring solver for the natural numbers is squirreled away
under `module:Data.Nat.Solver`. We can pull it into scope, and get access to the
solver itself by subsequently opening `module:+-*-Solver`:


```agda
module Example-Nat-Solver where
  open import Data.Nat.Solver
  open +-*-Solver
```

Of course, we'd like the naturals themselves in scope, so we have something to
prove about:

```agda
  open import Data.Nat
```

In our pen and paper example above, we did a lot of work to show the equality of
$ac + (cx + az + xzn) \times n$ and $c \times (a + xn) + zn \times (a + xn)$.
Let's prove this with the ring solver. We can start with the type, which already
is quite gnarly:

```agda
  open import Relation.Binary.PropositionalEquality

  -- TODO(sandy): these work, but are make interactive editing slow
  -- uncomment them when done
  -- lemma₁
  --     : (a c n x z : ℕ)
  --     → a * c + (c * x + a * z + x * z * n) * n
  --     ≡ c * (a + x * n) + z * n * (a + x * n)
```

Inside of `module:+-*-Solver` is `def:solve`, which is our front-end for
invoking the ring solver. The type of `def:solve` is a dependent nightmare, but
we can give its arguments informally:

1. `type:n : ℕ`: the number of variables that exist in the expression.
2. A function from `n` variables to a *syntactic* representation of the
   expression you'd like solved.
3. A proof that the two expressions have the same normal form. This is almost
   always simply `ctor:refl`.
4. `n` more arguments, for the specific values of the variables.

In `def:lemma₁` we have five variables (`a`, `c`, `n`, `x`, and `z`), and so our
first argument to `solve` should be `5`.

Next we need to give a function which constructs the syntax of the equality
we're trying to show. In general this means replacing `type:_≡_` with
`def:_:=_`, `def:_+_` with `def:_:+_`, `def:_*_` with `def:_:*_`, and any
constant `k` with `def:con` `k`. The variables you receive from the function can
be used without any adjustment.

Thus the full implementation of `def:lemma₁` is:

```agda
  -- lemma₁ = solve 5
  --   (λ a c n x z
  --       →  a :* c :+ (c :* x :+ a :* z :+ x :* z :* n) :* n
  --       := c :* (a :+ x :* n) :+ z :* n :* (a :+ x :* n)
  --   ) refl
```

It's certainly not the most beautiful sight to behold, but you must admit that
it's much better than proving this tedious fact by hand.

The syntactic equality term we must build in the big lambda here is a curious
thing. What exactly is going on here? This happens to be a quirk of the
implementation of the solver, but it's there for a good reason. Recall that our
"usual" operations (that is, `def:_+_` and `def:_*_` and, in general values that
work over `ℕ`) are computational objects; Agda will compute and reduce them if
it is able to do so, and will make these rewrites regardless of what you
actually write down.

This syntax tree is an annoying thing to write, but is necessary to help the
ring solver know what it's trying to solve. Remember, just because we've written
out this expression with full syntax here doesn't mean this is the term Agda is
working on! Agda is free to expand definitional equalities, meaning it might
have already reduced some of these additions and multiplications away!

But when you think about solving these sorts of equations on paper, what you're
actually doing is working with the syntax, and not actually computing in any
real sense. The algorithm to solve equations is to use a series of syntactic
rewrite rules that allow us to move symbolic terms around, without ever caring
about the computational properties of those symbolic terms.

Thus, the lambda we need to give to `def:solve` is a concession to this fact;
we'd like Agda to prove, *symbolically,* that the two terms are equivalent,
without requiring any computation of the underlying terms in order to do so. And
in order to do so, we must explicitly tell Agda what the symbolic equation is,
since all it has access is to is some stuck value that exists in the theory of
Agda, rather than in the theory of the ring itself.

This duplication between the Agda expression of the term and the symbolic
version of the same is regrettable. Are we doomed to write them both, every
time? Thankfully not.


## Tactical Solving

Agda has a powerful *macro* system, which, in full glory, is beyond the scope of
this book. However, at a high level, the macro system allows regular Agda
programs to access the typechecker. This is a tremendous (if fragile)
superpower, and allows programmers to do all sorts of unholy things. One such
capability is to use the type currently expected by Agda in order to synthesize
values at compile time. Another, is to syntactically inspect an Agda expression
at compile time. Together, these features can be used to automatically derive
the symbolic form required for doing ring solving.

To illustrate broadly how this works, we can write code of this form:

```snippet
    a + (x + z) * n      ≡⟨ ? ⟩
    (a + x * n) + z * n
```

Agda knows that the type of the hole must be `type:a + (x + z) * n ≡ (a + x * n)
+ z * n`, and if we were to put a macro in place of the hole, that macro can
inspect the type of the hole. It can then perform all of the necessary
replacements (turning `def:_+_` into `def:_:+_` and so on) in order to write the
ring-solving symbolic lambda for us. All that is left to do is to tell the
solver which variables we'd like to use, by sticking them in a list.

We can demonstrate all of this by implementing `def:≈-trans` again. This time,
the tactical ring solver is found in `module:Data.Nat.Tactic.RingSolver`, and
requires lists to be in scope as well:

```agda
module Example-Tactical where
  open import Data.Nat.Tactic.RingSolver
  open import Data.List
    using ([]; _∷_)
```

We can then show `def:≈-trans`:

```agda
  -- open import Data.Nat
  -- open import Relation.Binary.PropositionalEquality

  -- ≈-trans
  --     : (a b c n x y z w : ℕ)
  --     → a + x * n ≡ b + y * n
  --     → b + z * n ≡ c + w * n
  --     → a + (x + z) * n ≡ c + (w + y) * n
  -- ≈-trans a b c n x y z w pxy pzw = begin
  --   a + (x + z) * n      ≡⟨ solve (a ∷ x ∷ z ∷ n ∷ []) ⟩
  --   (a + x * n) + z * n  ≡⟨ cong (_+ z * n) pxy ⟩
  --   (b + y * n) + z * n  ≡⟨ solve (b ∷ y ∷ n ∷ z ∷ []) ⟩
  --   (b + z * n) + y * n  ≡⟨ cong (_+ y * n) pzw ⟩
  --   c + w * n + y * n    ≡⟨ solve (c ∷ w ∷ n ∷ y ∷ []) ⟩
  --   c + (w + y) * n      ∎
  --   where open ≡-Reasoning
```

The `macro:solve` macro only works for terms of type `type:x ≡ y`, which means
it can't be used to show parameterized properties, like `def:lemma₁` earlier.
For that, we can instead invoke `macro:solve-∀`:


```agda
  -- lemma₁
  --     : (a c n x z : ℕ)
  --     → a * c + (c * x + a * z + x * z * n) * n
  --     ≡ c * (a + x * n) + z * n * (a + x * n)
  -- lemma₁ = solve-∀
```

As you can see, ring solving is an extremely powerful technique, capable of
automating away hours of tedious proof work. But where does these magical powers
come from? How can this possibly work? We will use the remainder of this chapter
to explore that question, implementing our own ring solver in the process.


## The Pen and Paper Algorithm

The question is --- how does any of this work? Is it built-in to the compiler,
or is it something we could have written for ourselves? Fascinatingly, the
answer is the latter. It's the sort of thing we can build for ourselves, which
we will explore now.

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
is a strong indication that you have internalized the polynomial canonical
form---whether or not you were aware of it.

Given the existence of canonical forms, we can now reduce the problem of proving
ring equality to be:

1. Prove both terms are equal to their canonical form.
2. Compare the canonical forms.
3. If the canonical forms match, compose the earlier proofs.

This is a powerful, widely-useful technique, and you would do well to add it to
your toolbox. Let's stop for a quick illustration of the idea in action. We'd
like to prove that $(x + 1)(x - 1)$ is equal to $x(1 + x) + 1 - x - 2$. The first step
is to reduce each to normal form:

$$
\begin{aligned}
(x + 1)(x - 1) &= x(x + 1) - 1(x + 1) \\
&= x^2 + x - 1(x + 1) \\
&= x^2 + x - x - 1 \\
&= x^2 - 1
\end{aligned}
$$

and

$$
\begin{aligned}
x(1+x) + 1 - x - 2 &= x + x^2 + 1 - x - 2 \\
&= x^2 + x - x + 1 - 2 \\
&= x^2 + 1 - 2 \\
&= x^2 - 1
\end{aligned}
$$

These expressions do in fact have the same normal form, and thus they are equal
to one another, which we can show simply by composing the two proofs:

$$
\begin{aligned}
(x + 1)(x - 1) &= x(x + 1) - 1(x + 1) \\
&= x^2 + x - 1(x + 1) \\
&= x^2 + x - x - 1 \\
&= x^2 - 1 \\
&= x^2 + 1 - 2 \\
&= x^2 + x - x + 1 - 2 \\
&= x + x^2 + 1 - x - 2 \\
&= x(1+x) + 1 - x - 2
\end{aligned}
$$

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

which is to say, we can always move the additions to be the outermost nodes in
the expression tree. Similarly, multiplication is commutative, we can freely
group together all of the same elements of the group. So, we can happily combine
the two $x$s in

$$
xyx = xxy = x^2y
$$

Finally, the commutativity of addition means we can reorder the outermost terms.
This allows us to sort the terms by their descending powers of $x$. This
collection of transformations clearly allows us to put any polynomial of one
variable into normal form. It's not immediately clear how the approach
generalizes to polynomials in multiple variables, but as we will see in a
moment, there is a very elegant trick that ties everything together.

Describing the canonical form in such detail also gives us an insight into why
we have ring solvers but not semigroup solvers. Semigroups, having only a
single, associative binary operator, simply don't have enough algebraic
structure to require interesting proofs. If your semigroup is commutative
("Abelian," in the jargon) then you can simply reorder all the terms so they
appear in a row. It's exactly the interplay between addition and multiplication
that makes the problem at all interesting.


## Horner Normal Form

In order to put a polynomial into normal form, we must have an technique for
doing so. Of course, we could just write a function that fiddles with an
expression tree until it is in normal form, but, in general, it's very difficult
to prove the correctness of "fiddling." A much better technique is to build a
type which is guaranteed to be in the desired form, and then write a
function that produces something of that type.

The natural representation of this normal form is a list of coefficients. If we
have $x^2+5x-3$, we can use `-3 ∷ 5 ∷ 1 ∷ []` as our normal form. Why in
reversed order, you might ask? Because we don't know what the biggest power in
the polynomial is until we reach the end. For the sake of easier bookkeeping, if
we store our powers as little endian, we can ensure that like terms are
always in the same place in the list. That is, adding $x^2+5x-3$ to $2x+2$ is
much easier to do when the lists are stored in little endian instead of big
endian!

While lists are the right intuition, they are not exactly right for our use
case, as they don't scale well to multiple variables. Instead, we look to a very
similar idea called *Horner's method* which expresses polynomial in a slightly
different form. Rather than writing $x^2+5x-3$, we instead write:

$$
(1x + 5)x - 3
$$

in *Horner normal form* (henceforth HNF.) Here, every expression in HNF is
either a constant `𝔸 → HNF`, or it is of the form `HNF → 𝔸 → HNF`. We can
express this as a data type:

```agda
module Sandbox-Univariate-HNF (𝔸 : Set) where
  data HNF : Set where
    coeff : 𝔸 → HNF
    _*x+_ : HNF → 𝔸 → HNF
```

Looking at this, what we really have is a non-empty snoc list under a different
guise. Despite its name, `HNF` is not truly a normal form, since we have
infinitely many ways of expressing any given term, simply by padding it with a
zero for its next power:

```agda
  postulate
    0# : 𝔸

  nonunique : HNF → HNF
  nonunique (coeff a) = coeff 0# *x+ a
  nonunique (a *x+ b) = nonunique a *x+ b
```

This is regrettable, but a very difficult thing to solve at the level of types.
Agda's real ring solver performs a normalization stage after every computation
to remove any highest-order zero powers, but this adds a great deal of
complexity. Since we are only putting together a toy example, we will not
concern ourselves with this problem, but do keep in mind its presence.

Horner normal form is desirable for computation since it gives rise to an
interpretation into `𝔸` directly, via:

```agda
  postulate
    _+_ : 𝔸 → 𝔸 → 𝔸
    _*_ : 𝔸 → 𝔸 → 𝔸

  eval : 𝔸 → HNF → 𝔸
  eval x (coeff a) = a
  eval x (a *x+ b) = (eval x a * x) + b
```

This requires only $O(n)$ multiplications of $x$, where $n$ is the highest power
in the polynomial. Compare that to the naive version in which you compute $x^3$
as `x * x * x`, which requires $O(n^2)$ multiplications.


## Multivariate Polynomials

All of our original examples of using ring solvers involved polynomial in
multiple variables; recall `def:lemma₁` which was a polynomial in five
variables. Clearly multivariate polynomials are important to actually getting
work done, and thus we must determine a means of encoding them.

The trick is both delightful and simple. In all of our analyses above, we
discussed how coefficients play into the thing, without explicitly defining what
these coefficients were. Based on our experience with single-variable
polynomials, we took for granted that the coefficients must be ring elements,
but this is not a necessity.

We can recover multivariate polynomials by instead insisting that our
coefficients be polynomials in a different variable. That is, we could express
the polynomial $x^2+y^2+xy+y+5x-3$ as $x^2+(y + 5)x+(y - 3)$. This technique
generalizes to any number of variables, simply by sticking another polynomial on
$z$ in as the coefficients on $y$ for example.

Let's start our actual ring solver module in order to explore this idea. Since
we would like eventual computational properties, we will add the bare minimum
structure on `𝔸` as parameters to our module.

```agda
module Sandbox-RingSolver {𝔸 : Set}
    (0# 1# : 𝔸)
    (_+_ _*_ : 𝔸 → 𝔸 → 𝔸)
    -- TODO(sandy): explain this let binding
    (let infixr 5 _+_; _+_ = _+_)
    (let infixr 6 _*_; _*_ = _*_) where
```

We will require many algebraic definitions to be in scope:

```agda
  open import Relation.Binary.PropositionalEquality

  module _ {A : Set} where
    open import Algebra.Definitions {A = A} _≡_ public
```

Encoding our multivariate HNF in Agda isn't too tricky; though admittedly the
resulting syntax leaves much to be desired. We can parameterize `HNF` by a
natural corresponding to how many distinct variables it has. Anywhere before we
used `HNF` we now use `HNF (suc n)`, and anywhere we used a scalar `𝔸` we
instead use `HNF n`.

```agda
  open import Data.Nat
    using (ℕ; zero; suc)

  private variable
    n : ℕ

  data HNF : ℕ → Set where
    const : 𝔸 → HNF zero
    coeff : HNF n → HNF (suc n)
    _*x+_ : HNF (suc n) → HNF n → HNF (suc n)
```

Notice that we have also added `ctor:const` in order to build polynomial in zero
variables, which corresponds to sticking in scalar values.

This representation works perfectly well, but requires a little alertness when
constructing its terms by hand. To take a concrete example, if we are working
with an `type:HNF 2`---a polynomial in two variables, call them $a$ and $b$---then
the `ctor:_*x+_` constructor is used to construct both the $a$ and $b$ univariate
polynomials! For example, we would write $a^2+ab+b^2$ as:

```agda
  a²+ab+b² : HNF 2
  a²+ab+b² =
    ( coeff (coeff (const 1#))
        *x+  -- x = a
          coeff (const 1#)
    ) *x+ (  -- x = a
      (coeff (const 1#)
        *x+  -- x = b
          const 0#
      ) *x+  -- x = b
          const 0#)
```

Here, `ctor:_*x+_` refers both to $a$ and to $b$, depending on its type (which
itself depends on the constructor's position in the tree.) As you can see, it is
no great joy to construct `type:HNF` terms by hand! Thankfully, we won't need
to, and will instead use `type:HNF` as a sort of "compilation target" for other
operations.


## Building a Semiring over HNF

The idea of `type:HNF` is that it is a particular encoding of polynomials.
Therefore, we should expect to be able to do anything with `type:HNF` that we
could do with polynomials encoded some other way. Furthermore, by virtue of it
being a normal form, we expect all of these operations to be *closed*---meaning,
if you combine two `type:HNF`s, you should always get back another `type:HNF`.

For example, we can implement addition over `type:HNF`s simply by adding like
terms:

```agda
  _⊕_ : HNF n → HNF n → HNF n
  const a ⊕ const b = const (a + b)
  coeff a ⊕ coeff b = coeff (a ⊕ b)
  coeff a ⊕ (b *x+ c) = b *x+ (a ⊕ c)
  (a *x+ b) ⊕ coeff c = a *x+ (b ⊕ c)
  (a *x+ b) ⊕ (c *x+ d) = (a ⊕ c) *x+ (b ⊕ d)
  infixr 5 _⊕_
```

Does this really implement addition, you might be wondering? And if so,
congratulations, you've acquired the correct mindset: that we should demand
proof for anything as complicated as this. Don't worry, we will prove that
`def:_⊕_` does in fact implement addition, although first we need to figure out
exactly how to formally phrase that question.

Another thing we'd like to be able to do is inject scalars directly into a
polynomial, rather than faffing about with big chains of `ctor:coeff` in order
to stick in a `ctor:const`. This is given by `def:↪`:

```agda
  ↪ : 𝔸 → HNF n
  ↪ {zero} a = const a
  ↪ {suc n} a = coeff (↪ a)
```

We can now lift `0#` and `1#` into any polynomial simply by injecting them:

```agda
  0H : HNF n
  0H = ↪ 0#

  1H : HNF n
  1H = ↪ 1#
```

Working our way towards multiplication over `type:HNF`, we will first need one last
piece in place---a helper function for multiplying by the current variable.

```agda
  x* : HNF (suc n) → HNF (suc n)
  x* a = a *x+ 0H
```

Note the type here; this is necessarily a function over `type:HNF (suc n)`,
since there are no variables to multiply when dealing with `type:HNF zero`.

We are now ready to implement `def:_⊗_`, which takes advantage of the well-known
foiling rule that $(ax+b)(cx+d) = acx^2 + acd + bcx + bd$.

```agda
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
```

We have now implemented `def:0H`, `def:1H`, `def:_⊕_` and `def:_⊗_` which are
all of the necessary moving pieces for a semiring. We could construct a
fully-blown ring instead by requiring a negation operation over `𝔸`, and closing
`type:HNF` over this operation as well, but that is left as an exercise to the
dedicated reader.


## Semantics

In order to prove that addition and multiplication do what they say on the tin,
we must give a *semantics* to `type:HNF`, in essence, giving a *specification*
for how they ought to behave. This is sometimes called a *denotation* or a
*model.*

Semantics are often given by a function into some other type. We saw a function
like this in our univariate example, in which we evaluated an `type:HNF` down to
a `𝔸`. We will do the same thing here, except that our new `def:eval` function
must take a mapping of variables to `𝔸`, which we can encode as a function `Fin
n → 𝔸`. Thus, we have:

```agda
  open import Function
    using (_∘_)
  open import Data.Fin
    using (Fin; zero; suc)

  eval : (Fin n → 𝔸) → HNF n → 𝔸
  eval v (const a) = a
  eval v (coeff a) = eval (v ∘ suc) a
  eval v (a *x+ b) = v zero * eval v a + eval (v ∘ suc) b
```

Given a model of `type:HNF`, we would now like to show that everything we've
built so far does in fact *preserve meaning,*  which is to say, addition in
`type:HNF` should correspond to addition over `𝔸`, and so on and so forth.
This mathematical property is known as a *homomorphism,*  which means "structure
preserving." The idea being that the homomorphism maps structure on one side to
equivalent structure on the other.

As a first example, we can give the type of nullary homomorphisms:

```agda

  Homomorphism₀ : HNF n → 𝔸 → Set
  Homomorphism₀ h a =
    ∀ v → eval v h ≡ a
```

and subsequently show that there exists a homomorphism between `↪ a : HNF n`
and `a : 𝔸`, as per `def:eval-↪`:

```agda
  eval-↪ : (a : 𝔸) → Homomorphism₀ {n} (↪ a) a
  eval-↪ {zero} a f = refl
  eval-↪ {suc n} a f = eval-↪ a (f ∘ suc)
```

There exist two special cases of `def:eval-↪`:

```agda
  eval-0H : Homomorphism₀ {n} 0H 0#
  eval-0H = eval-↪ 0#

  eval-1H : Homomorphism₀ {n} 1H 1#
  eval-1H = eval-↪ 1#
```

We also have two unary homomorphisms over `def:eval`, although their types are
tricky enough that we don't attempt to give a type synonym for them. The first
is that evaluation of a `ctor:coeff` term is equivalent to evaluating it having
dropped the current variable.

```agda
  eval-coeff
    : (f : Fin (suc n) → 𝔸)
    → (h : HNF n)
    → eval f (coeff h) ≡ eval (f ∘ suc) h
  eval-coeff f a = refl
```

and the other is that `def:to-var` (defined momentarily) simply evaluates to the
desired variable. First we will write `def:to-var`, which transforms a `type:Fin
n` into the corresponding variable in the correct coefficient space:

```agda
  to-var : Fin n → HNF n
  to-var zero = x* 1H
  to-var (suc x) = coeff (to-var x)
```

We would like to show that the evaluation of this term is equivalent to just
instantiating the correct variable. Constructing the homomorphism here requires
some of the semiring structure over `𝔸`, which we will postulate since we are
only making a toy example. In a real implementation, however, these postulates
should be required of whoever is instantiating the solver module.

```agda
  postulate
    +-identityʳ : RightIdentity 0# _+_
    *-identityʳ : RightIdentity 1# _*_

  eval-to-var
      : (f : Fin n → 𝔸)
      → (x : Fin n)
      → eval f (to-var x) ≡ f x
  eval-to-var f zero
    rewrite eval-0H (f ∘ suc)
    rewrite eval-1H (f ∘ suc)
    rewrite *-identityʳ (f zero)
      = +-identityʳ (f zero)
  eval-to-var f (suc x) = eval-to-var (f ∘ suc) x
```

There is a third unary homomorphism we'd like to show, namely that `def:x*` does
what it should.

```agda
  open ≡-Reasoning

  eval-x*
      : (f : Fin (suc n) → 𝔸)
      → (h : HNF (suc n))
      → eval f (x* h) ≡ f zero * eval f h
  eval-x* f (coeff a) =
    begin
      f zero * eval f' a + eval f' (↪ 0#)
    ≡⟨ cong ((f zero * eval f' a) +_) (eval-0H f') ⟩
      f zero * eval f' a + 0#
    ≡⟨ +-identityʳ _ ⟩
      f zero * eval f' a
    ∎
    where
      f' = f ∘ suc
  eval-x* f (a *x+ b) =
    let f' = f ∘ suc  -- ! 1
        ↓ = eval f
        ↓' = eval f' in
    begin
      f zero * (f zero * ↓ a + ↓' b) + ↓' (↪ 0#)
    ≡⟨ cong (f zero * (f zero * ↓ a + ↓' b) +_) (eval-0H f') ⟩
      f zero * (f zero * ↓ a + ↓' b) + 0#
    ≡⟨ +-identityʳ _ ⟩
      f zero * (f zero * ↓ a + ↓' b)
    ∎
```

Notice that at `ann:1` we have introduced a `keyword:let` binding in order to
give shorter names to common expressions that frequently occur in our proof.
This is a useful trick for managing the amount of mental capacity required to
work through a proof.

Now come the interesting pieces. We'd like to show two binary homomorphisms, one
from `def:_⊕_` to `def:_+_`, and another between `def:_⊗_`  and `def:_*_`.
First, we can give the definition of a binary homomorphism:

```agda
  Homomorphism₂ : (HNF n → HNF n → HNF n) → (𝔸 → 𝔸 → 𝔸) → Set
  Homomorphism₂ f g =
    ∀ v x₁ x₂ → eval v (f x₁ x₂) ≡ g (eval v x₁) (eval v x₂)
```

The details of these two homomorphisms are quite cursed. As my friend says,
"solvers are fun because they condense all the suffering into one place." The
idea is that we will take on all the pain of solving ring problems, and tackle
them once and for all. The result is hairy, to say the least. For the sake of
this book's length, we will not prove these two homomorphisms in their full
glory, instead we will sketch them out and leave the details for a particularly
motivated reader. To that extent, we will introduce two postulates which we will
use to hint the next step to the reader:

```agda
  postulate
    …algebra… : {x y : 𝔸} → x ≡ y
    …via… : {B : Set} {x y : 𝔸} → B → x ≡ y
```

Here, `def:…algebra…` suggests the next step follows by standard algebraic
tricks such as commutativity, associativity, or removing identities. Ironically,
this is the step that we'd expect a ring solver to be able to tackle for us.

Alternatively, we will use `def:…via…` to suggest that a `def:cong` needs to be
applied in order to massage the given proof term into the right place. Since
these expressions are exceptionally large, most of the work on these steps is
merely the construction of the `def:cong` target.

Anyway, in order to show the homomorphism for addition, we will require
`def:+-assoc`, which we again postulate, but in a real solver should instead be
brought in as part of the proof that `𝔸` is a (semi)ring in the first place.

```agda
  postulate
    +-assoc : Associative _+_

  eval-⊕ : Homomorphism₂ {n} _⊕_ _+_
  eval-⊕ f (const a) (const b) = refl
  eval-⊕ f (coeff a) (coeff b) = eval-⊕ (f ∘ suc) a b
  eval-⊕ f (coeff a) (b *x+ c)
    rewrite eval-⊕ (f ∘ suc) a c =
      begin
        f zero * eval f b + eval f' a + eval f' c
      ≡⟨ …algebra… ⟩
        eval f' a + f zero * eval f b + eval f' c
      ∎
    where f' = f ∘ suc
  eval-⊕ f (a *x+ b) (coeff c)
    rewrite eval-⊕ (f ∘ suc) b c =
      sym (+-assoc _ _ _)
  eval-⊕ f (a *x+ b) (c *x+ d)
    rewrite eval-⊕ f a c
    rewrite eval-⊕ (f ∘ suc) b d =
      begin
        f zero * (eval f a + eval f c)
          + (eval f' b + eval f' d)
      ≡⟨ …algebra… ⟩
        (f zero * eval f a + eval f' b)
          + f zero * eval f c + eval f' d
      ∎
    where f' = f ∘ suc
```

The real pain in writing a ring solver is in the homomorphism for
multiplication, which is presented here in a very sketched form. There are five
cases we need to look at, the first four of which are rather reasonable:

```agda
  postulate
    *-distribˡ-+ : _*_ DistributesOverˡ _+_
    *-distribʳ-+ : _*_ DistributesOverʳ _+_

  eval-⊗ : Homomorphism₂ {n} _⊗_ _*_
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
```

The final case, which multiplies `ctor:_*x+_` against `ctor:_*x+_`, is an
extremely nasty piece of work. Recall that in the definition of `def:_⊗_`, we
needed to invoke `def:x*` four times, `def:_⊕_` three times, and `def:_⊗_`
itself four times. Every instance of these uses requires an invocation of the
corresponding homomorphism, `def:cong`ed into the right place, and then
algebraically manipulated so that like terms can be grouped. This proof is no
laughing matter; remember, the ring solver coalesces all of the pain into one
place, and this is where it has accumulated.

```agda
  eval-⊗ f (a *x+ b) (c *x+ d) =
    let f' = f ∘ suc
        ↓ = eval f
        ↓' = eval f'
        v = f zero in
    begin
      v * (↓ (x* (a ⊗ c) ⊕ a ⊗ coeff d ⊕ c ⊗ coeff b))
        + ↓' (↪ 0# ⊕ ↪ 0# ⊕ b ⊗ d)
    ≡⟨ …algebra… ⟩
      v * (↓ (x* (a ⊗ c) ⊕ a ⊗ coeff d ⊕ c ⊗ coeff b))
        + ↓' (b ⊗ d)
    ≡⟨ …via… (eval-⊕ f) ⟩
      v * (↓ (x* (a ⊗ c)) + ↓ (a ⊗ coeff d ⊕ c ⊗ coeff b))
        + ↓' (b ⊗ d)
    ≡⟨ …via… (eval-⊕ f) ⟩
      v * (↓ (x* (a ⊗ c)) + ↓ (a ⊗ coeff d) + ↓ (c ⊗ coeff b))
        + ↓' (b ⊗ d)
    ≡⟨ …via… (eval-⊗ f a (coeff d)) ⟩
      v * (↓ (x* (a ⊗ c)) + ↓ a * ↓ (coeff d)
            + ↓ (c ⊗ coeff b))
        + ↓' (b ⊗ d)
    ≡⟨ …via… (eval-coeff f d) ⟩
      v * (↓ (x* (a ⊗ c)) + ↓ a * ↓' d + ↓ (c ⊗ coeff b))
        + ↓' (b ⊗ d)
    ≡⟨ …algebra… ⟩ -- …via… (eval-⊗ f c (coeff b)) ⟩
      v * (↓ (x* (a ⊗ c)) + ↓ a * ↓' d + ↓ c * ↓ (coeff b))
        + ↓' (b ⊗ d)
    ≡⟨ …via… (eval-coeff f b) ⟩
      v * (↓ (x* (a ⊗ c)) + ↓ a * ↓' d + ↓ c * ↓' b)
        + ↓' (b ⊗ d)
    ≡⟨ …via… (eval-⊗ f' b d) ⟩
      v * (↓ (x* (a ⊗ c)) + ↓ a * ↓' d + ↓ c * ↓' b)
        + ↓' b * ↓' d
    ≡⟨ …via… (eval-x* f (a ⊗ c)) ⟩
      v * (v * ↓ (a ⊗ c) + ↓ a * ↓' d + ↓ c * ↓' b)
        + ↓' b * ↓' d
    ≡⟨ …via… (eval-⊗ f a c) ⟩
      v * (v * ↓ a * ↓ c + ↓ a * ↓' d + ↓ c * ↓' b)
        + ↓' b * ↓' d
    ≡⟨ …algebra… ⟩
      ((v * ↓ a) * (v * ↓ c) + ↓' b * (v * ↓ c))
        + (v * ↓ a * ↓' d + ↓' b * ↓' d)
    ≡⟨ …via… *-distribʳ-+ ⟩
      ((v * ↓ a) * (v * ↓ c) + ↓' b * (v * ↓ c))
        + (v * ↓ a + ↓' b) * ↓' d
    ≡⟨ …via… *-distribʳ-+ ⟩
      (v * ↓ a + ↓' b) * (v * ↓ c) + (v * ↓ a + ↓' b) * ↓' d
    ≡⟨ sym (*-distribˡ-+ _ _ _) ⟩
      (v * ↓ a + ↓' b) * (v * ↓ c + ↓' d)
    ∎
```


## Sketching Out a Ring Solver

Next we will define the syntax for dealing with rings:

```agda
  -- infixr 5 _:+_
  -- infixr 6 _:*_

  -- data Syn : Set c where
  --   var : Syn
  --   con : A → Syn
  --   _:+_ : Syn → Syn → Syn
  --   _:*_ : Syn → Syn → Syn
```

And, just to show that this really is the syntax for our language, we can give
it semantics via `⟦_⟧`, which simply interprets the syntax as the actual ring
operations:

```agda
  -- ⟦_⟧ : Syn → A → A
  -- ⟦ var ⟧    v = v
  -- ⟦ con c ⟧  v = c
  -- ⟦ x :+ y ⟧ v = ⟦ x ⟧ v + ⟦ y ⟧ v
  -- ⟦ x :* y ⟧ v = ⟦ x ⟧ v * ⟦ y ⟧ v
```

Our next step is simply to give the semantics for `HNF`, completely analogously
to what we did for `Syn`:

```agda
  -- ⟦_⟧H : HNF → A → A
  -- ⟦ ⊘ ⟧H _ = 0#
  -- ⟦ a *x+ b ⟧H x = ⟦ a ⟧H x * x + b
```

We'd like to define a transformation from `Syn` into `HNF`, but that is going to
require addition and multiplication over `HNF`. Addition is straightforward:

```agda
  -- _+H_ : HNF → HNF → HNF
  -- ⊘ +H y = y
  -- (a *x+ b) +H ⊘ = a *x+ b
  -- (a *x+ b) +H (c *x+ d) = (a +H c) *x+ (b + d)

  -- infixl 5 _+H_
```

and multiplication isn't much more work, after we take advantage of the
algebraic fact that:

$$
(ax + b)(cx + d) = acx^2 + (bc + ad)x + bd
$$

```agda
  -- _*S_ : A → HNF → HNF
  -- k *S ⊘ = ⊘
  -- k *S (hnf *x+ x) = (k *S hnf) *x+ (k * x)
  -- infixl 6 _*S_

  -- _*H_ : HNF → HNF → HNF
  -- ⊘ *H _ = ⊘
  -- (a *x+ b) *H ⊘ = ⊘
  -- (a *x+ b) *H (c *x+ d) = (((a *H c) *x+ 0#) +H (b *S c) +H (d *S a)) *x+ (b * d)
  -- infixl 6 _*H_
```

With all of this machinery out of the way, we can implement `normalize`, which
transforms a `Syn` into an `HNF`:

```agda
  -- hnf : Syn → HNF
  -- hnf var = (⊘ *x+ 1#) *x+ 0#
  -- hnf (con x) = ⊘ *x+ x
  -- hnf (x :+ y) = hnf x +H hnf y
  -- hnf (x :* y) = hnf x *H hnf y
```

Believe it or not, that's most of the work to write a ring solver. We have one
more function to write, showing that evaluating the syntactic term is equal to
evaluating its normal form --- that is, that the normal form truly is a merely a
different representation of the same expression. This function has type:

-- ```agda
--   open import Relation.Binary.Reasoning.Setoid setoid

--   postulate
--     …algebra… : {x y : A} → x ≈ y
--     …via… : {ℓ : Level} {B : Set ℓ} {x y : A} → B → x ≈ y



--   +H-+-hom : ∀ x y v → ⟦ x +H y ⟧H v ≈ ⟦ x ⟧H v + ⟦ y ⟧H v
--   +H-+-hom ⊘ ⊘ v = sym (+-identityʳ 0#)
--   +H-+-hom (x *x+ x₁) ⊘ v =
--     begin
--       ⟦ x ⟧H v * v + x₁
--     ≈⟨ …algebra… ⟩
--       ⟦ x ⟧H v * v + x₁ + 0#
--     ∎
--   +H-+-hom ⊘ (y *x+ x₁) v = sym (+-identityˡ _)
--   +H-+-hom (x *x+ x₂) (y *x+ x₁) v =
--     begin
--       ⟦ x +H y ⟧H v * v + (x₂ + x₁)
--     ≈⟨ +-cong (*-cong (+H-+-hom x y v) refl) refl ⟩
--       (⟦ x ⟧H v + ⟦ y ⟧H v) * v + (x₂ + x₁)
--     ≈⟨ …algebra… ⟩
--       ⟦ x ⟧H v * v + x₂ + (⟦ y ⟧H v * v + x₁)
--     ∎

--   *S-*-hom : ∀ k x v → ⟦ k *S x ⟧H v ≈ k * ⟦ x ⟧H v
--   *S-*-hom k ⊘ v = sym (zeroʳ _)
--   *S-*-hom k (x *x+ x₁) v =
--     begin
--       ⟦ k *S x ⟧H v * v + k * x₁
--     ≈⟨ +-congʳ (*-congʳ (*S-*-hom k x v)) ⟩
--       k * ⟦ x ⟧H v * v + k * x₁
--     ≈⟨ …algebra… ⟩
--       k * (⟦ x ⟧H v * v + x₁)
--     ∎

--   foil : ∀ a b c d → (a + b) * (c + d) ≈ (a * c) + (b * c) + (a * d) + (b * d)
--   foil a b c d = …algebra…

--   *H-*-hom : ∀ x y v → ⟦ x *H y ⟧H v ≈ ⟦ x ⟧H v * ⟦ y ⟧H v
--   *H-*-hom ⊘ y v = sym (zeroˡ _)
--   *H-*-hom (x *x+ x₁) ⊘ v = sym (zeroʳ _)
--   *H-*-hom (a *x+ b) (c *x+ d) x =
--     let ⌊_⌋ a = ⟦ a ⟧H x in
--     begin
--       ⟦ ((a *H c) *x+ 0#) +H b *S c +H d *S a ⟧H x * x + b * d
--     ≈⟨ +-congʳ (*-congʳ (+H-+-hom (((a *H c) *x+ 0#) +H b *S c) (d *S a) x)) ⟩
--       (⟦ ((a *H c) *x+ 0#) +H b *S c ⟧H x + ⟦ d *S a ⟧H x) * x + b * d
--     ≈⟨ +-congʳ (*-congʳ (+-congʳ (+H-+-hom ((a *H c) *x+ 0#) (b *S c) x))) ⟩
--       (⌊ a *H c ⌋ * x + 0# + ⌊ b *S c ⌋ + ⌊ d *S a ⌋) * x + b * d
--     ≈⟨ …via… *S-*-hom ⟩
--       (⌊ a *H c ⌋ * x + (b * ⌊ c ⌋) + (d * ⌊ a ⌋)) * x + (b * d)
--     ≈⟨ +-congʳ (*-congʳ (+-congʳ (+-congʳ (*-congʳ (*H-*-hom a c x))))) ⟩
--       (⌊ a ⌋ * ⌊ c ⌋ * x + b * ⌊ c ⌋ + d * ⌊ a ⌋) * x + (b * d)
--     ≈⟨ …via… distribʳ ⟩
--       (⌊ a ⌋ * ⌊ c ⌋ * x * x) + (b * ⌊ c ⌋ * x) + (d * ⌊ a ⌋ * x) + (b * d)
--     ≈⟨ …algebra… ⟩
--       (⌊ a ⌋ * x * (⌊ c ⌋ * x)) + (b * (⌊ c ⌋ * x)) + (⌊ a ⌋ * x * d) + (b * d)
--     ≈⟨ sym (foil (⌊ a ⌋ * x) b (⌊ c ⌋ * x) d) ⟩
--       (⌊ a ⌋ * x + b) * (⌊ c ⌋ * x + d)
--     ∎

  -- _≈nested_>_<_ : A → {f : A → A} → (cong : {x y : A} → x ≈ y → f x ≈ f y) → {x y z : A} → x IsRelatedTo y → f y IsRelatedTo z → f x IsRelatedTo z
  -- _ ≈nested cong > relTo x=y < (relTo fy=z) = relTo (trans (cong x=y) fy=z)
  -- infixr 2 _≈nested_>_<_

  -- _□ : (x : A) → x IsRelatedTo x
  -- _□ = _∎

  -- infix  3 _□



  -- open import Function using (_∘_)

  -- *H-*-hom' : ∀ x y v → ⟦ x *H y ⟧H v ≈ ⟦ x ⟧H v * ⟦ y ⟧H v
  -- *H-*-hom' ⊘ y v = sym (zeroˡ _)
  -- *H-*-hom' (x *x+ x₁) ⊘ v = sym (zeroʳ _)
  -- *H-*-hom' (a *x+ b) (c *x+ d) x =
  --   let ⌊_⌋ a = ⟦ a ⟧H x in
  --   begin
  --     ⟦ ((a *H c) *x+ 0#) +H b *S c +H d *S a ⟧H x * x + b * d
  --   ≈nested (+-congʳ ∘ *-congʳ)
  --     >
  --       ⌊ ((a *H c) *x+ 0#) +H b *S c +H d *S a ⌋
  --     ≈⟨ +H-+-hom (((a *H c) *x+ 0#) +H b *S c) (d *S a) x ⟩
  --       ⌊((a *H c) *x+ 0#) +H b *S c ⌋ + ⌊ d *S a ⌋
  --     ≈⟨ +-congʳ (+H-+-hom ((a *H c) *x+ 0#) (b *S c) x) ⟩
  --       ⌊ a *H c ⌋ * x + 0# + ⌊ b *S c ⌋ + ⌊ d *S a ⌋
  --     ≈⟨ …via… *S-*-hom ⟩
  --       ⌊ a *H c ⌋ * x + (b * ⌊ c ⌋) + (d * ⌊ a ⌋)
  --     ≈⟨ +-congʳ (+-congʳ (*-congʳ (*H-*-hom a c x))) ⟩
  --       ⌊ a ⌋ * ⌊ c ⌋ * x + b * ⌊ c ⌋ + d * ⌊ a ⌋
  --   □ <
  --     (⌊ a ⌋ * ⌊ c ⌋ * x + b * ⌊ c ⌋ + d * ⌊ a ⌋) * x + (b * d)
  --   ≈⟨ …via… distribʳ ⟩
  --     (⌊ a ⌋ * ⌊ c ⌋ * x * x) + (b * ⌊ c ⌋ * x) + (d * ⌊ a ⌋ * x) + (b * d)
  --   ≈⟨ …algebra… ⟩
  --     (⌊ a ⌋ * x * (⌊ c ⌋ * x)) + (b * (⌊ c ⌋ * x)) + (⌊ a ⌋ * x * d) + (b * d)
  --   ≈⟨ sym (foil (⌊ a ⌋ * x) b (⌊ c ⌋ * x) d) ⟩
  --     (⌊ a ⌋ * x + b) * (⌊ c ⌋ * x + d)
  --   ∎

  -- sems : (s : Syn) → (v : A) → ⟦ s ⟧ v ≈ ⟦ hnf s ⟧H v
```

and is sketched out:

```agda
  -- sems var v = begin
  --   v                       ≈⟨ …algebra… ⟩
  --   (0# * v + 1#) * v + 0#  ∎
  -- sems (con c) v = begin
  --   c           ≈⟨ sym (+-identityˡ _) ⟩
  --   0# + c      ≈⟨ sym (+-congʳ (zeroˡ _)) ⟩
  --   0# * v + c  ∎
  -- sems (x :+ y) v = begin
  --   ⟦ x ⟧ v + ⟦ y ⟧ v                        ≈⟨ +-cong (sems x v) (sems y v) ⟩
  --   ⟦ hnf x ⟧H v + ⟦ hnf y ⟧H v  ≈⟨ sym (+H-+-hom (hnf x) (hnf y) v) ⟩
  --   ⟦ hnf x +H hnf y ⟧H v        ∎
  -- sems (x :* y) v = begin
  --   ⟦ x ⟧ v * ⟦ y ⟧ v                        ≈⟨ *-cong (sems x v) (sems y v) ⟩
  --   ⟦ hnf x ⟧H v * ⟦ hnf y ⟧H v  ≈⟨ sym (*H-*-hom (hnf x) (hnf y) v) ⟩
  --   ⟦ hnf x *H hnf y ⟧H v        ∎
```

Implementing `sems` will probably be the most work if you attempt this at home;
showing the homomorphisms between `_+H_` and `_+_` are not trivial, nor are
those for multiplication.

Finally, we can put everything together, solving proofs of the evaluation of two
pieces of syntax given a proof of their normalized forms:

```agda
  -- solve
  --     : (s t : Syn)
  --     → (v : A)
  --     → ⟦ hnf s ⟧H v ≈ ⟦ hnf t ⟧H v
  --     → ⟦ s ⟧ v ≈ ⟦ t ⟧ v
  -- solve s t v x = begin
  --   ⟦ s ⟧ v             ≈⟨ sems s v ⟩
  --   ⟦ hnf s ⟧H v  ≈⟨ x ⟩
  --   ⟦ hnf t ⟧H v  ≈⟨ sym (sems t v) ⟩
  --   ⟦ t ⟧ v             ∎
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

  hnf : Syn n → HNF n
  hnf (var x) = to-var x
  hnf (con x) = ↪ x
  hnf (x :+ b) = hnf x ⊕ hnf b
  hnf (x :* b) = hnf x ⊗ hnf b

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


  eval-hnf : (f : Fin n → 𝔸) → (s : Syn n) → eval f (hnf s) ≡ ⟦ s ⟧ f
  eval-hnf f (var a) = eval-to-var f a
  eval-hnf f (con a) = eval-↪ f a
  eval-hnf f (s :+ s₁)
    rewrite eval-⊕ f (hnf s) (hnf s₁)
    rewrite eval-hnf f s
    rewrite eval-hnf f s₁ = refl
  eval-hnf f (s :* s₁)
    rewrite eval-⊗ f (hnf s) (hnf s₁)
    rewrite eval-hnf f s
    rewrite eval-hnf f s₁ = refl


  open import Data.Vec using (Vec; []; _∷_; map; lookup)

  fins : Vec (Fin n) n
  fins {zero} = []
  fins {suc n} = zero ∷ map suc fins

  vars : Vec (Syn n) n
  vars = map var fins

  solve₀
      : (n : ℕ)
      → (x y : Vec (Syn n) n → Syn n)
      → hnf (x vars) ≡ hnf (y vars)
      → (v : Vec 𝔸 n)
      → ⟦ x vars ⟧ (lookup v) ≡ ⟦ y vars ⟧ (lookup v)
  solve₀ n x y x=y v = begin
    ⟦ x vars ⟧ f           ≡⟨ sym (eval-hnf f (x vars)) ⟩
    eval f (hnf (x vars))  ≡⟨ cong (eval f) x=y ⟩
    eval f (hnf (y vars))  ≡⟨ eval-hnf f (y vars) ⟩
    ⟦ y vars ⟧ f           ∎
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
      → hnf x ≡ hnf y
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



