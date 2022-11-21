# Ring Solving

```agda
module 6-ring-solving where

open import Relation.Binary.PropositionalEquality
open import Data.Nat
```

As you might have noticed, solving lemmas about simple mathematical facts can be
overwhelmingly complicated, even for simple tasks. Recall that when we were
implementing `*-cong₂-mod`, that is, `cong` for modular arithmetic, we built a
lot of setoid machinery and reasoning to avoid needing to solve these large
proofs by hand.

The problem if you recall, is that we're trying to solve the following:

$$
ac + (cx + az + xzn) \times n = bd + (dy + bw + ywn) \times n
$$

subject to the additional facts

$$
a + xn ≡ b + yn \\
c + zn ≡ d + wn
$$


Let's do the arithmetic by hand, just to get a lower-bound on how much effort is
involved here.

```arithmetic
  ac + (cx + az + xzn) * n
= ac + cxn + azn + xznn
= c * (a + xn) + azn + xznn
= c * (a + xn) + zn * (a + xn)
= c * (b + yn) + zn * (b + yn)
= cb + cyn + zn * (b + yn)
= cb + cyn + znb + zynn
= cb + znb + cyn + zynn
= b * (c + zn) + cyn + zynn
= b * (c + zn) + yn * (c + zn)
= b * (d + wn) + yn * (d + wn)
= bd + bwn + yn * (d + wn)
= bd + bwn + dyn + ywnn
= bd + dyn + bwn + ywnn
= bd + (dyn + bwn + ywnn)
= bd + (dy + bw + ywn) * n
```

This proof is already 15 lines long, and that's including the inherent shortcuts
that we take as humans, such as automatically reasoning over the associativity
and commutativity of addition and multiplication --- imagine how much longer
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
operation called "addition" and an associative --- but not necessarily
commutative --- binary operation called "multiplication." We also have
distinguished elements 0 and 1 that behave like you'd expect. Additionally, if
you'll excuse the pun, we require an additive inverse operation analogous to
unary negation, with the property that for any $a$ we have $a + -a = 0$.
Finally, multiplication is required to distribute over addition, that is, $a
\times b + c = ab + ac$.

By virtue of generalizing addition and multiplication, addition and
multiplication had better form a ring! And indeed they do, meaning we can use
the ring solver to tackle problems of this form. Let's set up the necessary
machinery again to describe the problem:

```agda
module _ (n : ℕ) where
  open import 6-setoids
  open mod-def


  *-cong₂-mod'
      : {a b c d : ℕ}
      → a ≈ b ⟨mod n ⟩
      → c ≈ d ⟨mod n ⟩
      → a * c ≈ b * d ⟨mod n ⟩
  *-cong₂-mod' {a} {b} {c} {d} (≈-mod x y pxy) (≈-mod z w pzw) =
```

Recall, in order to show congruence over `_*_` for modular arithmetic, we are
required to discover $p$ and $q$ such that $ac + pn = bd + qn$. The solutions
for $p$ and $q$ are given as:

```agda
    ≈-mod (c * x + a * z + x * z * n)
          (d * y + b * w + y * w * n)
          (begin
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
  a * c + (c * x + a * z + x * z * n) * n
= ...
= c * (a + x * n) + z * n * (a + x * n)
```

We can set up the problem by beginning our reasoning block:

```agda
      a * c + (c * x + a * z + x * z * n) * n
        ≡⟨
```

The ring solver is invoked via a call to `solve` with its first argument being
the number of free variables flying around needing to be solved for. In this
case we have 5 (a, c, n, x, z):

```agda
            solve 5
```

Our next step is to construct a *syntax tree* corresponding to the expression
we'd like to solve. Our goal is to show `a * c + (c * x + a * z + x * z * n) * n
= c * (a + x * n) + z * n * (a + x * n)`, so this is almost our syntax tree; all
that's required is to put a colon before each of `_+_`, `_*_` and `_=_`. We
put this tree inside of a lambda that bounds each of the free variables:

```agda
    (λ a c n x z →
        a :* c :+ (c :* x :+ a :* z :+ x :* z :* n) :* n
     := (a :+ x :* n) :* c :+ (a :+ x :* n) :* z :* n
    )
```

This syntax tree is an annoying thing to write, but is necessary to help the
ring solver know what it's trying to solve. Remember, just because we've written
out this expression with full syntax here doesn't mean this is the term Agda is
working on! Agda is free to expand definitional equalities, meaning it might
have already reduced some of these additions and multiplications away!

Finally, all that's left is to finish calling `solve` with `refl`, and then each
of the variables we mentioned in the lambda, in the same order, thus:

```agda
      refl a c n x z ⟩
```

Agda will happily accept the resulting proof, meaning we are now in a position
to `cong` `pxy` into the right place:

```agda
      (a + x * n) * c + (a + x * n) * z * n
    ≡⟨ cong (λ φ → φ * c + φ * z * n) pxy ⟩
      (b + y * n) * c + (b + y * n) * z * n
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
    ≡⟨ solve 5 (λ b c n y z →
          (b :+ y :* n) :* c :+ (b :+ y :* n) :* z :* n
        := b :* (c :+ z :* n) :+ y :* n :* (c :+ z :* n)
               )
         refl b c n y z
     ⟩
      b * (c + z * n) + y * n * (c + z * n)
```

We're now back in a place we can `cong`. Rather than walk through the rest of
the example, we will present it in its completeness:

```agda
      ≡⟨ cong (λ φ → b * φ + y * n * φ) pzw ⟩
        b * (d + w * n) + y * n * (d + w * n)
      ≡⟨ solve 5 (λ b d n w y →
            b :* (d :+ w :* n) :+ y :* n :* (d :+ w :* n)
         := b :* d :+ (d :* y :+ b :* w :+ y :* w :* n) :* n
                 )
           refl b d n w y
        ⟩
        b * d + (d * y + b * w + y * w * n) * n
      ∎ )
```

All that's left is to get our solver in scope, by importing it from
`Data.Nat.Solver` and opening the resulting `+-*-Solver` module:

```agda
    where
      open ≡-Reasoning
      open import Data.Nat.Solver
      open +-*-Solver
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


