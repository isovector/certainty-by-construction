# Proofs

```agda
module ok-hello where
```

What constitutes a mathematical proof? How do you know when you are done? This
was always the hardest part in my math education. The course notes from my first
class on proofs state:

https://cs.uwaterloo.ca/~cbruni/pdfs/Math135SeptDec2016/Lecture1.pdf

> A proof should be a convincing argument of a statement. A proof requires at
> least two people, a creator and an observer.

The challenge, of course, is that an argument that I find convincing might not
be convincing to an observer! Is my proof burden lessened if I am presenting to
a less mathematically-inclined audience? Is there an observer to whom "just
trust me on this" constitutes a mathematical proof?

Clearly this is an unsatisfying answer to "what is a proof?" In practice, a
proof seems to be "whatever satisfies the mathematical elders" --- which is to
say, does it convince whoever is grading your paper? The cynic might say that
what you're paying for is to have someone grade your papers. Under this lens, a
mathematics education is twinfold: the actual mathematical content, and an
out-of-band notion of "what sorts of arguments are convincing?"

This book answers that question not of its own accord, but by introducing you
to, and teaching you how to use, an *interactive theorem prover,* which
automates the job of checking proofs. You're not finished with your proof until
the theorem prover says so. This takes the guesswork out of the equation; just
bash through the proof until you're done. On the surface this sounds like a
tedious task, but fortunately interactive theorem provers are *interactive,*
which makes the job a great deal of fun.

Interactive theorem provers are programming languages, which bring with them an
added benefit --- you can reuse your knowledge of programming to help learn
math. Having a better understanding of mathematics will, in turn, improve the
software you write: both in terms of deconstructing problems, and in proving
your solutions are correct.


## Axioms

In any formal system like mathematics of programming, we are required to state
the objects of study. A huge amount of mathematics, as opposed to programming,
is coming up with definitions of things. We can assert the existence of a new
*type* via the `data` keyword:

```agda
data Bool : Set where
  tt : Bool
  ff : Bool
```

This definition asserts the existence of three things; a new `Set` of
things called `Bool`, as well as two elements of `Bool`, namely
`tt` and `ff`. We use the colon (`:`) notation to state a *typing
judgment*, namely that `Bool` has type `Set`, and both `tt`
and `ff` have type `Bool`.

The names `tt` and `ff` are meant to be evocative of "true" and
"false" respectively, but we don't use those names because the concepts of
truth and falsity are more developed in Agda than in most programming languages.

We can define computation operations over our data type, first by giving a
typing judgment:

```agda
not : Bool → Bool
```

which states that `not` is a function that takes a `Bool` as input
and produces another `Bool` as an output. We can define `not` by
cases --- that is, by saying what happens if the input is `tt` and what
happens if it is `ff`:

```agda
not tt = ff
not ff = tt
```

Notice that these are *equations.* We are saying literally that `not tt`
is *equal to* `ff` for all intents and purposes. That means you (and
Agda) can replace `not tt` with `ff` anywhere you'd like. Despite
this, Agda is strongly normalizing, and will *reduce* the left-hand side to the
right-hand side whenever possible. It is syntactically invalid to write this
equation as

```haskell
ff = not tt
```

even though logically it's fine to do so. As a quirk of Agda, you must put the
side which defines the function on the left side of the equals sign.

We can write (slightly) more interesting functions, for example, `and`
which computes the logical AND of two `Bool`s:

```agda
and : Bool → Bool → Bool
and tt tt = tt
and tt ff = ff
and ff tt = ff
and ff ff = ff
```

Notice how `and` *pattern matches* on every possible case of its two
arguments.


Exercise

:   Implement `or : Bool → Bool → Bool`, computing the logical OR of two
    `Bool`s


Solution

:   ```agda
or : Bool → Bool → Bool
or tt tt = tt
or tt ff = tt
or ff tt = tt
or ff ff = ff
```


## Propositional Equality OLD

So far, Agda looks like a pretty normal programming language, albeit with odd
syntax if you are coming from a traditional, procedural background. Where things
get more interesting is when we begin looking at *dependent types,* which allow
us, amoung other things, to state *propositions of equality.*  For example, we
can use these equalities as a sort of compile-time unit test.

The first step is to import `PropositionalEquality` from the Agda standard
library:

```agda
module _ where
  open import Relation.Binary.PropositionalEquality
```

We can now assert, for example, that `not (not tt)` is equal to
`tt`:

```agda
  not-not-tt-is-tt : not (not tt) ≡ tt
```

Here we use the triple equals (`_≡_`), not to define the equality of two
things, but to ensure it holds. Notice that `not (not tt) ≡ tt` comes on
the *right side* of a colon, which is to say that this thing is a *type.* This
is a very strange notion if you are coming from a language that thinks of types
as a means of laying out bits in memory, or one which eschews types altogether.
We will explore the notion of equalities as types more deeply in a little bit,
but for now, please suspend your disbelief.

Equalities are the domain of mathematics, and thus `not-not-tt-is-tt` is
making a mathematical claim. Mathematical claims require proofs, and thus we
must give one. Thankfully, the proof is extraordinarily easy:

```agda
  not-not-tt-is-tt = refl
```

The term `refl` is short for *reflexivity,* which is the mathematical
property that all things are equal to themselves. What's happening behind the
scenes here is that Agda is normalizing `not (not tt)` to `not ff`
and finally to `tt` by following the equations we wrote down earlier.
After doing that, it sees that `tt` is on both sides of the `_≡_`,
which is to say that `tt` is equal to itself, and thus that we are
justified in saying this proposition holds by reflexivity.

If you were to try to write a falsity, perhaps that:

```haskell
  not-tt-is-tt : not tt ≡ tt
  not-tt-is-tt = refl
```

you would instead get a big red error message from Agda, saying:

```response
ff != tt of type Bool
when checking that the expression refl has type not tt ≡ tt
```

Behind the scenes, Agda really is checking your proofs, and it will holler
loudly if they do not hold.

An interesting fact about `not` is that it goes away if you do it twice,
as we saw above with `not-not-tt-is-tt`. We can make this proof more
reusable by saying that for *any* `Bool` `x`, it is the case that `not
(not x) ≡ x`. As usual, we begin with a typing judgment:

```agda
  not-not : (x : Bool) → not (not x) ≡ x
```

which is a very strange type indeed. Here we're saying `not-not` is a
function which takes a `Bool` argument, names it `x`, and then produces
an equality proof for that same `x`! This is our first example of a *dependent
type,* which we will get significantly more practice with in due time.

You might expect that we can write this as simply

```haskell
not-not x = refl
```

but such a thing doesn't work. You see, we have rules for how to reduce `not
tt` and `not ff`, but nothing of the form `not x`. Because
we don't know which constructor of `Bool` `x`, we are unable to make
progress in the reduction. Such terms are said to be *stuck.*

The way we can unstick our computation is by pattern matching on `x`, and then
giving a proof for the case when `x` is `tt`, and another for when it is
`ff`. In both of these cases, pattern matching unsticks the computation
and reveals that the proof for each is merely `refl`:

```agda
  not-not tt = refl
  not-not ff = refl
```

This style of proof --- pattern match on every input, and return `refl`
for each --- is known as a *proof by exhaustion,* or, more colloquially, as a
*case bash.*

We can case bash our way through a proof that De Morgan's laws hold. As usual,
state the typing judgment:

```agda
  de-morgan : (x y : Bool) → or x y ≡ not (and (not x) (not y))
```

which is trivially proven by exhaustion:

```agda
  de-morgan tt tt = refl
  de-morgan tt ff = refl
  de-morgan ff tt = refl
  de-morgan ff ff = refl
```

Let's introduce one more lemma before doing something a little more interesting.
Notice that when the first argument of `and` is `tt`, `and`
returns its second argument unchanged. In the lingo, we say that `tt` is
a *left-unit* of `and`, and we can prove it again by case bash:

```agda
  and-unit : (x : Bool) → and tt x ≡ x
  and-unit tt = refl
  and-unit ff = refl
```

As it happens, `or` also has a left-unit, but this time it is
`ff`. Let's prove the following:

```agda
module _ where
  open import Relation.Binary.PropositionalEquality
  open ≡-Reasoning

  or-unit : (x : Bool) → or ff x ≡ x
```

but this time we will not show it by exhaustion, and instead do something a
little more traditionally mathematical. We can give a chain of reasoning steps,
using things we've already proven to make progress. We'll walk through the
argument "by hand" before writing it in Agda to get a feel for the idea.


Proof

:   We begin with `or ff x` which we know, by De Morgan's laws, is equal
    to `not (and (not ff) (not x))`. The definition of `not ff` is
    `tt`, so we can replace that, resulting in `not (and tt (not x))`. We
    know now that `tt` is a left unit for `and`, so this reduces to `not
    (not x)`, which then by the `not-not` rule reduces to `x`.
    We've now shown what we set out to, so we are done.


Our proof in Agda will follow exactly the same steps. At each step, we write the
expression as it currently stands, and then write a justification for why we can
transform it into the next step. These justifications are written inside of
`≡⟨_⟩` brackets. Our proof begins with the word `begin_`:

```agda
  or-unit x =
    begin
```

And we write the left-hand side of the equality.

```agda
      or ff x
```

We happen to know (and have a proof!) of De Morgan's laws, so we can use those
to rewrite the expression:

```agda
    ≡⟨ de-morgan ff x ⟩
      not (and (not ff) (not x))
```

This is definitionally equal to the following, so we require no justification:

```agda
    ≡⟨⟩
      not (and tt (not x))
```

We'd now like to invoke the `and-unit` law, but Agda requires us to
"target" it in the expression. We need to apply it *inside* of the call to
`not`, which we can do via the `cong not` function (discussed
soon):

```agda
    ≡⟨ cong not (and-unit (not x)) ⟩
      not (not x)
```

All that's left is to use `not-not`:

```agda
    ≡⟨ not-not x ⟩
      x
```

The proof is now finished, which mathematicians indicate with a black square:

```agda
    ∎
```

Don't ask why. I don't know. Tradition is a weird thing.

Perhaps having written `or-unit` has given you a taste of what
constitutes a mathematical proof. Here we didn't do any silly
proof-by-exhaustion stuff; `or-unit` is unquestionably a mathematical
proof --- and a very explicit one at that. As our mathematical vocabulary grows
larger (and our software library of proofs), we'll find ourselves capable of
proving more for less. But just like in software, math is built one layer of
abstraction at a time.


## Equivalence Relationships

```agda
module Example where
  open import Relation.Binary.PropositionalEquality using (_≡_)

  postulate

    refl  : {A : Set} {x y   : A} → x ≡ y
    sym   : {A : Set} {x y   : A} → x ≡ y → y ≡ x
    trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z

module _ where

  data ℕ : Set where
    zero : ℕ
    suc  : ℕ → ℕ

  _+_ : ℕ → ℕ → ℕ
  zero + y = y
  suc x + y = suc (x + y)


  open import Relation.Binary.PropositionalEquality

  +-zero : (x : ℕ) → x + zero ≡ x
  +-zero zero = refl
  +-zero (suc x) = cong suc (+-zero x)

  +-suc : (x y : ℕ) → x + suc y ≡ suc (x + y)
  +-suc zero y = refl
  +-suc (suc x) y = cong suc (+-suc x y)

  +-assoc : (x y z : ℕ) → x + (y + z) ≡ (x + y) + z
  +-assoc zero y z = refl
  +-assoc (suc x) y z = cong suc (+-assoc x y z)

  +-comm : (x y : ℕ) → x + y ≡ y + x
  +-comm zero y = sym (+-zero y)
  +-comm (suc x) y =
    begin
      suc (x + y)
    ≡⟨ cong suc (+-comm x y) ⟩
      suc (y + x)
    ≡⟨⟩
      suc y + x
    ≡⟨ sym (+-suc y x) ⟩
      y + suc x
    ∎
    where open ≡-Reasoning

  infixr 5 _+_
  infixr 6 _*_

  _*_ : ℕ → ℕ → ℕ
  zero * y = zero
  suc x * y = y + (x * y)

  *-zero : (x : ℕ) → x * zero ≡ zero
  *-zero zero = refl
  *-zero (suc x) = *-zero x

  +-swizzle : (x y z : ℕ) → x + (y + z) ≡ y + (x + z)
  +-swizzle x y z =
    begin
      x + y + z
    ≡⟨ +-assoc x y z ⟩
      (x + y) + z
    ≡⟨ cong (_+ z) (+-comm x y) ⟩
      (y + x) + z
    ≡⟨ sym (+-assoc y x z) ⟩
      y + x + z
    ∎
    where open ≡-Reasoning

  *-suc : (x y : ℕ) → x * suc y ≡ (x * y) + x
  *-suc zero y = refl
  *-suc (suc x) y =
    begin
      suc (y + x * suc y)
    ≡⟨ cong (\ φ → suc (y + φ)) (*-suc x y) ⟩
      suc (y + ((x * y) + x))
    ≡⟨ cong (\ φ → suc (y + φ)) (+-comm (x * y) x) ⟩
      suc (y + (x + (x * y)))
    ≡⟨ cong suc (+-swizzle y x (x * y)) ⟩
      suc (x + (y + (x * y)))
    ≡⟨⟩
      suc x + (y + x * y)
    ≡⟨ +-comm (suc x) (y + x * y) ⟩
      (y + x * y) + suc x
    ∎
    where open ≡-Reasoning

  +-*-distrib : (x y z : ℕ) → (x + y) * z ≡ x * z + y * z
  +-*-distrib zero y z = refl
  +-*-distrib (suc x) y z =
    begin
      z + (x + y) * z
    ≡⟨ cong (z +_) (+-*-distrib x y z) ⟩
      z + ((x * z) + (y * z))
    ≡⟨ +-assoc z (x * z) (y * z) ⟩
      (z + x * z) + y * z
    ∎
    where open ≡-Reasoning

  *-assoc : (x y z : ℕ) → x * (y * z) ≡ (x * y) * z
  *-assoc zero y z = refl
  *-assoc (suc x) y z =
    begin
      (y * z) + (x * (y * z))
    ≡⟨ cong ((y * z) +_) (*-assoc x y z) ⟩
      y * z + (x * y) * z
    ≡⟨ sym (+-*-distrib y (x * y) z) ⟩
      (y + x * y) * z
    ∎
    where open ≡-Reasoning

  *-comm : (x y : ℕ) → x * y ≡ y * x
  *-comm zero y = sym (*-zero y)
  *-comm (suc x) y =
    begin
      suc x * y
    ≡⟨⟩
      y + (x * y)
    ≡⟨ +-comm y (x * y) ⟩
      (x * y) + y
    ≡⟨ cong (_+ y) (*-comm x y) ⟩
      (y * x) + y
    ≡⟨ sym (*-suc y x) ⟩
      y * suc x
    ∎
    where open ≡-Reasoning

```



