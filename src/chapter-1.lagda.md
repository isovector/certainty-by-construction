## Proofs

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


### Axioms

In any formal system like mathematics of programming, we are required to state
the objects of study. A huge amount of mathematics, as opposed to programming,
is coming up with definitions of things. We can assert the existence of a new
*type* via the `data` keyword:

```agda
data Bool : Set where
  tt : Bool
  ff : Bool
```

This definition asserts the existence of three things; a new `Set`{.Agda} of
things called `Bool`{.Agda}, as well as two elements of `Bool`{.Agda}, namely
`tt`{.Agda} and `ff`{.Agda}. We use the colon (`:`) notation to state a *typing
judgment*, namely that `Bool`{.Agda} has type `Set`{.Agda}, and both `tt`{.Agda}
and `ff`{.Agda} have type `Bool`{.Agda}.

The names `tt`{.Agda} and `ff`{.Agda} are meant to be evocative of "true" and
"false" respectively, but we don't use those names because the concepts of
truth and falsity are more developed in Agda than in most programming languages.

We can define computation operations over our data type, first by giving a
typing judgment:

```agda
not : Bool → Bool
```

which states that `not`{.Agda} is a function that takes a `Bool`{.Agda} as input
and produces another `Bool`{.Agda} as an output. We can define `not`{.Agda} by
cases --- that is, by saying what happens if the input is `tt`{.Agda} and what
happens if it is `ff`{.Agda}:

```agda
not tt = ff
not ff = tt
```

Notice that these are *equations.* We are saying literally that `not tt`{.Agda}
is *equal to* `ff`{.Agda} for all intents and purposes. That means you (and
Agda) can replace `not tt`{.Agda} with `ff`{.Agda} anywhere you'd like. Despite
this, Agda is strongly normalizing, and will *reduce* the left-hand side to the
right-hand side whenever possible. It is syntactically invalid to write this
equation as

```AGDA
ff = not tt
```

even though logically it's fine to do so. As a quirk of Agda, you must put the
side which defines the function on the left side of the equals sign.

We can write (slightly) more interesting functions, for example, `and`{.Agda}
which computes the logical AND of two `Bool`{.Agda}s:

```agda
and : Bool → Bool → Bool
and tt tt = tt
and tt ff = ff
and ff tt = ff
and ff ff = ff
```

Notice how `and`{.Agda} *pattern matches* on every possible case of its two
arguments.


Exercise

:   Implement `or : Bool → Bool → Bool`{.Agda}, computing the logical OR of two
    `Bool`{.Agda}s


Solution

:   ```agda
or : Bool → Bool → Bool
or tt tt = tt
or tt ff = tt
or ff tt = tt
or ff ff = ff
```


### Propositional Equality

So far, Agda looks like a pretty normal programming language, albeit with odd
syntax if you are coming from a traditional, procedural background. Where things
get more interesting is when we begin looking at *dependent types,* which allow
us, amoung other things, to state *propositions of equality.*  For example, we
can use these equalities as a sort of compile-time unit test.

The first step is to import `PropositionalEquality` from the Agda standard
library:

```agda
open import Relation.Binary.PropositionalEquality
```

We can now assert, for example, that `not (not tt)`{.Agda} is equal to
`tt`{.Agda}:

```agda
not-not-tt-is-tt : not (not tt) ≡ tt
```

Here we use the triple equals (`_≡_`{.Agda}), not to define the equality of two
things, but to ensure it holds. Notice that `not (not tt) ≡ tt`{.Agda} comes on
the *right side* of a colon, which is to say that this thing is a *type.* This
is a very strange notion if you are coming from a language that thinks of types
as a means of laying out bits in memory, or one which eschews types altogether.
We will explore the notion of equalities as types more deeply in a little bit,
but for now, please suspend your disbelief.

Equalities are the domain of mathematics, and thus `not-not-tt-is-tt`{.Agda} is
making a mathematical claim. Mathematical claims require proofs, and thus we
must give one. Thankfully, the proof is extraordinarily easy:

```agda
not-not-tt-is-tt = refl
```

The term `refl`{.Agda} is short for *reflexivity,* which is the mathematical
property that all things are equal to themselves. What's happening behind the
scenes here is that Agda is normalizing `not (not tt)`{.Agda} to `not ff`{.Agda}
and finally to `tt`{.Agda} by following the equations we wrote down earlier.
After doing that, it sees that `tt`{.Agda} is on both sides of the `_≡_`{.Agda},
which is to say that `tt`{.Agda} is equal to itself, and thus that we are
justified in saying this proposition holds by reflexivity.

If you were to try to write a falsity, perhaps that:

```wrong
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

An interesting fact about `not`{.Agda} is that it goes away if you do it twice,
as we saw above with `not-not-tt-is-tt`{.Agda}. We can make this proof more
reusable by saying that for *any* `Bool`{.Agda} `x`, it is the case that `not
(not x) ≡ x`{.Agda}. As usual, we begin with a typing judgment:

```agda
not-not : (x : Bool) → not (not x) ≡ x
```

which is a very strange type indeed. Here we're saying `not-not`{.Agda} is a
function which takes a `Bool`{.Agda} argument, names it `x`, and then produces
an equality proof for that same `x`! This is our first example of a *dependent
type,* which we will get significantly more practice with in due time.



```agda
not-not tt = refl
not-not ff = refl
```

```agda
demorgan : (x y : Bool) → or x y ≡ not (and (not x) (not y))
demorgan tt tt = refl
demorgan tt ff = refl
demorgan ff tt = refl
demorgan ff ff = refl

and-unit : (x : Bool) → and tt x ≡ x
and-unit tt = refl
and-unit ff = refl

or-unit : (x : Bool) → or ff x ≡ x
or-unit x =
  begin
    or ff x
  ≡⟨ demorgan ff x ⟩
    not (and tt (not x))
  ≡⟨ cong not (and-unit (not x)) ⟩
    not (not x)
  ≡⟨ not-not x ⟩
    x
  ∎
  where
    open ≡-Reasoning



```

