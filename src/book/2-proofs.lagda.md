# Proofs

Hidden

:   ```agda
{-# OPTIONS --allow-unsolved-metas #-}
    ```

```agda
module 2-proofs where
```

In this chapter we will take our first looks at what constitutes a mathematical
proof, as well as how to articulate proofs in Agda. In the process, we will need
to learn a little more about Agda's execution model and begin exploring the
exciting world of dependent types.

My first encounter with proofs was in a first-year university algebra course,
where I quickly learned I had no idea what a proof was (and had the marks to
prove it!) A proof is supposed to be a mathematical argument that other
mathematicians find convincing; my problem was, things that seemed convincing to
me were inevitably unconvincing to the professor. Perhaps you have encountered
this same problem. If so, there is good news for you in this chapter---working
in Agda makes it exceptionally clear what constitutes a proof; either Agda is
happy with what you've written, or it isn't. In either case, the feedback cycle
is extremely quick, and it's easy to iterate until you're done.


## Constructivism

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

To illustrate this difference, suppose we'd like to prove that there exists a
prime number greater than 10. Under a classical worldview, a perfectly
acceptable proof would go something like this:

1. Suppose there does not exist a prime number greater than 10.
2. Therefore, the prime factorization of every number must consist only of 2, 3,
   5, and 7.
3. If a number $n$ has a prime factor $d$, then $n + 1$ does not have have $d$ as
   a prime factor.
4. The number $2 \times 3 \times 5 \times 7 = 210$ has prime factors of 2, 3, 5,
   and 7.
5. Therefore, $210 + 1 = 211$ does not have prime factors of 2, 3, 5, or 7.
6. Therefore, 211 has no prime factors.
7. This is a contradiction, because all numbers have prime factors.
8. Therefore, there does exist a prime number greater than 10. ∎

Contrast this against a constructive proof of the same proposition:

1. 11 is divisible by no number between 2 and 10.
2. Therefore, 11 is a prime number.
3. 11 is a number greater than 10.
4. Therefore, there exists a prime number greater than 10. ∎

Classical arguments are allowed to assume the negation, show that it leads to
absurdity, and therefore refute the negation. But constructive arguments are
*required* to build the object in question, and furthermore to take on the
burden to show that it satisfies the necessary properties.

Under a computational setting, constructive arguments are much more compelling
than classical ones. This is because constructive arguments correspond to
objects we can hold in our hands (or, at least, in memory), while classical
arguments come from counterfactual observations pointing out that something must
exist without telling you how to get your hands on such a thing. To put it
another way, constructive arguments correspond to *algorithms.*


## Propositions as Types

Now that we are familiar with our programming language, let's turn our focus
towards more mathematical ideas. When most humans think of mathematics, their
immediate thought is that of numbers. But of course, mathematics is a field
significantly larger than numbers, and we will not deal with numbers in this
section.

But what is mathematics, if not about numbers? I would say it is the process of
clear, logical deduction around precise ideas. Numbers are one such precise
idea, but they are not the only one. In fact, mathematics can be split into two
magisteria: propositions, and proofs of those propositions. Propositions are the
statements you're claiming to be true, while proofs are the evidence you have
that the statements *are* true. In mathematics, unlike science, evidence isn't
just *convincing*---it's necessarily so. A proof of a proposition has no
wiggle room or space for error; either it is an all-encompassing, argument that
necessitates belief in the premise, or it is not. There are no half measures in
belief in mathematics.

A corollary of this idea is that two mathematicians can have differing opinions
on whether a proposition is true, but once they have a proof, they both must
believe the proposition to be true. Any other result is to not have a proof in
the first place.

There is an analogy to software here---quite an apt one---that it's easy to
disbelieve a problem can be solved. That is, of course, until someone hands you
the algorithm that solves it. The algorithm itself is a proof artifact that
shows the problem can be solved.

It is exactly this analogy that we will exploit for the remainder of this book
in order to show the relationship between mathematics and programming, and
furthermore, to help programmers use the tools they already have to start being
productive in mathematics. But let's make the connection more formal.

-- TODO(sandy): what is a proposition

To be very explicit, our analogy equates *mathematical propositions* and
*types.* That is to say, any mathematical proposition has an encoding as a type,
and vice versa. Furthermore, every *proof of a proposition* corresponds to a
*program with that type*. For example, we can say that the following type:

```type
Bool
```

corresponds to the proposition "there exists a boolean." This is not a
particularly strong claim. Under a constructive lens, we can prove the
proposition merely by proving a boolean, thus proving at least one exists.

For further illustration, with a more complicated example, let's bring back our
`IsEven` type from @sec:numbers. First we can import the chapter module:

```agda
open import 2-numbers
```

then bring the types from the sandboxed module into scope:

```agda
open Naturals using (ℕ; IsEven)
```

and finally, bring the constructors of those types into scope:

```agda
open ℕ
open IsEven
```

We can then ask the question whether zero is an even number by formulating a
type to that effect:

```agda
zero-is-even : IsEven zero
```

Of course, zero *is* even, the proof of which we have seen before:

```agda
zero-is-even = zero-even
```

We can also ask whether one is an even number by writing down the type:

```agda
one-is-even : IsEven (suc zero)
one-is-even = ?
```

One however is not an even number, and thus there is no way to fill this hole.

These two examples illustrate the point. While we can always write down the type
of something we'd like to prove, we cannot always find a value with that type.
Therefore, we say that types correspond to propositions, while values are proofs
of those propositions. In the literature, this concept is known by the name
*types as propositions,* and, alternatively as the *Curry--Howard
correspondence.*

The Curry--Howard correspondence thus gives us a guiding principle for doing
constructive mathematics in a programming language. We encode down the problem
statement as a type, and then we construct a value of that type in order to show
the truth of the problem statement. Keeping this perspective in mind is the
secret to success.


## Hard to Prove or Simply False?

Of the absolute utmost importance in mathematics is the *principle of
consistency.* This is a fancy way of saying "there should be no proof for false
things." We use math as a tool for exploring truths about platonic abstractions,
and being able to prove a falsity would be devastating to the entire
formalization. The problem is that falsities beget falsities; if you find one,
you can use it to produce another. Mathematicians call this the *principle of
explosion* in English, or say *ex falso quodlibet* if they're feeling
particularly regal. All this means is that, given a proof of false, you can
subsequently provide a proof of anything. Therefore, contradictions are *really,
really* bad, and a huge chunk of logical development (including computation
itself) has arisen from people discovering contradictions arising from less
rigorous mathematics than we use today.

All of this is to say: it's desirable that it be very difficult to prove
something that is false. From afar, this sounds like a very good and righteous
desideratum. But when you're deep in the proof mines, having difficulties
eliciting the sought-after proof, it's often unclear whether you haven't tried
hard enough or whether the problem is impossible outright. I have spent weeks of
my life trying to prove false statements without realizing it, and I suspect
this is a necessary rite of passage.

Nevertheless, I hope you spare you from some of the toil spent wasted on a false
proposition. If you're ever finding a proof to be exceptionally hard, it's
worth taking some time out to prove the proposition for extremely simple,
concrete values. If you're working with numbers, see if it holds when everything
is zero or one. Working through the easiest cases by hand will usually point out
a fundamental problem if there is one, or might alert you to the fact that you
haven't yet built enough machinery (that is, library code around your particular
problem) to make proving things easy.

Remember, you can always prove something the stupid way first, and come back
with a better proof later on if you deem necessary. In proofs as in life, done
is better than perfect.


## The Equality Type

All of this is fine and dandy, but how do we go about actually building types
corresponding to mathematical propositions? Usually the technique is to use an
indexed type, like we did with `IsEven`.

One of the most common mathematical propositions---indeed, often synonymous with
math in school---is the *equation.* Equality is the proposition that two
different objects are in fact just one object. There is a wide and raging debate
about exactly what equality *means,* but for the time being we will limit
ourselves to the case that the two expressions will eventually *evaluate to the
exact same series of constructors.* This particular notion of equality is known
as *propositional equality* and is the basic notion of equality in Agda.

We can define propositional equality by making a type for it. The type should
relate two objects, stating that they are equal, and thus it must be *indexed by
two values.* These indices correspond to the values being related. In order for
two things to evaluate to the same constructors, they must have the same type.
And because we'd like to define propositional equality once and for all, we can
parameterize the whole thing by the type of things it relates. Solving all these
constraints simultaneously gives us the following `data` definition.

```agda
-- TODO(sandy): drop this module when the chapter is rewritten
module REMOVE-ME where

  data _≡_ {A : Set} : A → A → Set where
```

The `≡` symbol is input via `\==`.

Remember that the type corresponds to the proposition, while the constructors
are the primitive ways by which we can prove the proposition. In this case,
there is only one basic way to show an equality, which is to say, two things are
equal only if they are the same thing in the first place!

```agda
    refl : {x : A} → x ≡ x
```

The type here, `{x : A} → x ≡ x` says that for any value `x` we'd like, we know
that `x` is equal to itself. The constructor is called `refl`, which is short
for *reflexivity,* which is the technical jargon for the property that all
things are equal to themselves. We shorten "reflexivity" because we end up
writing this constructor *a lot.*

In order to play nicely with standard mathematical notation, we'd like `_≡_` to
bind very loosely, that is to say, to have a low precedence. Furthermore, we do
not want `_≡_` to associate at all, so we can use `infix` without a left or
right suffix to prevent this behavior:

```agda
  infix 4 _≡_
```

We have already encountered `_≡_` and `refl` in @sec:chapter1 where we called
them "unit tests." This was a little white-lie, about which I am now coming
clean. In fact, what we were doing before with our "unit tests" was proposing
the equality of two terms, and giving a proof saying that were already the same
thing. Because Agda will automatically do as much computation and simplification
as it can, for any two concrete expressions that are in fact eventually equal,
Agda will convince itself of this fact. As a practical technique, we often can,
and do, write little unit tests of this form. But, as we will see in a moment,
we can use propositional equality to assert much stronger claims than unit tests
are capable of determining.

Let's play around with our equality type to get a feel for how much work it can
do, without any further machinery.

```agda
  module Sandbox-Playground where
    open Naturals
      using (one; two; three; four; _+_; _*_)
```

It's no surprise that Agda can determine the equality of two syntactically
identical terms:

```agda
    3≡3 : suc (suc (suc zero)) ≡ suc (suc (suc zero))
    3≡3 = refl
```

Agda will also expand definitions:

```agda
    three≡3 : three ≡ suc (suc (suc zero))
    three≡3 = refl
```

including if those definitions require computation:

```agda
    three≡one+two : three ≡ one + two
    three≡one+two = refl
```

Each of these examples is of the "unit test" variety. Perhaps you'll be
delighted to learn that we can also use propositional equality to automatically
show some algebraic identities. For example, we'd like to show the following
fact:

$$
0 + x = x
$$

We can write this proposition as a type rather directly:

```agda
    0+x≡x : (x : ℕ) → zero + x ≡ x
```

In order to give a proof of this fact, we must bind the parameter on the left
side of the equals (in fact, we don't even need to give it a name), but `refl`
is sufficient on the right side:

```agda
    0+x≡x _ = refl
```

There are two equally valid interpretations of `0+x≡x`. The first is exactly the
equation we wrote earlier, namely:

$$
0 + x = x
$$

However, you can also train your keen computer-science eye at this and take the
type of `0+x≡x` more literally---that is, as a function. Namely: a function
which takes some `x` and gives you back a proof that *for that particular `x`*,
it is the case that $0 + x = x$.

Our examples thus far seem to indicate that `_≡_` can automatically show all of
the equalities we'd like. But this has been a careful ruse on my part.
Try as we might, however, Agda will refuse to type check the analogous equality
`x+0≡x`:

```illegal
    x+0≡x : (x : ℕ) → x + zero ≡ x
    x+0≡x _ = refl
```

```info
x + zero != x of type ℕ
when checking that the expression refl has type x + zero ≡ x
```

Inspecting the error message here is quite informative; Agda tells us that `x +
zero` is not the same thing as `x`. This should be quite reminiscent of our
investigations into stuck values in @sec:stuck, which it is. The problem in this
case is that `x` is stuck and `_+_` is defined by induction on its first
argument. Therefore, `_+_` is also stuck, and we are unable to make any progress
on this equality until we can unstick `x`. Like always, the solution to
stuckness is pattern matching:

```agda
    x+0≡x⅋₀ : (x : ℕ) → x + zero ≡ x
    x+0≡x⅋₀ zero = {! !}
    x+0≡x⅋₀ (suc x) = {! !}
```

Immediately, Agda gets unstuck, and tells us now the type of the first hole is
`zero ≡ zero`; which is an easy thing to prove:

```agda
    x+0≡x⅋₁ : (x : ℕ) → x + zero ≡ x
    x+0≡x⅋₁ zero = refl
    x+0≡x⅋₁ (suc x) = {! !}
```

This second goal here is `suc (x + zero) ≡ suc x`, which has arisen from
instantiating the original type at `suc x`. Thus we are trying to show `suc x +
zero ≡ suc x`, which Agda has reduced by noticing the leftmost argument to `_+_`
is a `suc` constructor.

Looking closely, this goal is almost exactly the type of `x+0≡x` itself, albeit
with a `suc` tacked onto either side. If we were to recurse, we could get a
proof of `x + zero ≡ x`, which then seems plausible that we could massage into
the right shape. Let's backtrack on our definition of `x+0≡x` for a moment in
order to work out this problem of fitting a `suc` into a proof-shaped hole.


## Congruence

At first blush, we are trying to solve the following problem:

```agda
    postulate
      _ : (x : ℕ)
        → x + zero ≡ x
        → suc (x + zero) ≡ suc x
```

which we read as "for any number `x : ℕ`, we can transform a proof of `x + zero
≡ x` into a proof of `suc (x + zero) ≡ suc x`." While such a thing is perfectly
reasonable, it seems to be setting the bar too low. Surely it's the case that we
could show the more general solution:

```agda
      _ : {x y : ℕ}
        → x ≡ y
        → suc x ≡ suc y
```


which we informally ready as "if `x` and `y` are equal, then so too are `suc x`
and `suc y`." Notice that while `x` was an *explicit* parameter to the previous
formulation of this idea, we here have made it *implicit.* Since there is no
arithmetic required, Agda is therefore able to unambiguously determine which two
things we're trying to show are equal.

Phrased this way, perhaps again our aims are too narrow. Recall that
propositional equality means "these two values evaluate to identical forms,"
which is to say that, at the end of the day, they are indistinguishable. And if
two things are indistinguishable, then there must not be any way that we can
distinguish between them, including making a function call. Therefore, we can
make the much stronger claim that "if `x` and `y` are equal, then so too are `f
x` and `f y` *for any function* `f`!"

This is a property known as *congruence*, which we again shorten to `cong` due
to the frequency with which we will use this technique in the field. The type of
`cong` is rather involved, but most of the work involved is binding the
relevant variables.

```agda
    cong⅋₀
        : {A B : Set}
        → {x y : A}
        → (f : A → B)
        → x ≡ y
        → f x ≡ f y
    cong⅋₀ f x≡y = ?
```

Proving `cong` is straightforward. We already have a proof that `x ≡ y`. If we
pattern match on this value, Agda is smart enough to rewrite every `y` in the
type as `x`. Thus, after a [MakeCase:x≡y](AgdaCmd):

```agda
    cong⅋₁
        : {A B : Set}
        → {x y : A}
        → (f : A → B)
        → x ≡ y
        → f x ≡ f y
    cong⅋₁ f refl = {! !}
```

our new goal has type `f x ≡ f y`, which is trivially a call to `refl`.

```agda
    cong
        : {A B : Set}
        → {x y : A}
        → (f : A → B)
        → x ≡ y
        → f x ≡ f y
    cong f refl = refl
```

You'll notice something cool has happened here. When we pattern match on a
proof, Agda uses the result as evidence, which can help it get unstuck and make
computational progress. This is an idea we will explore further in
@sec:dot-patterns.

For now, recall that we were looking for a means of completing the following
proof:

```agda
    x+0≡x⅋₂ : (x : ℕ) → x + zero ≡ x
    x+0≡x⅋₂ zero = refl
    x+0≡x⅋₂ (suc x) = {! !}
```

Our new `cong` function fits nicely into this hole:

```agda
    x+0≡x⅋₃ : (x : ℕ) → x + zero ≡ x
    x+0≡x⅋₃ zero = refl
    x+0≡x⅋₃ (suc x) = cong suc {! !}
```

which [Auto](AgdaCmd) will now happily fill for us using recursion:

```agda
    x+0≡x : (x : ℕ) → x + zero ≡ x
    x+0≡x zero = refl
    x+0≡x (suc x) = cong suc (x+0≡x x)
```

Congruence is an excellent tool for doing induction in proofs. You can do
induction as normal, but the resulting proof from the recursive step is usually
not quite be what you need. Luckily, the solution is often just a `cong` away.


## Identities

A common idiom in Agda's standard library are the `-identityˡ` and `-identityʳ`
functions, which are properties stating a binary operation has left- and right-
identities, respectively. An *identity* is any value which doesn't change the
result. As we have just now shown, 0 is both a right and left identity for
addition, because $x + 0 = x$ and $0 + x = x$. In order to get start getting
familiar with these idioms, we can give new our existing proofs:

```agda
    +-identityˡ : (x : ℕ) → zero + x ≡ x
    +-identityˡ = 0+x≡x

    +-identityʳ : (x : ℕ) → x + zero ≡ x
    +-identityʳ = x+0≡x
```

The superscript `l` and `r` here are input as




---






We're merely saying we can build a list, but saying nothing about it. As humans
we might imagine such a list would have length one, and contain the given
element, as in `f1`:

```agda
-- f1 : {A : Set} → A → List A
-- f1 a = a ∷ []
```



## rest

We begin by starting a new module for the chapter, and importing the necessary
proof machinery from Agda's standard library.

```agda
module 2-proofs where

open import Relation.Binary.PropositionalEquality

```

```agda
  -- ∨-identityˡ : (x : Bool) → false ∨ x ≡ x
  -- ∨-identityˡ x = refl
```

What's going on here? How can the right hand side be `refl` without having
pattern matched on the left? Didn't we just have a length discussion about
exactly this? The answer comes from the definition of `_∨_`, which as you will
recall is:

```agda
  -- _∨⅋_ : Bool → Bool → Bool
  -- false ∨⅋ other = other
  -- true  ∨⅋ other = true
```

The first equation here states that anything of the form `false ∨ other` gets
immediately rewritten to `other`, which is exactly what's happening in
`∨-identityʳ`. Agda doesn't need us to pattern match on `x` because the
definition of `_∨_` doesn't need inspect it in order to reduce.

Contrast `∨-identityˡ` to its mirror image:

```agda
  -- ∨-identityʳ : (x : Bool) → x ∨ false ≡ x
  -- ∨-identityʳ false = refl
  -- ∨-identityʳ true  = refl
```

Here we are required to pattern match on `x` because `_∨_` pattern matches on
its first argument, and thus this is the only way to get Agda unstuck. This
kind of asymmetry is intrinsic to Agda's evaluation model, and thus we must be
conscious of it. As a general rule, anything you pattern match on in the
implementation is something you'll need to pattern match on in a proof. As you
become more proficient in Agda, you will start to get an eye for how to write
definitions that are optimized for ease-of-proof. For any particular function,
many definitions are possible, but they will all compute the answer differently,
and thus will have impact upon how we go about proving things.


Exercise

: State and prove `∧-identityˡ`.


Solution

:   ```agda
  -- ∧-identityˡ : (x : Bool) → true ∧ x ≡ x
  -- ∧-identityˡ x = refl
    ```


Exercise

: State and prove `∧-identityʳ`.


Solution

:   ```agda
  -- ∧-identityʳ : (x : Bool) → x ∧ true ≡ x
  -- ∧-identityʳ false = refl
  -- ∧-identityʳ true  = refl
    ```


Identities are especially nice properties to find when designing mathematical
objects; they act like the number 1 does when multiplying (thus the name
"identity".) Identities are useful "placeholders" in algorithms when you need a
default value, but don't have an obvious choice. We will discuss the important
roles of identities further in @sec:objects.

Another useful property for a binary operator is the notion of *associativity,*
which is a familiar fact most commonly known about arithmetic, namely:

$$
(a + b) + c = a + (b + c)
$$

That is to say, the exact placement of parentheses is unimportant for
associative operators, and for that reason, we are justified in leaving them
out, as in:

$$
a + b + c
$$

Technically such a statement is ambiguous, but the great thing about
associativity is it means the two possible parses are equal. As it happens,
`_∨_` is associative, as we can show:

```agda
  -- ∨-assoc : (a b c : Bool) → (a ∨ b) ∨ c ≡ a ∨ (b ∨ c)
  -- ∨-assoc false b c = refl
  -- ∨-assoc true  b c = refl
```


Exercise

: Is `_∧_` also associative? If so, prove it. If not, explain why.


Solution

:   ```agda
  -- ∧-assoc : (a b c : Bool) → (a ∧ b) ∧ c ≡ a ∧ (b ∧ c)
  -- ∧-assoc false b c = refl
  -- ∧-assoc true  b c = refl
    ```

We have two final properties we'd like to prove about our binary number system,
which is the fact that `_∨_` and `_∧_` are *commutative.* Commutative operators
are ones which are symmetric about their arguments. Again, this property is best
known as a fact about addition:

$$
a + b = b + a
$$

In general, a binary operator is commutative if we can swap its arguments
without changing the result. We can prove this about `_∨_` by pattern matching
on every argument:

```agda
  -- ∨-comm : (x y : Bool) → x ∨ y ≡ y ∨ x
  -- ∨-comm false false = refl
  -- ∨-comm false true  = refl
  -- ∨-comm true  false = refl
  -- ∨-comm true  true  = refl
```

While such a thing works, this is clearly a very tedious proof. The amount of
effort grows exponentially with the number of arguments, which feels especially
silly when the right hand side is always just `refl`. Thankfully, Agda has a
tactic for this. A *tactic* is a generic algorithm for producing a proof term;
and in this case, we're looking for the `case-bash!` tactic. Using `case-bash!`,
we can rewrite `∨-comm` as:

```agda
  -- ∨-comm⅋ : (x y : Bool) → x ∨ y ≡ y ∨ x
  -- ∨-comm⅋ = case-bash!
  --   -- TODO(sandy): find the right module
  --   where open import case-bash
```

Similarly, we can case bash our way through `∧-comm`, though if we'd like, we
can import `case-bash` into the global scope:

```agda
  -- open import case-bash

  -- ∧-comm : (x y : Bool) → x ∧ y ≡ y ∧ x
  -- ∧-comm = case-bash!
```

We've now had some experience proving theorems about our code. Of course, the
finiteness of the booleans has dramatically simplified the problem, requiring no
creativity in finding the proofs; indeed the fact that the computer can write
them for us via `case-bash!` is a little disheartening. Nevertheless, it's a
great opportunity to get a feel for proving in a safe environment. We'll have to
learn some new tricks if we'd like to succeed in proving things about the
natural numbers.

In the future, if you need any properties about the booleans, you don't need to
prove them for yourself; most things you could possibly want are already proven
for you under `Data.Bool.Properties`.


## Facts About Natural Numbers

```agda
module Nat-Properties where
```

In this section, our goal is to prove associativity and commutativity of both
addition and multiplication of natural numbers. Now that we are working in an
infinite universe, with more naturals than we can enumerate, we find ourselves
lost in the dark. Our proof knowledge learned from boolean exposure is simply
not powerful to help us here. We are going to need to learn some new tricks.

The first and most important new technique we will need is `cong`, which you
already have available to you via `PropositionalEquality`. Nevertheless, its
definition is the rather overwhelming:

```agda
  cong⅋
      : {A B : Set} {x y : A}
      → (f : A → B)
      → x ≡ y
      → f x ≡ f y
  cong⅋ f refl = refl
```

This peculiar function's name is short for *congruence,* which is the property
that functions preserve equality. That is, given some function `f`, we know that
if `x ≡ y`, then it is surely the case that `f x ≡ f y`. It has to be, because
`x` and `y` are the same thing, so the function must map the one thing to one
place. Congruence is a real workhorse in proving, as it allows us to "move" a
proof of a smaller claim into the right place in a larger theorem. We will see
an example of it shortly.

Proving associativity of multiplication over the natural numbers is a very tall
order; this is not a fact that comes lightly to us. In fact, we will need to
prove nine smaller theorems first, gradually working our way up to the eventual
goal. This is not unlike software, where we decompose hard problems into easier
problems, solve them, and then recombine the solutions. A small theorem, proven
along the way of a bigger theorem, is often called a *lemma.*

Our first lemma is `+-identityʳ`, which is to say, that 0 acts as a right
identity to addition. That is, we're looking to show the following:

```agda
  -- +-identityʳ : (x : ℕ) → x + 0 ≡ x
```

We begin as we did for booleans; pattern matching on the argument. If it's zero,
we're already done:

```agda
  -- +-identityʳ zero = refl
```

If our parameter isn't zero, then it must be `suc x` for some `x`. In this case,
our goal is refined as `suc (x + 0) ≡ suc x`, which you will notice is very
close to `x + 0 ≡ x` --- that is, the thing we're trying to prove in the first
place! Recursion is almost certainly the answer, but it's not quite the right
shape; somehow we need to pin a `suc` on both sides.

Fortunately, this is exactly what `cong` does. Recursion will give us a proof of
`x + 0 ≡ x`, which we need to somehow massage into a proof that `suc (x + 0) ≡
suc x`. Therefore, our lemma is completed as:

```agda
  -- +-identityʳ (suc x) = cong suc (+-identityʳ x)
```


Exercise

: Determine the appropriate type of `*-identityʳ` and prove it.


Solution

:   ```agda
  -- *-identityʳ : (x : ℕ) → x * 1 ≡ x
  -- *-identityʳ zero = refl
  -- *-identityʳ (suc x) = cong suc (*-identityʳ x)
    ```


Exercise

: Use a similar technique to prove `+-suc : (x y : ℕ) → x + suc y ≡ suc (x + y)`.


Solution

:   ```agda
  -- +-suc : (x y : ℕ) → x + suc y ≡ suc (x + y)
  -- +-suc zero y = refl
  -- +-suc (suc x) y = cong suc (+-suc x y)
    ```


Believe it or not, but we now have enough lemmas in place to successfully be
able to prove the associativity and commutativity of `_+_`. We will do
associativity together, because the approach comes with a new proof technique:
*equational reasoning.* Whenever you are proving facts about `_≡_, you can `open
≡-Reasoning`, which brings some nice syntax for reasoning into scope. Consider
`+-assoc`:

```agda
  -- +-assoc : (x y z : ℕ) → (x + y) + z ≡ x + (y + z)
  -- +-assoc zero y z = refl
  -- +-assoc (suc x) y z = begin
  --   (suc x + y) + z    ≡⟨⟩
  --   suc (x + y) + z    ≡⟨⟩
  --   suc ((x + y) + z)  ≡⟨ cong suc (+-assoc x y z) ⟩  -- ! 1
  --   suc (x + (y + z))  ≡⟨⟩
  --   suc x + (y + z)    ∎
  --   where open ≡-Reasoning
```

In the second clause of `+-assoc`, we did `where open ≡-Reasoning`, which allows
us to write the series of equations above. Equational reasoning is an essential
technique for proofs; our human brains simply aren't sophisticated enough to
hold all the relevant details in mind. Instead, we can start with the left-
and right- hand sides of what we're trying to prove, and try to meet in the
middle. An equational reasoning block is started via `begin`, ended with the
"tombstone" character `∎`, and inside allows us to separate values via the
`_≡⟨⟩_` operator. If you look closely, you'll notice two separators here:
`_≡⟨⟩_` which helps the reader follow Agda's computational rewriting (but does
nothing to help Agda.) The other separator is `_≡⟨_⟩_` as used at [1](Ann),
which allows us to put a *justification* for the rewrite in between the
brackets. This form is necessary whenever you'd like to invoke a lemma to help
prove the goal.


Exercise

: Prove `+-comm : (x y : ℕ) → x + y ≡ y + x` using the equational reasoning
  style.


Solution

:   ```agda
  -- +-comm : (x y : ℕ) → x + y ≡ y + x
  -- +-comm zero y = sym (+-identityʳ y)
  -- +-comm (suc x) y = begin
  --   suc x + y    ≡⟨⟩
  --   suc (x + y)  ≡⟨ cong suc (+-comm x y) ⟩
  --   suc (y + x)  ≡⟨ sym (+-suc y x) ⟩
  --   y + suc x    ∎
  --   where open ≡-Reasoning
    ```

Often, a huge amount of the work to prove something is simply in manipulating
the expression to be of the right form so that you can apply the relevant lemma.
This is the case in `*-suc`, which allows us to expand a `suc` on the right side
of a multiplication term:

```agda
  -- *-suc : (x y : ℕ) → x * suc y ≡ x + x * y
  -- *-suc zero y = refl
  -- *-suc (suc x) y = begin
  --   suc x * suc y          ≡⟨⟩
  --   suc y + x * suc y      ≡⟨ cong (λ φ → suc y + φ) (*-suc x y) ⟩
  --   suc y + (x + x * y)    ≡⟨⟩
  --   suc (y + (x + x * y))
  --                        ≡⟨ cong suc (sym (+-assoc y x (x * y))) ⟩
  --   suc ((y + x) + x * y)
  --               ≡⟨ cong (λ φ → suc (φ + x * y)) (+-comm y x) ⟩
  --   suc ((x + y) + x * y)  ≡⟨ cong suc (+-assoc x y (x * y)) ⟩
  --   suc (x + (y + x * y))  ≡⟨⟩
  --   suc x + (y + x * y)    ≡⟨⟩
  --   suc x + (suc x * y)    ∎
  --   where open ≡-Reasoning
```

We're now on the homestretch. As a simple lemma, we can show that `_* zero` is
equal to zero:

```agda
  -- *-zeroʳ : (x : ℕ) → x * 0 ≡ 0
  -- *-zeroʳ zero = refl
  -- *-zeroʳ (suc x) = *-zeroʳ x
```

and we are now ready to prove `*-comm`, one of our major results in this
chapter.


Exercise

: Prove the commutativity of multiplication of the natural numbers.


Solution

  : ```agda
  -- *-comm : (x y : ℕ) → x * y ≡ y * x
  -- *-comm zero y = sym (*-zeroʳ y)
  -- *-comm (suc x) y = begin
  --   suc x * y  ≡⟨⟩
  --   y + x * y  ≡⟨ cong (y +_) (*-comm x y) ⟩
  --   y + y * x  ≡⟨ sym (*-suc y x) ⟩
  --   y * suc x  ∎
  --   where open ≡-Reasoning
    ```

```agda
  -- *-distribʳ-+ : (x y z : ℕ) → (y + z) * x ≡ y * x + z * x
  -- *-distribʳ-+ x zero z = refl
  -- *-distribʳ-+ x (suc y) z = begin
  --   (suc y + z) * x      ≡⟨⟩
  --   x + (y + z) * x      ≡⟨ cong (x +_) (*-distribʳ-+ x y z) ⟩
  --   x + (y * x + z * x)  ≡⟨ sym (+-assoc x (y * x) (z * x)) ⟩
  --   (x + y * x) + z * x  ≡⟨⟩
  --   suc y * x + z * x    ∎
  --   where open ≡-Reasoning

  -- *-assoc : (x y z : ℕ) → (x * y) * z ≡ x * (y * z)
  -- *-assoc zero y z = refl
  -- *-assoc (suc x) y z = begin
  --   suc x * y * z        ≡⟨⟩
  --   (y + x * y) * z      ≡⟨ *-distribʳ-+ z y (x * y) ⟩
  --   y * z + (x * y) * z  ≡⟨ cong (λ φ → y * z + φ) (*-assoc x y z) ⟩
  --   y * z + x * (y * z)  ≡⟨⟩
  --   suc x * (y * z)      ∎
  --   where open ≡-Reasoning
```
