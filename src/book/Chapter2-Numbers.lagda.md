---
suppress-bibliography: true
...

# An Exploration of Numbers {#sec:chapter2}

Hidden

:   ```agda
{-# OPTIONS --allow-unsolved-metas #-}
    ```

In this chapter, we will get our hands dirty, implementing several different
number systems in Agda. The goal is threefold: to get some experience thinking
about how to model problems in Agda, to practice seeing familiar objects with
fresh eyes, and to get familiar with many of the mathematical objects we'll need
for the remainder of the book.

Before we start, note that this chapter has prerequisite knowledge from
@sec:chapter1. And, as always, every new chapter must start a new module:

```agda
module Chapter2-Numbers where
```

Prerequisites

:   ```agda
import Chapter1-Agda
    ```


As you might expect, Agda already has support for numbers, and thus everything
we do here is purely to enhance our understanding. That being said, it's
important to get an intuition for how we can use Agda to solve problems. Numbers
are simultaneously a domain you already understand, and, in most programming
languages, they usually come as pre-built, magical primitives.

This is not true in Agda: numbers are *defined* in library code. Our approach
will be to build the same number system exported by the standard library so we
can peek at how it's done. Again, this is just an exercise; after this chapter,
we will just use the standard library's implementation, since it will be more
complete, and allow us better interopability when doing real work.


## Natural Numbers {#sec:naturals}

It is one thing to say we will "construct the numbers," but doing so is much
more involved. The first question to ask is *which numbers?* As it happens, we
will build all of them.

But that is just passing the buck. What do we mean by "all" the numbers? There
are many different sets of numbers. For example, there are the numbers we use to
count in the real world (which start at 1.) There are also the numbers we use to
index in computer science (which begin at 0.) There are the *integers*, which
contain negatives. And then there are the *rationals* which contain fractions,
and happen to be all the numbers you have ever encountered in real life.

But somehow, not even that is all the numbers. Beyond the rationals are the
*reals*, which are somehow bigger than all the numbers you have actually
experienced, and in fact are so big that the crushing majority of them are
completely inaccessible to us.

The party doesn't stop there. After the reals come the *complex numbers* which
have an "imaginary" part---whatever that means. Beyond those are the
*quaternions*, which come with three different varieties of imaginary parts, and
beyond those, the *octonions* (which have *seven* different imaginaries!)

In order to construct "the numbers," we must choose between these (and many
other) distinct sets. And those are just some of the number systems
mathematicians talk about. But worse, there are the number systems that computer
scientists use, like the *bits*, the *bytes*, the *words*, and by far the worst
of all, the IEEE 754 "floating point" numbers known as *floats* and *doubles*.

You, gentle reader, are probably a programmer, and it is probably in number
systems such as these that you feel more at home. We will not, however, be
working with number systems of the computer science variety, as these are
extremely non-standard systems of numbers, with all sorts of technical
difficulties that you have likely been burned so badly by that you have lost
your pain receptors.

Who among us hasn't been bitten by an integer overflow, where adding two
positive numbers somehow results in a negative one? Or by the fact that, when
working with floats, we get different answers depending on which two of three
numbers we multiply together first.

One might make a successful argument that these are necessary limitations of
our computing hardware. As a retort, I will only point to the co-Blub paradox
(@sec:coblub), and remind you that our goal here is to learn *how things can
be,* rather than limit our minds to the way we perceive things must be. After
all, we cannot hope to reach paradise if we cannot imagine it.

And so we return to our original question of which number system we'd like to
build. As a natural starting point, we will pick the simplest system that it
seems fair to call "numbers": the *naturals.* These are the numbers you learn as
a child, in a simpler time, before you needed to worry about things like
negative numbers, decimal points, or fractions.

The natural numbers start at 0, and proceed upwards exactly one at a time, to 1,
then 2, then 3, and so on and so forth. Importantly to the computer scientist,
there are *infinitely many* natural numbers, and we intend to somehow construct
*every single one of them.* We will not placate ourselves with arbitrary upper
limits, or with arguments of the form "X ought to be enough for anyone."


Hidden

:   ```agda
module ScopingTheExpr where
  open import Data.Nat
    ```

How can we hope to generate an infinite set of numbers? The trick isn't very
impressive---in fact, I've already pointed it out. You start at zero, and then
you go up one at a time, forever. In Agda, we can encode this by saying
`ctor:zero` is a natural number, and that, given some number `n`, we can
construct the next number up---its *successor*---via `ctor:suc` `n`. Such an
encoding gives rise to a rather elegant (if *inefficient*, but, remember, we
don't care) specification of the natural numbers. Under such a scheme, we would
write the number 3 as `expr:suc (suc (suc zero))`.

It is important to stress that this is a *unary* encoding, rather than the
traditional *binary* encoding familiar to computer scientists. There is nothing
intrinsically special about binary; it just happens to be an easy thing to build
machines that can distinguish between two states: whether they be magnetic
forces, electric potentials, or the presence or absence of a bead on the wire of
an abacus. Do not be distraught; working in unary *dramatically* simplifies
math, and if you are not yet sold on the approach, you will be before the end of
this chapter.

But enough talk. It's time to conjure up the natural numbers. In the
mathematical literature, the naturals are denoted by the *blackboard bold*
symbol `ℕ`---a convention we too will adopt. You can input this symbol via
[`bN`](AgdaMode).


Hidden

:   ```agda
-- fix indentation
    ```


```agda
module Definition-Naturals where
  data ℕ : Set where
    zero  : ℕ
    suc   : ℕ → ℕ  -- ! 1
```

Hidden

:   ```agda
  -- fix indentation
    ```

Here we use the `keyword:data` keyword to construct a type consisting of several
different constructors. In this case, a natural is either a `ctor:zero` or it is
a `ctor:suc` of some other natural number. You will notice that we must give
explicit types to constructors of a `keyword:data` type, and at [1](Ann) we give
the type of `ctor:suc` as `expr:ℕ → ℕ`. This is the precise meaning that a
`ctor:suc` is "of some other natural number." You can think of `ctor:suc` as the
mathematical function:

$$
x \mapsto x + 1
$$

although this is just a mental shortcut, since we do not yet have formal
definitions for addition or the number 1.


## Brief Notes on Data and Record Types

Before we play around with our new numeric toys, I'd like to take a moment to
discuss some of the subtler points around modeling data in Agda.

The `keyword:data` keyword also came up when we defined the booleans in
@sec:bools, as well as for other toy examples in @sec:chapter1.

Indeed, `keyword:data` will arise whenever we'd like to build a type whose
values are *apart*---that is, new symbols whose purpose is in their
distinctiveness from one another. The boolean values `ctor:false` and
`ctor:true` are just arbitrary symbols, which we assign meaning to only by
convention. This meaning is justified exactly because `ctor:false` and
`ctor:true` are *distinct symbols.*

This distinctness is also of the utmost importance when it comes to numbers. The
numbers are interesting to us only because we can differentiate one from two,
and two from three. Numbers are a collection of symbols, all distinct from one
another, and it is from their apartness that we derive importance.

As a counterexample, imagine a number system in which there is only one number.
Not very useful, is it?

Contrast this apartness to the tuple type, which you'll recall was a type
defined via `keyword:record` instead of `keyword:data`. In some sense, tuples
exist only for bookkeeping. The tuple type doesn't build new things, it just
lets you simultaneously move around two things that already exist. Another way
to think about this is that `keyword:record`s are made up of things that already
exist, while `keyword:data` types create new things *ex nihilo.*

Most programming languages have a concept of `keyword:record` types (whether
they be called *structures*, *tuples*, or *classes*), but very few support
`keyword:data` types. Booleans and numbers are the canonical examples of
`keyword:data` types, and the lack of support for them is exactly why these two
types are usually baked into to a language.

It can be tempting to think of types defined by `keyword:data` as enums, but
this is a subtly misleading. While enums are indeed apart from one another, this
comes from the fact that enums are just special names given to particular values
of ints. This is an amazingly restricting limitation.

Note that in Agda, `keyword:data` types are strictly more powerful than enums,
because they don't come with this implicit conversion to ints. As a quick
demonstration, note that `ctor:suc` is apart from `ctor:zero`, but `ctor:suc`
can accept any `type:ℕ` as an *argument!* While there are only $2^{64}$ ints,
there are *infinitely many* `type:ℕ`s, and thus types defined by `keyword:data`
in Agda must be more powerful than those defined as enums in other languages.

More generally, constructors in `keyword:data` types can take *arbitrary*
arguments, and we will often use this capability moving forwards.


## Playing with Naturals

Let's return now to our discussion of the naturals. Since we'd like to reuse the
things we build in future chapters, let's first import the natural numbers from
the standard library.

```agda
module Sandbox-Naturals where
  open import Data.Nat
    using (ℕ; zero; suc)
```

By repeated application of
`ctor:suc`, we can build an infinite tower of natural numbers, the first four of
which are built like this:

```agda
  one : ℕ
  one = suc zero

  two : ℕ
  two = suc one

  three : ℕ
  three = suc two

  four : ℕ
  four = suc three
```

Of course, these names are just for syntactic convenience; we could have instead
defined `def:four` thusly:

```agda
  four⅋ : ℕ
  four⅋ = suc (suc (suc (suc zero)))
```

It is tempting to use the traditional base-ten symbols for numbers, and of
course, Agda supports this (although setting it up will require a little more
effort on our part.) However, we will persevere with our explicit unary encoding
for the time being, to really hammer-in that there is no magic happening behind
the scenes here.

The simplest function we can write over the naturals is to determine whether or
not the argument is equal to 0. For the sake of simplicity, this function will
return a boolean, but note that this is a bad habit in Agda. There are
much better techniques that don't lead to *boolean blindness* that we will
explore in @sec:decidability. This function therefore is only provided to help
us get a feel for pattern matching over natural numbers.

We can get access to the booleans by importing them from our exports from
@sec:chapter1:

```agda
  open Chapter1-Agda
    using (Bool; true; false)
```

The function we'd like to write determines if a given `type:ℕ` is equal to
`ctor:zero`, so we can begin with a name, a type signature, and a hole:

```agda
  n=0?⅋₁ : ℕ → Bool
  n=0?⅋₁ = ?
```

After [MakeCase](AgdaCmd), our argument is bound for us:

```agda
  n=0?⅋₂ : ℕ → Bool
  n=0?⅋₂ n = {! !}
```

and, like when writing functions over the booleans, we can immediately
[`MakeCase:n`](AgdaCmd) to split `n` apart into its distinct possible
constructors:

```agda
  n=0?⅋₃ : ℕ → Bool
  n=0?⅋₃ zero     = {! !}
  n=0?⅋₃ (suc x)  = {! !}  -- ! 1
```

Interestingly, at [1](Ann), Agda has given us a new form, something we didn't
see when considering the booleans. We now have a pattern match of the form
`ctor:suc` `x`, which after some mental type-checking, makes sense. We said `n`
was a `type:ℕ`, but `ctor:suc` has type `expr:ℕ → ℕ`. That means, `n` can only
be a natural number of the `ctor:suc` form *if that function has already been
applied to some other number.* And `x` is that other number.

The interpretation you should give to this expression is that if $n$ is of the
form `ctor:suc` `x`, then $x = n - 1$. Note that `ctor:zero` is not of the form
`ctor:suc` `x`, and thus we don't accidentally construct any negative numbers
under this interpretation.

Returning to `def:n=0?`, we care only if our original argument `n` is
`ctor:zero`, which we can immediately solve from here---without needing to do
anything with `x`:

```agda
  n=0? : ℕ → Bool
  n=0? zero     = true
  n=0? (suc x)  = false
```

It will be informative to compare this against a function that computes whether
a given natural is equal to 2.


Exercise (Easy)

:   Implement `def:n=2?` `:` `expr:ℕ → Bool`


Solution

:   ```agda
  n=2? : ℕ → Bool
  n=2? zero                 = false
  n=2? (suc zero)           = false
  n=2? (suc (suc zero))     = true
  n=2? (suc (suc (suc x)))  = false
    ```

:   or, alternatively:

:   ```agda
  n=2?⅋ : ℕ → Bool
  n=2?⅋ (suc (suc zero))  = true
  n=2?⅋ _                 = false
    ```


## Induction

Unlike functions out of the booleans, where we only had two possibilities to
worry about, functions out of the naturals have (in principle) an infinite
number of possibilities. But our program can only ever be a finite number of
lines, which leads to a discrepancy. How can we possibly reconcile an infinite
number of possibilities with a finite number of cases?

Our only option is to give a finite number of interesting cases, and then a
default case which describes what to do for everything else. Of course, nothing
states that this default case must be constant, or even simple. That is to say,
we are not required to give the *same* answer for every number above a certain
threshold.

To illustrate this, we can write a function which determines whether its
argument is even. We need only make the (mathematical) argument that "a number
$n + 2$ is even if and only if the number $n$ is." This is expressed naturally
by recursion:

```agda
  even? : ℕ → Bool
  even? zero           = true
  even? (suc zero)     = false
  even? (suc (suc x))  = even? x
```

Here, we've said that `ctor:zero` is even, `def:one` is not, and for every other
number, you should subtract two (indicated by having removed two `ctor:suc`
constructors from `x`) and then try again.

This general technique---giving some explicit answers for specific inputs, and
recursing after refining---is known as *induction.*

It is impossible to overstate how important induction is. Induction is the
fundamental mathematical technique. It is the primary workhorse of all
mathematics.

Which makes sense; if you need to make some argument about an infinite number of
things, you can neither physically nor theoretically analyze each and every
possible case. You instead must give a few (usually very simple) answers, and
otherwise show how to reduce a complicated problem into a simpler one. This
moves the burden of effort from the theorem prover (you) to whomever wants an
answer, since they are the ones who become responsible for carrying out the
repetitive task of reduction to simpler forms. However, this is not so bad,
since the end-user is the one who wants the answer, and they necessarily have a
particular, finite problem that they'd like to solve.

Not being very creative, mathematicians often *define* the principle of
induction as being a property of the natural numbers. They say all of
mathematics comes from:

1. *a base case*---that is, proving something in the case that $n=0$
2. *an inductive case*---that is, showing something holds in the case of $n$
   under the assumption that it holds under $n - 1$.

However, the exact same technique can be used for any sort of
recursively-defined type, such as lists, trees, graphs, matrices, etc. While
perhaps you could shoe-horn these to fit into the natural numbers, it would be
wasted effort in order to satisfy nothing but a silly definition. That
notwithstanding, the terminology itself is good, and so we will sometimes refer
to recursive steps as "induction" and non-recursive steps as "base cases."


## Two Notions of Evenness {#sec:even}

We have now defined `def:even?` a function which determines whether a given natural
number is even. A related question is whether we can define a type for *only*
the even numbers. That is, we'd like a type which contains 0, 2, 4, and so on,
but neither 1, nor 3, nor *any* of the odd numbers.

In a monkey-see-monkey-do fashion, we could try to define a new type called
`type:Evenℕ` with a constructor for `ctor:zero`, but unlike `type:ℕ`, no
`ctor:suc`. Instead, we will give a constructor called `ctor:suc-suc`, intending
to be suggestive of taking two successors simultaneously:

```agda
  data Evenℕ : Set where
    zero     : Evenℕ
    suc-suc  : Evenℕ → Evenℕ
```

We can transform an `type:Evenℕ` into a `type:ℕ` by induction:

```agda
  toℕ⅋ : Evenℕ → ℕ
  toℕ⅋ zero         = zero
  toℕ⅋ (suc-suc x)  = suc (toℕ⅋ x)
```

This approach, however, feels slightly underwhelming. The reflective reader will
recall that in a `keyword:data` type, the *meaning* of the constructors comes
only from their types and the suggestive names we give them. A slight renaming
of `ctor:suc-suc` to `ctor:suc` makes the definition of `type:Evenℕ` look very
similar indeed to that of `def:ℕ`. In fact, the two types are completely
equivalent, modulo the names we picked.

As such, there is nothing stopping us from writing an incorrect (but not
*obviously* wrong) version of the `def:toℕ` function. On that note, did you
notice that the definition given above *was* wrong? Oops! Instead, the correct
implementation should be this:

```agda
  toℕ : Evenℕ → ℕ
  toℕ zero         = zero
  toℕ (suc-suc x)  = suc (suc (toℕ x))
```

You might want to double check this new definition, just to make sure I haven't
pulled another fast one on you. Double checking, however, is tedious and error
prone, and in an ideal world, we'd prefer to find a way to get the computer to
double check on our behalf.

Rather than trying to construct a completely new type for the even naturals,
perhaps we can instead look for a way to filter for only the naturals we want. A
mathematician would look at this problem and immediately think to build a
*subset*---that is, a restricted collection of the objects at study. In this
particular case, we'd like to build a subset of the natural numbers which
contains only those that are even.

The high-level construction here is we'd like to build `type:IsEven` `:` `expr:ℕ
→ Set`, which, like you'd think, is a function that takes a natural and returns
a type. The idea that we can *compute* types in this way is rare in programming
languages, but is very natural in Agda.

In order to use `type:IsEven` as a subset, it must return some sort of "usable"
type when its argument is even, and an "unusable" type otherwise. We can take
this function idea literally if we'd please, and postulate two appropriate
types:

```agda
  module Sandbox-Usable where
    postulate
      Usable    : Set
      Unusable  : Set

    IsEven : ℕ → Set
    IsEven zero           = Usable
    IsEven (suc zero)     = Unusable
    IsEven (suc (suc x))  = IsEven x
```

You will notice the definition of `type:IsEven` is identical to that of
`def:even?` except that we replaced `type:Bool` with `type:Set`, `ctor:true`
with `type:Usuable`, and `ctor:false` with `type:Unusuable`. This is what you
should expect, as `def:even?` was already a function that computed whether
a given number is even!

While we could flesh this idea out in full by finding specific (non-postulated)
types to use for `postulate:Usuable` and `postulate:Unusuable`, constructing
subsets in this way isn't often fruitful. Though it occasionally comes in handy,
and it's nice to know you can compute types directly in this way.

Let's drop out of the `module:Sandbox-Usable` module, and try defining
`type:IsEven` in a different way.

The situation here is analogous to our first venture into typing judgments in
@sec:bools. While it's possible to do all of our work directly with postulated
judgments, Agda doesn't give us any help in doing so. Instead, things
became much easier when we used a more principled structure---namely, using the
`keyword:data` type. Amazingly, here too we can use a `keyword:data` type to
solve our problem. The trick is to add an *index* to our type, which you can
think of as a "return value" that comes from our choice of constructor.

Don't worry, the idea will become much clearer in a moment after we look at an
example. Let's begin just with the `data` declaration:

```agda
  data IsEven : ℕ → Set where  -- ! 1
```

Every type we have seen so far has been of the form `keyword:data` `X :`
`type:Set`, but at [1](Ann) we have `type:ℕ` `→` `type:Set` on the right side of
the colon. Reading this as a type declaration directly, it says that this type
`type:IsEven` we're currently defining *is exactly* the function we were looking
for earlier---the one with type `type:ℕ → Set`. Because of this parameter, we
say that `type:IsEven` is an *indexed type*, and that the `type:ℕ` in question
is its index.

Every constructor of an indexed type must fill-in each index. To a first
approximation, constructors of an indexed type are *assertions* about the index.
For example, it is an axiom that `ctor:zero` is an even number, which we can
reflect directly as a constructor:

```agda
    zero-even : IsEven zero
```

Notice that this constructor is equivalent to the base case `def:even?`
`ctor:zero` `=` `ctor:true`. We would like to exclude odd numbers from
`type:IsEven`, so we can ignore the `ctor:suc zero` case for the moment. In the
inductive case, we'd like to say that if $n$ is even, then so too is $n + 2$:

```agda
    suc-suc-even : {n : ℕ} → IsEven n → IsEven (suc (suc n))
```

In a very real sense, our indexed type `type:IsEven` is the "opposite" of our
original decision function `def:even?`. Where before we removed two calls to
`ctor:suc` before recursing, we now recurse first, and then *add* two calls to
`ctor:suc`. This is not a coincidence, but is in fact a deep principle of
mathematics that we will discuss later.

The concept of indexed types is so foreign to mainstream programming that it is
prudent to spend some time here and work through several examples of
what-the-hell-is-happening. Let's begin by showing that `def:four` is even.
Begin with the type and a hole:

```agda
  four-is-even⅋₀ : IsEven four
  four-is-even⅋₀ = ?
```

Here's where things get cool. We can ask Agda to refine this hole via
[Refine](AgdaCmd). Recall that refine asks Agda to fill in the hole with the
only constructor that matches. Rather amazingly, the result of this invocation
is:

```agda
  four-is-even⅋₁ : IsEven four
  four-is-even⅋₁ = suc-suc-even {! !}
```

Even more impressive is that the new goal has type `expr:IsEven two`---which is
to say, we need to show that `def:two` is even in order to show that `def:four`
is even. Thankfully we can ask Agda to do the heavy lifting for us, and again
request a [Refine](AgdaCmd):

```agda
  four-is-even⅋₂ : IsEven four
  four-is-even⅋₂ = suc-suc-even (suc-suc-even {! !})
```

Our new hole has type `expr:IsEven zero`, which again Agda can refine for us:

```agda
  four-is-even : IsEven four
  four-is-even = suc-suc-even (suc-suc-even zero-even)
```

With all the holes filled, we have now successfully proven that `def:four` is in
fact even. But can we trust that this works as intended? Let's see what happens
when we go down a less-happy path. Can we also prove `expr:IsEven three`?

```agda
  three-is-even⅋₀ : IsEven three
  three-is-even⅋₀ = ?
```

Let's play the same refinement game. Invoking [Refine](AgdaCmd) results in:

```agda
  three-is-even : IsEven three
  three-is-even = suc-suc-even {! !}
```

Our new goal is `expr:IsEven one`. But if we try to refine again, Agda gives us
an error:

```info
No introduction forms found.
```

What's (correctly) going wrong here is that Agda is trying to find a constructor
for `expr:IsEven (suc zero)`, but no such thing exists. We have `ctor:zero-even`
for `expr:IsEven zero`, and we have `ctor:suc-suc-even` for `bind:n:IsEven (suc
(suc n))`. But there is no such constructor when we have only one `ctor:suc`!
Thus neither `ctor:zero-even` nor `ctor:suc-suc-even` will typecheck in our
hole. Since these are the *only* constructors, and neither fits, it's fair to
say that *nothing can possibly fill this hole.* There is simply no way to give
an implementation for `def:three-is-even`---it's impossible to construct an
`ctor:IsEven n` whenever `n` is odd.

This is truly a miraculous result, and might give you a glimpse at why we do
mathematics in Agda. The idea is to carefully construct types whose values are
possible only when our desired property is *actually true.* We will explore this
topic more deeply in @sec:proofs.


Exercise (Easy)

:   Build an indexed type for `type:IsOdd`.


Solution

:   ```agda
  data IsOdd : ℕ → Set where
    one-odd      : IsOdd one
    suc-suc-odd  : {n : ℕ} → IsOdd n → IsOdd (suc (suc n))
    ```

:   or, alternatively,

:   ```agda
  data IsOdd' : ℕ → Set where
    is-odd : {n : ℕ} → IsEven n → IsOdd' (suc n)
    ```


Hidden

:   ```agda
  -- fix indentation
    ```


Exercise (Easy)

:   Write an inductive function which witnesses the fact that every even number
    is followed by an odd number. This function should have type `expr:{n : ℕ} → IsEven n → IsOdd (suc n)`.


Solution

:   ```agda
  evenOdd : {n : ℕ} → IsEven n → IsOdd (suc n)
  evenOdd zero-even         = one-odd
  evenOdd (suc-suc-even x)  = suc-suc-odd (evenOdd x)
    ```

:  or, if you took the alternative approach in the previous exercise,

:   ```agda
  evenOdd' : {n : ℕ} → IsEven n → IsOdd' (suc n)
  evenOdd' = is-odd
    ```


## Constructing Evidence {#sec:maybe}

When we originally implemented `def:even?`, I mentioned that functions which
return booleans are generally a bad habit in Agda. You've done a lot of
computation in order to get the answer, and then throw away all of that work
just to say merely "yes" or "no." Instead of returning a `type:Bool`, we could
instead have `def:even?` return an `type:IsEven`, proving the number really is
even!

However, not *all* numbers are even, so we will first need some notion of
failure. This is an excellent use for the `type:Maybe` type, which is a
container that contains exactly zero or one element of some type `A`. We can
define it as:

```agda
  data Maybe (A : Set) : Set where
    just     : A →  Maybe A
    nothing  :      Maybe A
```

Here, `ctor:just` is the constructor for when the `type:Maybe` *does* contain an
element, and `ctor:nothing` is for when it doesn't. `type:Maybe` is a good type
for representing *partial functions*---those which don't always give back a
result. Our desired improvement to `def:even?` is one such function, since there
are naturals in the input which do not have a corresponding value in the output.

Our new function is called `def:evenEv`, to be suggestive of the fact that it
returns *evidence* of the number's evenness. The first thing to study here is
the type:

```agda
  evenEv⅋₀ : (n : ℕ) → Maybe (IsEven n)
  evenEv⅋₀ = ?
```

The type signature of `def:evenEv` says "for some `n :` `type:ℕ`, I can maybe
provide a proof that it is an even number." The implementation will look very
reminiscent of `def:even?`. First, we can do [MakeCase](AgdaCmd) a few times:

```agda
  evenEv⅋₁ : (n : ℕ) → Maybe (IsEven n)
  evenEv⅋₁ zero           = {! !}
  evenEv⅋₁ (suc zero)     = {! !}
  evenEv⅋₁ (suc (suc n))  = {! !}
```

Then, in the `ctor:suc zero` case where we know there is not an answer, we can
give back `ctor:nothing`:

```agda
  evenEv⅋₂ : (n : ℕ) → Maybe (IsEven n)
  evenEv⅋₂ zero           = {! !}
  evenEv⅋₂ (suc zero)     = nothing
  evenEv⅋₂ (suc (suc n))  = {! !}
```

In the case of `ctor:zero`, there definitely *is* an answer, so we refine our
hole with `ctor:just`:

```agda
  evenEv⅋₃ : (n : ℕ) → Maybe (IsEven n)
  evenEv⅋₃ zero           = just {! !}
  evenEv⅋₃ (suc zero)     = nothing
  evenEv⅋₃ (suc (suc n))  = {! !}
```

...but a `ctor:just` of what? The type `expr:IsEven zero` of the goal tells us,
but we can also elicit an answer from Agda by invoking [Refine](AgdaCmd) on our
hole:

```agda
  evenEv⅋₄ : (n : ℕ) → Maybe (IsEven n)
  evenEv⅋₄ zero           = just zero-even
  evenEv⅋₄ (suc zero)     = nothing
  evenEv⅋₄ (suc (suc n))  = {! !}
```

At this step in `def:even?` we just recursed and we were done. However, that
can't quite work here. The problem is that if we were to recurse, we'd get a
result of type `bind:n:Maybe (IsEven n)`, but we need a result of type
`bind:n:Maybe (IsEven (suc (suc n)))`. What needs to happen then is for us to
recurse, *inspect the answer,* and then, if it's `ctor:just`, insert a
`ctor:suc-suc-even` on the inside. It all seems a little convoluted, but the
types are always there to guide you should you ever lose the forest for the
trees.

Agda does allow us to pattern match on the result of a recursive call. This is
known as a `keyword:with` abstraction, and the syntax is as follows:

```agda
  evenEv⅋₅ : (n : ℕ) → Maybe (IsEven n)
  evenEv⅋₅ zero        = just zero-even
  evenEv⅋₅ (suc zero)  = nothing
  evenEv⅋₅ (suc (suc n)) with evenEv⅋₅ n  -- ! 1
  ... | result = {! !}  -- ! 2
```

At [1](Ann), which you will note is on the *left* side of the equals sign, we
add the word `keyword:with` and the expression we'd like to pattern match on.
Here, it's `def:evenEv` `n`, which is the recursive call we'd like to make. At
[2](Ann), we put three dots, a vertical bar, and a name for the resulting value
of the call we made, and then the equals sign. The important thing to note here
is that `result` is a binding that corresponds to the result of having called
`def:evenEv` `n`. This seems like quite a lot of ceremony, but what's cool is
that we can now run [MakeCase:result](AgdaCmd) in the hole to pattern match on
`result`:

```agda
  evenEv⅋₆ : (n : ℕ) → Maybe (IsEven n)
  evenEv⅋₆ zero        = just zero-even
  evenEv⅋₆ (suc zero)  = nothing
  evenEv⅋₆ (suc (suc n)) with evenEv⅋₆ n
  ... | just x   = {! !}
  ... | nothing  = {! !}
```

In the case that `result` is `ctor:nothing`, we know that our recursive call failed,
and thus that $n - 2$ is not even. Therefore, we too should return `ctor:nothing`.
Similarly for the `ctor:just` case:

```agda
  evenEv⅋₇ : (n : ℕ) → Maybe (IsEven n)
  evenEv⅋₇ zero        = just zero-even
  evenEv⅋₇ (suc zero)  = nothing
  evenEv⅋₇ (suc (suc n)) with evenEv⅋₆ n
  ... | just x   = just {! !}
  ... | nothing  = nothing
```

We're close to the end. Now we know that `x :` `type:IsEven` `n` and that our
hole requires an `bind:n:IsEven (suc (suc n))`. We can fill in the rest by hand,
or invoke [Auto](AgdaCmd) to do it on our behalf.

```agda
  evenEv : (n : ℕ) → Maybe (IsEven n)
  evenEv zero        = just zero-even
  evenEv (suc zero)  = nothing
  evenEv (suc (suc n)) with evenEv n
  ... | just x   = just (suc-suc-even x)
  ... | nothing  = nothing
```


## Addition {#sec:addition}

With the concept of induction firmly in our collective tool-belt, we are now
ready to tackle a much more interesting function: addition over the naturals.
Begin with the type, and bind the variables:

```agda
  _+⅋₁_ : ℕ → ℕ → ℕ
  x +⅋₁ y  = ?
```

At first blush, it's not obvious how we might go about implementing this.
Perhaps we could mess about at random and see comes out, but while such a thing
might be fun, it is rarely productive. Instead, we can go at this with a more
structured approach, seeing what happens if we throw induction at the problem.
Doing induction requires something to do *induction* on, meaning we can choose
either `x`, `y` or both simultaneously. In fact, all three cases will work, but,
as a general rule, if you have no reason to pick any parameter in particular,
choose the first one.

In practice, doing induction means calling [MakeCase](AgdaCmd) on your chosen
parameter, and then analyzing if a base case or an inductive case will help in
each resulting equation. Usually, the values which are recursively-defined will
naturally require recursion on their constituent parts. Let's now invoke
[MakeCase:x](AgdaCmd):

```agda
  _+⅋₂_ : ℕ → ℕ → ℕ
  zero   +⅋₂ y = {! !}
  suc x  +⅋₂ y = {! !}
```

Immediately a base case is clear to us; adding zero to something doesn't change
it. In fact, that's the *definition* of zero. Thus, we have:

```agda
  _+⅋₃_ : ℕ → ℕ → ℕ
  zero   +⅋₃ y = y
  suc x  +⅋₃ y = {! !}
```

The second case here clearly requires recursion, but it might not immediately be
clear what that recursion should be. The answer is to squint and reinterpret
`ctor:suc` `x` as $1 + x$, which allows us to write our left hand side as

$$
(1 + x) + y
$$

If we were to reshuffle the parentheses here, we'd get an $x + y$ term on its
own, which is exactly what we need in order to do recursion. In symbols, this
inductive case is thus written as:

$$
(1 + x) + y = 1 + (x + y)
$$

which translates back to Agda as our final definition of addition:


```agda
  _+_ : ℕ → ℕ → ℕ
  zero   + y = y
  suc x  + y = suc (x + y)
```

With a little thought, it's clear that this function really does implement
addition. By induction, the first argument might be of the form `ctor:zero`, in
which case it adds nothing to the result.

Otherwise, the first argument must be of the form `ctor:suc` `x`, in which case
we assume `bind:x y:x + y` properly implements addition. Then, we observe the
fact that $(1 + x) + y = 1 + (x + y)$. This is our first mathematical proof,
although it is a rather "loose" one: argued out in words, rather than being
*checked* by the computer. Nevertheless, it is a great achievement on our path
towards mathematical fluency and finesse.

To wrap things up, we will add a fixity declaration for `def:_+_` so that it
behaves nicely as an infix operator. We must choose a direction for repeated
additions to associate. In fact, it doesn't matter one way or another (and we
used the fact that it doesn't matter in the inductive case of `def:_+_`.) But,
looking forwards, we realize that subtraction *must* be left-associative in
order to get the right answer, and therefore it makes sense that addition should
also be left-associative. As a matter of convention, we will pick precedence 6
for this operator.

```agda
  infixl 6 _+_
```


## Termination Checking

There is a subtle point to be made about our implementation of `def:_+_`, namely
that the parentheses are extremely important. Our last line is written as
`ctor:suc` `x` `def:+` `y` `=` `ctor:suc` `(x` `def:+` `y)`, but if you were to
omit the parentheses, the last line becomes `ctor:suc` `x` `def:+` `y` `=`
`ctor:suc` `x` `def:+` `y`. Such a statement is unequivocally *true*, but is
also computationally *unhelpful.* Since both sides of the equation are
syntactically identical, Agda has no ability to make computational progress by
rewriting one side as the other. In fact, if such a thing were allowed, it would
let you prove anything at all! The only caveat would be that if you tried to
inspect the proof, your computer would fall into an infinite loop, rewriting the
left side of the equation into the right, forever.

Fortunately, Agda is smart enough to identify this case, and will holler,
complaining about "termination checking" if you attempt to do it:

```illegal
  _+⅋₀_ : ℕ → ℕ → ℕ
  zero   +⅋₀ y = y
  suc x  +⅋₀ y = suc x +⅋₀ y
```

```info
Termination checking failed for the following functions:
  Sandbox-Naturals._+⅋₀_
Problematic calls:
  suc x +⅋₀ y
```

By putting in the parentheses, `bind:x y:suc (x + y)` is now recursive, and,
importantly, it is recursive on *structurally smaller* inputs than it was given.
Since the recursive call must be smaller (in the sense of there is one fewer
`ctor:suc` constructor to worry about,) eventually this recursion must
terminate, and thus Agda is happy.

Agda's termination checker can help keep you out of trouble, but it's not the
smartest computer program around. The termination checker will only let you
recurse on bindings that came from a pattern match, and, importantly, you're not
allowed to fiddle with them first. As a quick, silly, illustration, we could
imagine an alternative `type:ℕ'`, which comes with an additional `ctor:2suc`
constructor corresponding to `ctor:suc`ing twice:

```agda
  module Example-Silly where
    open Chapter1-Agda
      using (not)

    data ℕ' : Set where
      zero  : ℕ'
      suc   : ℕ' → ℕ'
      2suc  : ℕ' → ℕ'
```

We can now write `def:even?'`, whose `ctor:2suc` case is `def:not` of
`def:even?'` (`ctor:suc` n):

```illegal
    even?'⅋ : ℕ' → Bool
    even?'⅋ zero      = true
    even?'⅋ (suc n)   = not (even?'⅋ n)
    even?'⅋ (2suc n)  = not (even?'⅋ (suc n))
```

Tracing the logic here, it's clear to us as programmers that this function will
indeed terminate. Unfortunately, Agda is not as smart as we are, and rejects the
program:

```info
Termination checking failed for the following functions:
  Sandbox-Naturals.Example-Silly.even?'
Problematic calls:
  even?' (suc n)
```

The solution to termination problems like these is just to unwrap another layer
of constructors:

```agda
    even?' : ℕ' → Bool
    even?' zero             = true
    even?' (suc n)          = not (even?' n)
    even?' (2suc zero)      = true
    even?' (2suc (suc n))   = not (even?' n)
    even?' (2suc (2suc n))  = even?' n
```

It's not the nicest solution, but it gets the job done.


## Multiplication and Exponentiation {#sec:multiplication}

With addition happily under our belt, we will try our hand at multiplication.
The approach is the same as with addition: write down the type of the operation,
bind the variables, do induction, and use algebraic identities we remember from
school to help figure out the actual logic. The whole procedure is really quite
underwhelming once you get the hang of out!

After writing down the type and binding some variables, we're left with the
following:

```agda
  _*⅋₁_ : ℕ → ℕ → ℕ
  a *⅋₁ b = {! !}
```

We need to do induction on one of these bindings; because we have no reason to
pick one or the other, we default to `a`:

```agda
  _*⅋₂_ : ℕ → ℕ → ℕ
  zero   *⅋₂ b = {! !}
  suc a  *⅋₂ b = {! !}
```

The first case is immediately obvious; zero times anything is zero:

```agda
  _*⅋₃_ : ℕ → ℕ → ℕ
  zero   *⅋₃ b = zero
  suc a  *⅋₃ b = {! !}
```

In order to solve what's left, we can dig into our mental cache of algebra
facts. Recall that `bind:a:suc a` is how we write $1 + a$ in Agda, thus:

$$
\begin{aligned}
(1 + a) \times b &= 1 \times b + a \times b \\
&= b + a \times b
\end{aligned}
$$

Therefore, our final implementation of multiplication is just:

```agda
  _*_ : ℕ → ℕ → ℕ
  zero   * b = zero
  suc a  * b = b + a * b
```

of course, we need to add a fixity definition for multiplication to play nicely
with the addition operator. Since `def:_*_` is just a series of additions (as
you can see from our implementation,) it makes sense to make multiplication also
associate left. However, we'd like the expression `bind:x y:y + x * y` to parse
as `bind:x y:y + (x * y)`, and so we must give `def:_*_` a higher precedence.
Thus we settle on

```agda
  infixl 7 _*_
```

Multiplication is just repeated addition, and addition is just repeated
counting---as is made *abundantly* clear when working in our unary
representation. We can repeat this pattern, moving upwards and building
something that is "just repeated multiplication"---*exponentiation*:

Begin as always, with the type and the bound variables:

```agda
  _^⅋₁_ : ℕ → ℕ → ℕ
  a ^⅋₁ b = {! !}
```

We'd again like to do induction, but we must be careful here. Unlike addition
and multiplication, exponentiation is not *commutative.*  Symbolically, it is
not the case that:

$$
x^y \neq y^x
$$

It's always a good habit to test claims like these. Because we're computer
scientists we can pick $a = 2$, and because we're humans, $b = 10$. Doing some
quick math, we see that this is indeed an inequality:

$$
2^{10} = 1024 \neq 100 = 10^2
$$

Due to this lack of commutativity, we must be careful when doing induction on
`def:_^_`. Unlike in all of our examples so far, getting the right answer in
exponentiation strongly depends on picking the right variable to do induction
on. Think of what would happen if we were to do induction on `a`---we would
somehow need to multiply smaller numbers together, each to the power of `b`.

Alternatively, doing induction on `b` means we get to multiply the same number
together, each to a smaller power. That sounds much more correct, so let's
pattern match on `b`:

```agda
  _^⅋₂_ : ℕ → ℕ → ℕ
  a ^⅋₂ zero   = {! !}
  a ^⅋₂ suc b  = {! !}
```

The first case is a usual identity, namely that

$$
a^0 = 1
$$

while the second case requires an application of the exponent law:

$$
a^{b + c} = a^b \times a^c
$$

Instantiating this gives us:

$$
\begin{aligned}
a^{1 + b} &= a^1 \times a^b \\
&= a \times a^b
\end{aligned}
$$

and thus:

```agda
  _^_ : ℕ → ℕ → ℕ
  a ^ zero   = one
  a ^ suc b  = a * a ^ b
```

As you can see, a judicious application of grade-school facts goes a long way
when reasoning through these implementations. It makes sense why; algebraic
identities are all about when are two expressions equal---and our Agda programs
really and truly are defined in terms of *equations.*


## Semi-subtraction {#sec:monus}

The natural numbers don't support subtraction, because we might try to take too
much away, being forced to subtract what we don't have. Recall that there is no
way to construct any negative naturals, and so this is not an operation we can
implement in general.

However, we have an operation closely related to subtraction, which instead
*truncates* at zero. That is, if the result would have gone negative, we
just return zero instead. This operation is called "monus", and given the symbol
`def:_∸_`, input as [`.-`](AgdaMode).


Exercise (Easy)

: Define `def:_∸_` : `expr:ℕ → ℕ → ℕ`


Solution

:   ```agda
  _∸_ : ℕ → ℕ → ℕ
  x      ∸ zero  = x
  zero   ∸ suc y = zero
  suc x  ∸ suc y = x ∸ y
    ```

Just to convince ourselves everything works, let's write a few unit tests:

```agda
  module Natural-Tests where
    open import Relation.Binary.PropositionalEquality

    _ : one + two ≡ three
    _ = refl

    _ : three ∸ one ≡ two
    _ = refl

    _ : one ∸ three ≡ zero
    _ = refl

    _ : two * two ≡ four
    _ = refl
```

Looks good to me!

You can find all of these goodies, and significantly more, in the standard
library's `module:Data.Nat` module. Additionally, you also get support for
natural literals. No more `def:four` `:` `type:ℕ`; just use `4 :` `type:ℕ`
instead!

By this point, you should be starting to get a good handle on the basics of
Agda---both syntactically, as well as how we think about modeling and solving
problems. Let's therefore ramp up the difficulty and put that understanding to
the test.


## Inconvenient Integers

In this section we will tackle the integers, which have much more
interesting mathematical structure than the naturals, and subsequently, present
many more challenges.

The integers extend the natural numbers by reflecting themselves onto the
negative side of the axis. The number line now goes off to infinity in two
directions simultaneously, both towards infinity and towards *negative*
infinity.

Some of the integers, are $\dots, -1000, \dots, -2, -1, 0, 1, \dots, 47, \dots$,
but of course, there are many, many more. The set of integers is often written
in blackboard bold, with the symbol `type:ℤ`, input as [`bZ`](AgdaMode).
`type:ℤ` might seem like a strange choice for the integers, but it makes much
more sense in German, where the word for "number" is *Zahl.*

Mathematically, the integers are an *extension* of the natural numbers. That is,
every natural number can be thought of as an integer, but there are some
(infinitely many) integers that do not correspond to any natural. When modeling
this problem in Agda, it would be nice if we could reuse the machinery we just
built for natural numbers, rather than needing to build everything again from
scratch. But before building integers the right way, we will first take an
intentional wrong turn, in order to highlight some issues when data modeling in
Agda.

Rather than pollute our global module with this intentional dead-end, we'll
start a new module which we can later use to "rollback" the idea. By analogy
with `type:ℕ`, which contains `ctor:zero` and `ctor:suc`, perhaps `type:ℤ` also
has a constructor `ctor:pred` which we will interpret as "one less than":

```agda
module Misstep-Integers₁ where
  data ℤ : Set where
    zero  : ℤ
    suc   : ℤ → ℤ
    pred  : ℤ → ℤ
```


Hidden

:   ```agda
  -- fix expr
    ```

Perhaps we could make an honest go with this definition for `type:ℤ`, but it has
a major problem---namely, that numbers no longer have a unique representation.
For example, there are now infinitely many ways of representing the number zero,
the first five of which are:

* `expr:zero`
* `expr:pred (suc zero)`
* `expr:suc (pred zero)`
* `expr:pred (suc (pred (suc zero)))`

This is not just a problem for zero; in fact, every number has infinitely many
encodings in this definition of `type:ℤ`. We could plausibly try to fix this
problem by writing a function `def:normalize`, whose job it is to cancel out
`ctor:suc`s with `ctor:pred`s, and vice versa. An honest attempt at such a
function might look like this:

```agda
  normalize : ℤ → ℤ
  normalize zero             = zero
  normalize (suc zero)       = suc zero
  normalize (suc (suc x))    = suc (normalize (suc x))
  normalize (suc (pred x))   = normalize x
  normalize (pred zero)      = pred zero
  normalize (pred (suc x))   = normalize x
  normalize (pred (pred x))  = pred (normalize (pred x))
```

It's unclear prima facie whether this function correctly normalizes all
integers. As it happens, it doesn't:

```agda
  module Counterexample where
    open import Relation.Binary.PropositionalEquality

    _ : normalize (suc (suc (pred (pred zero)))) ≡ suc (pred zero)
    _ = refl
```

I'm sure there is a way to make `def:normalize` work correctly, but I suspect
that the resulting ergonomics would be too atrocious to use in the real world.
The problem seems to be that we can't be sure that the `ctor:suc`s and
`ctor:pred`s are beside one another in order to cancel out. Perhaps we can try a
different type to model integers which doesn't have this limitation.


## Difference Integers

Instead, this time let's see what happens if we model integers as a pair of two
natural numbers---one for the positive count, and another for the negative
count. The actual integer in question is thus the difference between these two
naturals.

Because we'd like to use the natural numbers, we must import them. But we
anticipate a problem---addition over both the natural numbers and the integers
is called `def:_+_`, but in Agda, there can only be one definition in scope with
a given name. Our solution will be to `keyword:import` `module:Data.Nat`, but
not to `keyword:open` it:


```agda
module Misstep-Integers₂ where
  import Data.Nat as ℕ
```

This syntax gives us access to all of `module:Data.Nat`, but allows us to
use `module:ℕ` as the name of the module, rather than typing out
`module:Data.Nat` every time. However, not every definition in `module:ℕ` will
conflict with things we'd like to define about the integers, so we can *also*
`keyword:open` `module:ℕ` in order to bring out the definitions we'd like to use
unqualified:

```agda
  open ℕ using (ℕ; zero; suc)
```

We are now ready to take our second attempt at defining the integers.

```agda
  record ℤ : Set where
    constructor mkℤ
    field
      pos : ℕ
      neg : ℕ
```

Hidden

:   ```agda
  -- fix expr
    ```

This new definition of `type:ℤ` also has the problem that there are infinitely
many representations for each number, but we no longer need to worry about the
interleaving problem. To illustrate this, the first five representations of zero
are now:

* `expr:mkℤ 0 0`
* `expr:mkℤ 1 1`
* `expr:mkℤ 2 2`
* `expr:mkℤ 3 3`
* `expr:mkℤ 4 4`

Because the positive and negative sides are tracked independently, we can now
write `def:normalize` and be confident that it works as expected:

```agda
  normalize : ℤ → ℤ
  normalize (mkℤ zero neg)             = mkℤ zero neg
  normalize (mkℤ (suc pos) zero)       = mkℤ (suc pos) zero
  normalize (mkℤ (suc pos) (suc neg))  = normalize (mkℤ pos neg)
```

Given `def:normalize`, we can give an easy definition for `def:_+_` over our
"difference integers," based on the fact that addition distributes over
subtraction:

$$
(p_1 - n_1) + (p_2 - n_2) = (p_1 + p_2) - (n_1 + n_2).
$$

In Agda, this fact looks equivalent, after replacing $a - b$ with
`bind:a b:mkℤ a b`:

```agda
  _+_ : ℤ → ℤ → ℤ
  mkℤ p₁ n₁ + mkℤ p₂ n₂
    = normalize (mkℤ (p₁ ℕ.+ p₂) (n₁ ℕ.+ n₂))

  infixl 5 _+_
```

Subtraction is similar, but is based instead on the fact that subtraction
distributes over addition---that is:

$$
\begin{aligned}
(p_1 - n_1) - (p_2 - n_2) &= p_1 - n_1 - p_2 + n_2 \\
&= p_1 + n_2 - n_1 - p_2 \\
&= (p_1 + n_2) - (n_1 + p_2).
\end{aligned}
$$

This identity is exactly what's necessary to implement subtraction in Agda:

```agda
  _-_ : ℤ → ℤ → ℤ
  mkℤ p₁ n₁ - mkℤ p₂ n₂
    = normalize (mkℤ (p₁ ℕ.+ n₂) (n₁ ℕ.+ p₂))

  infixl 5 _-_
```

Finally we come to multiplication, which continues to be implemented by way of
straightforward algebraic manipulation. This time we need to multiply two
binomials, which we can do by distributing our multiplication across addition
twice. In symbols, the relevant equation is:

$$
\begin{aligned}
(p_1 - n_1) \times (p_2 - n_2) &= p_1 p_2 - p_1 n_2 - n_1 p_2 + n_1 n_2  \\
&= p_1 p_2 + n_1 n_2 - p_1 n_2 - n_1 p_2 \\
&= (p_1 p_2 + n_1 n_2) - (p_1 n_2 + n_1 p_2).
\end{aligned}
$$

Again, in Agda:

```agda
  _*_ : ℤ → ℤ → ℤ
  mkℤ p₁ n₁ * mkℤ p₂ n₂
    = normalize
        (mkℤ (p₁ ℕ.* p₂ ℕ.+ n₁ ℕ.* n₂)
             (p₁ ℕ.* n₂ ℕ.+ p₂ ℕ.* n₁))

  infixl 6 _*_
```

While each and every one of our operations here do in fact work, there is
nevertheless something dissatisfying about them---namely, our requirement that
each of `def:_+_`, `def:_-_`, and `def:_*_` end in a call to `def:normalize`.
This is by no means the end of the world, but it is *inelegant.* Ideally, we
would like each of these elementary operations to just get the right answer,
without needing to run a final pass over each result.

In many ways, what we have built with our difference integers comes from having
"computer science brain" as opposed to "math brain." We built something that
gets the right answer, but does it by way of an intermediary computation which
doesn't correspond to anything in the problem domain. There are all these calls
to `def:normalize`, but it's unclear what exactly `def:normalize` *actually
means*--as opposed to what it *computes.*

Where this problem will really bite us is when we'd like to start doing proofs.
What we'd really like to be able to say is that "these two numbers are the
same," but, given our implementation, all we can say is "these two numbers are
the same *after a call to* `def:normalize`." It is possible to work around this
problem, as we will see in @sec:setoids, but the solution is messier than the
problem, and is best avoided whenever we are able.

The crux of the matter is that we know what sorts of rules addition, subtraction
and multiplication ought to abide by, but it's much less clear what we should
expect of `def:normalize`. This function is a computational crutch---nothing
more, and nothing less. If we rewind to the point at which we introduced
`def:normalize`, we realize that this crutch was designed to work around the
problem that there are non-unique representations for each number. If we could
fix that problem directly, we could avoid `def:normalize` and all the issues
that arise because of it.


## Unique Integer Representations {#sec:integers}

The important takeaway from our last two wrong turns is that we should strive
for unique representations of our data whenever possible.

Let's take one last misstep in attempting to model the integers before we get to
the right tack. Our difference integers went wrong because they were built from
two different naturals, which we implicitly subtracted. Perhaps we were on the
right track using naturals, and would be more successful if we had only one at a
time.

So in this attempt, we will again reuse the natural numbers, but now build
integers merely by tagging whether that natural is postive or negative:

```agda
module Misstep-Integers₃ where
  open import Data.Nat

  data ℤ : Set where
    +_ : ℕ → ℤ
    -_ : ℕ → ℤ
```

This approach is much more satisfying than our previous attempt; it allows us to
reuse the machinery we wrote for natural numbers, and requires us only to wrap
them with a tag. The syntax is a little weird, but recall that the underscores
correspond to syntactic "holes," meaning the following are both acceptable
integers:

```agda
  _ : ℤ
  _ = - 2

  _ : ℤ
  _ = + 6
```

Note that the spaces separating `ctor:-` from `2`, and `ctor:+` from `6` are
*necessary.* Agda will complain very loudly---and rather incoherently---if you
forget them.

While our second approach dramatically improves on the syntax of integers and
eliminates most problems from `module:Misstep-Integers₂`, there is still one
small issue: there is still a non-unique representation for zero, as we can
encode it as being either positive or negative:

```agda
  _ : ℤ
  _ = + 0

  _ : ℤ
  _ = - 0
```

Perhaps there are some number systems in which it's desirable to have (distinct)
positive and negative zeroes, but this is not one of them. We are stuck with two
uncomfortable options---keep the two zeroes and insist that they are in fact two
different numbers, or duplicate all of our proof effort and somehow work in the
fact that the two zeroes are different encodings of the same thing. Such a thing
can work, but it's inelegant and pushes our poor decisions down the line to
every subsequent user of our numbers.

There really is no good solution here, so we must conclude that this attempt is
flawed too. However, it points us in the right direction.  Really, the only
problem here is our *interpretation of the syntax.* Recall that the symbols
induced by constructors are *just names,* and so we can rename our constructors
in order to change their semantics.

This brings us to our and final (and correct) implementation for the integers:

```agda
module Sandbox-Integers where
  import Data.Nat as ℕ
  open ℕ using (ℕ)

  data ℤ : Set where
    +_     : ℕ → ℤ
    -[1+_] : ℕ → ℤ
```


Hidden

:   ```agda
  -- fix indentation
    ```


You'll notice this definition of `type:ℤ` is identical to the one from
`module:Misstep-Integers₃`; the only difference being that we've renamed `ctor:-_`
to `ctor:-[1+_]`. This new name suggests that `bind:n:-[1+ n ]` corresponds to
the number $-(1+n) = -n - 1$. By subtracting this 1 from all negative numbers,
we have removed the possibility of a negative zero.

Given this machinery, we can now name three particularly interesting integers:

```agda
  0ℤ : ℤ
  0ℤ = + 0

  1ℤ : ℤ
  1ℤ = + 1

  -1ℤ : ℤ
  -1ℤ = -[1+ 0 ]
```

Of course, we'd still like our `def:suc` and `def:pred` functions that we
postulated our first time around. The constructors are already decided on our
behalf, so we'll have to settle for functions instead:

```agda
  suc : ℤ → ℤ
  suc (+ x)           = + ℕ.suc x
  suc -[1+ ℕ.zero  ]  = 0ℤ
  suc -[1+ ℕ.suc x ]  = -[1+ x ]
```

If `def:suc`'s argument is positive, it makes it more positive. If it's negative, it
makes it less negative, possibly producing zero in the process. Dually, we can
define `def:pred` which makes its argument more negative:

```agda
  pred : ℤ → ℤ
  pred (+ ℕ.zero)   = -1ℤ
  pred (+ ℕ.suc x)  = + x
  pred -[1+ x ]     = -[1+ ℕ.suc x ]
```


## Pattern Synonyms

It might be desirable to negate an integer; turning it negative if it's
positive, and vice versa. `def:-_` is a natural name for this operation, but its
implementation is not particularly natural:

```agda
  -⅋_ : ℤ → ℤ
  -⅋ (+ ℕ.zero)   = 0ℤ
  -⅋ (+ ℕ.suc x)  = -[1+ x ]
  -⅋ -[1+ x ]     = + ℕ.suc x
```

When converting back and forth from positive to negative, there's an annoying
`ctor:ℕ.suc` that we need to be careful to not forget. This irritant is an
artifact of our encoding. We now have the benefit of unique representations for
all numbers, but at the cost of the definition not being *symmetric* between
positive and negative numbers.

Thankfully, Agda has a feature that can help us work around this problem.
*Pattern synonyms* allow us to define new constructor syntax for types. While
`type:ℤ` is and always will be made up of `ctor:+_` and `ctor:-[1+_]`, we can
use pattern synonyms to induce other ways of thinking about our data.

For example, it would be nice if we could also talk about `ctor:+[1+_]`. This
doesn't give us any new power, as it would always be equivalent to `bind:x:+
ℕ.suc x`. Nevertheless, our definition of `def:-⅋_` above *does* include a
`bind:x:+ (ℕ.suc x)` case, so this pattern does seem like it might be useful.

We can define a pattern synonym with the `keyword:pattern` keyword. Patterns
look exactly like function definitions, except that they build constructors
(highlighted red, and can be used in pattern matches) rather than (blue)
function definitions.

```agda
  pattern +[1+_] n  = + ℕ.suc n
```

Let's also define a pattern for zero:

```agda
  pattern +0 = + ℕ.zero
```

These two patterns give us the option to define functions symmetrically with
respect to the sign of an integer. Where before in `def:-⅋_` we had to pattern
match on two cases, `ctor:+_` and `ctor:-[1+_]`, we can now instead choose to
match into *three* cases: `ctor:+0`, `ctor:+[1+_]` and `ctor:-[1+_]`.

Let's use our new patterns to rewrite `def:-⅋_`, leading to a significantly more
elegant implementation:

```agda
  -_ : ℤ → ℤ
  - +0        = +0
  - +[1+ x ]  = -[1+ x ]
  - -[1+ x ]  = +[1+ x ]
```

What exactly is going on with these pattern synonyms? We haven't actually
changed the constructors of `type:ℤ`; merely, we've extended our type with
different ways of thinking about its construction. Behind the scenes, whats
really happening when we write `bind:n:+[1+ n ]` is that Agda simply rewrites it
by the pattern equation---in this case, resulting in `bind:n:+ (ℕ.suc n)`.
It's nothing magic, but it does a lot in terms of ergonomics.

When should we use a `keyword:pattern` instead of a function definition? On the
surface, they might seem quite similar. You could imagine we might define
`ctor:+[1+_]` not as a pattern, but as a function:

```illegal
  +[1+_]⅋ : ℕ → ℤ
  +[1+_]⅋ n = + ℕ.suc n
```

The problem is such a definition creates `def:+[1+_]` as a function definition,
and note its blue color. In Agda, we're allowed to do pattern matching only on
red values, which correspond to constructors and pattern synonyms. On the left
side of the equality, Agda changes its namespace, and will only recognize known
red identifiers. Anything it doesn't recognize in this namespace becomes a black
binding, rather than a reference to a blue function. This is a reasonable
limitation. In general, function definitions can do arbitrary computation, which
would obscure---if not render uncomputable---Agda's ability to pattern match on
the left side of an equality. Thus, blue bindings are strictly disallowed on the
pattern matching side.

This is the reason behind the existence of pattern synonyms. Pattern definitions
are required to be made up of only red constructors and black bindings on both
sides. In doing so, we limit their expressiveness, but *because* of that
limitation, we have restricted them in such a way as to be usable in a pattern
context.

As a rule of thumb, you should define a pattern synonym whenever you notice
yourself frequently using the same series of constructors together.  Pattern
synonyms are valuable in providing a different lens into how you put your data
together.


## Integer Addition

With a satisfactory definition for the integers, and having completed our
discussion of pattern synonyms, it is now time to implement addition over
`type:ℤ`. As usual, we will intentionally go down the wrong (but obvious) path
in order to help you develop antibodies to antipatterns.

Our particular misstep this time around will be to "bash" our way through the
definition of addition---that is, match on all three of `ctor:+0`, `ctor:+[1+_]`
and `ctor:-[1+_]` for both arguments of `def:_+_`. There are a few easy cases,
like when one side is zero, or when the signs line up on both sides. After
filling in the obvious details, we are left with:

```agda
  module Naive-Addition where
    _+_ : ℤ → ℤ → ℤ
    +0        + y         = y
    +[1+ x ]  + +0        = +[1+ x ]
    +[1+ x ]  + +[1+ y ]  = +[1+ 1 ℕ.+ x ℕ.+ y ]
    +[1+ x ]  + -[1+ y ]  = {! !}
    -[1+ x ]  + +0        = -[1+ x ]
    -[1+ x ]  + +[1+ y ]  = {! !}
    -[1+ x ]  + -[1+ y ]  = -[1+ 1 ℕ.+ x ℕ.+ y ]
```

It's not clear exactly how to fill in the remaining holes, however. We must
commit to a constructor of `type:ℤ`, which mathematically means committing to
the sign of the result---but in both cases, the sign depends on whether `x` or
`y` is bigger.

Of course, we could now do a pattern match on each of `x` and `y`, and implement
integer addition inductively on the size of these natural numbers. That feels
unsatisfactory for two reasons---the first is that this function is already
doing a lot, and induction on the naturals feels like a different sort of thing
than the function is already doing. Our second dissatisfaction here is that the
two remaining holes are symmetric to one another; since we know that $x + y = y
+ x$, we know that the two holes must be filled in with equivalent
implementations. Both of these reasons point to the fact that we need a helper
function.

Recall in @sec:monus when we implemented the monus operator, which performed
truncated subtraction of natural numbers. The only reason it was required to
truncate results was that we didn't have a satisfactory type in which we could
encode the result if it went negative. With the introduction of `type:ℤ`, we now
have room for all of those negatives. Thus, we can implement a version of
subtraction whose inputs are the naturals, but whose output is an integer. We'll
call this operation `def:_⊖_`, input like you'd expect as [`o--`](AgdaMode)

```agda
  _⊖_ : ℕ → ℕ → ℤ
  ℕ.zero   ⊖ ℕ.zero   = +0
  ℕ.zero   ⊖ ℕ.suc n  = -[1+ n ]
  ℕ.suc m  ⊖ ℕ.zero   = +[1+ m ]
  ℕ.suc m  ⊖ ℕ.suc n  = m ⊖ n
```

By implementing `def:_+_` in terms of `def:_⊖_`, we can factor out a significant
portion of the logic. Note that all we care about is whether the signs of the
arguments are the same or different, meaning we can avoid the pattern matches on
`ctor:+0` and `ctor:+[1+_]`, instead matching only on `ctor:+_`:

```agda
  infixl 5 _+_

  _+_ : ℤ → ℤ → ℤ
  + x       + + y       = + (x ℕ.+ y)
  + x       + -[1+ y ]  = x ⊖ ℕ.suc y
  -[1+ x ]  + + y       = y ⊖ ℕ.suc x
  -[1+ x ]  + -[1+ y ]  = -[1+ x ℕ.+ ℕ.suc y ]
```

This new definition of `def:_+_` shows off the flexibility of Agda's parser.
Notice how we're working with `ctor:+_` and `def:_+_` simultaneously, and that
Agda isn't getting confused between the two. In fact, Agda is less confused here
than we are, as the syntax highlighting on the first line of the definition
gives us enough to mentally parse what's going on. The blue identifier on the
left of the equals sign is always the thing being defined, and its arguments
must always be red constructors or black bindings. Practice your mental parsing
of these definitions, as they will only get harder as we move deeper into
abstract mathematics.

Having implemented addition is the hard part. We can implement subtraction
trivially, via addition of the negative:

```agda
  infixl 5 _-_
  _-_ : ℤ → ℤ → ℤ
  x - y = x + (- y)
```

Last but not least, we can define multiplication, again as repeated addition.
It's a little trickier this time around, since we need to recurse on positive
and negative multiplicands, but the cases are rather simple. Multiplication by
zero is zero:


```agda
  infixl 6 _*_
  _*_ : ℤ → ℤ → ℤ
  x * +0 = +0
```

Multiplication by either 1 or $-1$ merely transfers the sign:

```agda
  x * +[1+  ℕ.zero ]  = x
  x * -[1+  ℕ.zero ]  = - x
```

and otherwise, multiplication can just perform repeated addition or
subtraction on one argument, moving towards zero:

```agda
  x * +[1+ ℕ.suc y ]  = (+[1+ y ] * x) + x
  x * -[1+ ℕ.suc y ]  = (-[1+ y ] * x) - x
```

Thankfully, our hard work is rewarded when the unit tests agree that we got the
right answers:

```agda
  module Tests where
    open import Relation.Binary.PropositionalEquality

    _ : - (+ 2) * - (+ 6) ≡ + 12
    _ = refl

    _ : (+ 3) - (+ 10) ≡ - (+ 7)
    _ = refl
```


## Wrapping Up

Our achievements in this chapter are quite marvelous. Not only have we defined
the natural numbers and the integers, but we've given their everyday operations,
and learned a great deal about Agda in the process. Rather famously, in the
Principia Mathematica, Whitehead and Russell took a whopping 379 pages to prove
that $1 + 1 = 2$. While we haven't yet *proven* this fact, we are well on our
way, and will do so in the next chapter when we reflect on the deep nature of
proof.

Before closing, we will explicitly list out our accomplishments from the
chapter, and export them from the standard library for use in the future. In
@sec:naturals we constructed the natural numbers `type:ℕ` and their constructors
`ctor:zero` and `ctor:suc`. Addition comes from @sec:addition, while
multiplication and exponentiation come from @sec:multiplication. The monus
operator `def:_∸_` is from @sec:monus.

```agda
open import Data.Nat
  using (ℕ; zero; suc; _+_; _*_; _^_; _∸_)
  public
```

We also gave definitions for the first four positive naturals:

```agda
open Sandbox-Naturals
  using (one; two; three; four)
  public
```

While discussing the natural numbers, we looked at two notions of evenness in
@sec:even. We'd like to export `type:IsEven` and its constructors
`ctor:zero-even` and `ctor:suc-suc-even`. For succinctness, however, we'll rename
those constructors to `ctor:z-even` and `ctor:ss-even` by way of a
`keyword:renaming` import modifier:

```agda
open Sandbox-Naturals
  using (IsEven)
  renaming ( zero-even     to z-even
           ; suc-suc-even  to ss-even
           )
  public
```

In @sec:maybe, we constructed the `type:Maybe` type, which we used to wrap
functions' return types in case there is no possible answer. If the function
can't return anything, we use the constructor `ctor:nothing`, but if it was
successful, it can use `ctor:just`:

```agda
open import Data.Maybe
  using (Maybe; just; nothing)
  public
```

Discussing the integers made for an interesting exercise, but we will not need
them again in this book, and therefore will not export them. Nevertheless, if
you'd like to use them in your own code, you can find all of our definitions
under `module:Data.Int`.


---

```unicodetable
₀ U+2080 SUBSCRIPT ZERO (\_0)
₁ U+2081 SUBSCRIPT ONE (\_1)
₂ U+2082 SUBSCRIPT TWO (\_2)
₃ U+2083 SUBSCRIPT THREE (\_3)
ℕ U+2115 DOUBLE-STRUCK CAPITAL N (\bN)
ℤ U+2124 DOUBLE-STRUCK CAPITAL Z (\bZ)
→ U+2192 RIGHTWARDS ARROW (\to)
∸ U+2238 DOT MINUS (\.-)
≡ U+2261 IDENTICAL TO (\==)
⊖ U+2296 CIRCLED MINUS (\o-)
```

