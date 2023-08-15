# An Exploration of Numbers

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
import 1-agda

module 2-numbers where
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


## Natural Numbers

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

One might make a successful argument that these are a necessarily limitations of
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
module Naturals where
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
@sec:booleans, as well as for other toy examples in @sec:chapter1.

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
types are usually baked-in to a language.

It can be tempting to think of types defined by `keyword:data` as enums, but
this is a subtly misleading. While enums are indeed apart from one another, this
comes from the fact that enums are just special names given to particular values
of ints. This is an amazingly restricting limitation.

Note that in Agda, `keyword:data` types are strictly more powerful than enums,
because they don't come with this implicit conversion to ints. As a quick
demonstration, note that `ctor:suc` is apart from `ctor:zero`, but `cotr:suc`
can accept any `type:ℕ` as an *argument!* While there are only $2^64$ ints,
there are *infinitely many* `type:ℕ`s, and thus types defined by `keyword:data`
in Agda must be more powerful than those defined as enums in other languages.

More generally, constructors in `keyword:data` types can take *arbitrary*
arguments, and we will often use this capability moving forwards.


## Playing with Naturals

Let's return now to our discussion of the naturals. By repeated application of
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
not the argument is equal to 0. For the same of simplicity, this function will
return a boolean, but note that this is a bad habit in Agda. There are
much better techniques that don't lead to *boolean blindness* that we will
explore in @sec:decidability. This function therefore is only provided to help
us get a feel for pattern matching over natural numbers.

We can get access to the booleans by importing them from our exports from
@sec:chapter1:

```agda
  open 1-agda.Exports
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
[`MakeCase:x`](AgdaCmd) to split `x` apart into its distinct possible
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


Exercise

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


## Two Notions of Evenness

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

Every type we have seen so far has been of the form `data X : Set`, but at
[1](Ann) we have `type:ℕ` `→` `type:Set` on the right side of the colon. Reading
this as a type declaration directly, it says that this type `type:IsEven` we're
currently defining *is exactly* the function we were looking for earlier---the
one with type `type:ℕ → Set`. Because of this parameter, we say that
`type:IsEven` is an *indexed type*, and that the `type:ℕ` in question is its
index.

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
inductive case, we'd like to say that if `n` is even, then so too is
`ctor:suc``(``ctor:suc` `n``))`:

```agda
    suc-suc-even : {n : ℕ} → IsEven n → IsEven (suc (suc n))
```

In a very real sense, our indexed type `type:IsEven` is the "opposite" of our
original decision function `def:even?`. Where before we removed two calls to
`ctor:suc` before recursing, we now recurse first, and then *add* two calls to
`ctor:suc`. This is not a coincidence, but is in fact a deep principle of
computation itself, that we will return to in @sec:todo.

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
for `IsEven (suc zero)`, but no such thing exists. We have `ctor:zero-even` for
`IsEven zero`, and we have `ctor:suc-suc-even` for `IsEven (suc (suc n))`. But there
is no such constructor when we have only one `ctor:suc`! Thus neither `ctor:zero-even` nor
`ctor:suc-suc-even` will typecheck in our hole. Since these are the *only*
constructors, and neither fits, it's fair to say that *nothing can fill this
hole!* That is, `def:three-is-even` is *unimplementable,* which means it's
impossible to construct an `IsEven n` whenever `n` isn't even!

This is truly a miraculous result, and perhaps might give you a glimpse at why
we can prove things about mathematics in Agda. The idea is to carefully
construct types for which we can give values only when the desired property *is
actually true.* But we will have much more to say about that later.


Exercise

:   Build an indexed type for `type:IsOdd`.


Solution

:   ```agda
  data IsOdd : ℕ → Set where
    one-odd      : IsOdd one
    suc-suc-odd  : {n : ℕ} → IsOdd n → IsOdd (suc (suc n))
    ```


Exercise

:   Write an inductive function `evenOdd : {n : ℕ} → IsEven n → IsOdd (suc n)`
    which witnesses the fact that every even number is followed by an odd
    number.


Solution

:   ```agda
  evenOdd : {n : ℕ} → IsEven n → IsOdd (suc n)
  evenOdd zero-even         = one-odd
  evenOdd (suc-suc-even x)  = suc-suc-odd (evenOdd x)
    ```


## Constructing Evidence

When we originally implemented `def:even?`, I mentioned that functions which
return booleans are generally a bad habit in Agda. The reason is that you have
done a bunch of computation in order to computer an answer, and then you end up
throwing all that work away to say merely "yes" or "no." Instead of returning a
`type:Bool`, we could instead return an `type:IsEven`, proving the number is
indeed even!

However, not all numbers are even, so we will first need some notion of failure.
Enter the `type:Maybe` type, which is a container that contains exactly zero or
one element of some type `A`.

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

Our new function is called `evenEv`, to be suggestive of the fact that it
returns *evidence* of the number's evenness. The first thing to study here is
the type:

```agda
  evenEv⅋₀ : (n : ℕ) → Maybe (IsEven n)
  evenEv⅋₀ = ?
```

The type here says "for some `n : ℕ`, I can maybe provide a proof that it is an
even number." The implementation will look very reminiscent of `def:even?`.
First, we can do [MakeCase](AgdaCmd) a few times:

```agda
  evenEv⅋₁ : (n : ℕ) → Maybe (IsEven n)
  evenEv⅋₁ zero           = {! !}
  evenEv⅋₁ (suc zero)     = {! !}
  evenEv⅋₁ (suc (suc n))  = {! !}
```

Then, everywhere we know there is definitely not an answer, we can fill in the
hole with `ctor:nothing`:

```agda
  evenEv⅋₂ : (n : ℕ) → Maybe (IsEven n)
  evenEv⅋₂ zero           = {! !}
  evenEv⅋₂ (suc zero)     = nothing
  evenEv⅋₂ (suc (suc n))  = {! !}
```

In the zero case, where we know there is an answer, we refine our hole with
`ctor:just`:

```agda
  evenEv⅋₃ : (n : ℕ) → Maybe (IsEven n)
  evenEv⅋₃ zero           = just {! !}
  evenEv⅋₃ (suc zero)     = nothing
  evenEv⅋₃ (suc (suc n))  = {! !}
```

but `ctor:just` what? The type `IsEven zero` of the goal tells us, but we can also
elicit an answer from Agda via [Refine:](AgdaCmd):

```agda
  evenEv⅋₄ : (n : ℕ) → Maybe (IsEven n)
  evenEv⅋₄ zero           = just zero-even
  evenEv⅋₄ (suc zero)     = nothing
  evenEv⅋₄ (suc (suc n))  = {! !}
```

At this step in `def:even?` we just recursed and we were done. However, that
can't quite work here. The problem is that if we were to recurse, we'd get a
result of type `Maybe (IsEven n)`, but we need a result of type `Maybe (IsEven
(suc (suc n)))`. What needs to happen then is for us to recurse, *inspect the
answer,* and then, if it's `ctor:just`, insert a `suc-suc-even` on the inside.
It seems a little convoluted, but the types are always there to guide you if you
ever lose the forest for the trees.

Agda does allow us to pattern match on the result of a recursive call. This is
known as a `with` abstraction, and the syntax is as follows:

```agda
  evenEv⅋₅ : (n : ℕ) → Maybe (IsEven n)
  evenEv⅋₅ zero        = just zero-even
  evenEv⅋₅ (suc zero)  = nothing
  evenEv⅋₅ (suc (suc n)) with evenEv⅋₅ n  -- ! 1
  ... | result = {! !}  -- ! 2
```

At [1](Ann), which you will note is on the *left* side of the equals sign, we
add the word `with` and the expression we'd like to pattern match on. Here, it's
`evenEv n`, which is the recursive call we'd like to make. At [2](Ann), we put
three dots, a vertical bar, and a name for the resulting value of the call we
made, and then the equals sign. The important thing to note here is that
`result` is a binding that corresponds to the result of having called `evenEv
n`. This seems like quite a lot of ceremony, but what's cool is that we can now
run [MakeCase:result](AgdaCmd) in the hole to pattern match on `result`:

```agda
  evenEv⅋₆ : (n : ℕ) → Maybe (IsEven n)
  evenEv⅋₆ zero        = just zero-even
  evenEv⅋₆ (suc zero)  = nothing
  evenEv⅋₆ (suc (suc n)) with evenEv⅋₆ n
  ... | just x   = {! !}
  ... | nothing  = {! !}
```

In the case that `result` is nothing, we know that our recursive call failed,
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

We're close to the end. Now we know that `x : IsEven n` and our hole requires an
`IsEven (suc (suc n))`. We can fill in the rest by hand, or invoke
[Auto](AgdaCmd) to do it on our behalf.

```agda
  evenEv : (n : ℕ) → Maybe (IsEven n)
  evenEv zero        = just zero-even
  evenEv (suc zero)  = nothing
  evenEv (suc (suc n)) with evenEv n
  ... | just x   = just (suc-suc-even x)
  ... | nothing  = nothing
```


## Addition

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
`suc x` as $1 + x$, which allows us to write our left hand side as

$$
(1 + x) + y
$$

If we were to reshuffle the parentheses here, we get an $x + y$ term on its own,
which is exactly what we need in order to do recursion. In symbols, this
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
addition. By induction, the first argument is either of the form `ctor:zero`, in
which case it adds nothing to the result, or it is of the form `suc x`, in which
case we assume `x + y` to properly implement addition, and we observe the fact
that $(m + n) + p = m + (n + p)$. This is our first mathematical proof, although
it is a rather "loose" one: argued out in words, rather than being *checked* by
the computer. Nevertheless, it is a great achievement on our path towards
mathematical fluency and finesse.

To wrap things up, we will add a fixity declaration for `def:_+_` so that it
behaves nicely as an infix operator. We must choose a direction for repeated
additions to associate. In fact, it doesn't matter one way or another, and we
used that fact in the inductive case of `def:_+_`. But, looking forwards, we
realize that subtraction *must* be left-associative in order to get the right
answer, and therefore it makes sense that addition have the same associativity.
And, as a matter of convention, we will pick precedence 6 for this operator.

```agda
  infixl 6 _+_
```


## Termination Checking

There is a subtle point to be made about our implementation of `def:_+_`, namely
that the parentheses are extremely important. Our last line is written as `suc x
+ y = suc (x + y)`, but if you were to omit the parentheses, the last line
becomes `suc x + y = suc x + y`. Such a statement is unequivocally *true*, but
it *extraordinarily unhelpful.* Since both sides of the equals sign are
syntactically identical, Agda has no ability to make computational progress by
rewriting one side as the other. In fact, if such a thing were allowed, it would
let you prove anything at all! The only caveat would be that if you tried to
inspect the proof, your computer would fall into an infinite loop, rewriting the
left side of the equation into the right, forever.

Fortunately, Agda is smart enough to identify this case, and will holler,
complaining about "termination checking," if you attempt to do it:

```error
Termination checking failed for the following functions:
  Sandbox-Naturals._+_
Problematic calls:
  suc x + y
```

By putting in the parentheses, `suc (x + y)` is now recursive, and, importantly,
it is recursive on *structurally smaller* inputs than it was given. Since the
recursive call must be smaller (in the sense of there is one fewer `ctor:suc` to
worry about,) eventually this recursion must terminate, and thus Agda is happy.


## Multiplication and Exponentiation

With addition happily under our belt, we will try our hand at multiplication.
The approach is the same as with addition: write down the type, bind the
variables, do induction, and use algebraic identities to help us figure out what
the cases should work out to. The whole thing is really quite underwhelming once
you get the hang of out!

After writing down the type and binding some variables, we're left with the
following:

```agda
  _*⅋₁_ : ℕ → ℕ → ℕ
  x *⅋₁ y = {! !}
```

We need to do induction on one of these bindings; because we have no reason to
pick one or the other, we default to `x`:

```agda
  _*⅋₂_ : ℕ → ℕ → ℕ
  zero   *⅋₂ y = {! !}
  suc x  *⅋₂ y = {! !}
```

From school, recall that zero times anything is zero:

```agda
  _*⅋₃_ : ℕ → ℕ → ℕ
  zero   *⅋₃ y = zero
  suc x  *⅋₃ y = {! !}
```

What's left is where we can dig into our mental cache of algebra facts. Recall
that `suc x` is how we write $1 + x$ in Agda, thus:

$$
\begin{aligned}
(1 + x) \times y &= 1 \times y + x \times y \\
&= y + x \times y
\end{aligned}
$$

Therefore, our final implementation of multiplication is just:

```agda
  _*_ : ℕ → ℕ → ℕ
  zero   * y = zero
  suc x  * y = y + x * y
```

of course, we need to add a fixity definition for everything to work out
properly. Since `def:_*_` is just repeated addition (as you can see from our
implementation,) it makes sense to give it the same associativity as addition
(left.) However, we'd like the expression `y + x * y` to parse as `y + (x * y)`,
and so we need to give `def:_*_` a *higher* precedence, to make it bind more
tightly. Thus we settle on

```agda
  infixl 7 _*_
```

Multiplication is just repeated addition, and addition is just repeated
counting---as made abundantly clear when working in our unary representation.
We can repeat this pattern, moving upwards and building something that is "just
repeated multiplication." That thing is, unsurprisingly, exponentiation.

Begin as always, with the type and the bound variables:

```agda
  _^⅋₁_ : ℕ → ℕ → ℕ
  x ^⅋₁ y = {! !}
```

We'd again like to do induction, but unlike all of our previous examples, we now
have a good reason to pick one of these variables over the other. We must be
careful here, because unlike addition and multiplication, exponentiation is not
*commutative.*  Symbolically, it is not the case that:

$$
x^y \neq y^x
$$

It's always a good habit to test claims like these. Because we're computer
scientists we can pick $x = 2$, and because we're humans, $y = 10$. Doing some
quick math, we see that this is indeed an inequality:

$$
2^{10} = 1024 \neq 100 = 10^2
$$

Due to this lack of commutativity, we must be careful when doing induction on
`def:_^_`. The standard definition of exponentiation, known to you---not
necessarily consciously---requires that we pattern match on `y`.

```agda
  _^⅋₂_ : ℕ → ℕ → ℕ
  x ^⅋₂ zero   = {! !}
  x ^⅋₂ suc y  = {! !}
```

The first case is a usual identity, namely that

$$
x^0 = 1
$$

while the second case requires an application of the exponent law:

$$
x^{a + b} = x^a \times x^b
$$

Instantiating this gives us:

$$
\begin{aligned}
x^{1 + y} &= x^1 \times x^y \\
&= x \times x^y
\end{aligned}
$$

and thus:

```agda
  _^_ : ℕ → ℕ → ℕ
  x ^ zero   = one
  x ^ suc y  = x * x ^ y
```




## Semi-subtraction

The natural numbers don't support subtraction, because we might try to take too
much away and be forced to go negative, but there are no negative natural
numbers. However, we have a closely related operation, subtraction with
*truncation* at zero---that is, if the result should be negative, it is instead
zero. We call this operation "monus", and use the symbol `def:_∸_`.


Exercise

: Define `_∸_ : ℕ → ℕ → ℕ`


Solution

:   ```agda
  _∸_ : ℕ → ℕ → ℕ
  x      ∸ zero  = x
  zero   ∸ suc y = zero
  suc x  ∸ suc y = x ∸ y
    ```

The last operation we will implement for natural numbers is multiplication,
which sounds like it might be hard until you remember that multiplication is
just repeated addition, which we define as follows:

Just to convince ourselves everything works, let's write a few unit tests:

```agda
  module Tests where
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

You can find all of these goodies, and significantly more, in the standard
library's `Data.Nat` module. Additionally, you also get support for natural
literals, that is, you get digital representations for every number. No more
`four : ℕ`; just use `4 : ℕ`!

By this point, you should be starting to get a good handle on the basics of
Agda---both syntactically, as well as how we think about modeling and solving
problems. In the next section we will tackle the integers, which have much more
interesting mathematical structure, and subsequently, present many more
challenges.


## Integers

The integers extend the natural numbers by reflecting them onto the negative
side of the axis as well. Our number line now goes off to infinity in two
directions, towards infinity and towards negative infinity. Some of the integers
then, are $\dots, -3, -2, -1, 0, 1, \dots$. We use the blackboard bold notation
`type:ℤ` to represent the set of integers, which might seem like a strange
choice until you learn the German word for "number" is *Zahl.*

Mathematically, we say the integers are an *extension* of the natural numbers.
That is, every natural number can be thought of as an integer, but there are
some (infinitely many) integers that do not correspond to any natural. When
modeling this problem in Agda, it would be nice if we could reuse the machinery
we just built for natural numbers, rather than needing to build everything again
from scratch. Before building integers the right way, we will first take an
intentional wrong turn, to clarify some issues around data modeling in Agda.

Let's put our misstep in a new module so as to not confuse ourselves when we
"rollback" the idea. By analogy with `type:ℕ`, which contains `ctor:zero` and
`ctor:suc`, perhaps `type:ℤ` also has a constructor `pred` which we interpret as
"subtracting one:"

```agda
module Naive-Integers₁ where
  data ℤ : Set where
    zero  : ℤ
    suc   : ℤ → ℤ
    pred  : ℤ → ℤ
```

The problem with this approach, is that numbers no longer have a unique
representation. For example, there are now infinitely many ways of representing
`ctor:zero`, the first three of which are:

* `ctor:zero`
* `ctor:pred (suc zero)`
* `ctor:suc (pred zero)`

Recall that constructors are always distinct from one another, and furthermore,
that they never compute to anything other than themselves. We could plausibly
try to fix this problem by writing a function `normalize`:

```agda
  normalize : ℤ → ℤ
  normalize zero             = zero
  normalize (suc zero)       = suc zero
  normalize (suc (suc x))    = suc (normalize (suc x))
  normalize (suc (pred x))   = normalize x
  normalize (pred zero)      = pred zero
  normalize (pred (suc x))   = normalize x
  normalize (pred (pred x))  = pred (normalize x)
```

which attempts to recursively "cancel out" subsequent applications of
`ctor:pred` and `ctor:suc`. However, it's unclear prima facie whether this
function correctly normalizes all integers (it doesn't,) and, even if it did,
the resulting ergonomics would be too atrocious to use in the real world. The
important takeaway from this wrong turn is to strive for unique representations
of data whenever possible.

Our first attempt doesn't work. Let's take another misstep to see what else can
go wrong when trying to build the integers. Maybe this time we can reuse the
natural numbers, and build integers merely by determining whether the natural is
postive or negative:

```agda
module Naive-Integers₂ where
  open import Data.Nat

  data ℤ : Set where
    +_ : ℕ → ℤ
    -_ : ℕ → ℤ
```

This approach is much more satisfying than our previous attempt; it allows us to
reuse the machinery we wrote for natural numbers, and requires us only to wrap
them with a tag. The syntax is a little weird, but recall that the underscores
correspond to syntactic "holes," meaning the following are all acceptable
integers:

```agda
  _ : ℤ
  _ = - 2

  _ : ℤ
  _ = + 6
```

Note that the spaces separating `-` from `2`, and `+` from `6` are *necessary.*
Agda will complain very loudly, and rather incoherently, if you forget them.

While our second approach dramatically improves on the syntax of integers and
eliminates most problems from `Naive-Integers₁`, there is still one small
issue---there are now two (and exactly two) representations of zero:

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

There really is no good solution here, so we must conclude that our second
attempt at defining the integers is also flawed. However, it points us in the
right direction. Really, the only problem here is our *interpretation of the
syntax.* This brings us to our third, and final implementation for the integers:

```agda
-- TODO(sandy): naive impl; indicate that; show the pain
module Sandbox-Integers where
  import Data.Nat as ℕ
  open ℕ using (ℕ)

  data ℤ : Set where
    +_     : ℕ → ℤ
    -[1+_] : ℕ → ℤ
```

You'll notice this definition of `type:ℤ` is identical to the one from
`module:Naive-Integers₂`; the only difference is that we've renamed `ctor:-_` to
`ctor:-[1+_]`. This new name suggests the numbers are one "more negative" than
the wrapped natural would otherwise indicate. We can then name three
particularly interesting integers:

```agda
  0ℤ : ℤ
  0ℤ = + 0

  1ℤ : ℤ
  1ℤ = + 1

  -1ℤ : ℤ
  -1ℤ = -[1+ 0 ]
```

The constructed form of `-1ℤ` is a little wordy, but successfully eliminates the
"double zero" problem we had before. Of course, we'd still like our `def:suc` and
`def:pred` functions that we postulated our first time around, and we can now
articulate these as computations:

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

It might be desirable to negate an integer; turning it negative if it's
positive, and vice versa. `def:-_` is a natural name for this operation, but its
implementation is not particularly natural:

```agda
  -⅋_ : ℤ → ℤ
  -⅋ (+ ℕ.zero)   = 0ℤ
  -⅋ (+ ℕ.suc x)  = -[1+ x ]
  -⅋ -[1+ x ]     = + ℕ.suc x
```

When converting back and forth from positive to negative, there's this annoying
`ctor:ℕ.suc` that we need to be careful to not forget about. This annoyance is an
artifact of the encoding we chose; which has the benefit of having unique
representations of all numbers, at the cost of not being *symmetric* in how it
treats positive and negative numbers. To work around this problem, Agda has
support for writing custom patterns, that is, other ways of deconstructing data.

We can define these pattern synonyms via the `keyword:pattern` keyword, and give a
rewrite rule with the desired name of the pattern on the left, and what it
should expand to on the right:

```agda
  pattern +0        = + 0
  pattern +[1+_] n  = + (ℕ.suc n)
```

These two patterns give us symmetry when working with integers. While before we
had to pattern match into two cases, `ctor:+_` and `ctor:-[1+_]`, we can now
instead choose to match into *three* cases: `ctor:+0`, `ctor:+[1+_]` and
`ctor:-[1+_]`. We can rewrite the `-_` function with this new capability, which
provides a significantly more elegant implementation:

```agda
  -_ : ℤ → ℤ
  - +0        = +0
  - +[1+ x ]  = -[1+ x ]
  - -[1+ x ]  = +[1+ x ]
```

Finally, the moment we've all been waiting for; it's time to implement addition
over integers. Doing so is a particularly finicky thing---there are lots of
ways in which positive and negative integers can interact! Fortunately, a lot of
the work is duplicated by virtue of addition being commutative, that is, the
answer is the same regardless of whether we write $a + b$ or $b + a$. Therefore,
we present addition of integers in pairs that are easy to check the equivalence
of.

First, adding zero to anything doesn't change the result:

```agda
  infixl 5 _+⅋_
  _+⅋_ : ℤ → ℤ → ℤ
  +0        +⅋ y   = y
  x         +⅋ +0  = x
```

Continuing on, we come across the case in which we're adding negative one to
positive one:

```agda
  +[1+ ℕ.zero ]  +⅋ -[1+ ℕ.zero ] = +0
  -[1+ ℕ.zero ]  +⅋ +[1+ ℕ.zero ] = +0
```

Otherwise, both arguments are positive or both negative, in which case we just
add their underlying naturals (being careful to `ctor:ℕ.suc` the result, since we
have two `1+`s on the left side!)

```agda
  +[1+ x ]  +⅋ +[1+ y ]  = +[1+ ℕ.suc (x ℕ.+ y) ]
  -[1+ x ]  +⅋ -[1+ y ]  = -[1+ ℕ.suc (x ℕ.+ y) ]
```

The next pair of cases is what happens if we are adding a negative one, in which
case it must cancel out a positive `ctor:ℕ.suc`:

```agda
  +[1+ ℕ.suc x  ]  +⅋ -[1+ ℕ.zero   ]  = +[1+ x ]
  -[1+ ℕ.zero   ]  +⅋ +[1+ ℕ.suc y  ]  = +[1+ y ]
```

Analogously, if we're adding a positive one:

```agda
  +[1+ ℕ.zero   ]  +⅋ -[1+ ℕ.suc y  ]  = -[1+ y ]
  -[1+ ℕ.suc x  ]  +⅋ +[1+ ℕ.zero   ]  = -[1+ x ]
```

The final case, is if we are adding a positive `ctor:ℕ.suc` to a negative
`ctor:ℕ.suc`, in which case the two cancel each other out and we add the
remaining terms:

```agda
  +[1+ ℕ.suc x ]  +⅋ -[1+ ℕ.suc y ]  = +[1+ x ]  +⅋ -[1+ y ]
  -[1+ ℕ.suc x ]  +⅋ +[1+ ℕ.suc y ]  = -[1+ x ]  +⅋ +[1+ y ]
```

What a headache! Who knew addition could be this hard? The good news is that I
didn't have to figure this all out on my own; Agda was extremely helpful. I
simply wrote the first line, and then thought to myself whether I could solve
the problem from there. If I could, great! If I couldn't, I asked Agda to split
one of the variables for me, which generated some new, more specific cases.
Rinse and repeat until all the holes are filled and everyone is happy.

While this is the most straightforward way to write `def:_+_` it falls somewhat
flat. The problem is that `def:_+_`, as written, needs to perform significant
inspection of its arguments in order to compute the result. As a general
principle, significant inspection is an antipattern, as it will require
duplicating all of that same effort in every subsequent proof. A better
technique is to separate out the logic for subtraction of natural numbers into
its own function:

```agda
  _⊝_ : ℕ.ℕ → ℕ.ℕ → ℤ
  ℕ.zero   ⊝ ℕ.zero   = +0
  ℕ.zero   ⊝ ℕ.suc n  = -[1+ n ]
  ℕ.suc m  ⊝ ℕ.zero   = +[1+ m ]
  ℕ.suc m  ⊝ ℕ.suc n  = m ⊝ n
```

By implementing `def:_+_` in terms of `def:_⊝_`, we can factor out a significant
portion of the logic:

```agda
  infixl 5 _+_

  -- TODO(sandy): need to rename earlier _+⅋_
  _+_ : ℤ → ℤ → ℤ
  (+ x)     + (+ y)     = + (x ℕ.+ y)
  (+ x)     + -[1+ y ]  = x ⊝ ℕ.suc y
  -[1+ x ]  + (+ y)     = y ⊝ ℕ.suc x
  -[1+ x ]  + -[1+ y ]  = -[1+ x ℕ.+ ℕ.suc y ]
```

This new definition of `def:_+_` is significantly shorter and more regular. As a
bonus, it shows the addition of positive and negative cases are both calls to
`def:_⊝_`, albeit with the order of the arguments flipped. This will make our
lives significantly easier when we go to prove facts about `def:_+_` in the next
chapter.

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
  x * +0             = +0
```

Multiplication by positive or negative one transfers the sign:

```agda
  x * +[1+ ℕ.zero  ]  = x
  x * -[1+ ℕ.zero  ]  = - x
```

and finally, we can perform repeated addition or subtraction:

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

This is quite a marvelous achievement. In this chapter we've defined three
number systems, in order of increasing complexity and challenge. While there are
many more number systems we could build: the rationals, the reals, the complex
numbers, to name some famous ones, we will leave it here. Instead, we will turn
our attention in the next chapter to the notion of proof, and learn how to do
better than unit tests to show our code works as expected.

