# Propositions as Types

```agda
module 4-curry-howard where

open import Data.List
open import Data.Nat
```

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
just *convincing* --- it's necessarily so. A proof of a proposition has no
wiggle room or space for error; either it is an all-encompassing, argument that
necessitates belief in the premise, or it is not. There are no half measures in
belief in mathematics.

A corollary of this idea is that two mathematicians can have differing opinions
on whether a proposition is true, but once they have a proof, they both must
believe the proposition to be true. Any other result is to not have a proof in
the first place.

There is an analogy to software here --- quite an apt analogy --- that it's easy
to disbelieve a problem can be solved. That is, of course, until someone hands
you the algorithm that solves it. The algorithm is a proof that the problem is
solvable.

It is exactly this analogy that we will exploit for the remainder of this book
in order to show the relationship between mathematics and programming, and
furthermore, to help programmers use the tools they already have to start being
productive in mathematics. But let's make the connection more formal.

To be very explicit, our analogy equates between *mathematical propositions* and
*types.* That is to say, any mathematical proposition has an encoding as a type,
and vice versa. Furthermore, every *proof of a proposition* corresponds to a
*program with that type*. For example, we can say that the following type:

```type
{A : Set} → A → List A
```

corresponds to the proposition "given a value, it is possible to create a list
of the same type." Notice however that this is not a particularly strong claim.
We're merely saying we can build a list, but saying nothing about it. As humans
we might imagine such a list would have length one, and contain the given
element, as in `f1`:

```agda
f1 : {A : Set} → A → List A
f1 a = a ∷ []
```

Because `f1` has type the given type, `f1` is thus a proof that we can indeed
construct a list given a value. However, `f1` is not the only proof of such a
claim. Indeed, while `f1` feels, in some sense, "natural," there are degenerate
programs with the same type. For example, the program which ignores its argument
and always gives back the empty list is a perfectly fine proof:

```agda
f2 : {A : Set} → A → List A
f2 a = []
```

Or perhaps, we could build a list of length five:

```agda
f3 : {A : Set} → A → List A
f3 a = a ∷ a ∷ a ∷ a ∷ a ∷ []
```

It doesn't really matter. There are in fact, infinitely many proofs that we can
construct a list given an argument of the same type --- one for every possible
length of the list.

Because most programming languages have shoddy type systems, it's difficult to
state any mathematically interesting ideas in them. But this is not so in Agda.
In Agda, our limitation is not in the type system, but in our ability to
transform thoughts into types. As we will see, as our agility manipulating types
improves, so too will our ability to grapple with the mathematical ideas.

Let's take another example. Consider the *pair type,* which allows us to package
two values together:

```agda
record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B
```

We can use pairs, for example, to return two values from a function. Consider
the integer division function, which we'd like to return both the quotient of
the division, as well as the remainder. We can get around the constraint that
functions can return only a single value by having it return a single pair,
which packages up the two results.

Of course, we can also do this same trick as a parameter. Rather than taking two
parameters, we can take one pair-typed parameter. As a matter of fact, this is
how most programming languages treat function calls. When you see `f(1, 2, 3)`
you are used to thinking about `f` as being a function of three arguments. But
instead, if you look closely, it is actually a tuple `(1, 2, 3)` that is being
sent to `f`! The reason we know this is that we are unable to only give `f` two
out of the three arguments. If `f` indeed took three separate parameters, we
would instead write it as `f(1)(2)(3)`.

However, this is an unimportant point, because the two forms are equivalent. We
can show this more formally by writing a type that says "if you give me a
function that takes a pair as an argument, I can convert it into a function that
takes two arguments."

```agda
curry : {A B C : Set} → (A × B → C) → (A → B → C)
curry f a b = f (a , b)
```

We can easily go the other direction too: transforming a function of multiple
arguments into a function of a tuple:

```agda
uncurry : {A B C : Set} → (A → B → C) → (A × B → C)
uncurry f (a , b) = f a b
```

By giving proofs in both directions, we have in fact shown something stronger:
the two forms of writing functions are *equivalent* --- that is, it is
unimportant which one you give us, because we can always convert it to the other
form without losing anything. In mathematical jargon, we have shown a
*bijection* or an *isomorphism* between the two varieties of functions. We will
come back to the notion of isomorphisms in @sec:isos.

You will notice that a lot of the work in giving these proofs is done by the
quantifiers over the types. We are saying not just that `curry` and `uncurry`
work on some functions, but in fact, that they work for *any functions* over
*any types* `A`, `B`, `C`. Imagine if we were to relax this type to instead be
over the natural numbers:

```agda
curry-nat : (ℕ × ℕ → ℕ) → ℕ → ℕ → ℕ
```

Now that the types are no longer different, we are unable to enforce that our
arguments move to the right place. For example, we could implement `curry-nat`
as follows:

```agda
curry-nat f a b = f (0 , 49)
```

in which we ignore the two arguments and always call the given function with 0
and 49. While the implementation of `curry-nat` truly is a proof of `(ℕ × ℕ → ℕ)
→ ℕ → ℕ → ℕ`, we are forced to conclude that `(ℕ × ℕ → ℕ) → ℕ → ℕ → ℕ` is a very
weak mathematical statement ("given a function of two numbers, and two other
numbers, it's possible to compute a number".) That's not very surprising, is it?

This leads us to our next point, that just like in programming, we should strive
to make our proofs as general as possible. That is to say, if the algorithm
requires a specific type as its input, but doesn't use any features of that
type, then it should be generalized to instead take a less specific type. To
illustrate this, let's look at another function:

```agda
swap-nat : ℕ × ℕ → ℕ × ℕ
swap-nat (fst , snd) = snd , fst
```

Our `swap-nat` function merely moves the first element in the pair to be the
second, and vice versa. It's stated to be a function over pairs of natural
numbers, but nothing in this definition requires the pair to *actually* be over
natural numbers. The algorithm works just as well for booleans, strings, or
other pairs. Instead, we can generalize the type:

```agda
swap-mono : {A : Set} → A × A → A × A
swap-mono (fst , snd) = snd , fst
```

which is a marked improvement, but is still too specific. We are now requiring
both elements in the pair to have the same type, but this isn't a necessary
precondition of the function, either. So instead we can generalize further:


```agda
swap : {A B : Set} → A × B → B × A
swap (fst , snd) = snd , fst
```

You'll notice that the actual implementations of `swap-nat`, `swap-mono` and
`swap` are completely identical; the only thing that has changed in these three
snippets has been the types involved. Furthermore, by finding the most general
type for `swap`, we have further constrained what it *can't do.* The final
`swap` function can't copy one element over both places in the result, because
the output must have one element from the type `A`, and another from type `B`.
By finding the most general type, we know a great deal about the implementation,
without necessarily needing to look at it.

Bringing this back to programming, having better control over our types can help
us avoid writing bugs (because they won't type check), and help us when
debugging (because we need only look at the types of things to see if they could
go wrong.) Good mathematical habits make for good programming habits, and vice
versa.


