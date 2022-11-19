# Agda Survival Guide

```agda
{-# OPTIONS --allow-unsolved-metas #-}

module 3-agda-survival-guide where

open import Level using (Level)
open import Data.Bool using (Bool; true; false)
open import Data.String
open import Data.Nat

pattern 1+ x = suc x
```

This book does all of its work in Agda, and encourages you, the reader, to also
do your work in Agda. Agda is a fine programming language, whose type system is
sufficiently powerful to express most concepts in mathematics that we care
about. Agda itself is relatively simple, at least, compared with finding
techniques in other languages to approximate the same tasks. That being said,
having a high-level idea of how the tool works and what features are available
to you will be instrumental in your success.

The language itself has very few edge cases, but the standard library is where
things go off the rails.


## Agda in a Nutshell

Agda is a pure, dependently-typed functional programming language. *Pure* means
that the language, for the most part, doesn't have any side-effects. That means,
modulo a few stipulations, Agda is unable to talk to the filesystem, make API
calls, check the time, print to stdout, or modify any variables. This is a
severe set of limitations, and probably is unlike any other programming language
you have ever used. The things you *can't* do in Agda consist of most of the
things anyone considers programming to be. And so in what way can we justify
calling Agda a programming language, and what sorts of programs can we write in
it?

In my opinion, Agda's strength is the power of its type system. You might have
heard the adage "if it compiles, it works" which is more true in Agda than in
any other programming language. Most of our interactions with Agda are not for
the purpose of writing programs, but instead, for having a conversation with its
typechecker. Agda lets us express extremely precise types, things like
"everything on the left side of this binary search tree is smaller than the
root." And once you've phrased that as a type, your program implementing
insertion into a binary search tree is *required to prove* that it maintains the
invariant. By virtue of having extremely powerful types, the burden falls upon
us to write extremely correct software, because, for likely the first in our
programming careers, we've had the ability to specify *what correctness means.*

As you know, the hard part about programming is the solving of the problem, not
the finger wiggling necessary to turn it into a program. Agda is a tool for
approaching the first half here: solving and understanding the problem in its
entirety. The odd consequence here is that our resulting programs have no choice
but to be right. We don't need to run them to verify we get the expected output,
because we have proven it in full generality.

After writing Agda daily for over a year, I still haven't felt the need to run
any of my programs. In fact, I don't even know how if I wanted to. The point is
to solidify our understanding and prove it correct. If we still want a
computable artifact, we are free to transpile Agda into some other language, or
rewrite the solution elsewhere now that the hard part is complete.

Aside from being pure, Agda is also a *functional* programming language, which
is opposed to procedural languages like C++, Python and Ruby, as well as opposed
to object-oriented languages like C# and Java. Functional programs look more
like a series of math equations than they do "recipes." Functional programs have
more of an emphasis on *what things are* rather than *how they compute.* To
illustrate, compare the definition of the factorial in C++:

```cpp
uint64_t factorial(uint64_t n) {
  int64_t result = 1;
  for (uint16_t i = 1; i <= n; i++) {
    result = result * i;
  }
  return result;
}
```

The C++ program is marked by explicit computation; we need to create an
accumulator variable, and then loop through every number, multiplying the
accumulator against the new index, and finally output the result.

Compare this to the same program in Agda:

```agda
factorial : ℕ → ℕ
factorial 0 = 1
factorial (1+ n) = (1+ n) * factorial n
```

in which we state a base case for what to do when the number is 0, and an
induction case for what to do otherwise. The Agda definition closely follows the
mathematical definition of the factorial, and lets us focus more on "what it is
we're talking about" rather than "how does the computer accomplish the task."

Is Agda's implementation of the factorial efficient? In some sense, this is a
meaningless question, because we do not intend to ever *run* the resulting
program. Our definitions are chosen for clarity of thought and reasoning, not
for the computer's sake. Computers are tools to do tedious work on our behalf;
it is simply ass-backwards to do tedious reasoning on behalf of the computer.

Of course, this can at odds with extracting efficient programs should that
desire ever arise. We usually solve this issue in two steps. First, solve the
problem at hand with simple reasoning techniques, and verify the solution is
correct. Second, find a computationally efficient means of tackling the same
problem, and give a proof that it is equivalent to the first way. This allows us
to separate our understanding of how to solve problems from our ability to
subsequently speed them up. But worrying about optimization too early in the
process often gets in the way of finding good solutions.

Functional programs are distinguished from other varieties of programs by being
entirely expressions, never statements. That is, we are syntactically unable to
write "recipe-style" programs of the form "do this, then do that, then do the
other thing." Our only means of expressing programs is as one big expression,
which means that everything is a value, and as a result, we can abstract over
significantly more parts of our program.

Because Agda is pure, it cannot have any side effects, so nothing will go wrong
if we define `if_then_else_`:

```agda
if_then_else_ : {ℓ : Level} {A : Set ℓ} → Bool → A → A → A
if true  then t else f = t
if false then t else f = f
```

Here we see quite a few things happening at once. The first is that we can
define the `if..then..else` syntax for ourselves that is usually wired directly
in to most languages. Agda has extremely flexible syntax, allowing us to build
new syntactic constructs using underscores to mark holes. The second thing to
notice is that on both the `then` and `else` branches we fully compute what
happens. But because of Agda's purity, it's impossible to observe the fact that
`if_then_else_` isn't pruning the branch left untaken.

This is a very freeing thought. Liberate your mind from the confines of
procedural programming!

Of course, because this fact is unobservable, we also have no proof that Agda
*isn't* pruning the branch left untaken. It's a non-question, because the
question presupposes a computational model that isn't on the table. The
semantics of Agda give us no means of differentiating whether or not this
optimization is happening, and to us it simply doesn't matter.

The major appeal of pure, functional programming languages is their *referential
transparency.* That is to say, we are free to replace the left-hand side of an
equation with the right-hand side whenever we please, and this is the way by
which computation happens. It means we can fully understand a program simply by
inlining definitions. There is no variable state that we need to mentally track
in order to determine which branch happens. There is no complicated line of
reasoning we need to follow about what happens if the program gets run on a
Tuesday. These are concepts we can't even speak about in Agda, and therefore are
not required to consider.

In this sense, Agda is extremely limited, but that's a feature, not a bug.
Because Agda is so constrained in its functionality, we can say a lot more about
what it does do, since the possibility space is smaller.

Best of all, you might be surprised that Agda is still (effectively) Turing
complete. Anything you can do in any other programming language you can do in
Agda. These limitations might seem severe, but they are not fundamental
problems. They are merely a different way of approaching problems, and one which
we will see is extremely fruitful.

Finally, of our adjectives used to describe, we said that Agda is
*dependently-typed.* Dependent type-systems are a formalization that allows
types to *depend* on values (hence the name.) What does this mean? In practice,
it means we are allowed to compute types in the exact same way we compute
values. That is to say, we can write a `crazy` function:

```agda
crazy : (b : Bool) → if b then ℕ else String
crazy false = "hello"
crazy true  = 17
```

where the *return type* of `crazy` depends on the *value* of its input. If we
pass in `true`, we get a number out, but if we pass in `false` we get out a
string. Notice also that we used the `if_then_else_` function that we just
defined in order to compute the type of `crazy`. Crazy, isn't it?

The flexibility afforded by dependent types is what many practitioners of
dynamically typed languages are chasing; they acknowledge a function should do
different things in different cases, but have been unable to encode that
reasoning in the typed languages they've seen. Rather than throwing out the type
systems that are unable to serve them, they throw out the entire idea of types
instead!

But types serve a valuable purpose; they allow us to document and enforce sanity
checks and invariants on our programs. Types might feel like a nuisance to
write in the moment, but their usefulness becomes immediately evident the first
time you've had the joy of performing a large refactoring a typed codebase. You
make the one change you had in mind, and then fix up the resulting type errors
until they are no more. The result is a working, easily-refactored program.

In addition to the benefits afforded by having a strong type system, a
dependently-typed system additionally allows us to blur the distinction between
types and values. We can compute types, and use terms as parameters in our
types, and stick types in our data containers. Dependent types de-stratify a
language --- there is no distinction between the value-level and the type-level.
Anything you want to do is straightforward, and you can use all the techniques
you already know of to implement it.


## Refining Agda Programs

Agda acknowledges that most of the time you're writing a program, it's an
*incomplete* program. Agda is an interactive tool, meaning it can help you
refine incomplete programs into slightly less-incomplete programs. Writing an
Agda program thus feels much more like a conversation with a compiler than it
does being left alone in your text editor, typing away until the program is
done.

Incomplete programs are programs that contain one or more *holes* in them, where
a hole is a bit of the program you haven't written yet. Thanks to Agda's
exceptionally strong type system, it knows a great deal about what shape your
hole must have, and what sorts of programs-fragments would successfully fill the
hole. In the process of filling a hole, perhaps by calling a function that
returns the correct type, you will create new holes, in this case corresponding
to the *arguments* of that function call. Thus the model is to slowly refine a
hole by filling in more and more details, possibly creating new, smaller holes
in the process. As you continue solving holes, eventually there will be no more
left, and then your program will be complete.

Let's take an example. Suppose we want to implement the `factorial` program from
above. We begin by writing out the type of `factorial`, and then giving its
definition as a hole (indicated in Agda code via a question mark):

```agda
factorial⅋ : ℕ → ℕ
factorial⅋ = ?
```

Saving the file will have Agda inform me that the type of this hole is `ℕ → ℕ`,
which makes sense, since the left-side of the equation must have the same type
as the right-side. I can now perform a [MakeCase](AgdaCmd) action in the
context of the hole, which causes Agda to bind my function argument on the left
side of the equals:

```agda
factorial⅋⅋ : ℕ → ℕ
factorial⅋⅋ x = {! !}
```

Notice that Agda has replaced my question mark hole with `{! !}`, which is
Agda's other syntax for holes. The `{! !}` syntax is preferred because it acts
like brackets and allows you to write partial code fragments inside, but is
slightly more work to type than `?`, thus the two options.

Inside the hole, I can now ask again for [MakeCase](AgdaCmd), and this time tell
it I'd like it to split the `x` variable. This is equivalent to asking Agda to
tell me what are the possible values of `x`, and to have me write down an
equation for each of them. The result is:

```agda
factorial⅋⅋⅋ : ℕ → ℕ
factorial⅋⅋⅋ zero = {! !}
factorial⅋⅋⅋ (suc x) = {! !}
```

where `suc` means "one more than." From the definition of factorial, I know that
the factorial of zero is `1`, so I can write that in place of the hole:

```agda
factorial⅋⅋⅋⅋ : ℕ → ℕ
factorial⅋⅋⅋⅋ zero = 1
factorial⅋⅋⅋⅋ (suc x) = {! !}
```

I am now left with one hole. Inside of it, I can make suggestions to Agda about
how to help fill it. In this case I can write `_*_` to suggest that Agda try
multiplication:

```agda
factorial⅋⅋⅋⅋⅋ : ℕ → ℕ
factorial⅋⅋⅋⅋⅋ zero = 1
factorial⅋⅋⅋⅋⅋ (suc x) = {! _*_ !}
```

I can then invoke [Refine](AgdaCmd) to have Agda use the given function, which
again gives me two goals:

```agda
factorial⅋⅋⅋⅋⅋⅋ : ℕ → ℕ
factorial⅋⅋⅋⅋⅋⅋ zero = 1
factorial⅋⅋⅋⅋⅋⅋ (suc x) = {! !} * {! !}
```

I know that I'd like to call `factorial` recursively, so I try putting that in
the first hole:

```agda
factorial⅋⅋⅋⅋⅋⅋⅋ : ℕ → ℕ
factorial⅋⅋⅋⅋⅋⅋⅋ zero = 1
factorial⅋⅋⅋⅋⅋⅋⅋ (suc x) = {! factorial !} * {! !}
```

and subsequently [Refine](AgdaCmd) again, resulting in:

```agda
factorial⅋⅋⅋⅋⅋⅋⅋⅋ : ℕ → ℕ
factorial⅋⅋⅋⅋⅋⅋⅋⅋ zero = 1
factorial⅋⅋⅋⅋⅋⅋⅋⅋ (suc x) = factorial {! !} * {! !}
```

Because I am in the `suc x` branch, that means `suc x` is one more than `x`, or
alternatively, that `x` is *one less* than `suc x`. So I'd like to use `x` in
this hole in order to drive my recursion:

```agda
factorial⅋⅋⅋⅋⅋⅋⅋⅋⅋ : ℕ → ℕ
factorial⅋⅋⅋⅋⅋⅋⅋⅋⅋ zero = 1
factorial⅋⅋⅋⅋⅋⅋⅋⅋⅋ (suc x) = factorial x * {! !}
```

By the same logic, I know that `suc x` is the number I'm *currently on*, so I
can fill in my last hole with this:

```agda
factorial⅋⅋⅋⅋⅋⅋⅋⅋⅋⅋ : ℕ → ℕ
factorial⅋⅋⅋⅋⅋⅋⅋⅋⅋⅋ zero = 1
factorial⅋⅋⅋⅋⅋⅋⅋⅋⅋⅋ (suc x) = factorial x * {! suc x !}
```

and then ask for one more [Refine](AgdaCmd) which completes the program:

```agda
factorial⅋⅋⅋⅋⅋⅋⅋⅋⅋⅋⅋ : ℕ → ℕ
factorial⅋⅋⅋⅋⅋⅋⅋⅋⅋⅋⅋ zero = 1
factorial⅋⅋⅋⅋⅋⅋⅋⅋⅋⅋⅋ (suc x) = factorial x * suc x
```

Every step of the way, I was responsible only for "navigating" where the code
went, but Agda did the hard work of typing it out for me. It is almost as if we
were collaborating in a pair programming session. Indeed, this is what it often
feels like.

