\beginhidden
```agda
module intro where
```
\endhidden

This book is ostensibly about math for programmers, but one of the major
takeaways is that the two fields are not nearly as distance as they might
appear.

Before we get into the nuts and bolts, however, let's ensure we're all on the
same page. The programming we'll be doing is not procedural in the vein of C++
or Python. Instead, we will write it in a functional style, like Haskell, LISP
or Agda. Of utmost importance here are the notions of values, functions and
types. You probably have intuitions about these things, but unless you have
spent a long time writing purely, functional programs, your intuitions are
likely slightly wrong.

*Values* are the simplest --- they're things the program can stick into memory
and pass around at runtime. Things like `"hello"`, `3`, `true`, and `[('x',
'y')]` are all values.

*Functions* are a particular sort of value. Functions deterministically map
input values to output values. Importantly, a function must give back the same
output for a given input --- and *do nothing else in the process.* Many
languages have features they call "functions" but which do not adhere to this
definition. To disambiguate, we will call such non-functions "procedures." While
procedures are allowed to perform IO, and refer to manipulate global state,
functions are not.

Functions are like they are in mathematics; they merely serve as shorthand for
longer expressions. Consider the following polynomial:

$$
f(x) = 5x^3 - \frac{7x}{4} + 1
$$

in which $f(2)$ is merely shorthand for $5\cdot 2^3 - \frac{7\cdot 2}{4} + 1$,
which itself is an unevaluated way of writing $\frac{89}{2}$. This is the
restriction to which we must hold ourselves if we hope to bridge programming and
mathematics.

If you are a procedural programmer, you are probably reeling in horror right
now. How can we possibly hope to get any *real* work done if we eschew
procedures for functions? How can we talk to the internet or save files?
Surprisingly, functions are equivalently powerful to procedures, at least, when
equipped with a proper runtime system.

While procedures change the world, functions *describe* desired changes in the
world that they hope the runtime system will *actually perform* for them. We
can't *escape* procedures, but we can push them outside of our program and do
all of our reasoning functionally to the same effect.

However, for the purposes of this book, we do not require our programs to
actually *do* anything; our goal is to get an intuitive grasp on mathematics in
terms of things we already understand. Since mathematics doesn't *do* anything
in the first place, neither need our program. In fact, while we will be
programming throughout the entirety of this book, we will not actually run any
of the resulting programs --- the fact that they *compile* in the first place
will be sufficient proof that they do what they say.

How can this be? Imagine if we could connect our unit tests to the compiler,
such that any failure of the tests would be a failure to compile. And then
imagine that we write a (correct) unit test for *literally* every possible code
path --- the resulting program would have no choice but to be correct if it
managed to compile.

This sounds far fetched, but is exactly what we'll do in this book. Of course,
we won't write out every possible case by hand; instead we'll give a
mathematical proof of every assertion. The proofs will guarantee our program
works as expected, and they will only compile if they are *true statements.*
Most amazingly, we'll see that writing proofs isn't any different than writing
programs --- they are one and the same thing.

Our last big topic to discuss now is that of *types.* If you ask ten programmers
what types are, you'll get eleven answers. C programmers think types are a means
of laying out memory. Java programmers think types are classes. Python
programmers don't think much about types at all. None of these answers is
satisfying for our purposes.

A type is a means of classifying values related in some way. Types allow us to
carve out abstraction boundaries by keeping colors separate from numbers
separate from linked lists full of functions that transform booleans into other
booleans. Every value has exactly one type, and for the purposes of the program,
values are interchangeable without anything going terribly wrong. The program
that prints colored text doesn't care one whit for the text being printed or the
color it's printed in. Furthermore, types enforce that text and colors are
*things distinct from one another.*

In a language with sufficiently strong types, you needn't think about what
happens if a function that expects a number gets called with a string: it
literally cannot happen. If you come from a background that doesn't place much
value in types, this feels like a limitation. In reality, it's always an error
if a function expecting a number gets a string: the choice is between whether
you want developers to learn about that problem at compile time, or your users
at runtime. Because mathematics (and therefore we) are interested in universal
truths, it is much more valid to get those problems at compile time, thus the
saying "if it compiles, it works."

Let us now discuss a fundamental concept of mathematics: *sets.* We will ignore
the formalities for the time being in order to develop the "vibe."

A *set* is an unordered collection of things called *elements* or *members*.
Sets can contain finite numbers of things, or even an infinite number of things.
In fact, they can hold just about anything so long as they don't come anywhere
in the vicinity of including themselves. A set $S$ is equipped with an operation
$\in$ which allows us to assert that an element is contained by the set. For
example, if $x$ is an element of $S$ we can write $x \in S$ (and furthermore,
this is a true statement.)

The simplest set is the empty set, which contains no elements, and is written as
$\{\}$. But the most immediately relevant set for programmers is the set of
booleans, written:

$$
\text{Bool} = \{\top, \bot\}
$$

Conventionally $\top$ is called "top" or "true" (the mnemonic is hopefully
clear,) while $\bot$ is called "bottom" or "false." We will prefer to call the
boolean members "top" and "bottom" and save the notions of *true* and *false*
for the validity of mathematical statements.

Notice that $\top$ and $\bot$ have no meaning: they are merely symbols. Their
only distinguishing feature is that they are *different* symbols from one
another. Any meaning we choose to impart upon these symbols is necessarily
arbitrary. A *corollary* is an immediate consequence of a mathematical
statement, and a corollary of the meaninglessness of the symbols in a set is
that the only distinguishing feature of a set is the number of elements it
contains.

To illustrate, I could choose to rewrite $\top$ as $a$ and $\bot$ as $b$, and
thus our earlier definition of the set of booleans becomes:

$$
\text{Bool}_2 = \{a, b\}
$$

Because the symbols have no meaning, it's a challenging thing to argue that
$\text{Bool}$ and $\text{Bool}_2$ are different in any real sense. Nevertheless,
it would be *false* to say that $a \in \text{Bool}$ or that $\bot \in
\text{Bool}_2$. Just because the symbols are meaningless doesn't mean we can
change our minds after the fact. We will later formalize this idea that sets
with the same number of elements are equivalent.

One particularly interesting set is the set of natural numbers, written
$\mathbb{N}$. This is an infinite set, so we cannot write it directly, and
instead need to invent new notation:

$$
\mathbb{N} = \{0, 1, \dots, 652, \dots \}
$$

stating that the natural numbers start at 0 and duly count their way up, one at
a time, forever. Of course, this understanding is merely by convention, and in
order to know what it means you must already understand the idea of numbers and
the number line. Instead, we can construct the natural numbers more precisely,
by noting that every natural number is either 0 or $1+$ some other natural
number. Thus, 2 can be constructed via $1+1+0$, 3 via $1+1+1+0$, and so on.
Using this formulation, we can define the natural numbers as the following
"recursive" definition:

$$
\mathbb{N} = \{0\} \cup \{ n \in \mathbb{N} \mid 1 + n\}
$$

Here the $\cup$ means "merge these two sets" and $\{ n \in \mathbb{N} \mid 1 + n\}$
means "construct a set by taking every element $n$ in $\mathbb{N}$, and
replacing it with $1 + n$." If you do that infinitely many times, eventually you
build all of the natural numbers.

To tie this back to computing, we make the observation that types are sets and
values are elements of those sets. This isn't strictly true, but it's *true
enough* for now. We clean up the subtleties in @sec:models. Ignoring those
details, we can build the *type* of `Bool`{.Agda}s:

```agda
data Bool : Set where
  ff : Bool
  tt : Bool
```

again, choosing arbitrary symbols for the two values of the type. Notice that
not only do we say `Bool : Set` (that is, that `Bool` is of type `Set`) but also
that `ff : Bool` (`ff` is of type `Bool`.) Perhaps it feels redundant to need to
write `Bool` on each line, but this is for a good reason that we will explore
soon.

These definitions `ff : Bool` and `tt : Bool` are known as *introduction rules,*
and between them state that the *only means* of constructing a `Bool`{.Agda} is
via `ff`{.Agda} or `tt`{.Agda}. That means if we have some other value, `x`,
which is known to be a `Bool`{.Agda}, it must be either `ff`{.Agda} or
`tt`{.Agda} --- there are no other options:

```agda
x : Bool
x = ff
```

Let us now construct the type of natural numbers. We will proceed in steps.
First, the type definition itself:

\beginhidden
```agda
module nats where
```
\endhidden


```agda
  data ℕ : Set where
```

We know that 0 is a natural number, and can state it directly:

```agda
    zero : ℕ
```

Our other means of building a natural number is by adding one to some other
natural number. This operation is traditionally known as taking the *successor,*
which we shorten to `suc`{.Agda}:

```agda
    suc  : ℕ → ℕ
```

\beginhidden
```agda
open import Data.Nat using (ℕ; zero; suc)
```
\endhidden

While the type of `zero`{.Agda} is `ℕ`{.Agda}, the type of `suc`{.Agda} is `ℕ →
ℕ`{.Agda}. The arrow represents a function, taking the type on the left side as
a parameter, and returning a value of the right side as a result. Thus,
`suc`{.Agda} is a function that takes a natural number and returns a new natural
number. Completely analogously to writing 3 as $1+1+1+0$, we can write it as
`suc (suc (suc zero))`{.Agda} under this formulation.

If you are sufficiently patient, you can construct any natural number out of
`zero`{.Agda} and `suc`{.Agda} --- but it might take a while! For pragmatic
purposes, we allow using traditional numbers as `ℕ`{.Agda}s, and Agda will treat
these as syntactic sugar over chains of `suc`{.Agda}s applied eventually to
`zero`{.Agda}.

This all sounds horribly inefficient --- and it would be, but remember, we're
not actually running any code here. And even if we were, nothing prevents us
from compiling our natural numbers into something more amenable to computation
after we've proven their correctness. Don't worry about it.

Closely related to the natural numbers are the linked lists. As our first
attempt, let's define the type of linked lists over natural numbers. A linked
list is a `Set`{.Agda}:

```agda
data ListOfℕ : Set where
```

which is either the empty list:

```agda
  [] : ListOfℕ
```

or a `ℕ`{.Agda} prepended to another list:

```agda
  _∷_ : ℕ → ListOfℕ → ListOfℕ
```

The symbol `_∷_`{.Agda} defines a binary infix operator, which we declare
associates to the right[^cons-list]:

[^cons-list]: That is, `1 ∷ 2 ∷ 3 ∷ []`{.Agda} is parsed as `1 ∷ (2 ∷ (3 ∷ []))`{.Agda}

```agda
infixr 3 _∷_
```

Armed with this, we can now give a linked list of the first five square numbers:

```agda
first-five-squares : ListOfℕ
first-five-squares = 1 ∷ 4 ∷ 9 ∷ 16 ∷ 25 ∷ []
```

Of course, we might want linked lists of things other than natural numbers. The
trick, as in many typed programming languages, is to define a "generic" type ---
which is to say, a type *indexed* by another. In this case, we'd like a generic
list type indexed by the type of its contents. Here we will use the variable `A`
to refer to the type of the contents, which we must add as a parameter to the
type, but otherwise the definition remains identical (substituting `A` for
`ℕ`{.Agda})

```agda
data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A
```

Just to prove it works, we can construct a linked list of `Bool`{.Agda}s:

```agda
all-bools : List Bool
all-bools = ff ∷ tt ∷ []
```

or a list of lists of natural numbers:

```agda
list-of-lists : List (List ℕ)
list-of-lists = (3 ∷ 2 ∷ 1 ∷ [])
              ∷ (10 ∷ [])
              ∷ []  -- ! 1
              ∷ []  -- ! 2
```

Notice at [1](Ann) we can insert an empty list into our list-of-lists. This list
necessarily has type `List ℕ`{.Agda}, while the empty list at [2](Ann)
terminates the "meta" list, and has type `List (List ℕ)`{.Agda}. We know this
must be the case because the argument on the left of `_∷_`{.Agda} is always the
*contained* type, while on the right, it is the *list* type.

We can write a function to compute the length of a `List`{.Agda}, appropriately
called `length`{.Agda}. This function takes as input a `List A`{.Agda} and
produces a `ℕ`{.Agda}, therefore its type must be `List A → ℕ`{.Agda}. This is
not quite true, however, since `A` doesn't actually name a type. We must first
bind `A` to a type, which we can do with the given syntax (explained in full
detail later):

```agda
length : {A : Set} → List A → ℕ
```

How can we implement this function? Recall that there are exactly two ways of
constructing a `List`{.Agda}: via `[]`{.Agda} or via `_∷_`{.Agda}. Therefore, we
must give two *separate* algorithms for computing a list's length: one for each
case. The empty case is easy: the length is just 0:

```agda
length [] = zero
```

Otherwise, the list must have been built via `_∷_`{.Agda}, which we know is a
single element prepended to a smaller list. Therefore, its total length must be
one more than the length of the smaller list:

```agda
length (_ ∷ as) = suc (length as)
```

If you are not already intimately familiar with recursion, you will be by the
end of this book. Recursion is everywhere in mathematics, primarily because of
how many mathematical objects are defined in terms of themselves. Wherever you
find that pattern, you're sure to find recursion.

How confident are we that `length`{.Agda} correctly computes the length of a
list? As it happens, it does, but seeing that requires performing recursion in
your head. Unfortunately, there are other functions with the same type as
`length`{.Agda} which compute the wrong answer --- for example,
`wrong-length`{.Agda}:

```agda
wrong-length : {A : Set} → List A → ℕ
wrong-length _ = zero
```

We could solve this problem by writing unit tests, but a better, longer-term
solution is to push enough information into the type so we can be confident it
does the right thing --- no thought or tests required.

One obvious approach would be to associate every list with its length. Such a
thing is called a `Vec`{.Agda} (short for "vector"), and can be thought of a
linked listed indexed not only by the type of its contents, *but also by its
length.* This is one of the most "out there" ideas in the whole book, because
it's a feature that almost no programming languages have.

We begin by defining our `Vec`{.Agda} type, by this time, instead of saying it's
type is `Set`, we now say it's type is a function `ℕ → Set`{.Agda}:

```agda
data Vec (A : Set) : ℕ → Set where
```

We are now responsible for *filling in* that natural number in each of our
constructors. The empty vector is easy enough, it has length zero:

```agda
  [] : Vec A zero
```

The `_∷_`{.Agda} case follows the same logic as it did in `length`{.Agda} --- it
prepends an element to a vector of size `n`, resulting in a vector of size `suc
n`. As before, like in `length`{.Agda}, we need to bind the variable `n` before
we use it:

```agda
  _∷_ : {n : ℕ}
```

and then we can proceed with the type of `_∷_`{.Agda}:

```agda
      → A → Vec A n → Vec A (suc n)
```

The type of `Vec A n` thus describes a linked list made of exactly `n` elements
of type `A`. By our rules above, anything else is a type error and simply won't
compile if we attempt it. For example, this is OK:

```agda
ok : Vec Bool 1
ok = ff ∷ []
```

but the following refuses to compile:

```wrong
bad : Vec Bool 2
bad = ff ∷ []
```

and results in the following error:

```error
0 != 1 of type ℕ
when checking that the expression [] has type Vec Bool 1
```

We are thus guaranteed that a `Vec A n` has length `n`, which we can state by
writing a function `vec-length`{.Agda}:

```agda
vec-length : {A : Set} {n : ℕ} → Vec A n → ℕ
```

TODO: oh crap this doens't work

```agda
vec-length {n = n} _ = n
```



