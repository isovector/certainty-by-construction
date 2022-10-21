```
module intro where
```

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


