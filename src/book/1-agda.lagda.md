# Introduction to Agda

This book in your hands is no ordinary prose. No, it is a living, breathing
document. Certainly this is a curious claim; on what grounds can it be made? The
book you are reading is not just a book, it is also a computer program written
in the *literate style.*

Literate programming is a technique for interspersing prose and computer
programs in the same document. The result is a "polyglot": a single artifact
that can be interpreted simultaneously as a book written in English, or a series
of program modules written in Agda.

The advantage of reading a literate program are that you can be sure the code
*actually works.* This is not by the virtue of having had a diligent
copy-editor; it's merely a byproduct of the process. The book simply can't be
assembled into its current form if it contains any syntax errors or if any of
its tests fail. And as we will see shortly, Agda programs come with very
extensive tests. Furthermore, presenting all the code means I, the author,
cannot sweep any nitty-gritty details under the rug.

When code is presented in this book, it will come in a box like the following:

```agda
module 1-agda where
```

This is not merely an example; it's necessary preamble when starting a new Agda
file. The `module` is Agda's simplest unit of compilation, and every chapter in
this book will begin a new module. Thus, you shouldn't be surprised to see
similar blocks of code at the beginning of each chapter.

One distinct advantage of organizing chapters into modules is that chapters thus
become conceptual units in our program. If a later chapter depends on an earlier
one, this fact must be explicitly documented in the prose by way of an `import`.
If later chapters require code or extend concepts from earlier ones, they can
simply import the necessary pieces. For example, we will require the following
modules from the standard library later on, which we can import as follows:

```agda
open import Data.Bool hiding (_≤_)
open import Data.Nat renaming (suc to 1+)
open import Data.Nat.Properties
open import Data.Product
open import Relation.Binary.PropositionalEquality
```

You can think of literate programming being similar to writing comments in your
code, with one important difference: comments rarely evolve with the code they
are meant to document. Comments are a second class citizen: in the land of
programming, code always wins.

The situation is a rather apt metaphor for doing programming in Agda. Most
programming languages are concerned only with "how" --- that is, *how* can we
instruct the computer to get us a result? The desired result of most programs is
implicitly hiding between the lines; the ultimate source of truth as to what a
program *does* is the series of steps it performs. Perhaps some documentation
exists of the function, but there are no guarantees it is correct.

Of course, nothing (automated) checks the prose of this book, but Agda is a
language not only about "how", but also "what." Agda allows us to articulate
extremely precise statements, for example "for any number, there exists a bigger
number":

```agda
no-biggest-number : ∀ (n : ℕ) → ∃[ m ] n ≤ m
```

Don't concern yourself with the exact details of `no-biggest-number` right this
moment. All that's important to takeaway here is that we have articulated a deep
mathematical fact in our language. This, is the *what* of our program.

Of course, Agda also supports the "how", and since it's a programming language,
we are required to give a "how" for every "what." The implementation of
`no-biggest-number` looks like this:

```agda
no-biggest-number n =
  1+ n , ≤-trans (≤-reflexive
                   (sym
                     (+-identityʳ n)))
                 (≤-trans
                   (+-mono-≤ {n} ≤-refl z≤n)
                   (≤-reflexive
                     (+-comm n 1)))
```

The implementation here might look overwhelming, but don't fret, the details
aren't important just now, and you'll understand this code just fine after a few
chapters.

Agda evidently allows us to state "mathematical" properties, like that there is
always a bigger number. But you might be wondering, how does mathematical
aptitude make it a *programming language?* A central theme of this book is just
how similar mathematics and programming are, and not just in the sense that you
need lots of mathematics to get things done in programming. As we will see, the
two are inseparably linked; mathematical prowess *is* computational prowess.


## Overview

Agda descends from the ML family of languages, making it related to Elm, F#,
Haskell, OCaml, PureScript, among many, many other cousins. This section will
give you a brief overview of how to conceptualize Agda as a programming
language, including some sense of how to mentally parse it.

Agda is divided into four distinct pieces of linguistic structure. First and
foremost, it is an *expression-based* language, meaning there are no statements
in the language. On the right side of every equals sign, Agda expects an
expression, which is to say, a program tree that produces a value. If you are
unfamiliar with ML-style languages, this will strike you as quite the
restriction; Agda has no mutable variable assignment, `for` loops, or early
`return` statements, because none of these things produce a value. Having no
loops sounds limiting, but it's OK in practice: we simply use recursion instead.

Syntactically, Agda's expression language can read a little peculiarly. While
Agda supports many of the operators you know and love, its syntax for function
calls is very different from that in other language families'. You are likely
familiar with ALGOL-style function calls which look like this:

```cpp
foo(bar, 5, true)
```

Instead of these parentheses and commas, Agda instead uses *juxtaposition* as
its syntax for function calls. The above call would look, in Agda, like this:

```example
foo bar 5 true
```

where arguments are separated from their function and one another by
white-space. If disambiguation is necessary, we surround the entire expression
in parentheses:

```example
baz 0 (f false) (foo bar 5 true)
```

which would be written in the ALGOL style as

```cpp
baz(0, f(false), foo(bar, 5, true))
```

While this might feel like an unnecessarily annoying break in conventional
syntax, there are mightily-good theoretical reasons for it.

Another interesting fact about Agda's syntax is it's extraordinary flexibility
when it comes to what constitutes an identifier. Besides a few special
characters, almost every string of non-whitespace characters is a valid
identifier. In our earlier example, we saw `+-identityʳ` and `+-mono-≤` both
used as identifiers, but the rabbit hole goes much deeper on what you can get
away with. Agda's standard library makes heavy use of Unicode characters you
didn't even know existed, let alone know the names of. Some of the wackier
identifiers used in the standard library include `0-coprimeTo-m⇒m≡1`, `_⊎-⟶_`
and `xs↭ys`. The general rule is that any series of characters that are not
separated by white-space make up a single identifier.


## Our First Agda Programs

As our first introduction to Agda programming, we will write a little function
that reverses a linked list. Because we will refine this definition several
times to showcase Agda's features, we will write each definition in its own
module. Agda's module system allows us to introduce new lexical scopes on a
whim. Furthermore, modules can contain other modules. We are still in the
file-level module `1-agda`, and can begin a new module with the `module`
keyword:

\begin{AgdaAlign}
```agda
module Directional where
```

Agda is a whitespace-sensitive language, so we can put things into this module
by indenting them relative to the first character of the containing scope. The
first thing we will do in this module is to define the type of a linked list:

```agda
  data List (A : Set) : Set where
```

This definition states that `List` is a type (written in Agda, unfortunately, as
`Set`.) Furthermore, `List` is parameterized by some other type named `A`, which
corresponds to the type of elements contained by this linked list. Note the two
spaces before the keyword `data`! These are necessary to ensure `List` exists in
the `Directional` module we defined above.

> TODO(sandy): next paragraph is not beautiful; we talk about intro forms in two
> paragraphs

By indenting further, we can define the *introduction forms* of `List`s. An
introduction form is a primitive means of constructing a value of a type. We
must thus ask ourselves, in which ways might we make a linked list? Either a
linked list is empty, or it is an element stuck on to the front of an existing
linked list.

We can describe these two cases as two introduction forms, or *constructors*,
for `List`s by indenting further, and giving two type declarations. The first
looks like this:

```agda
    [] : List A
```

which states that `[]` has type `List A`. In essence, we are saying, "for any
`A`, there exists a `List A` which contains no elements of `A`." Contrast `[]`
to `_∷→_`:

```agda
    _∷→_ : A       -- ! 1
         → List A  -- ! 2
         → List A  -- ! 3
```

which defines a new binary operator named `_∷→_`, used infix as `x ∷→ y`. In
this example, [1](Ann) states that the first argument to `_∷→_` has type `A`,
and [2](Ann) says the second argument is of type `List A`. Therefore, we could
say `x : A` and `y : List A`. Furthermore, [3](Ann) says the return type of
`_∷→_` is also a `List A`.

We can build a linked list using this definition as follows:

```agda
  open import Data.Nat

  _ : List ℕ
  _ = 1 ∷→ (1 ∷→ (2 ∷→ (3 ∷→ (5 ∷→ (8 ∷→ [])))))
```

This defines a new anonymous value whose type is `List ℕ` (a list of natural
numbers), equal to the first six terms of the Fibonacci sequence. Any value
whose name is `_` is considered an example or a test by Agda; such a thing
exists, but you can never refer to it again.

You will notice a great deal of parenthetical noise in our definition of `_`.
Since `_∷→_` is a binary operator, we need the parentheses to help Agda
determine the correct parse tree. The keen reader will notice, however, that
for any list, there is exactly one possible, type-correct parse. This is
guaranteed by the fact that the left and right sides of `_∷→_` consume values of
different types. The parentheses therefore must always go on the right side.

Agda's parser is extremely flexible, and thus allows us to automate away this
noise. We can give an `infix` declaration for our operator, telling Agda which
direction and with which precedence it should parse repeated applications of
`_∷→_`. This is done with the keyword `infixr` (for right-nesting expressions),
a precedence, and then the operator we'd like to change the parse rules of:

```agda
  infixr 3 _∷→_
```

After informing Agda of how we'd like repeated applications of `_∷→_` to parse,
we can give our same Fibonacci series, this time with many fewer keystrokes:

```agda
  _ : List ℕ
  _ = 1 ∷→ 1 ∷→ 2 ∷→ 3 ∷→ 5 ∷→ 8 ∷→ []
```

Recall that our goal is to reverse a linked list. Perhaps contrary to your
expectations, we will do this by first defining the type of a *reversed linked
list,* this time presented without further commentary:

```agda
  data RevList (A : Set) : Set where
    [] : RevList A
    _←∷_ : RevList A → A → RevList A

  infixl 3 _←∷_
```

which we can use to show the reversed Fibonacci series:

```agda
  _ : RevList ℕ
  _ = [] ←∷ 8 ←∷ 5 ←∷ 3 ←∷ 2 ←∷ 1 ←∷ 1
```

As this example shows, we can reuse the names of constructors; both `List` and
`RevList` contain a constructor named `[]`. As far as Agda is concerned, these
are completely different things that just happen to share the same syntax.
Thankfully, Agda is smart enough to infer which one you meant based on the
necessary type. If we wanted to, we could also pick the same name for `_∷→_` and
`_←∷_`, but do not for reasons of pedagogy.

Finally, we are ready to reverse a `List`, transforming it into a `RevList`.
First, we define the type of the `reverse` function:

```agda
  reverse : {A : Set} → List A → RevList A
```

The `{A : Set}` notation here means that `A` is a `Set`, and the curly braces
tell Agda to infer what `A` should be based on the way you use the function. In
English, we say "`A` is an implicit argument."

We then we give the definition of `reverse` by using a technique well-known by
the functional programming community. The high-level idea is to push the
elements of the list onto a stack as we discover them. When we discover the end
of the list, we pop the elements off the stack, which are now in reversed order.

Note however that, instead of using a stack, we can use `RevList` directly,
which saves us the effort of having to pop every element off; instead, our
intermediary structure *is* the final structure!

```agda
  reverse {A} = impl []                        -- ! 1
    where
      impl : RevList A → List A → RevList A    -- ! 2
      impl acc []        = acc                 -- ! 3
      impl acc (x ∷→ xs) = impl (acc ←∷ x) xs  -- ! 4
```

There is quite a lot going on in this definition, so we will look at its pieces
slowly. At [1](Ann) we bind the implicit type `A` so that it is in scope for the
remainder of the definition. We then call a function `impl` with the argument
`[]`.

What is this `impl` function? It's defined locally, lexically scoped to
`reverse` by way of the `where` block. At [2](Ann), we've given `impl` a type,
`RevList A → List A → RevList A`. The first `RevList A` is the stack
"accumulator," holding all the elements we've already discovered. This is why we
set it to `[]` at [1](Ann) --- when we first call `reverse` , we haven't
discovered any elements yet! The second argument to `impl` is a `List A`, which
is the part of the list we *haven't yet* explored.

Lines [3](Ann) and [4](Ann) showcase Agda's fantastic support for pattern
matching. We have given the definition for `impl` by showing two cases --- what
to do if its second argument is `[]`, and what to do if its second argument is
instead `x ∷→ xs` (for some values `x` and `xs`). These are the only
constructors of `List A`, and therefore we are guaranteed that every list must
be of one of these two forms.

At [3](Ann), we say that if the input list is empty, to simply return the
accumulated stack. Otherwise, in [4](Ann) we have discovered an element in the
list, which we then push into our stack, and recurse on the tail of the list.
This eliminates one element of the list, moving us closer to an empty list.

Between repeated applications of [4](Ann), eventually terminating in [3](Ann),
we will eventually reverse any list.


Exercise

: Implement `reverseRev : {A : Set} → RevList A → List A`, the function which
  reverses a reversed list back into a "forwards" list. You can use the same
  approach as `reverse`, but think carefully about which pieces need to be
  turned around.


Solution

:     ```agda
  reverseRev : {A : Set} → RevList A → List A
  reverseRev {A} = impl []
    where
      impl : List A → RevList A → List A
      impl acc [] = []
      impl acc (xs ←∷ x) = impl (x ∷→ acc) xs
      ```
\end{AgdaAlign}


## Introduction to Dependent Types

Implementing the `reverseRev` function, while simple, is nevertheless
unfortunate. `List` and `RevList` are so similar that it would be nice if we
could somehow write one `reverse` function that worked in both directions. Such
a thing is possible in general, but not with the way we've organized the
problem. So let's begin a new module (with zero indentation), and try again:

\begin{AgdaAlign}
```agda
module Bidirectional where
```

> TODO(sandy): clearer if we made our own type instead of bool

Our idea is to build a single `List` type, and parameterize it by whether or not
it's going backwards. To do so, we can pull booleans into scope:

```agda
  open import Data.Bool
```

and then try a new definition for `List`:

```agda
  data List (A : Set) : Bool → Set where
```

Notice that under this new formulation, `List A` now has type `Bool → Set`. New
type definitions always need to result directly in `Set` (not `Bool → Set`),
which we understand to mean that each constructor of `List` now gets to *choose*
a boolean corresponding to which direction the list is going.

We begin again with the empty list, but note that an empty list could be part of
a forwards or a backwards list. Therefore, we can add an implicit `Bool`
argument corresponding to whichever direction our list is being made:

```agda
    [] : {dir : Bool} → List A dir
```

However, this new `Bool` parameter for `List A` doesn't need to be polymorphic.
In the `_∷→_` case, we know the list is going forwards (and thus that it is
*not* reversed):

```agda
    _∷→_ : A → List A false → List A false
```

We can also build reversed lists via `_∷←_`, in which the direction boolean is
now `true`:

```agda
    _←∷_ : List A true → A → List A true
```

Since we started a new module with completely new definitions, we need to teach
Agda how to parse repeated applications of these operators again:

```agda
  infixl 3 _←∷_
  infixr 3 _∷→_
```

Our new definition of `List` is quite a peculiar thing; we can now choose
which constructors are allowed to be used, simply by changing the type. For
example:

```agda
  _ : List ℕ false
  _ = 1 ∷→ 1 ∷→ 2 ∷→ 3 ∷→ 5 ∷→ 8 ∷→ []

  _ : List ℕ true
  _ = [] ←∷ 8 ←∷ 5 ←∷ 3 ←∷ 2 ←∷ 1 ←∷ 1
```

Attempting to use `_∷→_` in a `List ℕ true`, or `_←∷_` in a `List ℕ false` will
result in a type error, and Agda will complain loudly, preventing you from doing
any further work until you've fixed the problem.

Having set up `List` in this way, the type of `reverse` becomes much more
interesting --- it simply negates the direction boolean:

```agda
  reverse
      : {A : Set} {dir : Bool}
      → List A dir
      → List A (not dir)
```

Unlike most other programming languages, in Agda we are allowed to use everyday
functions like `not : Bool → Bool` in our *types.* As we will see later, this
happens to be the killer feature that allows us to encode mathematics and proofs
in Agda. But let's not get too ahead of ourselves.

The new implementation of `reverse` is just as before, with one exception; we
now have three means of constructing a `List`, and so we must give three pattern
matches in `impl`: one for `[]`, and two for each direction of building up a
bigger list.

```agda
  reverse {A} {dir} = impl []
    where
      impl : List A (not dir) → List A dir → List A (not dir)
      impl acc []        = acc
      impl acc (x ∷→ xs) = impl (acc ←∷ x) xs  -- ! 1
      impl acc (xs ←∷ x) = impl (x ∷→ acc) xs
```

Something interesting happens at [1](Ann); by pattern matching on `x ∷→ xs`, we
(and, more importantly, Agda) learns that `dir` must be `false`, since that's the
type of `_∷→_ :: A → List A false → List A false`. Therefore, on the right-hand
side of the equals sign, we know we are now trying to build a `List A (not
false)` --- also known as `List A true`. Agda learns the opposite fact in the
`_←∷_` case.

\end{AgdaAlign}


## More Dependent Types

```agda

module Trees where
  open import Data.Nat

  data Tree (A : Set) : ℕ → Set where
    ⊘ : Tree A 0
    _◁_▷_ : {i j : ℕ} → Tree A i → A → Tree A j → Tree A (1 + (i ⊔ j))

  leaf : {A : Set} → A → Tree A 1
  leaf x = ⊘ ◁ x ▷ ⊘

  _ : Tree ℕ 3
  _ = (⊘ ◁ 3 ▷ (leaf 4)) ◁ 5 ▷ (leaf 6 ◁ 9 ▷ leaf 11)
```

