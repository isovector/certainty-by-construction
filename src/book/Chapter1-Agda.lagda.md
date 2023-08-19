# A Gentle Introduction to Agda {#sec:chapter1}

This book is no ordinary prose. It is not just a book, but it is also a piece of
software. Literate programming is a technique for interspersing text and
computer programs in the same document. The result is a single artifact that can
be interpreted simultaneously as a book written in English, or a series of
modules written in Agda.

Most technical books work only by dint of having been read by a diligent
copy-editor. But technical editors are fallible, and can nevertheless miss some
details. The compiler, however, is superhuman in its level of nitpicking
pedantry. By virtue of being a literate program, this book is capable of being
typeset only when all of the code actually works The book simply will not
compile if any of the Agda code presented in it doesn't typecheck, or if any of
its tests fail.

This last point is particularly important. As we will see shortly, Agda programs
come with *very* extensive tests.

In this chapter we will get acquainted with Agda's syntax, core ideas, and
interactive tooling. By the end, you will be able to parse Agda code mentally,
be able to write simple functions, and type the many funny Unicode characters
which are ubiquitous in real Agda code. Despite being written in Agda, this book
is not *about* Agda, and so the goal is to get you to a minimum degree of
competency as quickly as possible. Let's get going!


## Modules and Imports


Hidden

:   ```agda
{-# OPTIONS --allow-unsolved-metas #-}
open import Data.Product using () renaming (_×_ to _,⅋₉_)
    ```


When code is presented in this book, it will be shown with a thick left rule, as
below:

```agda
module Chapter1-Agda where
```

This one-line example is not merely an illustration to the reader. By virtue of
being a literate document, every chapter in this book must be a valid Agda file,
and every Agda file begins with a *module declaration* like above. This
declaration is mandatory prefacing every chapter, and we're not allowed to write
any code until we've done the `keyword:module` ritual.


The module is Agda's simplest unit of compilation.

> TODO(sandy): change me when publishing

Every Agda source file must begin with a module declaration which matches the
name of the file. Since this module is called `module:Chapter1-Agda`, if you'd like to
follow along at home, you must save your file as `Chapter1-Agda.agda`. Failure to do so
will result in a helpful error message:

```info
The name of the top level module does not match the file name.
```

Whenever feedback from the compiler is presented in this book, we will typeset
it as above. You'll learn how to interact with the compiler momentarily.


Agda modules act as namespaces: limiting access and visibility to definitions
within. Modules can be nested inside of one another, as in the following example:

```agda
module example where
  -- This is a comment
```

This introduces a new module `module:example` inside of `module:Chapter1-Agda`. You
will notice a lack of curly braces here. Unlike many programming languages, Agda
doesn't use delimiters to indicate blocks; instead, it uses *significant
whitespace.* That is, in order for the comment to be inside the module
`module:example`, it must be indented relative to the `keyword:module` keyword.
Because leading whitespace is meaningful in Agda, we must be careful to get our
indentation right.


OnlyBook

:   This nested indentation can get very deep in real programs. It's not a
    problem in a text editor, but in print---like you are reading now---,
    real-estate is very expensive. Therefore, we will try to elide as much
    indentation as possible. You might have noticed a little number 0 in the
    left margin gutter of each code block. This indicates how many spaces should
    precede each line of the code block. In this case, there should be no
    preceding indentation.

:   If the first line of block of code is at the same relative indent level as
    the last line of the previous one, we'll just mark the column depth in the
    gutter. However, if the indentation has increased, we'll draw attention to
    it with a $\rightarrowbar$ symbol. Likewise, if the indentation has
    decreased, we'll use a $\barleftarrow$ symbol.

:   Thus, you might see $\rightarrowbar$ 2, meaning that the indentation of this
    block has increased such that the leftmost character should be 2 spaces away
    from the beginning of the line. Note that this is an *absolute* positioning
    scheme; $\rightarrowbar$ 8 means that you should *begin* in column 8, *not*
    that you should add 8 additional spaces relative to the previous line.

:   To illustrate this convention, we can look at four code blocks presented
    separately. The first is a new module `module:foo`.

:     ```agda
module foo⅋ where
      ```

:   The second contains a doubly-nested submodule, first `module:bar` and then
    `module:qux`:

:     ```agda
  module bar⅋ where
    module qux⅋ where
      ```

:   Our third code block introduces yet another module---this time at the same
    relative indentation:

:     ```agda
    module zaz⅋ where
      ```

:   And finally, we come to our last code block illustrating the indentation
    convention of the book:

:     ```agda
  module ram⅋ where
      ```

:   If we wanted to lay out these four preceding blocks into our Agda file, the
    actual indentation for everything should look like this:

```agda
module foo where
  module bar where
    module qux where
    module zaz where
  module ram where
```


OnlyBook

:   Don't worry; this indentation convention will be much less tedious
    throughout the book than it seems. The illustration here is merely to get
    you paying attention to the indicators. Our actual code will require
    dramatically less changing of indentation.

:   The important point here is that you should indent when you see a
    $\rightarrowbar$, and likewise de-dent when you see a $\barleftarrow$. If
    you (or Agda) ever confused about where your indentation should be, use a
    number of spaces equal to number indicated. Getting your indentation wrong
    is a serious error that the compiler *will* complain about, so if you get
    mysterious errors when working through the code presented here, the first
    diagnostic step is to ensure your indentation is correct.

I said earlier that modules act as namespaces. In the case of multiple modules
in a single file, the modules are given *full-qualified name*, in which they
inherit the names of all of their parent modules as well. For example, in the
code block above, we have defined five sub-modules, which have the
fully-qualified names:

- `module:Chapter1-Agda.foo`
- `module:Chapter1-Agda.foo.bar`
- `module:Chapter1-Agda.foo.bar.qux`
- `module:Chapter1-Agda.foo.bar.zaz`
- `module:Chapter1-Agda.foo.ram`

The module structure of an Agda program always forms a tree.

We will use many modules throughout this book---albeit ones much more
interesting than presented thus far. A common pattern we will take is to
introduce a new module whenever we'd like to explore a new line of reasoning.
The idea being that learning abstract things like math requires lots of specific
examples, from which we will generalize. Thus, we need a mechanism to work out
the gory details of a specific example without "polluting" our eventual
results.

One distinct advantage of organizing chapters into modules is that chapters thus
become conceptual units in our program. If a later chapter depends on an earlier
one, this fact must be explicitly documented in the prose by way of an `import`.
If later chapters require code or extend concepts from earlier ones, they can
simply import the necessary pieces.

We will also assume the presence of the Agda standard library, but will first
derive the pieces we use from scratch before importing it. Agda's flexibility is
outstanding, and common "magical" constructions in other languages---like
numbers, booleans, and `if..then..else` syntax---are all defined by the
standard library. Getting a chance to define them for ourselves will help build
an appreciation that none of this stuff needs to be special.


## A Note on Interaction

Agda is an interactive programming language. That means at any point in time,
you can load an Agda file via the [`Load`](AgdaCmd) command. This will cause
Agda to parse, typecheck, and highlight the program. It's a good habit to reload
your file every time you make a syntactically valid change. Doing so will alert
you to problems as soon as they might occur.

While working through this book, you are encouraged to reload your file after
every code block.


## Importing Code

We will break our define-it-before-you-import-it rule just once to illustrate
how Agda's module importing system works. Because imports are scoped to the
currently open module, we will first open a new module:

```agda
module Example-Imports where
```

Inside this module we are free to import and define anything we like, without
fear that it will leak into `module:Chapter1-Agda` where we will do the majority of our
work.

We can import the booleans from the `module:Data.Bool` module as follows:

```agda
  import Data.Bool
```

This line tells Agda to go find a module called `module:Data.Bool` somewhere (which it
will do by looking in the current project and any globally-installed libraries
for a file called `Data/Bool.agda`.) Just importing it, however, is rarely what
we want, as all the identifiers have come in fully-qualified. Ignoring the
syntax for a moment, you will notice the following code example is much more
verbose than we'd like:

```agda
  _ : Data.Bool.Bool
  _ = Data.Bool.false
```

We will dive into the exact syntax here more fully in a moment, but first, it's
worth learning how to avoid the fully-qualified names. After importing a module,
we can also `open` it, in which case, all of its contents get dumped into the
current environment. Thus, we can rewrite the previous two code blocks as:

```agda
  import Data.Bool
  open Data.Bool

  _  : Bool
  _ = false
```

Of course, it's rather annoying to need to `keyword:import` and open a
`keyword:module` every time we'd like to use it. Thankfully, Agda provides us
some syntactic sugar here, via `keyword: open import`. Rewriting the code again,
we get:

```agda
  open import Data.Bool

  _  : Bool
  _ = false
```

There is significantly more to say about Agda's module system, but this is
enough to get you up and running. We will cover the more advanced topics when we
come to them.


## Semantic Highlighting

Unlike most programming languages, syntax highlighting in Agda is performed *by
the compiler,* rather than some hodgepodge regular expressions that do their
best to parse the program. Therefore, it's more correct to call Agda's
highlighting *semantic* rather than syntactic. Since Agda's grammar is so
flexible, getting trustworthy highlighting information from the compiler is a
necessity for quickly parsing what's going on. The lack of semantic highlighting
outside of text editors makes Agda a much harder language to read casually. If
you're ever snooping through Agda code, do yourself a favor and load it into an
editor to ensure you get the semantic highlighting. It makes a world of
difference.

The highlighting in this book was generated directly from the Agda compiler. The
default colors that Agda chooses when doing highlighting are helpful for
quickly conveying information, but they are by no means beautiful. For the sake
of the reader's enjoyment, I have chosen my own color-scheme for this book. It
is presented below, alongside the standard Agda colors, if you'd like a guide
for translating between the book and your editor:

|                    Element |                 Book                 |                     Editor                     |
|---------------------------:|:------------------------------------:|:----------------------------------------------:|
|                    Numbers |         \AgdaNumber{grey}            |         \AgdaNumber[Standard]{purple}          |
|                    Strings |         \AgdaString{grey}            |         \AgdaString[Standard]{red}             |
|                   Comments |         \AgdaComment{red}            |         \AgdaComment[Standard]{red}            |
|                   Keywords |         \AgdaKeyword{yellow}         |         \AgdaKeyword[Standard]{orange}         |
|               Constructors |    \AgdaInductiveConstructor{red}    |   \AgdaInductiveConstructor[Standard]{green}   |
|            Bound Variables |           \AgdaBound{grey}           |        \AgdaBound[Standard]{black}             |
|              Record Fields |       \AgdaField{forest green}       |           \AgdaField[Standard]{pink}           |
|               Module Names |          \AgdaModule{black}          |          \AgdaModule[Standard]{purple}         |
|                  Functions |          \AgdaFunction{blue}         |     \AgdaFunction[Standard]{even more blue}    |
|          Interactive Holes |  \AgdaHole{papaya background}     |   \AgdaHole[Standard]{green background}        |
| Underspecified Elaboration | \AgdaUnsolvedMeta{saffron background} | \AgdaUnsolvedMeta[Standard]{bright yellow background} |

We haven't yet discussed most of these ideas, but perhaps you can see why we
have not followed the standard color-scheme in this book; its high information
density comes at the cost of frenetic, psychedelic experience.

Don't feel like you need to memorize this table. Whenever a new concept is
introduced, I'll share the relevant highlighting information, both in the book
and in your editor. And with a little bit of experience, you'll internalize it
all just from exposure. But feel free to return to this section if you're ever
having a hard time mentally parsing what's going on.


## Types and Values {#sec:bools}

Since this is a book about using programming to do mathematics, it bears discussing a
great deal around *data*---that of the utmost importance to programmers. On a
physical machine, all data is stored as small valences of electrical charge,
arranged into a matrix of cells laid out onto physical wafers, mapped by the
operating system into a logical view that we pretend is laid out linearly into
neat chunks of eight or 64 pieces, that we then interpret as numbers in binary,
and which we then shuffle into higher order assemblages, building
domain- and application-specific logical structure on top.

This is a physical fact, caused by the path dependency that computation has
taken over history. Programmers are often split into two camps: those who
worship and count bits as if they are precious, and those of the opinion that we
have lots of memory, and thus room to ignore it.

Regardless of what camp you find yourself in, thinking about data in terms of
this hierarchy of abstraction will not be conducive to our purposes. A great
deal of this book involves *crafting* data; that is, designing the shapes that
constrain the values we are interested in discussing. Most problems in
mathematics and in programming reduce to finding the right set of constraints,
and rigorously pushing them from one form of data to another.

Data is constrained by *types,* which are rigorous means of constructing and
deconstructing data. You likely already have a notion of what types are, what
they do, and whether or not you like them, but the following section will
nevertheless be informative and elucidating.

Agda takes its types extremely seriously; it is strongly unlikely you have ever
used a language with a type system one tenth as powerful as Agda's. This is true
even if you're intimately familiar with strongly-typed languages like Rust,
TypeScript, Haskell, C++, or Scala. Agda is a *dependently-typed* programming
language, which means its types can be *computed.* For example, you might make a
function that returns a `String` if the 10th Fibonacci number is
56, and a `Boolean` otherwise. At first blush, this seems impractical---if not
useless---but it is in fact the defining feature which makes Agda suitable for
doing mathematics. But let's not get ahead of ourselves.

Of utmost importance in Agda is the notion of a *typing judgment:* the static
assertion that a particular value has a particular type. A typing judgment is
the fancy, academic name for a type declaration. For example, let's consider the
booleans, of which we have two values: `true` and `false`. Because `true` is a
`type:Bool`, we would write the judgment `true : Bool`, where the colon can be
read aloud as "has the type," or "is of type." We can't yet write this judgment
down, since we are in a new module and thus have lost our imports that brought
`true` and `type:Bool` into scope.

In Agda, we can assert the existence of things without having to give them a
definition by using the `keyword:postulate` keyword. As we will see later, this
is can be a very powerful tool, which must be used with great caution since it
is an excellent foot-gun. For now, we will be reckless, and use a postulate to
explicitly write down some typing judgments. First, we assert that the type
`type:Bool` exists:

```agda
module Example-TypingJudgments where
  postulate
    Bool : Set
```

and then, at the same level of indentation, we can postulate the existence of
our two booleans by also giving them typing judgments:

```agda
    false  : Bool
    true   : Bool
```

You will have noticed that `type:Bool : Set` itself looks a great deal like a
typing judgment. And in fact, it is. `type:Set` is one of the few built-in
things in Agda, and it corresponds as a first approximation to "the type of all
types." That is, the judgment `type:Bool : Set` says "`type:Bool` is a type."

And therefore, since `type:Bool` is a type, we are thus justified in saying
that `def:false` and `def:true` are of type `type:Bool`.

But we can't just put any old thing on the right side of the typing colon!
Try, for example, adding the following judgment to our postulate block:

```illegal
    illegal : false
```

If you attempt to load this definition into Agda via [`Load`](AgdaCmd), you'll
get an angry error message stating:

```info
Bool should be a sort, but it isn't
when checking that the expression false has type _4
```

This is not the easiest thing to decipher, but what Agda is trying to tell you
is that `def:false` is not a type, and therefore that it has no business being
on the right-hand side of a colon. The general rule here is that you can only
put `type:Foo` on the *right side* of a colon if you have earlier put it on the
*left* of `type:Set`. In code, we can say:

```agda
    Foo : Set
    -- ...
    bar : Foo
```

As a note on terminology, anything that belongs in `type:Set` we will call a
*type.* Anything which belongs to a type is called a *value.* Thus in the
previous example, we say `type:Foo` is a type, and `def:bar` is a value. As a
matter of convention, types' names will always begin with capital letters, while
values will be given lowercase names. This is not required by Agda; it's merely
for the sake of our respective sanities when the types inevitably get hairy.

It's important to note that while types may have many values, every value has
exactly one type. Since we know that `bar : Foo`, we know for a fact that `bar`
is NOT of type `Qux` (unless `Foo` and `Qux` happen to be the same type.)

Postulating types and values like we have been is a helpful piece of pedagogy,
but it's not how things usually get done. Just as Dijkstra popularized the role
of *structured programming* by arguing programmers should not be writing jumps
directly, but instead using `if` and `while` and so forth, we will note that
real programming does not get done by writing typing judgments directly (nor
does mathematics, for that matter.) Why is this?

One problem is, we'd like to say that `def:false` and `def:true` are *the only*
booleans. But of course, nothing stops us from further postulating another
`type:Bool`, perhaps:

```agda
    file-not-found : Bool
```

You can imagine the chaos that might occur if someone added such a judgment
after the fact. All of a sudden, our programs, carefully designed to handle only
the binary case of booleans, would now need to be retrofitted with extra logic
to handle the case of `file-not-found`. This possibility is anathema to the
concept of modular and composable programs---those that we can write and prove
correct once, without needing to worry about what the future will bring.

In short, working directly with postulates is dangerous and, in general, an
anti-pattern. We will return to postulates in @sec:postulates and see how they
can be useful as mathematical tools. Instead, we will investigate a tool that
instead allows us to simultaneously define `type:Bool`, `def:false` and
`def:true` into a *closed theory.* That is, we'd like to say that these are *the
only* two booleans, allowing us and Agda to reason about that fact.

To do this, we can use a `keyword:data` declaration:

```agda
module Booleans where
  data Bool : Set where
    false  : Bool
    true   : Bool
```

which simultaneously asserts the three typing judgments `Bool : Set`, `false :
Bool`, `true : Bool`, and further, states that this is an *exhaustive* list of
all the booleans. There are, and can be, no others. When written like this, we
often call `ctor:false` and `ctor:true` the *data constructors* or the
*introductory forms* of `type:Bool`.


## Your First Function

After all of this preamble, you are probably itching to write a program in Agda.
As a first step, let's write the `def:not` function, which transforms
`ctor:false` into `ctor:true` and vice-versa. Functions in Agda begin with a
typing judgment using a *function* arrow (which you can type in your editor via
[`to`](AgdaMode)), and are immediately followed by a *definition* of the
function:

```agda
  not⅋₀ : Bool → Bool  -- ! 1
  not⅋₀ = ?  -- ! 2
```

Line [1](Ann) should be read aloud as "`def:not` is a function that takes a
`type:Bool` argument and returns a `type:Bool`," or, alternatively, as
"`def:not` has type `type:Bool` to `type:Bool`." The question mark on line
[2](Ann) says to Agda "we're not sure how to implement this function."

Agda acknowledges that most of the time you're writing a program, it's an
*incomplete* program. Agda is an interactive tool, meaning it can help you
refine incomplete programs into slightly less-incomplete programs. Writing an
Agda program thus feels much more like a conversation with a compiler than it
does being left alone in your text editor, typing away until the program is
done.

Incomplete programs are programs that contain one or more *holes* in them, where
a hole is part of the program that you haven't written yet. Thanks to Agda's
exceptionally strong type system, it knows a great deal about what shape your
hole must have, and what sorts of program-fragments would successfully fill the
hole. In the process of filling a hole, perhaps by calling a function that
returns the correct type, you will create new holes, in this case corresponding
to the *arguments* of that function call. Thus the model is to slowly refine a
hole by filling in more and more details, possibly creating new, smaller holes
in the process. As you continue solving holes, eventually there will be no more
left, and then your program will be complete.

The question mark above at [2](Ann) is one of these holes. After invoking
[`Load`](AgdaCmd) on our file, we can ask it for help in implementing `def:not`.
Position your cursor on the hole and invoke [`MakeCase`](AgdaCmd), which will
replace our definition with:

```agda
  not⅋ : Bool → Bool
  not⅋ x = {! !}
```

You will notice two things have now happened; Agda wrote `x` on the left side of
the equals sign, and it replaced our `?` with `{! !}`. This latter change is a
no-op; `?` and `{! !}` are different syntax for the same thing---a hole. As a
reader playing at home, you will also have noticed Agda's info panel has
changed, updating our "visible" goal from

```info
?1 : Bool → Bool
```

to

```info
?1 : Bool
```

Believe it or not, these changes engendered by invoking [`MakeCase`](AgdaCmd)
have a lot to teach us about how Agda works. Our first hole, way back at
[1](Ann) had type `Bool → Bool`, because we had written `not = ?`. But we
already knew what type `def:not` had, because of the type signature we gave it
on the line immediately above (`type:Bool → Bool`).

After running [`MakeCase`](AgdaCmd) however, our code is now `not x = {! !}`,
and our hole has changed types, now bearing only `type:Bool`. Somehow we lost
the `Bool →` part of the type---but where did it go? As it happens, this first
`Bool →` in the type corresponded to the function's *parameter*. Saying `not :
Bool → Bool` is the same as saying "`not` is a function that takes a `type:Bool`
and returns a `type:Bool`."

We can verify this interpretation by asking Agda another question. By moving
your cursor over the `hole:{! !}` and running [`TypeContext`](AgdaCmd), Agda
will respond in the info window with:

```info
Goal: Bool
———————————————————
x : Bool
```

We can see now that the hole itself (called `Goal` in the info window) is a
missing expression whose type should be `type:Bool`. But, more interestingly,
Agda is also telling us that we now have a variable `x` in scope, whose type
is `type:Bool`. In order to pull the `Bool →` off of the type signature, we were
forced to introduce a binding `x` of type `type:Bool`, which corresponds
exactly to `def:not`'s function argument.

There is an important lesson to be learned here, more than just about how Agda's
type system works. And that's that you can invoke [`TypeContext`](AgdaCmd) at
any time, on any hole, in order to get a better sense of the big picture. In
doing so, you can "drill down" into a hole, and see everything you have in
scope, as well as what type of thing you need to build in order to fill the
hole.

We can ask Agda for more help to continue. This time, if we put our cursor in
the hole and invoke [`MakeCase:x`](AgdaCmd), Agda will enumerate every possible
constructor for `x`, asking us to fill in the result of the function for
each case. Here, that looks like:

```agda
  not⅋⅋ : Bool → Bool
  not⅋⅋ false  = {! !}
  not⅋⅋ true   = {! !}
```

You'll notice where once there was one hole there are now two, one for every
possible value that `x` could have been. Since `x` is a `type:Bool`,
and we know there are exactly two booleans, Agda gives us two cases---one for
`ctor:false` and another for `ctor:true`.

From here, we know how to complete the function without any help from Agda; we'd
like `ctor:false` to map to `ctor:true`, and vice versa. We can write this by
hand; after all, we are not required to program interactively!

```agda
  not : Bool → Bool
  not false  = true
  not true   = false
```

Congratulations, you've just written your first Agda function! Take a moment to
reflect on this model of programming. The most salient aspect is that the
compiler wrote most of this code for us, prompted only by our invocations of
interactivity. Agda supports a great deal of interactive commands, and you will
learn more as you progress through this book. The amount of work that Agda can
do for you is astounding, and it is a good idea to remember what the commands do
and how to quickly invoke them for yourself. In particular, you will get a huge
amount of value out of [`MakeCase`](AgdaCmd) and [`TypeContext`](AgdaCmd); use
the former to get Agda to split variables into their constituent values, and the
latter to help you keep track of what's left to do in a given hole.

The other important point to reflect upon is the *declarative* style that an
Agda program takes on. Rather than attempting to give an algorithm that
transforms some bit pattern corresponding to `def:false` into one corresponding
to `ctor:true`, we simply give a list of definitions and trust the compiler to
work out the details. It doesn't matter *how* Agda decides to map `not false`
into `ctor:true`, so long as it manages to!


## Normalization

At any point in time, we can ask Agda to *normalize* an expression for us,
meaning we'd like to replace as many left-hand sides of equations with their
right-hand sides. This is done via the [`Normalize`](AgdaCmd) command, which
takes an argument asking us what exactly we'd like to normalize.

But before running it for yourself, let's work out the details by hand to get a
sense of what the machine is doing behind the scenes. Let's say we'd like to
normalize the expression `expr:not (not false)`---that is, figure out what it
computes to.

When we look at what "equations" we have to work with, we see that we have the
two lines which define `def:not`. Inspecting our expression again, we see that
there is no rule which matches the outermost `def:not`. The expression `not
false` is neither of the form `ctor:false`, nor is it `ctor:true`, and so the
outermost `def:not` can't expand to its definition.

However, the innermost call to `def:not` is `expr:not false`, which matches one
of our equations exactly. Thus, we can rewrite `expr:not false` to `ctor:true`,
which means we can write the whole expression to `expr:not true`.

At this point, we now have an expression that matches one of our rules, and so
the other rule kicks in, rewriting this to `ctor:false`. Because every "rewrite"
equation comes from a function definition, and there are no more function calls
in our expression, no more rewrite rules can match, and therefore we are done.
Thus, the expression `expr:not (not false)` normalizes to `ctor:false`.

Of course, rather than do all of this work, we can just ask Agda to evaluate the
whole expression for us. Try now invoking [`Normalize:not (not
false)`](AgdaCmd). Agda will respond in the info window:

```info
false
```


## Unit Testing

While [`Normalize`](AgdaCmd) is a nice little tool for interactively computing
small results, we can instead write a small unit test. Breaking our "don't
import it before you define it" rule again, we can bring some necessary
machinery into scope:

```agda
  open import Relation.Binary.PropositionalEquality
```

Now, we can write a unit test that asserts the fact that `expr:not (not false)`
is `ctor:false`, just as we'd expect. Using [`==`](AgdaMode), we can type the
`≡`
symbol, which is necessary in the following snippet:

```agda
  _ : not (not false) ≡ false
  _ = refl
```

Whenever we'd like to show that two expressions normalize to the same thing, we
can write a little unit test of this form. Here, we've defined a value called
`_` (which is the name we use for things we don't care about), and have given it
a strange type and a stranger definition. We will work through all the details
later in @sec:propeq.

The important bits here are only the two expressions on either side of
`type:_≡_`, namely `not (not false)` and `ctor:false`, which we'd like to show
normalize to the same form.

Attempting to [`Load`](AgdaCmd) the file at this point will be rather
underwhelming, as nothing will happen. But that's both OK and to be expected;
that means our unit test passed. Instead, we can try telling Agda a lie:

```illegal
  _ : not (not false) ≡ true
  _ = refl
```

Try running [`Load`](AgdaCmd) again, which will cause Agda to loudly proclaim a
problem in the info window:

```info
false != true of type Bool
when checking that the expression refl has type not (not false) ≡ true
```

This error is telling us that our unit test failed; that `not (not false)`
is actually `ctor:false`, but we said it was `ctor:true`. These unit tests only
yell when they fail. In fact, it's worse than that; these unit tests *prevent
compilation* if they fail. Thus when dealing with tests in Agda, it's just like
the old proverb says---no news is good news!


## Dealing with Unicode

In the last section, we got our first taste of how Agda uses Unicode, when we
were required to use the character `≡`. This is the first of much, much more
Unicode in your future as an Agda programmer.

The field of programming has a peculiar affinity for the standard ASCII
character set, which is somewhat odd when you think about it. What symbol is
`==` supposed to be, anyway? Is it *merely* a standard equals sign? If so, why
not just use a single `=`, which would be much more reasonable. Maybe instead
it's supposed to be an elongated equals sign? Does that correspond to anything
historically, or was it just a new symbol invented for the purpose? If we're
inventing symbols anyway, surely `=?` would have been a better name for the
test-for-equality operator.

In fact, Agda follows this line of reasoning, but decides that, since we have a
perfectly good Unicode symbol anyway, we ought to just use `≟` instead!

Unicode, more than the weird lack of computation and advanced type system, is
many programmers' biggest challenging when coming to Agda. Learning to wrangle
all of the Unicode characters is be daunting for at least three reasons---how
can we distinguish all of these characters, what should we call them, and how in
heck do we input them?

The first problem---that of identification---is that there are great swathes of
Unicode characters, many of which are identical.  For example, when I was
getting started, I was often flummoxed by the difference between `⊎` and `⊎`.
Believe it or not, the former symbol is extremely important in Agda, while the
latter won't play nicely with the standard library. As it happens, the former
symbol is the "multiset union", while the latter is the "n-ary union operator
with plus." As far as Unicode (and Agda) is concerned, these are completely
different characters, but, as far as you and I can tell, they are
indistinguishable.

Unfortunately, there is no real solution to this problem, other than putting in
the time, and feeling the pain while you're sorting things out in your head.

However, this is less of a problem in practice than it might seem. When you're
first getting started, you're not going to dream up the `⊎` operator on your
own. Instead, you'll just read some code that happens to use this operator, and
thus we can apply the imitable monkey-see-monkey-do strategy. Whenever you
encounter a symbol you aren't familiar with, simply invoke Agda's
[`DescribeChar`](AgdaCmd) command. When invoked with the cursor over `⊎`, the
info window will respond the following output:

```info
            character: ⊎ (displayed as ⊎)
code point in charset: 0x228E
             to input: type "\u+" with Agda input method

Character code properties:
  name: MULTISET UNION
```

The real output from Agda has been truncated here, but there are two important
pieces of information here. The first is under the *name* heading, which tells
you what to call this particular symbol. And the other is under *to input*,
which is how exactly you can type this character in your editor. Try typing
[`u+`](AgdaMode) in your editor, and you should indeed get a `⊎` on screen.

Of course, this hunt-and-peck approach works only when you're trying to learn
how to input a particular symbol that you have access to in source code. What
can you do instead if you have a particular symbol in mind? Thankfully we don't
need to resort to skimming code, hoping to find what we're looking for. Instead,
we can attempt to *compose* the symbol, by guessing the necessary keystrokes.

When writing Agda, you can input Unicode characters by typing a backslash, and
then a mnemonic for the character you'd like. There are a few different naming
schemes used by Agda, but for abstract symbols like `⊎` a good bet is to try to
press a series of characters that together build the one you want.

To illustrate this composition of abstract symbols, we can take a look at some
examples. None of these should be surprising to you.

- `∙` is input by typing [`.`](AgdaMode)
- `∘` is input by typing [`o`](AgdaMode)
- `×` is input by typing [`x`](AgdaMode)
- `¿` is input by typing [`?`](AgdaMode)
- `⊎` is input by typing [`u+`](AgdaMode)
- `⊚` is input by typing [`oo`](AgdaMode)
- `⊗` is input by typing [`ox`](AgdaMode)
- `⊙` is input by typing [`o.`](AgdaMode)
- `→` is input by typing [`->`](AgdaMode)
- `←` is input by typing [`<-`](AgdaMode)
- `≋` is input by typing [`~~~`](AgdaMode).
- `≗` is input by typing [`=o`](AgdaMode)
- `≟` is input by typing [`=?`](AgdaMode).

As you have already seen, one common binding you'll need is that for function
arrows, `→`. This is typed in the obvious way, [`->`](AgdaMode), but can also be
written in fewer keystrokes as [`to`](AgdaMode). Typesetting aficionados might
be delighted that this is mnemonic that LaTeX uses to inset the arrow symbol. If
you're familiar with LaTeX, many bindings you know from there will also work in
Agda:

- typing [`to`](AgdaMode) produces `→`
- typing [`in`](AgdaMode) produces `∈`
- typing [`inn`](AgdaMode) produces `∉`
- typing [`sub`](AgdaMode) produces `⊂`
- typing [`neg`](AgdaMode) produces `¬`
- typing [`top`](AgdaMode) produces `⊤`
- typing [`bot`](AgdaMode) produces `⊥`

Similarly to LaTeX, we can prefix bindings with `_` or `^` to make subscript or
superscript versions of characters, as in:

- [`_1`](AgdaMode) for `₁`
- [`_2`](AgdaMode) for `₂`
- [`_x`](AgdaMode) for `ₓ`
- [`^1`](AgdaMode) for `¹`
- [`^f`](AgdaMode) for `ᶠ`
- [`^z`](AgdaMode) for `ᶻ`

All numbers have sub- and superscript versions, but only some letters do. This
is not Agda's fault; address your complaints to the Unicode Consortium regarding
the unfortunate lack of a subscript `f`.

Mathematicians and Agda-users alike are very fond of Greek letters, which you
can type by prefixing the Latin-equivalent letter with [`G`](AgdaMode).

- type [`Ga`](AgdaMode) for `α`, which is the Greek letter for `a`
- type [`Gd`](AgdaMode) for `δ`, which is the Greek letter for `d`
- type [`GD`](AgdaMode) for `Δ`, which is the Greek letter for `D`
- type [`Gl`](AgdaMode) for `λ`, which is the Greek letter for `l`
- type [`GL`](AgdaMode) for `Λ`, which is the Greek letter for `L`

As you can see, the input system is quite well organized when you wrap your head
around it---assuming you know Greek!

There is one other block of symbols you will probably need at first: the
so-called *blackboard bold* letters. These are often used in mathematics to
describe sets of numbers---the natural numbers being `ℕ`, the reals being `ℝ`,
the rationals being `ℚ` (short for "quotients"), and so on. You can type
blackboard bold numbers with the [`b`](AgdaMode) prefix. The three examples here
are input as [`bN`](AgdaMode), [`bR`](AgdaMode) and [`bQ`](AgdaMode)
respectively.

Suspend your disbelief; programming in Unicode really is quite delightful if you
can push through the first few hours. Having orders of magnitude more symbols
under your fingers is remarkably powerful, meaning you can shorten your
identifiers without throwing away information. In addition, you will notice a
common vocabulary for how these symbols get used. Being able to recognize more
symbols means you can recognize more concepts at a distance. For example, we
will often use the floor brackets `⌊⌋` (given by [`clL`](AgdaMode) and
[`clR`](AgdaMode)) for as a name for an "evaluation" function.

As a bonus, when transcribing mathematics, your program can look exceptionally
close to the source material. This is nice, as it minimizes the cognitive load
required to keep everything in your head. You're already dealing with big ideas,
without having to add a layer of naming indirection into the mix.


## Expressions and Functions

Agda descends from the ML family of languages, making it related to Elm, F#,
Haskell, OCaml, PureScript, among many, many other cousins. This section will
give you a brief overview of how to conceptualize Agda as a programming
language, including some sense of how to mentally parse it.

Agda is an expression-based language, meaning that every unit of code must
produce a value. Therefore, there are no control-flow statements in this
language, because control flow doesn't directly produce a value. Agda has no
support for common constructions like `for` or `while` loops, and while it does
support `if..then..else` its prevalence is very subdued. In Agda, we have much
better tools for branching, as we will see soon in @sec:patterns.

This ascetic expression dedication precludes many other features that you might
think be ubiquitous in programming languages. The most substantial of these
elided features is that Agda does not support any form of mutable variables.
While at first blush this feels like an insane limitation, mutable variables
don't end up being a thing you miss after a little time apart.

The problem with mutable variables is that code with access to them can no
longer be isolated and studied on its own. In the presence of mutable variables,
the behavior of a piece of code depends not only on the program snippet, but
also implicitly on the historical context under which this snippet is being run.
By the Law of Demeter---which states that code should assume as little as
possible about anything---mutable variables are quite a taxing feature, in that
they effectively limit our ability to confidently reuse code.

Writing real code without mutable variables is surprisingly comfortable, once
you've wrapped your head around how. The trick is a to perform a series of
syntactic transformations which eliminate the mutation. For example, whenever
you need to read from a mutable variable, instead, just pass in a function
argument. That is, instead of:

```cpp
int foo;

function bar() {
  // ...
  int a = foo;
  // ...
}
```

you can write:

```cpp
function bar(int a) {
  // ...
}
```

If you'd like to *change* a mutable variable, instead, just return it as an
additional result of the function! While this seems (and is) clunky in C-like
languages, it's much less painful in Agda. We will not discuss the matter
further, instead hoping the motivated reader will pick up the necessary tricks
as we go.

There is one further point about functions in Agda that I'd like to make,
however. The syntax can be rather weird. You are likely familiar with
C-style function calls which look like this:

```c
foo(bar, 5, true)
```

Instead of these parentheses and commas, Agda instead uses *juxtaposition* as
its syntax for function calls. The above call would look, in Agda, like this:

```example
foo bar 5 true
```

Note that the arguments here are separated here only by whitespace. If
disambiguation is necessary (which it will be whenever we have nested function
calls) we surround the entire expression in parentheses:

```example
baz 0 (f false) (foo bar 5 true)
```

This would be written in the ALGOL style as

```cpp
baz(0, f(false), foo(bar, 5, true))
```

While it might feel like an unnecessarily annoying break in conventional syntax,
there are mightily-good theoretical reasons for it, addressed in @sec:currying.
Given this new lens on the syntax of function calls, it's informative to look
back at our definition of `def:not`; recall:

```agda
  not⅋⅋⅋⅋ : Bool → Bool
  not⅋⅋⅋⅋ false  = true
  not⅋⅋⅋⅋ true   = false
```

we can now mentally parse these definitions differently, that is, we can read
them *literally.* The left side of each equation is just a function call!
Therefore, the first equation says "the function `def:not` called with argument
`ctor:false` is equal to `ctor:true`".

The equals sign is really and truly an *equals* sign; it denotes that we have
*defined* `expr:not⅋⅋⅋⅋ false` to be `ctor:true`. And the funny thing about
equalities is that they go both directions, so it's also correct to say that
`ctor:true` is equal to `expr:not⅋⅋⅋⅋ false``.

This equality is very deep. While Agda will simplify the left side to the right
whenever possible, the two sides are exactly equivalent in all computational
contexts, and we can pick whichever is the most helpful for our proof. Indeed,
many proofs depend on finding two complicated expressions that are exactly equal
in this way. Much of the work is in figuring out which two complicated
expressions we need to find.


## Operators

Armed with a better understanding of how Agda works, we can return to writing
actual code. One simple operation over booleans is logical OR; that is, the
result is true if at least one of its arguments is true. Mathematicians often
use the symbol $\vee$ (pronounced "vel") for this operation, which we will
follow. Note that this is not the Latin letter that comes before `w`, but
instead the Unicode character produced by typing [`or`](AgdaMode).

This odd choice for a function name is justified because that's what the
standard library calls it, and we'd like to reimplement the standard library as
a pedagogical exercise. Incidentally, the standard library didn't just make up
this name; `∨` is the mathematical symbol used for joins in a semilattice, and
`OR` is exactly that join on the boolean semilattice. Don't worry if you don't
yet know what this means, as we'll look investigate semilattices in
@sec:semilattices.

We can start our implementation for `def:_∨⅋⅋_` by writing out a function
signature, and then giving a hole on the next line, as in:

```agda
  _∨⅋⅋_ : Bool → Bool → Bool
  _∨⅋⅋_ = ?
```

The function signature here is a little strange, as we'd expect it to be
something more akin to `expr:(Bool ,⅋₉ Bool) → Bool`---that is, a function from
two booleans to one. For the time being, just imagine that *is* the type
signature. The point is rather subtle, and we will address the point of
confusion soon, in @sec:currying.

In order to implement `def:_∨⅋⅋_`, we will again interactively ask for Agda's
help. Place your cursor in the hole and run [`MakeCase`](AgdaCmd). Agda will
respond with:

```agda
  _∨⅋⅋⅋_ : Bool → Bool → Bool
  x ∨⅋⅋⅋ x₁ = {! !}
```

You will notice that the left-hand side of our equation has changed. Where
before we had two underscores, we now have `x` and `x₁`. As it happens, those
underscores were not literal underscores, but instead marked placeholders for
in the operator's syntax for its arguments.

One advantage to the `hole:{! !}` form for Agda's holes is that we can type
inside of them. If you fill the hole with `hole:{! x x₁ !}`, as in:

```agda
  _∨⅋⅋⅋⅋_ : Bool → Bool → Bool
  x ∨⅋⅋⅋⅋ x₁ = {! x x₁ !}
```

you can now invoke [`MakeCase`](AgdaCmd), and rather than prompting you like
usual, Agda will just use the arguments you wrote inside the hole. Thus, we
receive a very satisfying four lines of code that we didn't have to write for
ourselves:

```agda
  _∨⅋⅋⅋⅋⅋_ : Bool → Bool → Bool
  false  ∨⅋⅋⅋⅋⅋ false  = {! !}
  false  ∨⅋⅋⅋⅋⅋ true   = {! !}
  true   ∨⅋⅋⅋⅋⅋ false  = {! !}
  true   ∨⅋⅋⅋⅋⅋ true   = {! !}
```

We can finish the definition of `def:_∨_` by giving filling in the desired
answers in each hole:

```agda
  _∨⅋_ : Bool → Bool → Bool
  false  ∨⅋ false  = false
  false  ∨⅋ true   = true
  true   ∨⅋ false  = true
  true   ∨⅋ true   = true
```

Here we have taken the same approach as in `def:not`: for each argument, we
enumerate every possibilities, giving the answer on the right side of the equals
sign. You will quickly notice that this strategy grows exponentially fast; a
function of five booleans would require 32 clauses to enumerate every
possibility. Fortunately, this is not the only way to define `def:_∨_`. We can
instead throw some thought at the problem, and realize the goal is to identify
whether or not one of the arguments is `ctor:true`. This doesn't require pattern
matching on *both* parameters---some clever insight indicates we can get away
with matching only on one.

If the argument we matched on is `ctor:true`, we're done, without needing to
inspect the other. Otherwise, if our matched argument is `ctor:false`, it
doesn't affect the answer, because the result is `ctor:true` only with the other
argument is `ctor:true`.

Thus, in neither the `ctor:true` nor `ctor:false` case do we need to look at
the second argument. We can take advantage of this fact by using a variable to
abstract over the second parameter. Instead, let us define `def:_∨_` in this
way:

```agda
  _∨_ : Bool → Bool → Bool
  false  ∨ other = other
  true   ∨ other = true
```

Pay attention to the syntax highlighting here, as this is the first time it is
taking advantage of the compiler's knowledge. Here, we've written `other` on the
right side of `def:_∨_`, and Agda has colored it black rather than the usual
red. This is because Agda reserves the red for *constructors* of the type, of
which there are only two (`ctor:true` and `ctor:false`.) By writing anything
*other* than the name of a constructor, Agda assumes we'd like to treat such a
thing as a variable binding.

In both cases, we now have a new variable `other :` `type:Bool` in scope,
although we only end up using it when the first argument was `ctor:false`.

As our Agda examples get more complicated, being able to quickly read the
information conveyed in the syntax highlighting will dramatically improve your
life. Red identifiers are reserved for constructors of a type. Blue is for types
and functions, and black is for locally-bound constant variables---all three of
which are visible in this last example.

Note that we call `other` a variable, but it is a variable in the mathematical
sense rather than in the usual programming sense. This variable is a way of
talking about something whose value we don't know, like the $x$ in the
expression $f(x) = 2x$ (but not like the $x$ in $x^2 = 9$.) Here, $x$ exists,
but its value is set once and for all by the user of $f$. When we are talking
about $f(5)$, $x = 5$, and it is never the case that $x$ changes to 7 while
still in the context of $f(5)$. In any given context, $x$ is always *bound* to a
specific value, even if we don't know what that value is. For this reason, we
sometimes call variables *bindings.*


## Agda's Computational Model

Let's compare our two definitions of `def:_∨_`, reproduced here with slightly
different names:

```agda
  _∨₁_ : Bool → Bool → Bool  -- ! 1
  false  ∨₁ false  = false
  false  ∨₁ true   = true
  true   ∨₁ false  = true
  true   ∨₁ true   = true
```

and

```agda
  _∨₂_ : Bool → Bool → Bool  -- ! 2
  false  ∨₂ other  = other
  true   ∨₂ other  = true
```

Besides the amount of code we needed to write, is there a reason to prefer
[2](Ann) over [1](Ann)? These two implementations are equivalent, but have very
different computational properties as Agda programs. Let's explore why that is.

While [1](Ann) is perhaps slightly clearer if you're coming from a truth-table
background, [2](Ann) is a better program because it branches less often. It's
easy to read the branching factor directly off the definition: `def:_∨₁_` takes
four lines to define, while `def:_∨₂_` requires only two. Every time we must
inspect which particular boolean value a parameter has, we are required to
bifurcate our program.

We will return to this idea when we discuss writing proofs about functions like
`def:_∨_`. But for the time being, we can directly observe the difference in how
Agda computes between `def:_∨₁_` and `def:_∨₂_`.

At its root, [2](Ann) is a better program *because* it needs to inspect less
data in order to make a decision. `def:_∨₂_` is able to make meaningful progress
towards an answer, even when the second argument isn't yet known, while `def:_v₁_`
is required to wait for both arguments.

Agda supports *partial application* of functions, which means we're allowed to
see what would happen if we were to fill in some function arguments, while
leaving others blank. The syntax for doing this on operators is to reintroduce
an underscore on the side we'd like to leave indeterminate. For example, if we'd
like to partially apply the first argument of `def:_∨₁_`, we could write
`expr:true ∨₁_`, while we can partially apply the second argument via `expr:_∨₁
true`. You will sometimes hear this called "taking a *section* of `def:_∨₁_`."

We can observe the difference between `def:_∨₁_` and `def:_∨₂_` by looking at
how Agda computes a section over each of their first arguments. We can evaluate
arbitrary snippets of Agda code with the [`Normalise`](AgdaCmd) command. First,
try normalizing `expr:true ∨₂_`, to which Agda will respond:

```info
λ other → true
```

The lambda notation here is Agda's syntax for an anonymous function. Thus, Agda
tells us that `expr:true ∨₂_` is equal to a function which ignores its argument
and always returns `ctor:true`. This is what we would expect semantically, based
on the definitions we gave above for `def:_∨₂_`.

It's informative to compare these results against running [`Normalise:true
∨₁_`](AgdaCmd):

```info
true ∨₁_
```

Here, Agda simply returns what we gave it, because it is unable to make any
progress towards evaluating this value. There's simply no way to make any
reductions until we know what the second argument is!


## Stuckness

Terms which are unable to reduce further are called *stuck*, and can make no
progress in evaluation until something unsticks them. The usual reason something
behind being stuck is that it's waiting to inspect a value which hasn't yet been
provided.

Stuckness can be quite a challenge to debug if you're unaware of it, so it bears
some discussion.

In our example trying to normalize `expr:true ∨₁_`, because we don't yet know
the value of the second argument, our pattern match inside of `def:_∨₁_` is
stuck, and thus the value of the call to `expr:true ∨₁_` is *also* stuck. As
soon as the second argument is provided, the pattern match will unstick, and so
too will the final result.

Another way by which stuckness can occur is through use of postulated values.
Recall that the `keyword:postulate` keyword allows us to bring into scope a
variable of any type we'd like. However, we have no guarantee that such a thing
necessarily exists. And so Agda offers us a compromise. We're allowed to work
with postulated values, but they are always stuck, and our program will not be
able to proceed if it ever needs to inspect a stuck value.

To demonstrate this, we can postulate a boolean value aptly named
`postulate:always-stuck`:


```agda
  postulate always-stuck : Bool
```

Our new `postulate:always-stuck` binding is, as its name suggests, always stuck.
For example, we can learn nothing more about it by running
[`Normalise:always-stuck`](AgdaCmd):

```info
always-stuck
```

Nor can we reduce `expr:not always-stuck` to a value, because `def:not` must
inspect its value in order to make progress:

```info
not always-stuck
```

Don't believe the response from [`Normalise`](AgdaCmd);
`expr:not always-stuck` is indeed always stuck (although it *is* distinct from
`postulate:always-stuck`.) Rather, the entire call to `def:not`
with argument `postulate:always-stuck` is stuck. And, as you might expect,
[`Normalise:true ∨₁ always-stuck`](AgdaCmd) is also stuck:

```info
true ∨₁ always-stuck
```

Fascinatingly however, attempting to normalize `expr:true ∨₂ always-stuck`
computes just fine:

```info
true
```

It is exactly because of this computational progress, even when the second
argument is stuck (`postulate:always-stuck` or otherwise), that we prefer
`def:_∨₂_` over `def:_∨₁_`.

While this example might seem somewhat contrived, you would be amazed at how
often it comes up in practice. Avoiding a pattern match in an implementation
means you can avoid a pattern match in every subsequent proof *about* the
implementation, and can be the difference between a three line proof and an 81
line proof.

We will return to this point when we discuss proof techniques, but for now, try
not to get into the habit of "bashing" your way through every implementation if
you can help it.


## Records and Tuples

In @sec:bools, we saw how the `keyword:data` keyword could be used to create
types with distinct values. Most programming languages do not admit any features
analogous to the `keyword:data` type former, which is why booleans and
numbers---two types that are *all about* distinct values---are usually baked
directly into most languages. We have already looked at defining our own
booleans, in @sec:numbers we will focus on defining numbers for ourselves.

To tide us over in the meantime, we will look at the more-familiar *record
types*: those built by sticking a value of *this* type, and a value of *that*
type, and maybe even *one of the other* type together, all at the same time.

Let's put together a little example. Imagine we're modeling the employee
database at a company. First, let's start a new module, bring our
`module:Booleans` into scope, and import `def:String`s:

```agda
module Example-Employees where
  open Booleans
  open import Data.String
    using (String)
```

Our company has five departments. Every employee must belong to one of these.
Whenever you hear the words "one of" used to describe how a piece of
information, you should think about modeling it using a `keyword:data` type:

```agda
  data Department : Set where
    administrative engineering finance marketing sales : Department
```

Let's say employees at our company have three relevant pieces of information:
their name, which department they're in, and whether they've been hired
recently. Whenever you hear "and" when describing a type, you should think about
using a `keyword:record`, as in:

```agda
  record Employee : Set where
    field
      name         : String
      department   : Department
      is-new-hire  : Bool
```

We can build a value of `type:Employee` also by using the `keyword:record`
keyword, as in:

```agda
  tillman : Employee
  tillman = record
    { name         = "Tillman"
    ; department   = engineering
    ; is-new-hire  = false
    }
```

Sometimes we'd like to just stick two pieces of information together, without
going through the rigmarole of needing to make a custom type for the occassion.
In these cases, we'll need a *generic* record type, capable of sticking any two
values together.

In essence, then, the goal is to build a record type with two generic,
independently-typed fields. We can't hard-code the types we'd like for the
fields, because then it wouldn't be generic. So instead, we do what we always do
in situations like this, and parameterize things:

```agda
module Sandbox-Tuples where
  record _×⅋_ (A : Set) (B : Set) : Set where  -- ! 1
    field
      proj₁  : A
      proj₂  : B
```

There is quite a lot going on here. First, note that the name `type:_×_` here is
not the Latin letter `x`, but is instead the *times symbol,* input as
[`x`](AgdaMode).

At [1](Ann) we parameterize the our type `type:_×_` by two other types, called
`A` and `B`. You can see from the black syntax highlighting on `A` and `B` that
these are not types in their own right, but locally-bound variables which are
later *instantiated* as types. The entire situation is analogous to functions;
think of `type:_×_` as a function which takes two types and returns a third
type.

Inside the `keyword:record`, we've given two fields, `field:proj₁` and
`field:proj₂`. These names are intentionally vague, since we have no idea how
real people will end up using `type:_×_` in practice. Incidentally, "proj" is
short for *projection*---which is the mathy word for reducing a complicated
structure down along some axis. In this case we have two different "axes": the
first and the second elements of our tuple.

We can try out our new tuple type, as usual by plunking a hole down on the right
hand side of the equals sign:

```agda
  open Booleans

  my-tuple⅋⅋ : Bool ×⅋ Bool
  my-tuple⅋⅋ = ?
```

This time we will use the [`Refine`](AgdaCmd) command, which asks Agda to build
us a value of the correct type, leaving holes for every argument. The result is:

```agda
  my-tuple⅋ : Bool ×⅋ Bool
  my-tuple⅋ = record { proj₁ = ? ; proj₂ = ? }
```

Note that these two holes both have type `type:Bool`, corresponding exactly to the
type of the tuple (`Bool × Bool`.) We can fill them in with arbitrary boolean
expressions:

```agda
  my-tuple : Bool ×⅋ Bool
  my-tuple = record { proj₁ = true ∨ true ; proj₂ = not true }
```

Congratulations! We've made a reusable---if not very syntactically
beautiful---tuple type! We'd now like to extract the two fields from
`def:my-tuple`. How can we do that? Agda provides three means of projecting
fields out of records. The first is a regular old pattern match:

```agda
  first : Bool ×⅋ Bool → Bool
  first record { proj₁ = proj₁ ; proj₂ = proj₂ } = proj₁
```

The syntax here brings pleasure to no one's heart, but it does work. There are
some things to note. First, I didn't write this definition out by hand. I
instead wrote down the type, stuck in a hole, and then invoked
[`MakeCase`](AgdaCmd) twice. Nobody has type to write out this ugly syntax; just
get the computer to do it for you.

Second, once again, Agda's syntax highlighting has done us a great favor. Look
at the unpacking happening inside the `keyword:record` constructor. We have a
green `field:proj₁` being equal to a black `proj₁`. Agda highlights field names
in green, and bindings in black, which means we know immediately know what this
syntax must be doing. The green part is which field we're looking at, and the
black piece is the name we'd like to bind it to. Thus, the following definition
is equivalent:

```agda
  first⅋ : Bool ×⅋ Bool → Bool
  first⅋ record { proj₁ = x ; proj₂ = y } = x
```

Even better, we don't need to bind fields that we don't intend to use, so we can
write `def:first` more tersely again:

```agda
  first⅋₀ : Bool ×⅋ Bool → Bool
  first⅋₀ record { proj₁ = x } = x
```

I said there were three ways to project a field out of a record. If we don't
want to do a gnarly pattern match like this, what are our other options? One
other means is via *record access* syntax, where the field name is prepended
with a dot and given *after* the tuple:

```agda
  my-tuple-first : Bool
  my-tuple-first = my-tuple ._×⅋_.proj₁
```

You will notice that we needed to give a *fully-qualified* field name here.
Rather than just writing `field:proj₁` we needed to give `expr:_×⅋_.proj₁` in
full. But don't fret, this is still the field name. We'll see momentarily how to
clean things up.

Our other means for projecting fields out of records is via the *record
selector* syntax. Under this syntax, we use the field name as if we were making
a function call:

```agda
  my-tuple-second : Bool
  my-tuple-second = _×⅋_.proj₂ my-tuple
```

The reason that record selector syntax looks like a function call is because it
*is* a function call. Every record field `field:f` of type `type:F` in record
`type:R` gives rise to a function `field:f` `:` `type:R → F`.

Record access and record selectors just different syntax for the exact same
functionality, and it's a matter of personal preference as to which you pick.
Personally, I like using record selectors, because it means I can forget the
fact that I'm working with *records* and think only about *functions.*

In reading the above, it cannot have escaped your attention that these two call
sites are *ugly.* What is this `expr:_×⅋_.proj₁` nonsense? Do we really need to
use a fully-qualified name every time we want to access a field? Fortunately, we
do not.

Believe it or not, every `keyword:record` creates a new `keyword:module` with
the same name. Thus, we can bring `field:proj₁` and `field:proj₂` into the
top-level scope by opening our new module, allowing us to rewrite the previous
two definitions as:


```agda
  open _×⅋_

  my-tuple-first⅋ : Bool
  my-tuple-first⅋ = my-tuple .proj₁

  my-tuple-second⅋ : Bool
  my-tuple-second⅋ = proj₂ my-tuple
```

Much nicer, isn't it?


## Copatterns and Constructors

We now have nice syntax for projecting out of records. But can we do anything to
improve the syntax involved in building them? It would be really nice to be able
to avoid the `record { proj₁ = ... }` boilerplate every time we wanted to make a
tuple.

If we don't mind giving a name to our tuple, we can use *copattern* syntax to
build one. The idea is rather than define the record itself, we need only give
definitions for each of its fields. Agda can help us with this. Start as usual
with a type and a hole:

```agda
  my-copattern⅋₀ : Bool ×⅋ Bool
  my-copattern⅋₀ = ?
```

If we now attempt to perform a [`MakeCase:`](AgdaCmd) inside the hole, we will
be rewarded with a copattern match:

```agda
  my-copattern⅋₁ : Bool ×⅋ Bool
  proj₁ my-copattern⅋₁ = {! !}
  proj₂ my-copattern⅋₁ = {! !}
```

Copatterns can be nested, for example, in the case when we have a nested tuple:

```agda
  nested-copattern⅋₁ : Bool ×⅋ (Bool ×⅋ Bool)
  proj₁ nested-copattern⅋₁ = {! !}
  proj₁ (proj₂ nested-copattern⅋₁) = {! !}
  proj₂ (proj₂ nested-copattern⅋₁) = {! !}
```

We will make extensive use of copatterns later in this book, and will discuss
them in much more depth in @sec:copatterns. For the time being, it's nice to
know that this is an option.

Suppose however, we'd like to not use copatterns---perhaps because we'd like to
build an anonymous value of a record type. For that, we can instead write a
helper function that will clean up the syntax for us.

```agda
  _,⅋_  : {A B : Set} → A → B → A ×⅋ B  -- ! 1
  _,⅋_  = ?
```

The type of `def:_,_` should really be `A → B → A × B`. However, recall that `A`
and `B` are variables standing in for *whatever type the user wants.*
Unfortunately for us, we don't know what those types are yet, but we need them
in order to give a proper type to `def:_⅋_`. Since those variables are not in
scope, we must bind them ourselves.

This binding is what's happening in the `{A B : Set}` syntax that prefixes the
type at [1](Ann). It's responsible for bringing `A` and `B` both into scope, and
letting Agda know they are both of type `type:Set`. We will discuss what exactly
the curly braces mean momentarily, in @sec:implicits.

Implementing `def:_,_` isn't hard to do by hand; but we can be lazy and ask Agda to
do it for us. Begin as usual by getting Agda to bind our arguments, via
[`MakeCase`](AgdaCmd) in the hole:

```agda
  _,⅋⅋_  : {A B : Set} → A → B → A ×⅋ B
  x ,⅋⅋ x₁ = {! !}
```

and follow up by invoking [`Auto`](AgdaCmd), which asks Agda to just write the
function for you. Of course, this doesn't always work, but it's surprisingly
good for little functions like `def:_,_`. The result is exactly what we'd expect
it to be:

```agda
  _,⅋⅋⅋_  : {A B : Set} → A → B → A ×⅋ B
  x ,⅋⅋⅋ x₁ = record { proj₁ = x ; proj₂ = x₁ }
```

The `def:_,_` is now shorthand for writing out a `keyword:record` value. We can
reimplement `def:my-tuple` thus:

```agda
  my-tuple' : Bool ×⅋ Bool
  my-tuple' = (true ∨ true) ,⅋⅋⅋ not true
```

The parentheses here are necessary because Agda doesn't know if it should parse
the expression `ctor:true` `def:∨` `ctor:true` `def:,⅋` `def:not` `ctor:true` as
`expr:true ∨ (true ,⅋ not true)` or as the expression intended above.

Of course, you and I know that the other parse doesn't even typecheck, so it
must be the unintended. You can, however, imagine a much larger expression could
take an exponential amount of time in order to find a unique way of adding
parentheses to make the types work out properly. We will fix this limitation
in the next section.

As it happens, we can get Agda to automatically create `def:_,_`, rather
than needing to define it ourselves. Doing so, however, requires changing the
definition of `def:_×⅋_`, which we are now unable to do, since we have defined
things after the fact.

Let's start a new module, and redefine `def:_×_` in order to get `def:_,_` for
free.

```agda
module Sandbox-Tuples₂⅋ where
  open Booleans

  record _×_ (A : Set) (B : Set) : Set where
    constructor _,_  -- ! 1
    field
      proj₁ : A
      proj₂ : B

  open _×_
```

There is one small change compared to our previous definition, and that's the
`keyword:constructor` keyword at [1](Ann). Adding a `keyword:constructor`
definition tells Agda that we'd like to avoid the whole `keyword:record` `{ ...
}` nonsense. Instead, we we automatically get `ctor:_,_` for free, which you
will notice is now colored red, to let us know that it is a constructor.


## Fixities {#sec:fixity}

We return now to the problem of getting Agda to correctly parse the expression
`ctor:true` `def:∨` `ctor:true` `def:,⅋` `def:not` `ctor:true` the implied
parentheses on the left. Infix operators like `def:_∨_` and `ctor:_,_` are
parsed in every language according to rules of *precedence* and
*associativity.* Together, these two concepts are known as *fixities.*

The *precedence* of an operator lets the parser know how "tightly" an operator
should bind with respect to other operators. In this case, because we'd like the
parentheses to go around `def:_∨_`, we would like `def:_∨_` to have a higher precedence
than `ctor:_,_`. Agda assumes a precedence of 20 (on a scale from 0 to 100) by
default for any operator, so we must give `ctor:_,_` a *lower* precedence than 20. By
convention, we give `ctor:_,_` a precedence of 4, which makes it play nicely with the
conventions for the more usual mathematic operators like addition and
subtraction.

The *associativity* of an operator describes how to insert parentheses into
repeated applications of the operator. That is, should we parse `x , y , z` as
`(x , y) , z` or as `x , (y , z)`? The former here is said to be
*left-associative*, while the latter is, appropriately, *right-associative.* For
reasons that will make sense later, we'd like `ctor:_,_` to be right-associative.

We can tell Agda's parser about our preferences, that `ctor:_,_` be
right-associative with precedence 4 via the following declaration:

```agda
  infixr 4 _,_
```

Here, the `r` at the end of `keyword:infixr` tells Agda that our preference is
for associativity to be to the right. The analogous keyword `keyword:infixl`
informs Agda of the opposite decision. With this fixity in place, Agda will now
automatically insert parentheses, parsing `expr:true , false , true , false` as
`expr:true , (false , (true , false))`. Of course, if you ever *do* want an
explicit left-nested tuple, you are free to insert the parentheses on the left
yourself.

While `ctor:_,_` is the operator for building *values* of tuple types,
`type:_×_` is the operator for building the tuple type itself. The values and
their types should be in a one-to-one correspondence. That is to say, if we have
`a : A`, `b : B` and `c : C`, we'd like that `a` `ctor:,` `b` `ctor:,` `c` have
type `type:A × B × C`. By this reasoning, must also choose right-associativity
for `type:_×_`. Traditionally, `type:_×_` is given a precedence of 2.

```agda
  infixr 2 _×_
```


## Function Types

It is now time to tackle the question of what's up with the funny syntax for
functions with multiple arguments. Most programming languages assign a type of
the form `type:(A × B) → C` to functions with two arguments, while in Agda we
instead write `type:A → B → C`. Why is this?

In order to help understand this type, we can stop for a moment to think
about the issue of parsing again. Although the function arrow is intrinsically
magical and built-in to Agda, let's ask ourselves how it *ought* to work.

Spiritually, `type:_→_` is a binary operator, meaning we can ask about its
precedence and associativity. In Agda, the typing judgment `_:_` binds with the
lowest precedence of all, with `type:_→_` coming in as a close second. What this
means is that in practice, `type:_→_` always acts as a separator between types,
and we don't need to worry ourselves about where exactly the parentheses should
go.

The associativity for `type:_→_`, on the other hand, is to the right. That
means, given the type `type:A → B → C`, we must read it as `type:A → (B → C)`. A
literal interpretation of such a thing is a function that takes an `A` argument
and *returns a function.* That returned function itself takes a `B` argument and
then returns a `C`. At the end of the day, by the time we get a `C`, the
function did indeed take two arguments: both an `A` and a `B`.

What's nice about this encoding is that, unlike in most programming languages,
we are not required to give every argument at once.  In fact, we can
*specialize* a function call by slowly filling in its parameters, one at a time.

Let's take an example. The following models a family pet with a record. The
`type:Pet` has a species, temperament, and a name.

```agda
  module Example-Pets where
    open import Data.String
      using (String)

    data Species : Set where
      bird cat dog reptile : Species

    data Temperament  : Set where
      anxious chill excitable grumpy : Temperament

    record Pet : Set where
      constructor makePet
      field
        species      : Species
        temperament  : Temperament
        name         : String
```

Imagine now we'd like to specialize the `ctor:makePet` constructor, so we can
make a series of grumpy cats in rapid succession. Our first attempt is to write a
helper function `def:makeGrumpyCat`:

```agda
    makeGrumpyCat⅋ : String → Pet
    makeGrumpyCat⅋ name = makePet cat grumpy name
```

This definition absolutely would work, but it doesn't demonstrate the cool part.
Let's consider `ctor:makePet` as a function. It takes three arguments, before
returning a `type:Pet`, and so its type *must be* `expr:Species → Temperament →
String → Pet`.

If we were to insert the implicit parentheses, we'd instead get
`expr:Species → (Temperament → (String → Pet))`. You will note that the
innermost parentheses here are `expr:String → Pet`, which just so happens to be
the type of `def:makeGrumpyCat`. Thus, we can *define* `def:makeGrumpyCat` as
being `ctor:makePet` applied to `ctor:cat` and `ctor:grumpy`, as in:

```agda
    makeGrumpyCat : String → Pet
    makeGrumpyCat = makePet cat grumpy
```

I like to think of this a lot like "canceling" in grade-school algebra. Because,
in our original equation, both sides of the equality ended in `name`, those
arguments on either side cancel one another out, and we're left with this
simpler definition for `def:makeGrumpyCat`.

This ability to partially apply functions isn't a language feature of Agda. It
arises simply from the fact that we write our functions' types as a big series
of arrows, one for each argument.


## The Curry/Uncurry Isomorphism {#sec:currying}

Of course, nothing stops us from encoding our functions in the more standard
form, where we are required to give all arguments at once. The transformation is
merely syntactic. We could write `def:_∨₂_` instead as a function `def:or`:

```agda
  or : Bool × Bool → Bool
  or (false , y)  = y
  or (true  , y)  = true
```

Rather amazingly, when we encode functions this way, we get back the same
function-call notation that other languages use:

```agda
  _ : Bool
  _ = or (true , false)
```

From this result, we can conclude that other languages' functional calling
mechanisms are similar to Agda's. The only difference is that Agda lets you
elide parentheses around a function call which requires only one argument.

It feels "correct" that the difference between Agda and other languages'
functions should be entirely syntactic; after all, presumably at the end of the
day we're all talking about the same functions, regardless of the language used.
But can we make this analogy more formal?

A usual tool in mathematics to show two things are equivalent is the
*isomorphism.* We will study this technique in much more detail in
@sec:isomorphisms, but for now, you can think of an isomorphism as a pair of
functions which transform back and forth between two types. Whenever you have an
isomorphism around, it means the two types you're transforming between are
*equivalent* to one another.

Of course, not just any two functions will do the trick; the two functions must
"undo" one another, in a very particular sense that we will explore in a moment.

So as to convince any potential doubters that our one-at-a-time function
encoding (also known as *curried functions*) is equivalent to the usual "take
all your arguments at once as a big tuple," we can show an isomorphism between
the two. That is, we'd like to be able to transform functions of the shape `type:A ×
B → C` into `type:A → B → C` and vice versa. We'll work through the first half of
this isomorphism together, and leave the other direction as an exercise to try
your hand at writing some Agda for yourself (or talking Agda into writing it for
you!)

In particular, the first function we'd like to write has this types:

```agda
  curry⅋ : {A B C : Set} → (A × B → C) → (A → B → C)
  curry⅋ = ?
```

That's quite the intimidating type; avoid the temptation to panic, and we'll
break it down together. Let's ignore the `{A B C : Set} →` part, which you'll
recall exists only to bring the type variables into scope. Of course, these
variables are necessary for our code to compile, so the next few code blocks
won't actually work. Nevertheless, it will be instructive to study them,
compiling or no.


Hidden

:   ```agda
module Invisible (A B C : Set) where
  open Sandbox-Tuples₂⅋
  open _×_
    ```

We begin with the "simplified" type of `def:curry`:

```illegal
  curry⅋₀ : (A × B → C) → (A → B → C)
```

Because we know that `_→_` has lower precedence than `def:_×_`, we can add some
implicit parentheses:

```illegal
  curry⅋₁ : ((A × B) → C) → (A → B → C)
```

Furthermore, we know that `_→_` is right associative, so a chain of multiple
function arrows nests its parentheses to the right, as in:

```illegal
  curry⅋₂ : ((A × B) → C) → (A → (B → C))
```

Now, we know that a chain of rightward-nested function arrows is the same as a
function taking one argument at a time, so we can drop the outermost pair of
parentheses on the right side of the outermost arrow. This results in:


```illegal
  curry⅋₄ : ((A × B) → C) → A → (B → C)
```

Doing the same trick, we can eliminate another pair of parentheses:

```illegal
  curry⅋₅ : ((A × B) → C) → A → B → C
```

This type is now as simple as we can make it. Although its first parameter is
still rather scary, we can ignore the remaining set of parentheses for a moment,
to see that `def:curry` is a function of three arguments, which eventually
returns a `C`. The second and third arguments are easy enough, they are just `A`
and `B`.

Because the first set of parentheses themselves contain a function arrow, this
means that the first parameter to `def:curry` is a *function.* What function is
it? We're not sure, all we know is that it's a function which takes a tuple of
`expr:A × B`, and produces a `C`.

Thought about in this fashion, it's not too hard to see how to go about
implementing `def:curry`. Because `C` could be any type at all, we can't just
build one for ourselves. Our only means of getting a `C` is to call our function
which produces one, and in order to do that, we must construct a pair of `expr:A
× B`. Since we have both an `A` and a `B` as arguments, this is not an onerous
requirement. Thus, all we need to do is to call the given function after tupling
our arguments:

Hidden

:     ```agda
  curry⅋₅ = ?
  curry⅋₄ = ?
  curry⅋₂ = ?
  curry⅋₁ = ?
  curry⅋₀ = ?
      ```

:     ```agda
module Sandbox-Tuples₂ where
  open Booleans
  open Sandbox-Tuples₂⅋ public
  open _×_
      ```


```agda
  curry : {A B C : Set} → (A × B → C) → (A → B → C)
  curry f a b = f (a , b)
```

For all its complicated type signature, `def:curry` turns out to be a remarkably
simple function. And this makes a great deal of sense when you recall *why* we
wanted to write `def:curry` in the first place. Remember that we would like to
show the equivalence of function calls that receive their arguments all at once,
vs those which receive them one at a time. But at the end of the day, it's the
same function!

Now for an exercise to the reader. Our function `def:curry` forms one side of
the isomorphism between the two ways of calling functions. Your task is to
implement the other half of this isomorphism, using all of the tools you've now
learned. The type you're looking for is:

```agda
  uncurry⅋ : {A B C : Set} → (A → B → C) → (A × B → C)
  uncurry⅋ = ?

```


Exercise

:   Implement `def:uncurry`. Remember that [`TypeContext`](AgdaCmd) is an
    invaluable tool if you don't know how to make progress.


Solution

:    ```agda
  uncurry : {A B C : Set} → (A → B → C) → (A × B → C)
  uncurry f (a , b) = f a b
     ```


Because we were able to implement `def:curry` and `def:uncurry`, we have shown
that curried functions (used in Agda) are equivalent in power to uncurried
functions (used in most programming languages.) But the oddity of our choice
leads to our ability to "cancel" arguments that are duplicated on either side of
a function definition, and this happens to be extremely useful for "massaging"
functions. Often, we have a very general function that we will need to
specialize to solve a particular task, and we can do exactly that by partially
filling in its arguments.


## Implicit Arguments {#sec:implicits}

There is one final concept we must tackle before finishing this chapter. It's
been a long slog, but there is light at the end of the tunnel. As our last
push, we will investigate what exactly those curly braces mean in type
signatures.

As a motivating example, let's play around with our new `def:uncurry` function.
In particular, let's try applying it to `def:_∨_`. What type must this thing
have? If we don't want to do the thought-work ourselves, we can just leave a
hole in the type signature:

```agda
  _ : ?
  _ = uncurry _∨_
```

If Agda has enough information to work out the hole for itself, we can command
it to do so via [`Solve`](AgdaCmd). The result is:

```agda
  _ : Bool × Bool → Bool
  _ = uncurry _∨_
```

The [`Solve`](AgdaCmd) command asks Agda to infer the contents of a hole based
on information it already knows from somewhere else. In this case, Agda knows
the type of `def:_∨_` (that is, `expr:Bool → Bool → Bool`,) and so it can infer
the type of `expr:uncurry _∨_` as `expr:Bool × Bool → Bool`. Since this is the
entire expression, the type of our definition is fully known to Agda, and it
will happily solve it for us.

As you can see, Agda is quite the clever! The constraint solving exhibited here
is a generally useful tool when coding. For example, you can state a proof as
being trivial, and then work backwards---asking Agda to synthesize the solution
for you! It sounds absolutely bonkers, but somehow this actually works.

Let's explore this concept further. But first, we will make a new module. The
booleans we implemented by hand in the previous section exist in the standard
library, under the module `module:Data.Bool`. Better yet, they are defined
identically to how we've built them, so there will be no surprises when bringing
them in. `module:Data.Bool` is quite a big module, so we will take only the
pieces we need via the `keyword:using` modifier:

```agda
module Sandbox-Implicits where
  open import Data.Bool
    using (Bool; false; true; not; _∨_)
```

Additionally, tuples are also defined in the standard library, under
`module:Data.Product`.

```agda
  open import Data.Product
    using (_×_; proj₁; proj₂)
```

`module:Data.Product` also supplies `ctor:_,_`, `def:curry` and `def:uncurry`,
but they are implemented in more generality than we've presented. Rather than
get bogged down in the details, we can instead just import the specialized
versions which *do* correspond to our implementations. By using the
`keyword:renaming` modifier on this same `keyword:import` of
`module:Data.Product`, we can ask Agda to shuffle some identifiers around for
us:

```agda
    renaming ( _,′_      to _,_
             ; curry′    to curry
             ; uncurry′  to uncurry
             )
```

Note that these tick marks at the end of `def:curry` and `def:uncurry` are
*primes*, not apostrophes. Primes can be input via [`'`](AgdaMode).

When you import `module:Data.Product` for yourself in the future, you won't need
this `keyword:renaming`. It's necessary here only to simplify some details that
we don't usually care about (or even notice.)

Our sandbox is now be equivalent to our last environment, where we defined
everything by hand. In Agda like any other programming language, it's desirable
to use existing machinery rather than build your own copy, although admittedly
building it for yourself leads to better understanding.

Let's now look again at the types of `def:_,_`, `def:curry`, and `def:curry`, in
their full curly-braced glory:


```agda
  _,_⅋      : {A B : Set} → A → B → A × B
  curry⅋    : {A B C : Set} → (A × B → C) → (A → B → C)
  uncurry⅋  : {A B C : Set} → (A → B → C) → (A × B → C)
```

Each of these types is preceded by curly braces containing a list of types,
which are brought into scope for the remainder of the type signature. But what
exactly is going on here?

The first thing to realize is that the notation `{A B : Set}` is syntactic sugar
for `{A : Set} → {B : Set}`, and so on for more variables. We can therefore
rewrite the type of `def:_,_` more explicitly:

```agda
  _,_⅋⅋ : {A : Set} → {B : Set} → A → B → A × B
```

Hidden

:   ```agda
  _,_⅋      = ?
  curry⅋    = ?
  uncurry⅋  = ?
  _,_⅋⅋     = ?
    ```

In this form, it looks a lot like `A : Set` and `B : Set` are *arguments* to
`def:_,_`. Rather amazingly, *they are!* The curly braces around them make these
*invisible,* or *implicit,* arguments. Something interesting happens if we
replace them with regular parentheses instead of braces. Let's make a new
function called `def:mk-tuple` using regular, visible arguments:

```agda
  mk-tuple⅋ : (A : Set) → (B : Set) → A → B → A × B
  mk-tuple⅋ = ?
```

We will do the usual ceremony to bind our arguments via [`MakeCase:`](AgdaCmd):

```agda
  mk-tuple⅋⅋ : (A : Set) → (B : Set) → A → B → A × B
  mk-tuple⅋⅋ A B x x₁ = {! !}
```

And then run [`Auto`](AgdaCmd) to implement the function for us.

```agda
  mk-tuple : (A : Set) → (B : Set) → A → B → A × B
  mk-tuple A B x x₁ = x , x₁
```

Here you can see that the implementation of `def:mk-tuple` *completely ignores*
its `A` and `B` arguments. That's peculiar, isn't it?

We can try using `def:mk-tuple` to build ourselves a tuple. Starting from a
delimited hole:

```agda
  _ : Bool × Bool
  _ = {! !}
```

we can type `def:mk-tuple` *inside the hole:*

```agda
  _ : Bool × Bool
  _ = {! mk-tuple !}
```

and then invoke [`Refine`](AgdaCmd), asking Agda to use the given function to try
to fill the hole:

```agda
  _ : Bool × Bool
  _ = mk-tuple {! !} {! !} {! !} {! !}
```

This expression now has four holes for the four arguments to `def:mk-tuple`. The
first two are the previously-implicit type parameters of the tuple, while the
last two are the actual values we'd like to fill our tuple with. Thankfully,
Agda can [`Solve`](AgdaCmd) the first two holes for us:

```agda
  _ : Bool × Bool
  _ = mk-tuple Bool Bool {! !} {! !}
```

and we are free to fill in the latter two to our heart's content.

What's more interesting is if we fill in one of these types incorrectly; that is
to say, with a type that isn't `type:Bool`. This is not an onerous task, as it's
very easy to spin up new types at will:

```agda
  data PrimaryColor : Set where
    red green blue : PrimaryColor
```


Hidden

:   ```agda
  -- fix indentation
    ```


We can now see what happens when we fill in one of those `type:Bool`s with
`type:PrimaryColor` instead:


```illegal
  bad-tuple : Bool × Bool
  bad-tuple = mk-tuple PrimaryColor Bool {! !} {! !}
```

The response from Agda is immediate and serious:

```info
PrimaryColor != Bool of type Set
when checking that the expression mk-tuple PrimaryColor Bool ? ?
has type Bool × Bool
```

Agda is telling us off for writing `type:PrimaryColor` when we should have
written `type:Bool`. Amazingly, Agda *knows* that this type must be `type:Bool`,
and all its doing is checking if we wrote down the correct thing. Which we
didn't.

How does Agda know this? Because we wrote the type of `def:bad-tuple` as
`expr:Bool × Bool`. You will notice this situation is all a bit stupid. If Agda
knows what exactly what we should write into this hole, and yells at us if we
don't do it properly, why do we have to do it at all?

As it happens, we don't.

Instead, in any expression, we can leave behind an underscore, asking Agda to
make an informed decision and fill it in for us. Thus, we can write the
following:

```agda
  color-bool-tuple : PrimaryColor × Bool
  color-bool-tuple = mk-tuple _ _ red false
```

and Agda will (silently, without changing our file) fill in the two underscores
as `type:PrimaryColor` and `type:Bool`, respectively. Filling in arguments in
this way is known as *elaboration,* as it offloads the work of figuring out
exactly what your program should be to the compiler. No human input necessary.

It is exactly this elaboration that is happening behind the scenes of our
invisible parameters. Whenever you mark a parameter invisible by ensconcing it
in curly braces, you're really just asking Agda to elaborate that argument for
you by means of inserting an underscore.

We can make the invisible visible again by explicitly filling in implicit
arguments for ourselves. The syntax for this is to give our implicit arguments
as regular arguments, themselves in curly braces. We can also use the explicit
names to these implicits, so that we need to fill them all in order to fill only
one:

```agda
  mk-color-bool-tuple
      : PrimaryColor
      → Bool
      → PrimaryColor × Bool
  mk-color-bool-tuple = _,_ {A = PrimaryColor} {B = Bool}
```

Of course, implicit elaboration is not magic. It cannot write your entire
program for you; it can only elucidate specific details that are already true,
but which you would prefer not to write out. To illustrate, Agda can't solve the
following, because it doesn't know whether you want to use `ctor:false` or
`ctor:true`---there is no unambiguous answer!

```agda
  ambiguous : Bool
  ambiguous = _
```

You'll notice the syntax highlighting for this implicit has gone yellow; that's
Agda informing us that it doesn't have enough information to elaborate. In
addition, you'll also see a warning message like this in the info window:

```info
Invisible Goals:
_236 : Agda.Builtin.Bool.Bool [at 1518,15-16]
```

Agda refers to problems like these as *unsolved metas.*

Whenever you see this yellow background, something has gone wrong, and it's
worth fixing before powering on. Ambiguities have a habit of propagating
themselves forwards, and so what is one unsolved meta now might turn into ten a
few functions down the line.


## Wrapping Up

You have managed to survive an *extremely* whirlwind tour of Agda. While you
likely are not yet the world's best Agda programmer, you now know much more than
the vast majority of programmers. The attentive reader has been exposed to the
majority of this gentle language's most "astronautic" features.

What we have seen here are Agda's fundamental building blocks. While they are
interesting in their own right, the fun parts come when we start putting them
together into funky shapes. Throughout our progression we will learn
that there was more to learn about these simple pieces all along. Indeed,
perhaps these primitive elements are much more sophisticated than they look.

As a convention in this book, we will end by making one final module. This
module exists only to be imported from future chapters. Since we built a lot of
things by hand, made several examples, and generally went down the garden path,
we will use this module as the definitive export list. This module is the final
artifact of our exploration in this chapter.

For the best portability, we will not use our own definitions, but rather those
from the standard library.

```agda
module Exports where
  open import Data.Bool
    using (Bool; false; true; not; _∨_)
    public

  open import Data.Product public
    using (_×_; _,_; curry; uncurry; proj₁; proj₂)
    public
```

Note the `keyword:public` modifier on both of these `keyword:import`s. By
default, Agda won't export anything you imported, but the `keyword:public`
keyword changes this behavior, allowing us to re-export definitions that we
didn't write for ourselves.

We have not even begun to scratch the surface of what interesting things are
possible in Agda, but we now have enough background that we can earnestly get
into the meat of this book. Prepare yourself.

