# A Gentle Introduction to Agda

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
    ```


When code is presented in this book, it will be shown with a thick left rule, as
below:

```agda
module 1-agda where
```

This one-line example is not merely an illustration to the reader. By virtue of
being a literate document, every chapter in this book must be a valid Agda file,
and every Agda file begins with a *module declaration* like above. This
declaration is mandatory prefacing every chapter, and we're not allowed to write
any code until we've done the `keyword:module` ritual.


The module is Agda's simplest unit of compilation.

> TODO(sandy): change me when publishing

Every Agda source file must begin with a module declaration which matches the
name of the file. Since this module is called `module:1-agda`, if you'd like to
follow along at home, you must save your file as `1-agda.agda`. Failure to do so
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

This introduces a new module `module:example` inside of `module:1-agda`. You
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

- `module:1-agda.foo`
- `module:1-agda.foo.bar`
- `module:1-agda.foo.bar.qux`
- `module:1-agda.foo.bar.zaz`
- `module:1-agda.foo.ram`

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
fear that it will leak into `module:1-agda` where we will do the majority of our
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


## Types and Values

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

To do this, we can use a `data` declaration:

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
Agda is also telling us that we now have a variable `bind:x` in scope, whose type
is `type:Bool`. In order to pull the `Bool →` off of the type signature, we were
forced to introduce a binding `bind:x` of type `type:Bool`, which corresponds
exactly to `def:not`'s function argument.

There is an important lesson to be learned here, more than just about how Agda's
type system works. And that's that you can invoke [`TypeContext`](AgdaCmd) at
any time, on any hole, in order to get a better sense of the big picture. In
doing so, you can "drill down" into a hole, and see everything you have in
scope, as well as what type of thing you need to build in order to fill the
hole.

We can ask Agda for more help to continue. This time, if we put our cursor in
the hole and invoke [`MakeCase:x`](AgdaCmd), Agda will enumerate every possible
constructor for `bind:x`, asking us to fill in the result of the function for
each case. Here, that looks like:

```agda
  not⅋⅋ : Bool → Bool
  not⅋⅋ false  = {! !}
  not⅋⅋ true   = {! !}
```

You'll notice where once there was one hole there are now two, one for every
possible value that `bind:x` could have been. Since `bind:x` is a `type:Bool`,
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

Agda is divided into several distinct pieces of linguistic structure. First and
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

Note that the arguments here are separated here only by whitespace. If
disambiguation is necessary (which it is, whenever we have nested function
calls,) we surround the entire expression in parentheses:

```example
baz 0 (f false) (foo bar 5 true)
```

This would be written in the ALGOL style as

```cpp
baz(0, f(false), foo(bar, 5, true))
```

While it might feel like an unnecessarily annoying break in conventional syntax,
there are mightily-good theoretical reasons for it, addressed soon. Given this
new lens on the syntax of function calls, it's informative to look back at our
definition of `def:not`; recall:

```agda
  not⅋⅋⅋⅋ : Bool → Bool
  not⅋⅋⅋⅋ false  = true
  not⅋⅋⅋⅋ true   = false
```

we can now mentally parse these definitions differently, that is, reading them
literally. The first of which, says "the function `def:not` called with argument
`ctor:false` is equal to `ctor:true`". Thus, this equals sign is really and
truly an *equals* sign. It is *not* the "assignment" operator found in all
stateful descendants of ALGOL, nor is it some sort of test-for-equality that
usually gets called `==`. No, we are saying the thing on the left side is
exactly the same thing as on the right!

This equality is very deep. While Agda will simplify the left side to the right
whenever possible, the two sides are exactly equivalent in all non-pattern
(TODO: what does this mean?) contexts. Indeed, many proofs depend on finding two
complicated expressions that are exactly equal in this way, and much of the work
is in showing that equivalence.


## Operators

Another simple operation over booleans is logical OR; that is, the result is
true if at least one of its arguments is true. Mathematicians often use the
symbol $\vee$ (pronounced "vel") for this operation, which we will follow. Note
that this is not the Latin letter `v`, but the Unicode character
[`or`](AgdaMode).

This odd choice for a function name is justified by our goal to reimplement the
Agda standard library, with the same names. The standard library calls this
`def:_∨_`, and so we will too. The underscores are also meaningful, as we will
see momentarily.

```agda
  _∨⅋⅋_ : Bool → Bool → Bool
  _∨⅋⅋_ = ?
```

We will again interactively ask for Agda's help here. Place your cursor in the
hole and run [`MakeCase`](AgdaCmd). Agda will respond:

```agda
  _∨⅋⅋⅋_ : Bool → Bool → Bool
  x ∨⅋⅋⅋ x₁ = {! !}
```

You will notice that `def:_∨_` has been replaced with `x ∨ x₁`. The underscores
are not literal underscores, but instead mark placeholders for the operator's
syntax. If we fill the resulting hole with the names of both arguments `x` and
`x₁`, we can again ask Agda to [`MakeCase`](AgdaCmd):

```agda
  _∨⅋⅋⅋⅋_ : Bool → Bool → Bool
  x ∨⅋⅋⅋⅋ x₁ = {! x x₁ !}
```

This time Agda will use the variables named in the hole as input on what to
split. The result is a very satisfying four lines of code that we didn't need to
write for ourselves:

```agda
  _∨⅋⅋⅋⅋⅋_ : Bool → Bool → Bool
  false  ∨⅋⅋⅋⅋⅋ false  = {! !}
  false  ∨⅋⅋⅋⅋⅋ true   = {! !}
  true   ∨⅋⅋⅋⅋⅋ false  = {! !}
  true   ∨⅋⅋⅋⅋⅋ true   = {! !}
```

We can finish the definition of `def:_∨_` by giving filling in the desired answers
in each hole:

```agda
  _∨⅋_ : Bool → Bool → Bool
  false  ∨⅋ false  = false
  false  ∨⅋ true   = true
  true   ∨⅋ false  = true
  true   ∨⅋ true   = true
```

Here we have taken the same approach as in `def:not`: for each argument, we
enumerate every possibilities, giving the answer on the right side of the equals
sign. You will notice that this strategy grows enormously; a function of five
booleans would require 32 clauses to enumerate every possibility. Fortunately,
this is not the only way to define `def:_∨_`. We can instead throw some thought
at the problem, and realize the goal is to identify whether or not one of the
arguments is `ctor:true`. This doesn't require pattern matching on *both*
parameters---some clever insight indicates we can get away with matching only on
one.

If the argument we matched on is `ctor:true`, we're done, without needing to
look at the other argument. If our matched argument is `ctor:false`, then the
result is `ctor:true` only when the second argument is `ctor:true`. In neither
case do we need to inspect both of the arguments! We can take advantage of this
fact by using a variable to abstract over the second parameter. Instead, let us
define `def:_∨_` in this way:

```agda
  _∨_ : Bool → Bool → Bool
  false  ∨ other = other
  true   ∨ other = true
```

Because we wrote `other`---rather than any of the constructors of `type:Bool`--- Agda
knows we don't want to perform a pattern match. Instead, this introduces a new
variable `other : Bool`. In the `ctor:false` case, we simply return this argument,
and in the `ctor:true` case we ignore it completely because we've already found the
`ctor:true` we're looking for.

Note that we call `other` a variable, but **it is a variable in the mathematical
sense rather than in the usual programming sense.** This variable is a way of
talking about something whose value we don't know, like the $x$ in the
expression $f(x) = 2x$ (but not like the $x$ in $x^2 = 9$.) Here, $x$ exists,
but its value is set once and for all by the user of $f$. When we are talking
about $f(5)$, $x = 5$, and it is never the case that $x$ changes to 7 while
still in the context of $f(5)$. In any given context, $f$ is always *bound* to a
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

At its root, [2](Ann) is a better program *because* it needs to inspect less
data in order to make a decision. `def:_∨₂_` is able to make meaningful progress
towards an answer, even when the second argument isn't yet known, while `def:_v₁_`
is required to wait for both arguments. We can observe this in action with the
[`Normalise`](AgdaCmd) command, which asks Agda to evaluate an expression for us.

We can fill in only one argument to an operator by removing only one of the
underscores. Thus, we can see what happens when we invoke `def:_v₂_` with only its
first argument. This is known as a *segment.* Try invoking [`Normalise:true
v₂_`](AgdaCmd), to which Agda will respond:

```info
λ other → true
```

This response is Agda's syntax for an anonymous function (also known as a
*lambda*.) It takes an argument, called `other`, completely ignores it, and
immediately returns `ctor:true`. Writing lambdas like this is valid Agda syntax,
but we will not use it except for extremely small functions.

Nevertheless, let's compare this output to the result of [`Normalise:true
∨₁_`](AgdaCmd):

```info
true ∨₁_
```

Here, Agda simply returns what we gave it, because it is unable to make any
progress towards evaluating this value. Terms like this are called *stuck*, and
can make no progress in evaluation until something unsticks them. In this case,
because we don't know the value of the second argument, it is stuck, and thus
the pattern match on it in `def:_∨₁_` is *also* stuck. When the second argument is
provided, the pattern match will unstick, and so too will the final result.

We can see this behavior more clearly by postulating a boolean value. Postulated
values are always stuck, and thus `def:always-stuck` is an apt name for one:

```agda
  postulate
    always-stuck : Bool
```

Our new `stuck` is always stuck. For example, we can learn nothing more about it
with [`Normalise:always-stuck`](AgdaCmd):

```info
always-stuck
```

Nor can we reduce [`Normalise:not always-stuck`](AgdaCmd) to a value:

```info
not always-stuck
```

Don't believe the response, this *is* indeed always stuck (although it is not
the same as the `def:always-stuck` variable.) Rather, the entire call to `def:not`
with argument `def:always-stuck` is stuck. And, as you might expect, [`Normalise:true ∨₁
stuck`](AgdaCmd) is also stuck:

```info
true ∨₁ always-stuck
```

Fascinatingly however, [`Normalise:true ∨₂ stuck`](AgdaCmd) computes just fine:

```info
true
```

This progress of computation even when the second argument is stuck
(`def:always-stuck`, or otherwise) is the reason by which we prefer `def:_∨₂_`
over `def:_∨₁_`.

While this example might seem somewhat contrived, you would be amazed at how
often it comes up in practice. Avoiding a pattern match in an implementation
means you can avoid a pattern match in every subsequent proof *about* the
implementation, and can be the difference between a three line proof and an 81
line proof. We will return to this point when we discuss proof techniques, but
for now, try not to get into the habit of bashing your way through every
implementation if you can at all help it.


## Records and Tuples

In this section, we will play around with record types, as a lead up to
discussing functions in more detail. These two seemingly disparate ideas have a
surprising amount of interplay between them. We would like to motivate an answer
to the question of "what's up with the funny arrow `→` in function types?" Why
does `def:_∨_` have type `type:Bool → Bool → Bool`, instead of a more "standard"
type like it would in most everyday programming languages. For example, you
might argue that we should write `def:_∨_`'s type as `type:(Bool, Bool) → Bool`,
so that it's very clear which are the parameters and which is the return.

Types like `type:(Bool, Bool)` are known as *tuple* types, which we can encode
to a in Agda as record types. Record types are types with a number of subfields.
A special case of records are tuples, which we can think of as anonymous records
with only two fields. As a first approximation, we can write the tuple type like
this:

```agda
module Sandbox-Tuples where
  open Booleans

  record _×⅋_ (A : Set) (B : Set) : Set where  -- ! 1
    field -- ! 2
      proj₁  : A
      proj₂  : B
```

There is quite a lot going on here, which we will tackle one step at a time. At
[1](Ann) we parameterize the entire type `type:_×_` by two other types, call
them `A` and `B`. This is because we'd like to be able to form tuples of any two
types, whether they be integers and booleans, tuples of tuples, or more exotic
things still. Note that this name `type:_×_` is not the Latin letter `x`, but is
instead the *times symbol,* input via [`x`](AgdaMode).

At [2](Ann) we say "inside of the `type:_×_` type, there are two fields." These
two fields are named `field:proj₁` and `field:proj₂`, and have types `A` and
`B`, respectively. This is what you would expect; if we have a record
corresponding to a tuple of two things, *it should have two things in it.*

We can try out our new tuple type, as usual by plunking a hole down on the right
hand side of the equals sign:

```agda
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
beautiful---tuple type! We'd now like to extract the two fields from `my-tuple`.
How can we do that? Agda provides two means of *projecting* fields from records;
the first is with the *record access* syntax, where the field name is prepended
with a dot and given *after* the tuple:

```agda
  my-tuple-first : Bool
  my-tuple-first = my-tuple ._×⅋_.proj₁
```

The other form is we can omit the dot, and put the field name *before* the tuple:

```agda
  my-tuple-second : Bool
  my-tuple-second = _×⅋_.proj₂ my-tuple
```

The attentive reader will notice that this syntax looks a lot like a function
call---which, in a very real sense, it is! These two syntactic forms are
completely equivalent to Agda, and it's a matter of personal preference as to
which you pick. Personally, I prefer using the prefix form, because it means I
can forget the fact that I'm working with *records* and think only about
*functions.*

In reading the above, it cannot have escaped your attention that these two call
sites are *ugly.* What is this `_×_.proj₁` nonsense? Do we really need to use a
fully-qualified name every time we want to access a field? Fortunately, we do
not. Believe it or not, every `record` creates a new `module` with the same
name. Thus, we can bring `field:proj₁` and `field:proj₂` into the top-level scope by opening
our new module, allowing us to rewrite the previous two definitions as such:


```agda
  open _×⅋_

  my-tuple-first⅋ : Bool
  my-tuple-first⅋ = my-tuple .proj₁

  my-tuple-second⅋ : Bool
  my-tuple-second⅋ = proj₂ my-tuple
```

Much nicer, isn't it? All that's left is to clean up the syntax for
*constructing* tuples in the first place. It would be really nice to be able to
avoid the `record { proj₁ = ... }` boilerplate every time we wanted to make a
tuple. Instead, we can write a helper function that will clean up the syntax for
us.

```agda
  _,⅋_  : {A B : Set} → A → B → A ×⅋ B  -- ! 1
  _,⅋_  = ?
```

The type of `def:_,_` should really be `A → B → A × B`, however, recall that `A` and
`B` are variables standing in for *whatever type the user wants.* But those
variables are not in scope, so we must bind them ourselves. This is the meaning
of the `type:{A B : Set} →` prefix of the type at [1](Ann)---it's responsible for
bringing `A` and `B` both into scope and letting Agda know they are both types
(that is, they are both of type `type:Set`.) We will discuss Agda's scoping mechanism
in more detail in @sec:implicits.

Implementing `def:_,_` isn't hard to do by hand; but we can be lazy and ask Agda to
do it for us. Begin as usual by getting Agda to bind our arguments, via
[`MakeCase`](AgdaCmd) in the hole:

```agda
  _,⅋⅋_  : {A B : Set} → A → B → A ×⅋ B
  x ,⅋⅋ x₁ = {! !}
```

and follow up by invoking [`Auto`](AgdaCmd), which asks Agda to just write the
function for you. Of course, this doesn't always work, but it's surprisingly
good for little functions like this. The result is exactly what we'd expect it
to be:

```agda
  _,⅋⅋⅋_  : {A B : Set} → A → B → A ×⅋ B
  x ,⅋⅋⅋ x₁ = record { proj₁ = x ; proj₂ = x₁ }
```

Move the definition of `def:_,_` above the definition of `def:my-tuple`, which we can
now reimplement:

```agda
  my-tuple⅋⅋⅋ : Bool ×⅋ Bool
  my-tuple⅋⅋⅋ = (true ∨ true) ,⅋⅋⅋ not true
```

The parentheses here are necessary because Agda doesn't know if it should parse
the expression `true ∨ true , not true` as `true ∨ (true , not true)` or as the
intended expression above. Of course, we know that the other parse doesn't even
typecheck and thus it must be the unintended one, but you can imagine a much
larger expression could take an exponential amount of time in order to find a
unique way of adding parentheses to make the types work out properly. This is
not a hard limitation, but we will not fix it here, since the stack of concepts
currently on the reader's brain is likely reaching its breaking point. We will
solve this problem of helping Agda parse bigger expressions in a moment.

Our exploration of this topic has gotten somewhat out of hand, requiring us to
go back and amend definitions. To avoid the mental anguish of keeping ourselves
all on the same page, let's just start a new sandbox module:

```agda
module Sandbox-Tuples₂ where
  open Booleans
```

We will again define our tuple type; this time however, we will make one small
addition:

```agda
  record _×_ (A : Set) (B : Set) : Set where
    constructor _,_  -- ! 1
    field
      proj₁ : A
      proj₂ : B

  open _×_
```

The keyword `keyword:constructor` at [1](Ann) tells Agda we'd like to avoid the whole
`keyword:record { ... }` nonsense we had to deal with last on the go-around, instead
asking it to just automate writing the `def:_,_` function for us. Sorry to have
led you down the garden path, but it's nice to see for ourselves what tedium
each language feature can assuage.

We can return to the problem of getting Agda to correctly parse `true ∨ true ,
false` with the implied parentheses on the left. Infix operators like `def:_∨_` and
`ctor:_,_` are parsed, in every language, according to rules of *precedence* and
*associativity.*

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

We can tell Agda's parser about our preferences, that `ctor:_,_` be right-associative
with precedence 4 with the following declaration:

```agda
  infixr 4 _,_
```

Here, the `r` at the end of `infixr` tells Agda about our associativity
preference. Of course, you could use `infixl` instead if you wanted
left-associativity (although you don't in this case.) Of course, if you ever
*do* want an explicit left-nested tuple, you are free to insert the parentheses
on the left yourself!

While `ctor:_,_` is the operator for building *values* of tuple types, `type:_×_` is the
operator for building the tuple type itself. The values and their types should
be in one-to-one correspondence. That is to say, if we have `a : A`, `b : B` and
`c : C`, we'd like it to be the case that `a , b , c` have type `type:A × B × C`. And
thus, we must also choose right-associativity for `type:_×_`. For mysterious reasons,
however, `type:_×_` is traditionally given a preference of 2:

```agda
  infixr 2 _×_
```

We will end our discussion of record types here, as this is enough to get you
started.


## Function Types

It is now time to tackle the question of what's up with the funny syntax for
functions with multiple arguments. Most programming languages assign a type of
the form `type:(A × B) → C` to functions with two arguments, while in Agda we instead
write `type:A → B → C`. The reason for this is, in short, that they are equivalent,
but that the latter is more useful.

In order to see this equivalence directly, we can stop for a moment to think
about the issue of parsing again. Although the function arrow is intrinsically
magical and built-in to Agda, we can ask ourselves how it ought to work.
Spiritually, `type:_→_` is a binary operator, which means we can ask about its
precedence and associativity. In Agda, the typing judgment `_:_` binds with the
lowest precedence of all, while `type:_→_` comes in just after as the second-lowest
precedence in the language. What this means is that in practice, `type:_→_` always
acts as a separator between types, and we don't need to worry ourselves about
where the parentheses should go.

The associativity for `type:_→_`, on the other hand, is to the right. That means,
given the type `type:A → B → C`, we must read it as `type:A → (B → C)`. A literal
interpretation of such a thing is a function that takes an `A` argument and
*returns a function.* That returned function itself takes a `B` argument and
returns a `C`. At the end of the day, we did take two arguments, an `A` and a
`B`, in order to produce a `C`.

What's nice about this encoding is that, unlike in most programming languages,
we don't to give every argument at once. In fact, we can *specialize* a function
call by slowly fixing its parameters as in this example:

```agda
  module Example where
    data AnimalVariety : Set where  -- ! 1
      dog      : AnimalVariety
      cat      : AnimalVariety
      bird     : AnimalVariety
      reptile  : AnimalVariety

    postulate
      Name  : Set  -- ! 2
      Age   : Set
      SpecificAnimal : Set

      makeAnimal
        : AnimalVariety → Age → Name → SpecificAnimal  -- ! 3

    makeBird : Age → Name → SpecificAnimal  -- ! 4
    makeBird age name = makeAnimal bird age name
```

Here, we've made a new `keyword:data` type at [1](Ann), enumerating possible sorts of
animals one might have. At [2](Ann) we postulate the existence of some other
types with suggestive names, in order to give our postulated function
`def:makeAnimal` a suggestive type at [3](Ann). Finally, at [4](Ann) we specialize
the `def:makeAnimal` function into `def:makeBird`, where we always decide the animal
variety should be a `bird`.

This doesn't yet exhibit the desirability of one-at-a-time functions we'd like
to showcase. But we will note that `def:makeBird` is a function whose definition
binds two arguments (`age` and `name`), and simply passes them off to
`def:makeAnimal`. If you were to drop a hole on the right side of this equation,
you'd see that the type of the hole is `type:SpecificAnimal`. By the law of
equality, this means the left-hand side must also have type
`type:SpecificAnimal`. If we were to drop the `name` binding on the left side,
the hole now has type `type:Name → SpecificAnimal`. Dropping now the `age`
parameter too, we see the resulting hole now has type `type:Age → Name →
SpecificAnimal`, exactly what we expect from the type definition.

Are you ready for the cool part? If we insert the implicit parentheses into the
type of `def:makeAnimal`, we get `type:AnimalVariety → (Age → (Name → SpecificAnimal))`;
a creative reading of which will suggest to us that we can fill the hole with
less ceremony:

```agda
    makeBird⅋ : Age → Name → SpecificAnimal
    makeBird⅋ = makeAnimal bird
```

I like to think of this a lot like "canceling" in grade-school algebra. Because,
in our original equation, both sides of the equality ended in `age name`, those
arguments on either side cancel one another out, and we're left with a simpler
equation.


## The Curry/Uncurry Isomorphism

A usual tool in mathematics to show two things are equivalent is the
*isomorphism.* We will study this technique in much more detail in
@sec:isomorphisms, but for now, you can think of an isomorphism as a pair of
functions which transform back and forth between two types. Whenever you have an
isomorphism around, it means the two types you're transforming between are
*equivalent* to one another.

So as to convince any potential doubters that our one-at-a-time function
encoding (also known as *curried functions*) are equivalent to the usual "take
all your arguments at once as a big tuple," we can show an isomorphism between
the two. That is, we'd like to be able to transform functions of the shape `type:A ×
B → C` into `type:A → B → C` and vice versa. We'll work through the first half of
this isomorphism together, and leave the other direction as an exercise to try
your hand at writing some Agda for yourself (or talking Agda into writing it for
you!)

-- TODO(sandy): actually, do this example as an exercise, and show uncurry in
-- full

In particular, the first function we'd like to write has this types:

```agda
  curry : {A B C : Set} → (A × B → C) → (A → B → C)
```

If this is your first time looking at function arrows, avoid the temptation to
panic. The first step is always to parse out exactly what's going on. Let's look
at `def:curry`. Let's ignore the `{A B C : Set} →` part, which you'll recall exists
only to bring the type variables into scope:

```type
  curry : (A × B → C) → (A → B → C)
```

After inserting the parentheses arising from the interaction of
`_→_` as the lowest precedence operator, we obtain some parentheses around the
tuple:

```type
  curry : ((A × B) → C) → (A → B → C)
```

We can then insert the parentheses from the function arrow's right-associativity
to the innermost parentheses:

```type
  curry : ((A × B) → C) → (A → (B → C))
```

Written like this, we see that `def:curry` is a function which itself takes a
*function* as an *argument,* and also produces a function as its *return type.*
Alternatively, we can drop the last two pairs of parentheses, and think about
`def:curry` like this:

```type
  curry : ((A × B) → C) → A → B → C
```

That is, `def:curry` is a function that takes *three* inputs, one is a function, and
the other two are an `A` and a `B` respectively, at the end of the day returning
a `C`. Written in this form, it's a little easier to see how you would go about
implementing such a thing, while the previous form gives a better sense of what
exactly you're trying to accomplish.


Exercise

:   Implement the `def:curry` function for yourself. If you get stuck, don't forget
    you can always ask Agda for help by using [`TypeContext`](AgdaCmd) to inspect
    what you have lying around in scope, [`MakeCase`](AgdaCmd) to bind arguments
    and [`Refine`](AgdaCmd) to construct values for you.


Solution

:   ```agda
  curry f a b = f (a , b)
    ```


Going the other direction and implementing `def:uncurry` is slightly harder, since
it requires you to remember how to project fields out of record types. The type
you want is:

```agda
  uncurry : {A B C : Set} → (A → B → C) → (A × B → C)
```

Exercise

:   Implement `def:uncurry`. Remember that you can use `field:proj₁` and `field:proj₂` to get
    the fields out of a tuple.


Solution

:    ```agda
  uncurry f ab = f (proj₁ ab) (proj₂ ab)
     ```


It's slightly annoying needing to project both fields out of `ab` in the
implementation of `def:uncurry`. This leads us to one last trick. Start again,
having just bound your arguments:

```agda
  uncurry⅋ : {A B C : Set} → (A → B → C) → (A × B → C)
  uncurry⅋ f ab = {! !}
```

From here, we can ask Agda to pattern match on `ab` directly by invoking
[`MakeCase:ab`](AgdaCmd), which results in:

```agda
  uncurry⅋⅋ : {A B C : Set} → (A → B → C) → (A × B → C)
  uncurry⅋⅋ f (proj₃ , proj₄) = {! !}
```

Agda has replaced `ab` with the `ctor:_,_` constructor that is used to build the
tuple type `type:_×_`, and then bound the two projections that result from tearing
apart `ctor:_,_`. It's debatable whether or not the names it chose (`field:proj₁` and
`field:proj₂`) are good or bad---on one hand, those are the names we said the fields
have, on the other, they shadow the projections that are already in scope and
have different types. I prefer to rename them:

```agda
  uncurry⅋⅋⅋ : {A B C : Set} → (A → B → C) → (A × B → C)
  uncurry⅋⅋⅋ f (a , b) = {! !}
```

and from here, Agda will happily write the remainder of the function via
[`Auto`](AgdaCmd).

Because we were able to implement `def:curry` and `def:uncurry`, we have shown that
curried functions (used in Agda) are equivalent in power to uncurried functions
(used in most programming languages.) But the oddity of our choice leads to our
ability to "cancel" arguments that are duplicated on either side of a function
definition, and this happens to be extremely useful for massaging general
functions into the right shape so that they can be used in place of
more-specific functions.


## Implicit Arguments

Let's try using our `def:uncurry` function from before. As a first example, we can
uncurry the `def:_∨_` function. If we don't want to do the work to figure out what
type this thing should have, we can simply leave behind a hole in its type
judgment:

```agda
  _ : ?
  _ = uncurry _∨_
```

and then ask Agda to fill it in for us via [`Solve`](AgdaCmd):

```agda
  _ : Bool × Bool → Bool
  _ = uncurry _∨_
```

The [`Solve`](AgdaCmd) command asks Agda to infer the contents of a hole based on
information it already knows from somewhere else. In this case, Agda knows the
type of `def:_∨_` (that is, `Bool → Bool → Bool`,) and so it can infer the type of
`uncurry _∨_` as `Bool × Bool → Bool`. Since this is the entire expression, the
type of our definition is fully known to Agda, and it will happily fill it in
for us.

As you can see, Agda is quite the clever language! The constraint solving
exhibited here is a generally useful tool when coding. For example, you can
state a proof as being trivial, and then work backwards---asking Agda to
synthesize the solution for you!

Time to make a new sandbox. The booleans we implemented by hand in the previous
section exist in the standard library, under the module `Data.Bool`. This is
quite a big module, but we can import only the pieces we need via a `using`
modifier:

```agda
module Sandbox-Implicits where
  open import Data.Bool
    using (Bool; false; true; not; _∨_)
```

The tuple type exists under `Data.Product`:

```agda
  open import Data.Product
    using (_×_; proj₁; proj₂)
```

In addition, `Data.Product` also supplies `ctor:_,_`, `def:curry` and `def:uncurry`. However,
the ones it implements are slightly more general than the ones we have looked
at. The exact functions we wrote above are instead named `type:_,′_`, `def:curry′` and
`def:uncurry′` in the standard library, so we can use a `renaming` modifier on our
import in order to get our sandbox into an equivalent state as the one above:

```agda
    renaming ( _,′_      to _,_
             ; curry′    to curry
             ; uncurry′  to uncurry
             )
```

Note that these are *primes* at the end of `def:curry` and `def:uncurry`, not
apostrophes. Primes can be input via [`'`](AgdaMode).

It is now time to investigate the mysterious curly braces that prefix several of
our functions. As a reminder, we have the following functions in scope, with
the given typing judgments:


Hidden

:   ```agda
  postulate
    ```


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
rewrite the type of `ctor:_,_` in its full glory:

```agda
    _,_⅋⅋ : {A : Set} → {B : Set} → A → B → A × B
```

In this form, it looks a lot like `A : Set` and `B : Set` are *arguments* to
`ctor:_,_`. And rather amazingly, *they are!* The curly braces around them make these
*invisible* arguments. Something interesting happens if we replace them with
parentheses instead. Let's make a new function called `mk-tuple` using regular,
visible arguments:

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

Here you can see that the implementation of `mk-tuple` *completely ignores* its
`A` and `B` arguments. Peculiar. We can try using `mk-tuple` to build ourselves
a tuple. Starting from a delimited hole:

```agda
  _ : Bool × Bool
  _ = {! !}
```

we can type `mk-tuple` *inside the hole:*

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

This expression now has four holes for the four arguments to `mk-tuple`. The
first two are the type parameters of the tuple, while the last two are the
actual values we'd like to fill our tuple with. Thankfully, Agda can
[`Solve`](AgdaCmd) the first two holes for us:

```agda
  _ : Bool × Bool
  _ = mk-tuple Bool Bool {! !} {! !}
```

and we are free to fill in the latter two to our heart's content. Perhaps more
interestingly, we can see what happens if we fill in one of these types
*incorrectly*---that is to say, with a type which *isn't* `type:Bool`. Thankfully,
it's easy to spin up new types at will:

```agda
  data PrimaryColor : Set where
    red green blue : PrimaryColor
```

and we can try again:


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

Agda is telling us off, for writing down `type:PrimaryColor` when we should have
written `type:Bool`. The language knows this should be a `type:Bool` since our type claims
to be a `type:Bool × Bool`. You will notice this is all a bit stupid. If Agda knows
what exactly what we should write into this hole, and yells at us if we don't do
it properly, why do we have to do it at all? As it happens, we don't!

Instead, in any expression, we can leave behind an underscore, asking Agda to
make an informed decision and fill it in for us. Thus, we can write the
following:

```agda
  color-bool-tuple : PrimaryColor × Bool
  color-bool-tuple = mk-tuple _ _ red false
```

and Agda will (silently, without changing our file) fill in the two underscores
as `type:PrimaryColor` and `type:Bool`, respectively. Filling in arguments in this way is
known as *elaboration,* as it offloads the work of figuring out exactly what
your program should be to the compiler. No human input necessary.

It is exactly this elaboration that is happening behind the scenes of our
invisible parameters. Whenever you mark a parameter as invisible by ensconcing
it in curly braces, you're really just asking Agda to elaborate that argument
for you by means of inserting an underscore.

We can make the invisible visible again by explicitly filling in implicit
arguments for ourselves. The syntax for this is to give our implicit arguments
as regular arguments, but themselves in curly braces. We can also use the
explicit names to these implicits, so that we need to fill them all in order to
fill only one:

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
following, because it doesn't know whether you want `ctor:false` or `ctor:true`:

```agda
  ambiguous : Bool
  ambiguous = _
```

You'll notice the syntax highlighting for this implicit has gone yellow; that's
Agda informing us that it doesn't have enough information to elaborate.
Agda refers to this as an *unsolved meta.* In addition, you'll also see a warning
message like this in the info window:

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
likely are not yet the world's best Agda programmer, the attentive reader has
been exposed to the majority of this gentle language's most astronautic
features.

What we have seen here are Agda's fundamental building blocks. While they are
interesting in their own right, the fun parts come when we start putting them
together into funky shapes. Throughout our progression we will learn
that there was more to learn about these simple pieces all along. Indeed,
perhaps these primitive elements are much more sophisticated than they look.

We have not even begun to scratch the surface of what interesting things are
possible in Agda, but we now have enough background that we can earnestly get
into the meat of this book. Prepare yourself.

