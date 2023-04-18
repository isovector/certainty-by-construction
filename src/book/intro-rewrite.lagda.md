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


## Modules and Imports

When code is presented in this book, it will come in a box like the following:

```agda
module intro-rewrite where
```

This is not merely an example; it's necessary preamble when starting a new Agda
file. The `module` is Agda's simplest unit of compilation, and every chapter in
this book will begin a new module. Thus, you shouldn't be surprised to see
similar blocks of code at the beginning of each chapter.

-- TODO(sandy): CHANGE ME WHEN PUBLISHING

Every Agda source file must begin with a module declaration corresponding to the
file name. Since this module is called `intro-rewrite`, if you want to follow
along at home, you will have to save your file as `intro-rewrite.agda`.

Agda modules can contain other modules, in which case they act as namespacing
tools. For example, we can make a submodule inside of `intro-rewrite`:

```agda
module example where
  -- I am an example
```

This introduces a new module `example` inside of `intro-rewrite`. Unlike many
programming languages, Agda doesn't use delimiters to indicate blocks; instead,
it uses *significant whitespace.* That is, in order to show that the comment `I
am an example` is inside the module `example`, it must be indented relative to
the `module`. Indeed, we can go absolutely mad with the module hierarchy (and
with power):

```agda
module foo where
  module bar where
    module qux where
  module zaz where
```

Here, we have defined four sub-modules, which have the *fully-qualified* names:

- `intro-rewrite.foo`
- `intro-rewrite.foo.bar`
- `intro-rewrite.foo.bar.qux`
- `intro-rewrite.foo.zaz`

We will use many modules throughout this book---albeit ones which are much more
interesting than the ones presented thus far. Our primary use for them will be
to scope out sections of prose. And since modules act as namespaces, we will
often open a new one in order to illustrate anti-patterns and false starts
without polluting our main results.

One distinct advantage of organizing chapters into modules is that chapters thus
become conceptual units in our program. If a later chapter depends on an earlier
one, this fact must be explicitly documented in the prose by way of an `import`.
If later chapters require code or extend concepts from earlier ones, they can
simply import the necessary pieces.

We will also assume the presence of the Agda standard library, but will first
derive the pieces we use from scratch before importing it. Agda's flexibility is
outstanding, and common "magical" constructions in other languages---like
numbers, booleans, and `if..then..else` syntax--- are all defined by the
standard library. Getting a chance to define them for ourselves will help build
an appreciation that none of this stuff needs to be special.

However, we will break this define-it-before-you-import-it rule just once to
illustrate how Agda's import syntax works. Imports are also scoped to the
current module, so we will first start a new module to sandbox the imports, and
immediately follow up with how you can define them for yourself.

We can import the `Data.Bool` module as follows:

```agda
module Sandbox-Bool where
  import Data.Bool
```

This line tells Agda to go find a module called `Data.Bool` somewhere (which it
will do by looking in the current project and any globally-installed libraries
for a file called `Data/Bool.agda`.) Just importing it, however, is rarely what
we want, as all the identifiers have come in fully-qualified:

```agda
  _ : Data.Bool.Bool
  _ = Data.Bool.false
```

We will dive into the exact syntax here more fully in a moment, but first, it's
worth learning how to avoid the fully-qualified names. After importing a module,
we can also `open` it, in which case, all of its contents get dumped into the
current environment:

```agda
  open Data.Bool

  _  : Bool
  _ = false
```

Of course, this is quite a lot of work, so we can combine the `import` and
`open` statements together rather than doing them separately:

```agda
  open import Data.Bool
```

There is significantly more to say about Agda's module system, but this is
enough to get you up and running. We will cover the more advanced topics when we
come to them.


## Types

```agda
module Sandbox-Judgments where
```

Because this is a book about mathematics for programmers, it bears discussing a
great deal around *data* --- that of the utmost importance to programmers. On a
physical machine, all data is stored as small valences of electrical charge,
arranged into a matrix of cells laid out onto physical wafers, mapped by the
operating system into a logical view that we pretend is laid out linearly into
neat chunks of eight or 64 pieces, that we then interpret as numbers in binary,
and which we then shuffle into higher order assemblages, building
domain- and application-specific logical structure on top again.

This is a physical fact, caused by the path dependency that computation has
taken over history. Programmers are often split into two camps: those who
worship and count bits as if they are precious, and those of the opinion that we
have lots of memory, and thus room to ignore it. Curiously, there are very few
who consider memory at a lower level than it is presented in C; perhaps the
human mind simply isn't capable of keeping track of all the layers of
abstraction.

Regardless of what camp you find yourself in, thinking about data in terms of
this hierarchy of abstraction will not be conducive to our purposes. A great
deal of this book involves *crafting* data; that is, designing the shapes that
constrain values we are interested in discussing. Most problems in mathematics
and in programming reduce to finding the right set of constraints, and
rigorously pushing them from one form of data to another.

Data is constrained by *types,* which are rigorous means of constructing and
deconstructing data. You likely already have a notion of what types are and what
they do, but the following section will nevertheless be informative and
elucidating.

Agda takes its types extremely seriously; it is strongly unlikely you have ever
used a language with a type system one tenth as powerful as Agda's. This is true
even if you're extremely familiar with strongly-typed languages like Rust,
TypeScript, Haskell, C++, or Java. Agda is a *dependently-typed* programming
language, which means its types can be *computed.* For example, you might make a
function that returns a `String` if (and only if) the 10th Fibonacci number is
56 (it isn't.) At first blush, this seems impractical---if not useless---but it
is in fact the defining feature which makes Agda suitable for doing mathematics.
But let's not get ahead of ourselves.

Of utmost importance in Agda is the notion of a *typing judgment:* the (static)
assertion that a particular value has a particular type. A typing judgment is
the fancy, academic name for a type declaration. Because `true` is a `Bool`, we
would write the judgment `true : Bool`, where the colon can be read aloud as
"has the type," or "is of type." We can't yet write this judgment down, since we
are in a new module and thus have lost our imports that brought `true` and
`Bool` into scope.

In Agda, we can assert the existence of things without having to give them a
definition by using the `postulate` keyword. This is an extremely useful tool,
as we will see later. For now, we can use it to explicitly write down some
typing judgments. First, we assert that the type `Bool` exists:

```agda
  postulate
    Bool : Set
```

and then, at the same level of indentation, we can postulate two booleans into
existence by giving them typing judgments as well:

```agda
    false : Bool
    true  : Bool
```

You will have noticed that `Bool : Set` itself looks a great deal like a typing
judgment. And in fact, it is. `Set` is one of the few built-in things in Agda,
and it corresponds, as a first approximation, to "the type of all types." That
is, the judgment `Bool : Set` says "`Bool` is a type."

Since `Bool` is a type, we are now *justified* in saying that `false` and `true`
are of type `Bool`. However, we can't just put any old thing on the right side
of the typing colon. Try, for example, adding the following judgment to our
postulate block:

```illegal
    illegal : false
```

If you attempt to load this definition into Agda (TODO: how?), you'll get an
angry error message stating:

```response
Bool should be a sort, but it isn't
when checking that the expression false has type _4
```

This is not the easiest thing to decipher, but what Agda is trying to tell you
is that `false` is not a type, and thus it has no business being on the
right-hand side of a colon. The general rule here is that you can only put `X`
on the right side of a colon if you have earlier put it on the left of `: Set`,
as in:

```agda
    X : Set
    y : X
```

Postulating types and values like this is a helpful piece of pedagogy, but it's
not how we usually get things done. Just as Dijkstra popularized the role of
*structured programming* by arguing programmers should not be writing jumps
directly, but instead using `if` and `while` and so forth, we will note that
real programming does not get done by writing typing judgments directly (nor
does mathematics, for that matter.) Why is this?

One problem is, we'd like to say that `false` and `true` are *the only*
booleans. But of course, nothing stops us from further postulating additional
booleans, perhaps:

```agda
    file-not-found : Bool
```

You can imagine the chaos that might occur if someone added this after the fact.
All of a sudden, our programs, carefully designed to handle only the binary case
of booleans, would now need to be retrofitted with extra logic to handle the
case of `file-not-found`. Such a possibility is anathema to the concept of
modular and composable programs --- those that we can write and prove correct
once, without needing to worry about what the future will bring.

In short, working directly with postulates is dangerous and, in general, an
anti-pattern. We will return to postulates in @sec:postulates and see how they
can be useful as mathematical tools. Instead, we will investigate a tool that
instead allows us to simultaneously define `Bool`, `false` and `true` into a
*closed theory.* That is, we'd like to say that these are *the only* two
booleans, allowing us and Agda to reason about that fact.

To do this, we can use a `data` declaration:

```agda
data Bool : Set where
  false : Bool
  true : Bool
```

which simultaneously asserts the three typing judgments `Bool : Set`, `false :
Bool` and `true : Bool`, and further, states that this is an exhaustive list of
all the booleans. There are no others. When written like this, we often call
`false` and `true` the ** *data constructors* or the *introductory forms* of
`Bool`.

After all of this foreplay, you are probably itching to write a program in Agda.
As a first step, let's write the `not` function, which transforms `false` into
`true` and vice-versa. Functions in Agda begin with a typing judgment using a
*function* arrow (which you can type in your editor via `\to`), and are
immediately followed by a *definition* of the function:

```agda
not : Bool → Bool  -- ! 1
not = ?  -- ! 2
```

Line [1](Ann) should be read aloud as "`not` is a function that takes a `Bool`
argument and returns a `Bool`," or, alternatively, as "`not` has type `Bool` to
`Bool`." The question mark on line [2](Ann) says to Agda "we're not sure how to
implement this function."

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

The question mark above at [2](Ann) is one of these holes. After reloading the
file in Agda (TODO: how?), we can ask it for help in implementing `not`.
Position your cursor on the hole and invoke the [MakeCase](AgdaCmd), which will
replace our definition with:

```agda
not⅋ : Bool → Bool
not⅋ x = {! !}
```

You will notice two things have happened; Agda wrote `x` on the left side of the
equals sign, and it replaced our `?` with `{! !}`. The latter is slightly
different syntax for a hole that has some benefits, but is a few more keystrokes
for a human to type for themselves. The reader playing along at home will also
have noticed the "visible goal" in the info panel has changed from `?1 : Bool →
Bool` to `?1 : Bool`.

The changes engendered by invoking [MakeCase](AgdaCmd) like we did have a lot to
teach us about how Agda works. Our first hole, way back at [1](Ann) had type
`Bool → Bool`, because we had written `not = ?`, and we knew already that `not`
had type `Bool → Bool`. In giving a definition for `not`, we had better give a
definition that has the same type as the one we claimed!

After [MakeCase](AgdaCmd) however, we instead had `not x = {! !}`, with the hole
now having type `Bool`. Somehow we lost the `Bool →` part of the type---but
where did it go? The answer is that the `Bool →` corresponded to the function's
parameter. In addition to the type of the hole changing, we also obtained an `x`
on the left of the equals sign. It's a good bet that this `x` is indeed our
parameter.

To verify this, we can put the cursor in the whole and this time invoke the
[TypeContext](AgdaCmd) command, which will replace the info window with the
following:

```info
Goal: Bool
————————————————————————————————————————————————————————————
x : Bool
```

[TypeContext](AgdaCmd) is useful whenever you'd like to "drill down" into a
hole. Not only does it tell us what the type of the hole is, it also tells us
everything else we have in scope. In this case, the only thing we have is `x :
Bool`. Thus it's confirmed: `x` is indeed our function parameter.

We can ask Agda for more help. This time, if we put our cursor in the hole and
invoke [MakeCase:x](AgdaCmd), we will instead get:

```agda
not⅋⅋ : Bool → Bool
not⅋⅋ false = {! !}
not⅋⅋ true = {! !}
```

You'll notice where once there was one hole there are now two. We asked Agda to
"pattern match" on `x`, which means it looked at `x`, determined it had type
`Bool`, and subsequently split our goal into two---one for if the argument is
`false`, and one for if it's `true`. From here, we know how to complete the
function without any help from Agda; we'd like `false` to map to `true`, and
vice versa:

```agda
not⅋⅋⅋ : Bool → Bool
not⅋⅋⅋ false = true
not⅋⅋⅋ true = false
```

Congratulations, you've just written your first Agda function, and in doing so
learned quite a lot about how Agda's interactivity can help. We can admire our
handiwork by interactively running [Normalize:not false](AgdaCmd), which will
leave the computed answer (`true`) in the info window.

While [Normalize](AgdaCmd) is a nice little tool for interactively computing
small results, we can instead write a small unit test. Breaking our "don't
import it before you define it" rule for the last time, we can write two unit
tests as follows[^equals-sign]:

[^equals-sign]: You can input `≡` by typing `\==`.

```agda
open import Relation.Binary.PropositionalEquality

_ : not⅋⅋⅋ false ≡ true
_ = refl

_ : not⅋⅋⅋ true ≡ false
_ = refl
```

There's quite a lot going on here, which, rest assured, we will get into in
@sec:propeq. For the time being, we will content ourselves with the knowledge
that these are automatically-run unit tests. You can convince yourself of this
by writing another test with an intentionally wrong result:

```illegal
_ : not⅋⅋⅋ true ≡ true
_ = refl
```

which results in an error message after running [Load](AgdaCmd):

```info
false != true of type Bool
when checking that the expression refl has type not⅋⅋⅋ true ≡ true
```

This error is telling us that our unit test failed; that `not true` is actually
`false`, but we said it was `true`! We will discuss these strange `≡` and `refl`
things in great detail soon.










