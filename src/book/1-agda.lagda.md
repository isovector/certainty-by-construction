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


Hidden

:   ```agda
{-# OPTIONS --allow-unsolved-metas #-}
    ```


```agda
module 1-agda where
```

This is not merely an example; it's necessary preamble when starting a new Agda
file. The `module` is Agda's simplest unit of compilation, and every chapter in
this book will begin a new module. Thus, you shouldn't be surprised to see
similar blocks of code at the beginning of each chapter.

-- TODO(sandy): CHANGE ME WHEN PUBLISHING

Every Agda source file must begin with a module declaration corresponding to the
file name. Since this module is called `1-agda`, if you want to follow
along at home, you will have to save your file as `1-agda.agda`.

Agda modules can contain other modules, in which case they act as namespacing
tools. For example, we can make a submodule inside of `1-agda`:

```agda
module example where
  -- I am an example
```

This introduces a new module `example` inside of `1-agda`. Unlike many
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

- `1-agda.foo`
- `1-agda.foo.bar`
- `1-agda.foo.bar.qux`
- `1-agda.foo.zaz`

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


## Syntax Highlighting

Unlike most programming languages, syntax highlighting in Agda is performed *by
the compiler,* rather than just some hodgepodge set of regular expressions that
hope to do a reasonably good job of parsing the program. In many ways, thus,
it's more correct to call this *semantic highlighting*. Since Agda's parser is
so flexible, getting trustworthy highlighting information from the compiler is a
necessity for quickly parsing what's going on. This, along with the lack of
[GotoDefinition](AgdaCmd), is the main reason Agda is challenging to read
outside of a text editor.

Because this book is a literate Agda document, all of the syntax highlighting
you see was produced directly by the Agda compiler. This is unfortunately the
most help I can give to the reader of this book in hard copy.

As a quick guide, you can visually spot the following pieces of Agda:

- \AgdaKeyword{orange}: keywords
- \AgdaInductiveConstructor{green}: constructors
- \AgdaBound{black}: bound variables
- \AgdaField{salmon}: record fields
- \AgdaModule{purple}: modules
- \AgdaFunction{blue}: other definitions
- \AgdaHole{green background}: interactive holes
- \AgdaUnsolvedMeta{yellow background}: underspecified elaboration

We haven't yet discussed all of these ideas, but these conventions will be used
throughout the book. Feel free to return to this section if you're ever having a
hard time mentally parsing what's going on.


## Types

-- TODO(sandy): a value has exactly one type


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
module Booleans where
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

Congratulations, you've just written your first Agda function!

This function gives us a taste of how we can do computation in Agda; on the left
side of the equals, we match on the distinct possibilities for our parameters,
and give a result for each on the right side of the equals sign.

In implementing this little function, we learned quite a lot about how Agda's
interactivity can help. We can admire our handiwork by interactively running
[Normalize:not false](AgdaCmd), which will leave the computed answer (`true`) in
the info window.

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
things in great detail soon enough.


## Dealing with Unicode

Personally, my biggest challenge coming to Agda was learning to wrangle all of
the Unicode characters. The field of programming has a peculiar affinity for the
standard ASCII character set, which is somewhat odd when you think about it.
What symbol is `==` supposed to be, anyway? Is it *merely* a standard equals
sign? If so, why not just use `=`? Is it supposed to be an elongated equals
sign? In the case we really wanted to stick with ASCII, surely `=?` would be a
better choice, since this operator *tests* for equality. Agda follows this path,
but decides that, since we have a perfectly good unicode symbol anyway, why not
use `≟`?

There are two primary arguments here to make here against the usage of unicode.

The first, is unfamiliarity with symbols when *reading* code. For example, when
I was getting started, I was often flummoxed by `⊎` and `⨄`, which are easy to
distinguish when placed beside one another, but much harder when they're in the
wild. When you're reading code, how do you know which symbol is which? And how
do you assign names to them?

Agda provides [DescribeChar](AgdaCmd) to help with this problem, which when run
with the cursor over `⊎` will produce the following output:

```verbatim
            character: ⊎ (displayed as ⊎) (codepoint 8846, #o21216, #x228e)
              charset: unicode (Unicode (ISO10646))
code point in charset: 0x228E
               script: symbol
               syntax: w    which means: word
             category: .:Base
             to input: type "\u+" with Agda input method

Character code properties: customize what to show
  name: MULTISET UNION
  general-category: Sm (Symbol, Math)
  decomposition: (8846) ('⊎')
```
In particular, we see the name of this symbol is *multiset union*, which is
significantly more pronounceable than `⊎`.

The second problem that beginners have with Unicode is the problem of how the
heck do you actually type these strange characters? As you can see in the
response from [DescribeChar](AgdaCmd) above, there's a little section labeled
"to input."

When writing Agda, you can input Unicode characters by typing a backslash, and
then a mnemonic for the character you'd like. There are a few different naming
schemes used by Agda, but for abstract symbols like `⊎` a good bet is to try to
press a series of characters that together build the one you want. For example,
`≈` is input by typing `\~~`, and `≋` is similarly just `\~~~`. We can write `≗`
via `\=o`, and `≟` via `\=?`. Some characters require only one additional
keypress. We can write `∙` by typing `\.` and `∘` with `\o`.

One common binding you'll need is that for function arrows, `→`. This is typed
in the obvious way, `\->`, but can also be written in fewer keystrokes as `\to`.
As it happens, this is the same mnemonic that LaTeX uses to type the arrow
symbol. If you're familiar with LaTeX, most bindings you know from there will
also work in Agda.

Similarly to LaTeX, we can prefix bindings with `_` or `^` to make subscript or
superscript versions of characters. That means we can get `₁` via `\_1`, and get
a squared symbol `²` via `\^2`. All numbers have sub- and superscript versions,
but only some letters do. This is not Agda's fault; address your complaints to
the Unicode Consortium regarding the lack of subscript `f`.

Mathematicians, and thus Agda-users, are also particularly fond of Greek
letters. You can type Greek letters by prefixing the Latin-equivalent letter
with `\G`. That is, if you'd like a `λ` (and what good functional programmer
wouldn't?) you'd type `\Gl`, because `λ` is the Greek version of the Latin
letter `l`. And if you want an uppercase lambda `Λ`, well, that one is just
`\GL`. As you can see, the system is quite well organized when you wrap your
head around it.

The other block of symbols you'll probably need at first are the so-called
*blackboard bold* letters, which are often used in mathematics to describe sets
of numbers --- the natural numbers being `ℕ`, the reals being `ℝ`, the rationals
being `ℚ` (short for "quotients"), and so on. You can type blackboard bold
numbers with the `\b` prefix.

Suspend your disbelief; programming in Unicode really is quite delightful if you
can push through the first few hours. Having orders of magnitude more symbols
under your fingers is remarkably powerful, meaning you can shorten your
identifiers without throwing away information. And as a bonus, especially when
transcribing mathematics, your program can look exceptionally close to the
source material --- nice to minimize the cognitive load. You're already dealing
with big ideas, without having to add a layer of naming indirection into the
mix.


## A Note on Syntax

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
syntax, there are mightily-good theoretical reasons for it. With this knowledge
of function calls, it's interesting to look back at our definition of `not`;
recall:

```agda
  not⅋⅋⅋⅋ : Bool → Bool
  not⅋⅋⅋⅋ false = true
  not⅋⅋⅋⅋ true = false
```

we can now mentally parse these definitions differently, that is, reading them
literally. The first of which, says "the function call `not false` is equal to
`true`". Thus, this equals sign is really and truly an *equals* sign. It is
*not* the "assignment" operator found in all stateful descendants of ALGOL, nor
is it some sort of test-for-equality that usually gets called `==`. No, we are
saying the thing on the left side is exactly the same thing as on the right!

This equality is very deep. While Agda will simplify the left side to the right
whenever possible, the two sides are exactly equivalent in all non-pattern
(TODO: what does this mean?) contexts. Indeed, many proofs depend on finding two
complicated expressions that are exactly equal in this way, and much of the work
is in showing that equivalence.


## Operators

Another simple operation over booleans is logical OR; that is, the result is
true if at least one of its arguments is true. Mathematicians often use the
symbol $\vee$ (pronounced "vel") for this operation, which we will follow, since
the goal is to define the same interface as is present in the Agda standard
library. This operator is used infix, which we can communicate to Agda by naming
the OR function `_∨_`; note that this is not a latin `v`, but the unicode
character `\or`. Note also the underscores on either side of it!

```agda
  _∨⅋⅋_ : Bool → Bool → Bool
  _∨⅋⅋_ = ?
```

We will again interactively ask for Agda's help here. Place your cursor in the
hole and run [MakeCase](AgdaCmd). Agda will respond:

```agda
  _∨⅋⅋⅋_ : Bool → Bool → Bool
  x ∨⅋⅋⅋ x₁ = {! !}
```

You will notice that `_∨_` has been replaced with `x ∨ x₁`. The underscores are
not literal underscores, but instead mark placeholders for the operator's
syntax. If we fill the resulting hole with the names of both arguments `x` and
`x₁`, we can again ask Agda to `[MakeCase](AgdaCmd)`:

```agda
  _∨⅋⅋⅋⅋_ : Bool → Bool → Bool
  x ∨⅋⅋⅋⅋ x₁ = {! x x₁ !}
```

This time Agda will use the variables named in the hole as input on what to
split. The result is a very satisfying four lines of code that we didn't need to
write for ourselves:

```agda
  _∨⅋⅋⅋⅋⅋_ : Bool → Bool → Bool
  false ∨⅋⅋⅋⅋⅋ false = {! !}
  false ∨⅋⅋⅋⅋⅋ true  = {! !}
  true  ∨⅋⅋⅋⅋⅋ false = {! !}
  true  ∨⅋⅋⅋⅋⅋ true  = {! !}
```

We can finish the definition of `_∨_` by giving filling in the desired answers
in each hole:

```agda
  _∨⅋_ : Bool → Bool → Bool
  false ∨⅋ false = false
  false ∨⅋ true  = true
  true  ∨⅋ false = true
  true  ∨⅋ true  = true
```

Here we have taken the same approach as in `not`: for each argument, we
enumerate every possibilities, giving the answer on the right side of the equals
sign. You will notice that this strategy grows enormously; a function of five
booleans would require 32 clauses to enumerate every possibility. Fortunately,
this is not the only way to define `_∨_`. We can instead throw some thought at
the problem, and realize the goal is to identify whether or not one of the
arguments is `true`. This doesn't require pattern matching on *both*
parameters---some clever thought indicates we can get away with matching only on
one.

If the argument we matched on is `true`, we're done, without looking at the
other argument. If our matched argument is `false`, then the result is `true`
only when the second argument is `true`. In neither case do we need to inspect
both of the arguments! We can take advantage of this fact by using a variable to
abstract over the second parameter. Instead, let us define `_∨_` in this way:

```agda
  _∨_ : Bool → Bool → Bool
  false ∨ other = other
  true  ∨ other = true
```

Because we wrote `other`---rather than any of the constructors of `Bool`--- Agda
knows we don't want to perform a pattern match. Instead, this introduces a new
variable `other : Bool`. In the `false` case, we simply return this argument,
and in the `true` case we ignore it completely because we've already found the
`true` we're looking for.

Note that we call `other` a variable, but **it is a variable in the mathematical
sense rather than in the usual programming sense.** This variable is a way of
talking about something whose value we don't know, like the $x$ in the
expression $f(x) = 2x$. Here, $x$ exists, but its value is set once and for all
by the user of $f$. When we are talking about $f(5)$, $x = 5$, and it is never
the case that $x$ changes to 7 while still in the context of $f(5)$. In a given
context, $f$ (or `other`) is always *bound* to a specific value, even if we
don't know what that value is. For this reason, we sometimes call variables
*bindings.*


## Agda's Computational Model

Let's compare our two definitions of `_∨_`, reproduced here with slightly
different names:

```agda
  _∨₁_ : Bool → Bool → Bool  -- ! 1
  false ∨₁ false = false
  false ∨₁ true  = true
  true  ∨₁ false = true
  true  ∨₁ true  = true
```

and

```agda
  _∨₂_ : Bool → Bool → Bool  -- ! 2
  false ∨₂ other = other
  true  ∨₂ other = true
```

Besides the amount of code we needed to write, is there a reason to prefer
[2](Ann) over [1](Ann)? These two implementations are equivalent, but have very
different computational properties as Agda programs. Let's explore why that is.

At its root, [2](Ann) is a better program *because* it needs to inspect less
data in order to make a decision. `_∨₂_` is able to make meaningful progress
towards an answer, even when the second argument isn't yet known, while `_v₁_`
is required to wait for both arguments. We can observe this in action with the
[Normalise](AgdaCmd) command, which asks Agda to evaluate an expression for us.

We can fill in only one argument to an operator by removing only one of the
underscores. Thus, we can see what happens when we invoke `_v₂_` with only its
first argument. Try invoking [Normalise:true v₂_](AgdaCmd), to which Agda will
respond:

```info
λ other → true
```

[]

This response is Agda's syntax for an anonymous (lambda) function. It takes an
argument, called `other`, ignores it, and immediately returns `true`. Writing
lambdas like this is valid Agda code, but this syntax is often reserved for
niche circumstances.

Nevertheless, let's compare this output to the result of [Normalise:true
∨₁_](AgdaCmd):

```info
true ∨₁_
```

Here, Agda simply returns what we gave it, because it is unable to make any
progress towards evaluating this value. Terms like this are called *stuck*, and
can make no progress in evaluation until something unsticks them. In this case,
because we don't know the value of the second argument, it is stuck, and thus
the pattern match on it in `_∨₁_` is *also* stuck. When the second argument is
provided, the pattern match will unstick, and so too will the final result.

We can see this behavior more clearly by postulating a boolean value. Postulated
values are always stuck, and thus `stuck` is an apt name for one:

```agda
  postulate
    stuck : Bool
```

Our new `stuck` is always stuck. For example, we can learn nothing more about it
with [Normalise:stuck](AgdaCmd):

```info
stuck
```

Nor can we reduce [Normalise:not stuck](AgdaCmd) to a value:

```info
not stuck
```

Don't believe the response, this is indeed stuck~ Rather, the entire call to
`not` with argument `stuck` is stuck. And, as you might expect, [Normalise:true
∨₁ stuck](AgdaCmd) is also stuck:

```info
true ∨₁ stuck
```

Fascinatingly however, [Normalise:true ∨₂ stuck](AgdaCmd) computes just fine:

```info
true
```

This progress of computation even when the second argument is stuck (`stuck`, or
otherwise) is the reason by which we prefer `_∨₂_` over `_∨₁_`. While this
example might seem somewhat contrived, it isn't, in fact. Avoiding a pattern
match in an implementation means you can avoid a pattern match in every
subsequent proof *about* the implementation, and can be the difference between a
three line proof and an 81 line proof. We will return to this point when we
discuss proof techniques, but for now, try not to get into the habit of bashing
your way through every implementation if you can at all help it.


## Records and Tuples

In this section, we will play around with record types, as a lead up to
discussing functions. These two seemingly disparate ideas have a surprising
amount of interplay between them. We would like to motivate an answer to the
question of "what's up with the funny arrow `→` in function types?" Why does
`_∨_` have type `Bool → Bool → Bool`, instead of a more "standard" type like it
would in most everyday programming languages. For example, we might write
`_∨_`'s type as `(Bool, Bool) → Bool`, which makes it very clear which are the
parameters and which is the return.

Types like `(Bool, Bool)` are known as *tuple* types, which we can encode to a
in Agda as record types. Record types are types with a number of subfields. A
special case of records are tuples, which we can think of as anonymous records
with only two fields. As a first approximation, we can write the tuple type like
this:

```agda
module Sandbox-Tuples where
  open Booleans

  record _×⅋_ (A : Set) (B : Set) : Set where  -- ! 1
    field -- ! 2
      proj₁ : A
      proj₂ : B
```

There is quite a lot going on here, which we will tackle one step at a time. At
[1](Ann) we parameterize the entire type `_×_` by two other types, call them `A`
and `B`. This is because we'd like to be able to form tuples of any two types,
whether they be integers and booleans, tuples of tuples, or more exotic things
still. Note that this name `_×_` is not the Latin letter `x`, but is instead the
*times symbol,* input via `\x`.

At [2](Ann) we say "inside of the `_×_` type, there are two fields." These two
fields are named `proj₁` and `proj₂`, and have types `A` and `B`, respectively.
This is what you would expect; if we have a record corresponding to a tuple of
two things, *it should have two things in it.*

We can try out our new tuple type, as usual by plunking a hole down on the right
hand side of the equals sign:

```agda
  my-tuple⅋⅋ : Bool ×⅋ Bool
  my-tuple⅋⅋ = ?
```

This time we will use the [Refine](AgdaCmd) command, which asks Agda to build us
a value of the correct type, leaving holes for every argument. The result is:

```agda
  my-tuple⅋ : Bool ×⅋ Bool
  my-tuple⅋ = record { proj₁ = ? ; proj₂ = ? }
```

Note that these two holes both have type `Bool`, corresponding exactly to the
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
name. Thus, we can bring `proj₁` and `proj₂` into the top-level scope by opening
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

The type of `_,_` should really be `A → B → A × B`, however, recall that `A` and
`B` are variables standing in for *whatever type the user wants.* But those
variables are not in scope, so we must bind them ourselves. This is the meaning
of the `{A B : Set} →` prefix of the type at [1](Ann)---it's responsible for
bringing `A` and `B` both into scope and letting Agda know they are both types
(that is, they are both of type `Set`.) We will discuss Agda's scoping mechanism
in more detail in @sec:implicits.

Implementing `_,_` isn't hard to do by hand; but we can be lazy and ask Agda to
do it for us. Begin as usual by getting Agda to bind our arguments, via
[MakeCase](AgdaCmd) in the hole:

```agda
  _,⅋⅋_  : {A B : Set} → A → B → A ×⅋ B
  x ,⅋⅋ x₁ = {! !}
```

and follow up by invoking [Auto](AgdaCmd), which asks Agda to just write the
function for you. Of course, this doesn't always work, but it's surprisingly
good for little functions like this. The result is exactly what we'd expect it
to be:

```agda
  _,⅋⅋⅋_  : {A B : Set} → A → B → A ×⅋ B
  x ,⅋⅋⅋ x₁ = record { proj₁ = x ; proj₂ = x₁ }
```

Move the definition of `_,_` above the definition of `my-tuple`, which we can
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

The keyword `constructor` at [1](Ann) tells Agda we'd like to avoid the whole
`record { ... }` nonsense we had to deal with last on the go-around, instead
asking it to just automate writing the `_,_` function for us. Sorry to have
led you down the garden path, but it's nice to see for ourselves what tedium
each language feature can assuage.

We can return to the problem of getting Agda to correctly parse `true ∨ true ,
false` with the implied parentheses on the left. Infix operators like `_∨_` and
`_,_` are parsed, in every language, according to rules of *precedence* and
*associativity.*

The *precedence* of an operator lets the parser know how "tightly" an operator
should bind with respect to other operators. In this case, because we'd like the
parentheses to go around `_∨_`, we would like `_∨_` to have a higher precedence
than `_,_`. Agda assumes a precedence of 20 (on a scale from 0 to 100) by
default for any operator, so we must give `_,_` a *lower* precedence than 20. By
convention, we give `_,_` a precedence of 4, which makes it play nicely with the
conventions for the more usual mathematic operators like addition and
subtraction.

The *associativity* of an operator describes how to insert parentheses into
repeated applications of the operator. That is, should we parse `x , y , z` as
`(x , y) , z` or as `x , (y , z)`? The former here is said to be
*left-associative*, while the latter is, appropriately, *right-associative.* For
reasons that will make sense later, we'd like `_,_` to be right-associative.

We can tell Agda's parser about our preferences, that `_,_` be right-associative
with precedence 4 with the following declaration:

```agda
  infixr 4 _,_
```

Here, the `r` at the end of `infixr` tells Agda about our associativity
preference. Of course, you could use `infixl` instead if you wanted
left-associativity (although you don't in this case.) Of course, if you ever
*do* want an explicit left-nested tuple, you are free to insert the parentheses
on the left yourself!

While `_,_` is the operator for building *values* of tuple types, `_×_` is the
operator for building the tuple type itself. The values and their types should
be in one-to-one correspondence. That is to say, if we have `a : A`, `b : B` and
`c : C`, we'd like it to be the case that `a , b , c` have type `A × B × C`. And
thus, we must also choose right-associativity for `_×_`. For mysterious reasons,
however, `_×_` is traditionally given a preference of 2:

```agda
  infixr 2 _×_
```

We will end our discussion of record types here, as this is enough to get you
started.


## Function Types

It is now time to tackle the question of what's up with the funny syntax for
functions with multiple arguments. Most programming languages assign a type of
the form `(A × B) → C` to functions with two arguments, while in Agda we instead
write `A → B → C`. The reason for this is, in short, that they are equivalent,
but that the latter is more useful.

In order to see this equivalence directly, we can stop for a moment to think
about the issue of parsing again. Although the function arrow is intrinsically
magical and built-in to Agda, we can ask ourselves how it ought to work.
Spiritually, `_→_` is a binary operator, which means we can ask about its
precedence and associativity. In Agda, the typing judgment `_:_` binds with the
lowest precedence of all, while `_→_` comes in just after as the second-lowest
precedence in the language. What this means is that in practice, `_→_` always
acts as a separator between types, and we don't need to worry ourselves about
where the parentheses should go.

The associativity for `_→_`, on the other hand, is to the right. That means,
given the type `A → B → C`, we must read it as `A → (B → C)`. A literal
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
      dog : AnimalVariety
      cat : AnimalVariety
      bird : AnimalVariety
      reptile : AnimalVariety

    postulate
      Name : Set  -- ! 2
      Age : Set
      SpecificAnimal : Set

      makeAnimal
        : AnimalVariety → Age → Name → SpecificAnimal  -- ! 3

    makeBird : Age → Name → SpecificAnimal  -- ! 4
    makeBird age name = makeAnimal bird age name
```

Here, we've made a new `data` type at [1](Ann), enumerating possible sorts of
animals one might have. At [2](Ann) we postulate the existence of some other
types with suggestive names, in order to give our postulated function
`makeAnimal` a suggestive type at [3](Ann). Finally, at [4](Ann) we specialize
the `makeAnimal` function into `makeBird`, where we always decide the animal
variety should be a `bird`.

This doesn't yet exhibit the desirability of one-at-a-time functions we'd like
to showcase. But we will note that `makeBird` is a function whose definition
binds two arguments (`age` and `name`), and simply passes them off to
`makeAnimal`. If you were to drop a hole on the right side of this equation,
you'd see that the type of the hole is `SpecificAnimal`. By the law of equality,
this means the left-hand side must also have type `SpecificAnimal`. If we were
to drop the `name` binding on the left side, the hole now has type `Name →
SpecificAnimal`. Dropping now the `age` parameter too, we see the resulting hole
now has type `Age → Name → SpecificAnimal`, exactly what we expect from the type
definition.

Are you ready for the cool part? If we insert the implicit parentheses into the
type of `makeAnimal`, we get `AnimalVariety → (Age → (Name → SpecificAnimal))`;
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
the two. That is, we'd like to be able to transform functions of the shape `A ×
B → C` into `A → B → C` and vice versa. We'll work through the first half of
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
at `curry`. Let's ignore the `{A B C : Set} →` part, which you'll recall exists
only to bring the type variables into scope:

```illegal
  curry : (A × B → C) → (A → B → C)
```

After inserting the parentheses arising from the interaction of
`_→_` as the lowest precedence operator, we obtain some parentheses around the
tuple:

```illegal
  curry : ((A × B) → C) → (A → B → C)
```

We can then insert the parentheses from the function arrow's right-associativity
to the innermost parentheses:

```illegal
  curry : ((A × B) → C) → (A → (B → C))
```

Written like this, we see that `curry` is a function which itself takes a
*function* as an *argument,* and also produces a function as its *return type.*
Alternatively, we can drop the last two pairs of parentheses, and think about
`curry` like this:

```illegal
  curry : ((A × B) → C) → A → B → C
```

That is, `curry` is a function that takes *three* inputs, one is a function, and
the other two are an `A` and a `B` respectively, at the end of the day returning
a `C`. Written in this form, it's a little easier to see how you would go about
implementing such a thing, while the previous form gives a better sense of what
exactly you're trying to accomplish.


Exercise

:   Implement the `curry` function for yourself. If you get stuck, don't forget
    you can always ask Agda for help by using [TypeContext](AgdaCmd) to inspect
    what you have lying around in scope, [MakeCase](AgdaCmd) to bind arguments
    and [Refine](AgdaCmd) to construct values for you.


Solution

:   ```agda
  curry f a b = f (a , b)
    ```


Going the other direction and implementing `uncurry` is slightly harder, since
it requires you to remember how to project fields out of record types. The type
you want is:

```agda
  uncurry : {A B C : Set} → (A → B → C) → (A × B → C)
```

Exercise

:   Implement `uncurry`. Remember that you can use `proj₁` and `proj₂` to get
    the fields out of a tuple.


Solution

:    ```agda
  uncurry f ab = f (proj₁ ab) (proj₂ ab)
     ```


It's slightly annoying needing to project both fields out of `ab` in the
implementation of `uncurry`. This leads us to one last trick. Start again,
having just bound your arguments:

```agda
  uncurry⅋ : {A B C : Set} → (A → B → C) → (A × B → C)
  uncurry⅋ f ab = {! !}
```

From here, we can ask Agda to pattern match on `ab` directly by invoking
[MakeCase:ab](AgdaCmd), which results in:

```agda
  uncurry⅋⅋ : {A B C : Set} → (A → B → C) → (A × B → C)
  uncurry⅋⅋ f (proj₃ , proj₄) = {! !}
```

Agda has replaced `ab` with the `_,_` constructor that is used to build the
tuple type `_×_`, and then bound the two projections that result from tearing
apart `_,_`. It's debatable whether or not the names it chose (`proj₁` and
`proj₂`) are good or bad---on one hand, those are the names we said the fields
have, on the other, they shadow the projections that are already in scope and
have different types. I prefer to rename them:

```agda
  uncurry⅋⅋⅋ : {A B C : Set} → (A → B → C) → (A × B → C)
  uncurry⅋⅋⅋ f (a , b) = {! !}
```

and from here, Agda will happily write the remainder of the function via
[Auto](AgdaCmd).

Because we were able to implement `curry` and `uncurry`, we have shown that
curried functions (used in Agda) are equivalent in power to uncurried functions
(used in most programming languages.) But the oddity of our choice leads to our
ability to "cancel" arguments that are duplicated on either side of a function
definition, and this happens to be extremely useful for massaging general
functions into the right shape so that they can be used in place of
more-specific functions.


## Implicit Arguments

Let's try using our `uncurry` function from before. As a first example, we can
uncurry the `_∨_` function. If we don't want to do the work to figure out what
type this thing should have, we can simply leave behind a hole in its type
judgment:

```agda
  _ : ?
  _ = uncurry _∨_
```

and then ask Agda to fill it in for us via [Solve](AgdaCmd):

```agda
  _ : Bool × Bool → Bool
  _ = uncurry _∨_
```

The [Solve](AgdaCmd) command asks Agda to infer the contents of a hole based on
information it already knows from somewhere else. In this case, Agda knows the
type of `_∨_` (that is, `Bool → Bool → Bool`,) and so it can infer the type of
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

In addition, `Data.Product` also supplies `_,_`, `curry` and `uncurry`. However,
the ones it implements are slightly more general than the ones we have looked
at. The exact functions we wrote above are instead named `_,′_`, `curry′` and
`uncurry′` in the standard library, so we can use a `renaming` modifier on our
import in order to get our sandbox into an equivalent state as the one above:

```agda
    renaming ( _,′_     to _,_
             ; curry′   to curry
             ; uncurry′ to uncurry
             )
```

Note that these are *primes* at the end of `curry` and `uncurry`, not
apostrophes. Primes can be input via `\'`.

It is now time to investigate the mysterious curly braces that prefix several of
our functions. As a reminder, we have the following functions in scope, with
the given typing judgments:

```agda
  postulate  -- HIDEME
    ⅋_,_ : {A B : Set} → A → B → A × B
    ⅋curry : {A B C : Set} → (A × B → C) → (A → B → C)
    ⅋uncurry : {A B C : Set} → (A → B → C) → (A × B → C)
```

Each of these types is preceded by curly braces containing a list of types,
which are brought into scope for the remainder of the type signature. But what
exactly is going on here?

The first thing to realize is that the notation `{A B : Set}` is syntactic sugar
for `{A : Set} → {B : Set}`, and so on for more variables. We can therefore
rewrite the type of `_,_` in its full glory:

```agda
    ⅋⅋_,_ : {A : Set} → {B : Set} → A → B → A × B
```

In this form, it looks a lot like `A : Set` and `B : Set` are *arguments* to
`_,_`. And rather amazingly, *they are!* The curly braces around them make these
*invisible* arguments. Something interesting happens if we replace them with
parentheses instead. Let's make a new function called `mk-tuple` using regular,
visible arguments:

```agda
  mk-tuple⅋ : (A : Set) → (B : Set) → A → B → A × B
  mk-tuple⅋ = ?
```

We will do the usual ceremony to bind our arguments via [MakeCase:](AgdaCmd):

```agda
  mk-tuple⅋⅋ : (A : Set) → (B : Set) → A → B → A × B
  mk-tuple⅋⅋ A B x x₁ = {! !}
```

And then run [Auto](AgdaCmd) to implement the function for us.

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

and then invoke [Refine](AgdaCmd), asking Agda to use the given function to try
to fill the hole:

```agda
  _ : Bool × Bool
  _ = mk-tuple {! !} {! !} {! !} {! !}
```

This expression now has four holes for the four arguments to `mk-tuple`. The
first two are the type parameters of the tuple, while the last two are the
actual values we'd like to fill our tuple with. Thankfully, Agda can
[Solve](AgdaCmd) the first two holes for us:

```agda
  _ : Bool × Bool
  _ = mk-tuple Bool Bool {! !} {! !}
```

and we are free to fill in the latter two to our heart's content. Perhaps more
interestingly, we can see what happens if we fill in one of these types
*incorrectly*---that is to say, with a type which *isn't* `Bool`. Thankfully,
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

Agda is telling us off, for writing down `PrimaryColor` when we should have
written `Bool`. The language knows this should be a `Bool` since our type claims
to be a `Bool × Bool`. You will notice this is all a bit stupid. If Agda knows
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
as `PrimaryColor` and `Bool`, respectively. Filling in arguments in this way is
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
following, because it doesn't know whether you want `false` or `true`:

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

