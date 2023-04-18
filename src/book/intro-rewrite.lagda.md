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

We haven't yet discussed all of these ideas, but these conventions will be used
throughout the book. Feel free to return to this section if you're ever having a
hard time mentally parsing what's going on.


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

As you might expect, [Normalise:true ∨₁ stuck](AgdaCmd) is also stuck:

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


