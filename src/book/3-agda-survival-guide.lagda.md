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
definition as a hole (indicated in Agda code via a question mark, and in the
following code samples via a green background):

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


### Navigating the Agda Standard Library

Much more so than any other programming language I have ever encountered, Agda
code does not lend itself to being read outside of a code editor. The irony of
this statement in a book presenting Agda code is not lost on the author, but he
will do his best to keep the cognitive load to a minimum. The motivated reader
is highly encouraged to follow along in their text editor.

Inside the editor, your best friend is [GotoDefinition](AgdaCmd), which unlike
many compiled languages, will take you to definitions in any package you have
installed, not just those in the same package you're currently working on.
[GotoDefinition](AgdaCmd) is *necessary* for getting any real work done,
especially in the beginning of your Agda experience when you don't have the
standard library's idioms paged into your head.

The standard library itself is laid out hierarchically, into a few main
categories, with relatively consistent structure. As we are just getting
started, we will limit ourselves to the following top-levels of the module
hierarchy:

- `Data.*`
- `Function`
- `Relation.Binary.*`

The `Data` hierarchy contains all the data types you'll ever need, things like
numbers, booleans, strings, lists, optional values, tuples, trees, that sort of
thing. In particular, we will use (in descending order of relative queerness):

- `Data.Nat` --- natural numbers
- `Data.Bool` --- booleans
- `Data.Product` --- tuples
- `Data.Fin` --- bounded numbers
- `Data.List` --- lists
- `Data.Vec` --- lists with an exact size
- `Data.Unit` --- the type with only one value
- `Data.Sum` --- either/or types
- `Data.Empty` --- the type with no values

Each of these modules contains the core data types and their most usual
operations. This book, and Agda as well, is primarily about *proving things,*
and to that extent, Agda already comes with a great deal of proofs. This work
exists inside the `.Properties` sub-module of each of the above. That is, if
you're looking for a proof about lists, you would do well to look inside of
`Data.List.Properties`. Don't forget to use [GotoDefinition](AgdaCmd) to explore
around when you get there.

The `Function` module contains a lot of the common machinery you'd expect from a
functional programming language, things like the `id`entity function, the
`const`ant function, and function composition (via `_∘_`.) If this means nothing
to you yet, don't fret, we'll get there. Otherwise, this is the place to look if
you're unsure of where to find any particular function combinator.

Finally, we come to the `Relation.Binary` hierarchy, which contains tools for
*proving* equality (rather than *testing for equality* like most languages do),
as well as discussing different sorts of equality. As a beginner, the most
important module in this hierarchy is `Relation.Binary.PropositionalEquality`
which has everything we'll need to begin thinking about proofs in chapter
@sec:proofs.


## Normalization

Unfortunately, huge swathes of the standard library are completely
incomprehensible. Worse, it seems like someone must be playing an elaborate joke
on us. Something you'll run across sooner than later is `_Preserves_⟶_`, which
states that some function preserves equality, for example. The details are not
important right now. We can look at the definition of `_Preserves_⟶_` hoping to
gain some insight, but all we are given is this:

```wtf
_Preserves_⟶_ : (A → B) → Rel A ℓ₁ → Rel B ℓ₂ → Set _
f Preserves P ⟶ Q = P =[ f ]⇒ Q
```

Clearly the definition here depends on `_=[_]⇒_`, so we can follow its
definition via [GotoDefinition](AgdaCmd). Unfortunately, this doesn't really
clarify anything:

```wtf
_=[_]⇒_ : Rel A ℓ₁ → (A → B) → Rel B ℓ₂ → Set _
P =[ f ]⇒ Q = P ⇒ (Q on f)
```

Where we once had one puzzle, now we have two: `_⇒_` and `_on_`. Let's proceed
cautiously:

```wtf
_⇒_ : REL A B ℓ₁ → REL A B ℓ₂ → Set _
P ⇒ Q = ∀ {x y} → P x y → Q x y
```

Thankfully the buck stops at `_⇒_`, cashing out into merely being the type of a
function applying two variables pairwise. Again, the purpose here and now is not
necessarily to understand this code, merely to ward off the eventual terror and
despair one might feel if discovering this for themselves. We look into the
pleasantly named `_on_` function, and this is when things begin to really go
wrong:


```wtf
_on_ : (B → B → C) → (A → B) → (A → A → C)
_*_ on f = f -⟨ _*_ ⟩- f
```

Uh oh. Now we need to investigate `_-⟨_⟩-_`? Surely we must be getting close to
the end. One more [GotoDefinition](AgdaCmd), and, oh, god no:

```wtf
_-⟨_⟩-_ : (A → C) → (C → D → E) → (B → D) → (A → B → E)
f -⟨ _*_ ⟩- g = f -⟨ const ∣ -⟪ _*_ ⟫- ∣ constᵣ ⟩- g
```

Surely someone must be pulling our leg here. What in tarnation is all of this
syntax? The unfortunate truth is that this is all library defined, and that Agda
is flexible enough to allow it. We can continue following definitions, but at
this point, personally, my eyes have glazed over and there is no possible way
I'm going to be able to reconstitute all of these definitions back up to
`_Preserves_⟶_` to answer my original question. Just to take the visual gag a
little further, let's look at a few more functions in this call stack:

```wtf
_-⟨_∣ : (A → C) → (C → B → D) → (A → B → D)
f -⟨ _*_ ∣ = f ∘₂ const -⟪ _*_ ∣

_-⟪_∣ : (A → B → C) → (C → B → D) → (A → B → D)
f -⟪ _*_ ∣ = f -⟪ _*_ ⟫- constᵣ

_-⟪_⟫-_ : (A → B → C) → (C → D → E) → (A → B → D) → (A → B → E)
f -⟪ _*_ ⟫- g = λ x y → f x y * g x y
```

You can't make this stuff up. I'm not sure how these definitions got here, but I
do know this is someone who has gone mad with power.

So, playing the [GotoDefinition](AgdaCmd) game clearly hasn't worked for us. Is
there something else we can try to get an understanding of `_Preserves_⟶_`?
Indeed there is --- the [Normalise](AgdaCmd) command, which asks Agda to
evaluate an expression as far as possible. After running [Normalise](AgdaCmd),
we are prompted for what we'd like to evaluate, and we can simply enter
`_Preserves_⟶_`. Our efforts are immediately rewarded with a response from Agda:

```repl
λ f P Q → {x y : z} → P x y → Q (f x) (f y)
```

What's happened here is that we've asked Agda to automate the reasoning chain of
playing [GotoDefinition](AgdaCmd) and attempting to reconstitute an
understanding of the insane choices made in the standard library. While we might
not yet understand Agda's response, we will in a few chapters.

The takeaway here is Agda is extremely good at chasing definitions; feel free to
ask it for help whenever you're feeling overwhelmed.


## Dealing with Unicode

Personally, my biggest challenge coming to Agda was learning to wrangle all of
the unicode characters. The field of programming has a peculiar affinity for the
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

The second problem that beginners have with unicode is the problem of how the
heck do you actually type these strange characters? As you can see in the
response from [DescribeChar](AgdaCmd) above, there's a little section labeled
"to input."

When writing Agda, you can input unicode characters by typing a backslash, and
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

Suspend your disbelief; programming in unicode really is quite delightful if you
can push through the first few hours. Having orders of magnitude more symbols
under your fingers is remarkably powerful, meaning you can shorten your
identifiers without throwing away information. And as a bonus, especially when
transcribing mathematics, your program can look exceptionally close to the
source material --- nice to minimize the cognitive load. You're already dealing
with big ideas, without having to add a layer of naming indirection into the
mix.


## A Note on Identifiers

As we saw earlier when we defined `if_then_else_`, a so-called *mixfix
operator,* Agda's syntax is extremely permissive. But this is really just the
beginning. Most programming languages have strong restrictions on what letters
can occur in identifiers. Agda takes the opposite approach, and says only that
identifiers may not contain any of `.;(){}@`. That's it. Anything else is fair
game.

Oh, and also, because of the mixfix parsing above, you can't use `_` as a
literal character; it always means "a hole for other syntax goes here." If you'd
like an alternative to the `snake_case` you write in other languages, consider
instead using `kebab-case`.

Aside from a few keywords, any other identifier is OK. Do you want to name your
proof that $m = n$ something like `m=n`? Agda isn't going to complain. As we saw
above, the standard library itself makes some very strange choices for its names
as well.

One consideration of the mixfix rules above is that all binary operators are
thus named with a leading and a trailing underscore. Thus, the addition
operator's name is `_+_`, because it leaves syntactical holes on either side to
fill in. This means you can define any binary operator you'd like, with any
name, including a name consisting wholly of ASCII characters. The standard
library does more of this than is my personal preference, but your mileage will
vary.

Because Agda is so permissive when it comes to identifiers, spaces are extremely
significant. That is, the expression `5+6` is *a single identifier*, while `5 +
6` is actually parsed as `_+_ 5 6` --- that is, apply the addition operator to
two arguments, 5 and 6. Be very particular with spaces; a good rule of thumb is
to separate everything with a space, with the exception of anything that abuts
against any of the reserved letters `.;(){}@`.

Over your first few hours, you'll probably get a flurry of strange parse errors
and unknown identifiers. The solution is almost always to just insert more
spaces.


## Syntax Highlighting in Agda

Unlike most programming languages, syntax highlighting in Agda is performed *by
the compiler,* rather than just some hodgepodge set of regular expressions that
hope to do a reasonably good job of parsing the program. Since Agda's parser is
so flexible, getting trustworthy highlighting information from the compiler is a
necessity for quickly parsing what's going on. This, along with
[GotoDefinition](AgdaCmd), is another reason Agda is challenging to read
outside of a text editor.

This book is a literate Agda document, which means the entire thing is a
working, typechecking Agda program with prose written around it. All of the
syntax highlighting you see in this book was produced by the Agda compiler,
which is the most help I can give to you reading this book in hard copy.

