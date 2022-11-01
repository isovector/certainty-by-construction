```agda
module types where
```

## Data and Types

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

Of utmost importance is the notion of a *judgment,* which is an axiomatic
statement we take to be true. Type theorists take judgments extremely far, but
for our purposes, we will need only one: the *typing judgment.* A typing
judgment is of the form `A : B`, and axiomatic states "`A` is of type `B`." We
also have the "primitive" type `Set`, which we say is the "type of types."

Already, this is probably not the way you are used to thinking about types. But
what we have is already very powerful; for example, we can construct the
booleans by stating that `Bool` is a type:

```agda
module Impractical where
  postulate
    Bool : Set
```

and then that `false` and `true` have type `Bool`:

```agda
    false : Bool
    true  : Bool
```

Introduction rules come with a piece of "metatheory": that two introduction
rules correspond to two distinct things.  That is, `false` is a completely
different thing than `true`; they both exist as `Bool`s, but they are separate
from one another. As you can imagine, it might be clever to say our tests
all pass by equating `false` with `true`, but type theory doesn't allow us to do
so. And for clearly good reason.

In many programming languages, booleans are special and privileged, often baked
directly into the language. Being able to define them ourselves so trivially is
an early indication of the power of things to come.

Just as Dijkstra popularized the role of *structured programming* by arguing
programmers should not be writing jumps directly, we will note that real
programming does not get done by writing typing judgments directly (nor does
mathematics, for that matter.) Why is this?

You can imagine the chaos that might occur if someone added a new introduction
rule for `Bool`s, maybe:

```agda
    file-not-found : Bool
```

All of a sudden, our programs, carefully designed to handle only the binary case
of booleans, would now need to be retrofitted with extra logic to handle the
case of `file-not-found`. Such a possibility is anathema to the concept of
modular and composable programs --- those that we can write and prove correct
once, without needing to worry about what the future will bring.

Instead of allowing introduction rules anywhere at any time, we allow them only
in the context of a type declaration. Type declarations define the type and its
introduction forms all at once, in a closed way. This ensures nobody can come
along later and extend the type. While such a thing might sounds stifling at
first, please suspend your disbelief; it all works out in practice.

We give a type definition in Agda with the `data` keyword, followed by the
introduction form for the type itself, followed by the word `where`:

```agda
data Bool : Set where
```

and then inside, simply give the introduction forms for each value in the type:

```agda
  false : Bool
  true  : Bool
```

These introduction forms must be indented relative to the `data` keyword. And as
soon as this indentation is de-dented, the data type is finished. `Bool`s now
exist, with exactly two introduction forms in `false` and `true`,  and that's
all there is to say about that.

Whenever we'd like a closed "universe" of values, we can introduce a new type.
Say we're writing a drawing program and have a need to enumerate the primary
(additive) colors. Easy enough:

```agda
data PrimaryColor : Set where
  red   : PrimaryColor
  green : PrimaryColor
  blue  : PrimaryColor
```

Don't let the familiar names here fool you. We have introduced three values of
type `PrimaryColor`, but crucially, *we have said nothing about what colors
are.* We have just named a few, making the claim that they are distinct. Of
further dubiousness, we are also saying that these are *all* of the primary
colors. It would be misleading to call this type `Color`, because there are
infinitely many more colors than these three, but perhaps we will not get in
trouble saying that these three are the primary colors.

Simple data types like these fill the role of enums in many procedural
languages, and can be used anywhere you might think to use one. But do not be
fooled, data types are not enums; they are immensely more powerful and useful.

In what way are data types more powerful than simple enums? Unlike enums in
C-like languages, which are merely syntactic sugar over the integers, data types
are capable of storing other pieces of data inside of them. For example, perhaps
we really would like a three-state `Bool`. We can't call it `Bool` because that
name is already taken, but we can go with something similar:

```agda
data Tribool : Set where
  file-not-found : Tribool
  fromBool : Bool → Tribool
```

Here not only have we've brought back our old friend `file-not-found`, but also
added a new `fromBool` value. Remember the rule that says that whatever comes on
the right side of a colon must be the type, therefore `fromBool` must have type
`Bool → Tribool`. What does this mean?

The arrow says that `fromBool` is a transformation from `Bool`s into `Tribool`s.
In essence, it's a more convenient way of writing the following:

```wrong
data Tribool : Set where
  file-not-found : Tribool
  fromBool false : Tribool
  fromBool true  : Tribool
```

That is to say, there are exactly three introduction forms for `Tribool`s. We
have `file-not-found`, `fromBool false` and `fromBool true`. Tricks like these
are why I said earlier it's not limiting to have our types be closed; we can
always open them back up by making a new type with the extra structure we'd like
to see, and adding a constructor like `fromBool` to help "lift" one type into
the other.

The curious reader will wonder what happens if we make a recursive constructor
form. What would happen, for example, if we build the following type?

```agda
data N : Set where
  z : N
  s : N → N
```

What values of type `N` do we have? Well, we can enumerate them one at a time.
We have `z`. And if we'd like to use `s`, we need to transform some existing `N`
--- of which we only know `z`! Therefore `s z` is of type `N`. But now we know a
second value of type `N`, so we can also say that `s (s z)` is an `N`! You can
repeat this "application" of `s` as many times as you please, building ever
bigger, arbitrarily-deep chains of the form `s (s (... (s z)))`.

With a little creative renaming, we can see that what we have really done is
just define the *natural numbers:*

```wrong
data ℕ : Set where
  0 : ℕ
  1+ : ℕ → ℕ
```

It's a bit tedious to get anything done with this encoding of the natural
numbers (for example, 5 is necessarily written as `1+ (1+ (1+ (1+ (1+ 0))))`)
but you must agree that this does give us a means of generating every
non-negative whole number. It goes without saying that this is an extremely rare
feature in a programming language: not even *numbers* need to be built-in.

You are likely screaming right now. "That's a terribly inefficient way of
representing numbers! It will be too slow to do anything!" And you're absolutely
right, except that it misses the forest for the trees. This is not your fault;
it is a standard part of the education of all software engineers that
computational efficiency is of the utmost importance. And it is important, but
problems arise when we start ignoring simple, easily-comprehensible solutions.
So much of computing is lost to folklore that we often have forgotten that any
of our affordances were originally done in the name of efficiency, and worse,
"efficiency" which is often no longer relevant on modern hardware.

All of this is to say, ignore the computational stupidity for now. Stupid
solutions are much easier to put together than clever, optimized ones. And the
problems we intend to tackle in this book are sufficiently hard that our only
hope of making progress is to reason about simple structures and optimize only
at the end. But this is getting ahead of ourselves; we will see this technique
fleshed out in overwhelming amounts of detail in @sec:denotations.

### Data Structures

Closely related to the natural numbers are (rather surprisingly) a common data
structure: linked lists. The exact nature of this relationship we will not
explore right this instant, but the reader is encouraged to ponder it
themselves. For our purposes, a linked list contains zero or more nodes of the
same type. But which type? Any type you want, so long as you are consistent all
the way through the list.

We can define a linked list as follows, where we add a new `A : Set` parameter
to the type itself, parameterizing us over the type of the contents of the list.

```agda
data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

infixr 3 _∷_
```

We use the `[]` constructor to indicate an empty list, while the infix `_∷_`
operation allows us to stick an `A` value in front of an existing list. Thus, we
can make a `List` that enumerates our primary colors:

```agda
all-primary-colors : List PrimaryColor
all-primary-colors = red ∷ green ∷ blue ∷ []
```

Now that we have a flavor of implementing a data structure, let's see what other
data structures we can build. One particularly elegant data structure is the
*binary tree.* There are many variants of binary trees, but ours will keep data
only in the internal nodes.

A binary tree is thus parameterized by its contents:

```agda
data BinTree (A : Set) : Set where
```

and is either an empty tree:


```agda
  empty : BinTree A
```

or is an internal node, with subtrees on the left and right, and a piece of data
between them:

```agda
  branch : BinTree A → A → BinTree A → BinTree A
```

Recall that the last arrow indicates the resulting type, while every one before
the final arrow indicates a parameter. Thus `branch` has three parameters, its
left sub-tree `BinTree A`, data contents `A`, and a right sub-tree `BinTree A`.

Notice that all we are doing here is describing the *shape* of values of a data
structure. We are not implementing any of the interfaces or operations for
working with these structures. As it turns out, getting the shapes right is the
hard part; when those are in place, the operations come mostly "for free." All
of the work has been done in ensuring the necessary invariants hold at the
type-level.

This gives us a new way of thinking about types: they are maintainers of
invariants. For example, binary trees have the invariant that they are either
empty, or have a left and a right sub-tree. We have constrained the creation of
binary trees to always be exactly one of these cases --- you can either build
one out of `empty`, or one out of `branch`. It is impossible (and meaningless)
to construct a `BinTree` that has three immediate sub-trees.


Exercise

:   Give a type corresponding to a stack data structure. Does it remind you of
    anything?


Many programming languages have "the billion dollar mistake" --- a value called
`null` that lives as an extra inhabitant inside of every type. While `null` can
be convenient in some circumstances, primarily in cases of not-yet-initialized,
intentionally-excluded, or no-result, making it omnipresent in all types means
the programmer must be hyper vigilant. No matter how well-reasoned their code
is, there's always the possibility that something which logically must exist
could somehow be set to `null`.

In the type theory, we forbid the omnipresent `null`, while acknowledging that
it has its time and its place: the need to "extend" some other type with a
possible extra value corresponding to nothingness. As such, we can build a
nullable type in the same way that we built our silly `Tribool` earlier: just
extend a different type!

"Nullable" types are better known as `Maybe`, which are parameterized by the
desired "wrapped" type:

```agda
data Maybe (A : Set) : Set where
```

We have two ways of building a `Maybe A`; either you don't have an `A` in the
first place, in which case you have the "null" case:

```agda
  nothing : Maybe A
```

or you do in fact have an `A`, in which case you can build it via `just`:

```agda
  just : A → Maybe A
```

As a result, `nothing` isn't an inhabitant of `Bool`, but it *is* an inhabitant
of `Maybe Bool`. Dually, `true` isn't an inhabitant of `Maybe Bool`, but it has
an equivalent, `just true` which is. By being more rigid about what types things
have, we have completely eliminated an entire family of bugs. In this
formulation, there is no such thing as a forgotten null check; the check is
either impossible to write (in the case of `Bool`), or mandated (in the case of
`Maybe Bool` where it's impossible to be used as a `Bool` until you've proven it
isn't `nothing`.)


