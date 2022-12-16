# The Glory of Numbers

In this chapter, we will get our hands dirty, implementing some basic number
systems in Agda. The goal is threefold: to get some experience thinking about
how to model problems in Agda, to get some experience seeing familiar objects
with fresh eyes, and to get familiar with many of the mathematical objects
we'll need for the remainder of the book. As always, we start with a new module
for the chapter:

```agda
module 2-numbers where
```

As you might expect, Agda already has support for numbers, and they are not
things we necessarily need to build for ourselves. That being said, it's
important to get an intuition for how we can use Agda to solve problems, and
numbers are simultaneously a domain you already understand, and are usually
*built-in,* magical constructs in most programming languages. This is not true
in Agda: numbers are defined in the standard library. Our approach will be to
build the same number system exported by the standard library so we can peek at
how it's done. However, this is just an exercise; after this chapter, we will
just use the standard library's implementation, since it will be more complete,
and allow us better interopability when doing real work.


## Booleans

To begin, we will open a new module to sandbox our work, without needing to leak
our newly defined numbers into the global namespace. The simplest "number"
system are the booleans, so we will start our foray there.

```agda
module Sandbox-Bools where
```

We start by defining the booleans, which we can do by enumerating all of them,
of which there are only two:

```agda
  data Bool : Set where
    false : Bool
    true  : Bool
```

This definition creates a new type, `Bool`, and two *constructors* of that type,
`false` and `true`. It's important to note that all constructors of a type are
considered *distinct*. That is to say, `false` and `true` are two separate
things. All we have said about them thus far is that they exist, are both
`Bool`s, and are not equal to one another. In fact, we have also said that
*every* `Bool` is either `false` or `true` --- a direct consequence of the
semantics of data type constructors.

The simplest function over booleans is their negation, given by `not`:

```agda
  not : Bool → Bool
  not false = true
  not true  = false
```

This function gives us a taste of how we can do computation in Agda; on the left
side of the equals, we match on the distinct possibilities for our parameters,
and give a result for each on the right side of the equals sign.

Another simple operation over booleans is logical OR; that is, the result is
true if at least one of its arguments is true. Mathematicians often use the
symbol $\vee$ (pronounced "vel") for this operation, which we will follow, since
the goal is to define the same interface as is present in the Agda standard
library. This operator is used infix, which we can communicate to Agda by naming
the OR function `_∨_`:


```agda
  _∨⅋_ : Bool → Bool → Bool
  false ∨⅋ false = false
  false ∨⅋ true  = true
  true  ∨⅋ false = true
  true  ∨⅋ true  = true
```

Here we take the same approach as `not`; for each argument, we enumerate every
possibilities, giving the answer on the right side of the equals sign. You will
notice that this strategy grows enormously; a function of five booleans would
require 32 clauses to enumerate every possibility. Fortunately, this is not the
only way to define `_∨_`. We can instead throw some thought at the problem, and
realize the goal is to identify whether or not one of the arguments is `true`.
This doesn't require pattern matching on *both* parameter, we can get away
matching only on one.

If the argument we matched on is `true`, we're done, without looking at the
other argument. If our matched argument is `false`, then the result is `true` if
and only if the second argument is `true`. In neither case do we need to inspect
one of the arguments. We can take advantage of this fact by using a variable to
abstract over the second parameter. Instead, let us define `_∨_`

```agda
  _∨_ : Bool → Bool → Bool
  false ∨ other = other
  true  ∨ other = true
```

Here, because we wrote `other` rather than any of the constructors of `Bool`,
Agda knows we don't want to perform a pattern match, and instead have
introduced a new variable `other : Bool`. In the `false` case, we simply return
this argument, and in the `true` case we ignore it completely.

We can take the same approach to define the logical AND operation, which returns
`true` if and only if both of its arguments are `true`. Mathematicians use the
$\wedge$ symbol for this one, pronounced "wedge."

```agda
  _∧_ : Bool → Bool → Bool
  false ∧ y = false
  true  ∧ y = y
```

You are likely wondering why we're discussing booleans in a chapter about
defining number systems. The answer is that booleans behave a lot like numbers,
as we can show in a little test module.

```agda
  module Tests where
```

As a number system, the booleans have exactly two numbers, 0 and 1:

```agda
    0𝔹 : Bool
    0𝔹 = false

    1𝔹 : Bool
    1𝔹 = true
```

and, given these definitions, OR behaves exactly like addition, while AND takes
the place of multiplication:

```agda
    _+_ : Bool → Bool → Bool
    _+_ = _∨_

    _*_ : Bool → Bool → Bool
    _*_ = _∧_
```

To illustrate this, we will pull in Agda's testing machinery from
`Relation.Binary.PropositionalEquality`, and show that adding `0𝔹` doesn't
change the result, nor does multiplying `1𝔹` change the result --- exactly the
properties you'd expect to hold in a number system with only two values.

```agda
    open import Relation.Binary.PropositionalEquality

    0+-is-id : (x : Bool) → 0𝔹 + x ≡ x  -- ! 1
    0+-is-id x = refl

    1*-is-id : (x : Bool) → 1𝔹 * x ≡ x  -- ! 2
    1*-is-id x = refl
```

Take note of the line marked by [1](Ann), which we interpret as the mathematical
statement:

> for any `x : Bool`, it is the case that `0𝔹 + x` is equal to `x`

[2](Ann) makes a similar claim about the relationship between `1𝔹` and
multiplication. We will investigate how these strange-looking tests work in due
time; for now, be content with the fact that the booleans form a number system,
although admittedly, not a very interesting one.


## Natural Numbers

Booleans probably aren't the first thing that comes to mind when you think about
number systems. So let's instead build something a little more representative of
numbers: the *natural numbers.* The natural numbers are those non-negative whole
numbers that we use for counting: $0, 1, 2, 3, \dots$. Mathematicians describe
this set of numbers by the "blackbord bolded" symbol `ℕ`, which is the notation
we too will use.

The natural numbers are sometimes known as Peano numbers, named after Giuseppe
Peano, whose 1889 mathematical formulation of them has enjoyed wide popularity.
The first thing to note is that there are infinitely many natural numbers, which
means any attempt at formulating them cannot possibly be exhaustive; we'd tire
long before getting to the end! However, there is a natural starting point,
namely, zero. From there, we notice that given any natural number $n$, there
exists a "next" number $1 + n$. The pedants among readers might, fairly, object
to our usage of $1$ (and $+$, for that matter) in this formalization. Instead,
we can compress the $1 +$ part into a function `suc : ℕ → ℕ`, whose existence we
postulate, which constructs the "successive" number.

In Agda, we can build this set by introducing a new `data` type with two
introduction forms --- one for zero, and one for succession:

```agda
module Sandbox-Naturals where
  data ℕ : Set where
    zero : ℕ
    suc  : ℕ → ℕ
```

By repeated application of `suc`, we can build an infinite tower of natural
numbers, the first four of which are built like this:

```agda
  one : ℕ
  one = suc zero

  two : ℕ
  two = suc one

  three : ℕ
  three = suc two

  four : ℕ
  four = suc three
```

Of course, these names are just for syntactic convenience; we could have instead
defined `four` thusly:

```agda
  four⅋ : ℕ
  four⅋ = suc (suc (suc (suc zero)))
```

The simplest function we can write over the naturals is to determine whether or
not the argument is equal to 0. For the same of simplicity, this function will
return a boolean, but this is a bad habit in Agda thus this function is only
provided to help us get a feel for pattern matching over natural numbers.
Furthermore, rather than using our home-grown booleans, we will import them from
the standard library.

```agda
  open import Data.Bool

  n=0? : ℕ → Bool
  n=0? zero    = true
  n=0? (suc x) = false  -- ! 1
```

The `n=0?` function returns true if and only if its argument is `zero`. At
[1](Ann) we see another use of a variable in a pattern match, but this time it's
for the number the argument is one bigger than. Because there are an infinite
number of naturals, *it is impossible* to write this function exhaustively. We
therefore are forced to use a variable to describe every other possibility,
which is OK because we'd like to handle them in identical ways, namely returning
`false`.

A more natural function to define over `ℕ` is addition. Again, we are unable
(and wouldn't want) to build a table explicitly giving the result for every
possible pair of inputs. Instead we must be more clever, and take inspiration
from the booleans, noticing that adding `zero` to anything doesn't change the
result. If the input wasn't zero, it was one more than some other value $x$; in
which case we can add $x$ to the right hand side, and take the `suc` afterwards.

```agda
  _+_ : ℕ → ℕ → ℕ
  zero  + y = y
  suc x + y = suc (x + y)  -- ! 1
```

Convince yourself that `_+_` correctly implements addition before continuing.

There is a subtle point to be made here. Notice at [1](Ann) the right hand side
is written as `suc (x + y)`; you might wonder if those parentheses are strictly
necessary. In fact, they are. Without those parentheses, our equation turns into
`suc x + y = suc x + y`, which you will notice has the exact express on both
sides of the equals sign. While this statement is mathematically true, it is
computationally worthless. Behind the scenes, Agda is silently rewriting the
left hand sides of these equalities as the right hand sides whenever it comes
across one. So a definition of the form `x = x` puts Agda into a loop, trying
forever to make progress computationally. Fortunately, Agda is smart enough to
identify this case, and will holler, complaining about "termination checking,"
if you attempt to do it:

```error
2-numbers.lagda.md:258,3-260,24
Termination checking failed for the following functions:
  Sandbox-Naturals._+_
Problematic calls:
  suc x + y
    (at 2-numbers.lagda.md:260,21-22)
```

By putting in the parentheses, `suc (x + y)` is now recursive, and, importantly,
it is recursive on *structurally smaller* inputs than it was given. Since the
recursive call must be smaller (in the sense of there is one fewer `suc` to
worry about,) eventually this recursion must terminate, and thus Agda is happy.
We can tie a little bow on `_+_` by giving a hint to Agda about how to parse it,
saying it should nest to the left with precedence 5:

```agda
  infixl 5 _+_
```



```agda
  infixl 5 _∸_
  _∸_ : ℕ → ℕ → ℕ
  x     ∸ zero  = x
  zero  ∸ suc y = zero
  suc x ∸ suc y = x ∸ y

  infixl 6 _*_
  _*_ : ℕ → ℕ → ℕ
  x * zero = zero
  x * suc y = (x * y) + x

  module Tests where
    open import Relation.Binary.PropositionalEquality

    _ : one + one ≡ two
    _ = refl

    _ : two * two ≡ four
    _ = refl

    suc-is-one+ : (x : ℕ) → one + x ≡ suc x
    suc-is-one+ x = refl
```

```agda
module Integers where
  import Data.Nat as ℕ
  open ℕ using (ℕ)

  data ℤ : Set where
    +_ : ℕ → ℤ
    -[1+_] : ℕ → ℤ

  0ℤ : ℤ
  0ℤ = + 0

  1ℤ : ℤ
  1ℤ = + 1

  -1ℤ : ℤ
  -1ℤ = -[1+ 0 ]

  suc : ℤ → ℤ
  suc (+ x) = + ℕ.suc x
  suc -[1+ ℕ.zero ] = 0ℤ
  suc -[1+ ℕ.suc x ] = -[1+ x ]

  pred : ℤ → ℤ
  pred (+ ℕ.zero) = -1ℤ
  pred (+ ℕ.suc x) = + x
  pred -[1+ x ] = -[1+ ℕ.suc x ]

  pattern +0 = + 0
  pattern +[1+_] n = + (ℕ.suc n)

  -_ : ℤ → ℤ
  - (+0) = +0
  - +[1+ x ] = -[1+ x ]
  - -[1+ x ] = +[1+ x ]


  infixl 5 _+_
  _+_ : ℤ → ℤ → ℤ
  +0             + y              = y
  +[1+ x       ] + +0             = +[1+ x ]
  -[1+ x       ] + +0             = -[1+ x ]
  +[1+ ℕ.zero  ] + -[1+ ℕ.zero  ] = +0
  -[1+ ℕ.zero  ] + +[1+ ℕ.zero  ] = +0
  +[1+ x       ] + +[1+ y       ] = +[1+ ℕ.suc (x ℕ.+ y) ]
  -[1+ x       ] + -[1+ y       ] = -[1+ ℕ.suc (x ℕ.+ y) ]
  +[1+ ℕ.suc x ] + -[1+ ℕ.zero  ] = +[1+ x ]
  -[1+ ℕ.zero  ] + +[1+ ℕ.suc y ] = +[1+ y ]
  +[1+ ℕ.zero  ] + -[1+ ℕ.suc y ] = -[1+ y ]
  -[1+ ℕ.suc x ] + +[1+ ℕ.zero  ] = -[1+ x ]
  +[1+ ℕ.suc x ] + -[1+ ℕ.suc y ] = +[1+ x ] + -[1+ y ]
  -[1+ ℕ.suc x ] + +[1+ ℕ.suc y ] = -[1+ x ] + +[1+ y ]

  infixl 5 _-_
  _-_ : ℤ → ℤ → ℤ
  x - y = x + (- y)

  infixl 6 _*_
  _*_ : ℤ → ℤ → ℤ
  x * +0             = +0
  x * +[1+ ℕ.zero  ] = x
  x * -[1+ ℕ.zero  ] = - x
  x * +[1+ ℕ.suc y ] = (+[1+ y ] * x) + x
  x * -[1+ ℕ.suc y ] = (-[1+ y ] * x) - x

  module Tests where
    open import Relation.Binary.PropositionalEquality

    _ : - (+ 2) * - (+ 6) ≡ + 12
    _ = refl

    _ : (+ 3) - (+ 10) ≡ - (+ 7)
    _ = refl



```

