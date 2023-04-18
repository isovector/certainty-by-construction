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

```agda
module Sandbox-Bools where
```

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

```agda
  not : Bool → Bool
  not false = true
  not true  = false
```

```agda
  _∨_ : Bool → Bool → Bool
  false ∨ other = other
  true  ∨ other = true
```

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
this set of numbers by the "blackboard bolded" symbol `ℕ`, which is the notation
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

The natural numbers don't support subtraction, because we might try to take too
much away and be forced to go negative, but there are no negative natural
numbers. However, we have a closely related operation, subtraction with
*truncation* at zero --- that is, if the result should be negative, it is
instead zero. We call this operation "monus", and use the symbol `_∸_`.


Exercise

: Define `_∸_ : ℕ → ℕ → ℕ`


Solution

:   ```agda
  _∸_ : ℕ → ℕ → ℕ
  x     ∸ zero  = x
  zero  ∸ suc y = zero
  suc x ∸ suc y = x ∸ y
    ```

The last operation we will implement for natural numbers is multiplication,
which sounds like it might be hard until you remember that multiplication is
just repeated addition, which we define as follows:

```agda
  infixl 6 _*_
  _*_ : ℕ → ℕ → ℕ
  zero  * y = zero
  suc x * y = (x * y) + y
```

Just to convince ourselves everything works, let's write a few unit tests:

```agda
  module Tests where
    open import Relation.Binary.PropositionalEquality

    _ : one + two ≡ three
    _ = refl

    _ : three ∸ one ≡ two
    _ = refl

    _ : one ∸ three ≡ zero
    _ = refl

    _ : two * two ≡ four
    _ = refl
```

You can find all of these goodies, and significantly more, in the standard
library's `Data.Nat` module. Additionally, you also get support for natural
literals, that is, you get digital representations for every number. No more
`four : ℕ`; just use `4 : ℕ`!

By this point, you should be starting to get a good handle on the basics of Agda
--- both syntactically, as well as how we think about modeling and solving
problems. In the next section we will tackle the integers, which have much more
interesting mathematical structure, and subsequently, present many more
challenges.


## Integers

The integers extend the natural numbers by reflecting them onto the negative
side of the axis as well. Our number line now goes off to infinity in two
directions, towards infinity and towards negative infinity. Some of the
integers then, are $\dots, -3, -2, -1, 0, 1, \dots$. We use the blackboard bold
notation `ℤ` to represent the set of integers, which might seem like a strange
choice until you learn the German word for "number" is *Zahl.*

Mathematically, we say the integers are an *extension* of the natural numbers.
That is, every natural number can be thought of as an integer, but there are
some (infinitely many) integers that do not correspond to any natural. When
modeling this problem in Agda, it would be nice if we could reuse the machinery
we just built for natural numbers, rather than needing to build everything again
from scratch. Before building integers the right way, we will first take an
intentional wrong turn, to clarify some issues around data modeling in Agda.

Let's put our misstep in a new module so as to not confuse ourselves when we
"rollback" the idea. By analogy with `ℕ`, which contains `zero` and `suc`,
perhaps `ℤ` also has a constructor `pred` which we interpret as "subtracting
one:"

```agda
module Naive-Integers₁ where
  data ℤ : Set where
    zero : ℤ
    suc  : ℤ → ℤ
    pred : ℤ → ℤ
```

The problem with this approach, is that numbers no longer have a unique
representation. For example, there are now infinitely many ways of representing
`zero`, the first three of which are:

* `zero`
* `pred (suc zero)`
* `suc (pred zero)`

Recall that constructors are always distinct from one another, and furthermore,
that they never compute to anything other than themselves. We could plausibly
try to fix this problem by writing a function `normalize`:

```agda
  normalize : ℤ → ℤ
  normalize zero = zero
  normalize (suc zero) = suc zero
  normalize (suc (suc x)) = suc (normalize (suc x))
  normalize (suc (pred x)) = normalize x
  normalize (pred zero) = pred zero
  normalize (pred (suc x)) = normalize x
  normalize (pred (pred x)) = pred (normalize x)
```

which attempts to recursively "cancel out" subsequent applications of `pred` and
`suc`. However, it's unclear prima facie whether this function correctly
normalizes all integers (it doesn't,) and, even if it did, the resulting
ergonomics would be too atrocious to use in the real world. The important
takeaway from this wrong turn is to strive for unique representations of data
whenever possible.

Our first attempt doesn't work. Let's take another misstep to see what else can
go wrong when trying to build the integers. Maybe this time we can reuse the
natural numbers, and build integers merely by determining whether the natural is
postive or negative:

```agda
module Naive-Integers₂ where
  open import Data.Nat

  data ℤ : Set where
    +_ : ℕ → ℤ
    -_ : ℕ → ℤ
```

This approach is much more satisfying than our previous attempt; it allows us to
reuse the machinery we wrote for natural numbers, and requires us only to wrap
them with a tag. The syntax is a little weird, but recall that the underscores
correspond to syntactic "holes," meaning the following are all acceptable
integers:

```agda
  _ : ℤ
  _ = - 2

  _ : ℤ
  _ = + 6
```

Note that the spaces separating `-` from `2`, and `+` from `6` are *necessary.*
Agda will complain very loudly, and rather incoherently, if you forget them.

While our second approach dramatically improves on the syntax of integers and
eliminates most problems from `Naive-Integers₁`, there is still one small issue
--- there are now two (and exactly two) representations of zero:

```agda
  _ : ℤ
  _ = + 0

  _ : ℤ
  _ = - 0
```

Perhaps there are some number systems in which it's desirable to have (distinct)
positive and negative zeroes, but this is not one of them. Unfortunately, our
second attempt at defining the integers is also flawed, but it points us in the
right direction. Really, the only problem here is our *interpretation of the
syntax.* This brings us to our third, and final implementation for the integers:

```agda
module Sandbox-Integers where
  import Data.Nat as ℕ
  open ℕ using (ℕ)

  data ℤ : Set where
    +_     : ℕ → ℤ
    -[1+_] : ℕ → ℤ
```

You'll notice this definition of `ℤ` is identical to the one from
`Naive-Integers₂`; the only difference is that we've renamed `-_` to `-[1+_]`.
This new name suggests the numbers are one "more negative" than the wrapped
natural would otherwise indicate. We can then name three particularly
interesting integers:

```agda
  0ℤ : ℤ
  0ℤ = + 0

  1ℤ : ℤ
  1ℤ = + 1

  -1ℤ : ℤ
  -1ℤ = -[1+ 0 ]
```

The constructed form of `-1ℤ` is a little wordy, but successfully eliminates the
"double zero" problem we had before. Of course, we'd still like our `suc` and
`pred` functions that we postulated our first time around, and we can now
articulate these as computations:

```agda
  suc : ℤ → ℤ
  suc (+ x)          = + ℕ.suc x
  suc -[1+ ℕ.zero  ] = 0ℤ
  suc -[1+ ℕ.suc x ] = -[1+ x ]
```

If `suc`'s argument is positive, it makes it more positive. If it's negative, it
makes it less negative, possibly producing zero in the process. Dually, we can
define `pred` which makes its argument more negative:

```agda
  pred : ℤ → ℤ
  pred (+ ℕ.zero) = -1ℤ
  pred (+ ℕ.suc x) = + x
  pred -[1+ x ] = -[1+ ℕ.suc x ]
```

It might be desirable to negate an integer; turning it negative if it's
positive, and vice versa. `-_` is a natural name for this operation, but its
implementation is not particularly natural:

```agda
  ⅋-_ : ℤ → ℤ
  ⅋- (+ ℕ.zero)  = 0ℤ
  ⅋- (+ ℕ.suc x) = -[1+ x ]
  ⅋- -[1+ x ]    = + ℕ.suc x
```

When converting back and forth from positive to negative, there's this annoying
`ℕ.suc` that we need to be careful to not forget about. This annoyance is an
artifact of the encoding we chose; which has the benefit of having unique
representations of all numbers, at the cost of not being *symmetric* in how it
treats positive and negative numbers. To work around this problem, Agda has
support for writing custom patterns, that is, other ways of deconstructing data.

We can define these pattern synonyms via the `pattern` keyword, and give a
rewrite rule with the desired name of the pattern on the left, and what it
should expand to on the right:

```agda
  pattern +0 = + 0
  pattern +[1+_] n = + (ℕ.suc n)
```

These two patterns give us symmetry when working with integers. While before we
had to pattern match into two cases, `+_` and `-[1+_]`, we can now instead
choose to match into *three* cases: `+0`, `+[1+_]` and `-[1+_]`. We can rewrite
the `-_` function with this new capability, which provides a significantly more
elegant implementation:

```agda
  -_ : ℤ → ℤ
  - +0       = +0
  - +[1+ x ] = -[1+ x ]
  - -[1+ x ] = +[1+ x ]
```

Finally, the moment we've all been waiting for; it's time to implement addition
over integers. Doing so is a particularly finicky thing --- there are lots of
ways in which positive and negative integers can interact! Fortunately, a lot of
the work is duplicated by virtue of addition being commutative, that is, the
answer is the same regardless of whether we write $a + b$ or $b + a$. Therefore,
we present addition of integers in pairs that are easy to check the equivalence
of.

First, additing zero to anything doesn't change the result:

```agda
  infixl 5 _+⅋_
  _+⅋_ : ℤ → ℤ → ℤ
  +0             +⅋ y              = y
  +[1+ x       ] +⅋ +0             = +[1+ x ]
  -[1+ x       ] +⅋ +0             = -[1+ x ]
```

These last two cases would be more naturally written as `x + +0 = x`, but we are
forced to expand out `x` for technical reasons. Continuing on, we come across
the case in which we're adding negative one to positive one:

```agda
  +[1+ ℕ.zero  ] +⅋ -[1+ ℕ.zero  ] = +0
  -[1+ ℕ.zero  ] +⅋ +[1+ ℕ.zero  ] = +0
```

Otherwise, both arguments are positive or both negative, in which case we just
add their underlying naturals (being careful to `ℕ.suc` the result, since we
have two `1+`s on the left side!)

```agda
  +[1+ x       ] +⅋ +[1+ y       ] = +[1+ ℕ.suc (x ℕ.+ y) ]
  -[1+ x       ] +⅋ -[1+ y       ] = -[1+ ℕ.suc (x ℕ.+ y) ]
```

The next pair of cases is what happens if we are adding a negative one, in which
case it must cancel out a positive `ℕ.suc`:

```agda
  +[1+ ℕ.suc x ] +⅋ -[1+ ℕ.zero  ] = +[1+ x ]
  -[1+ ℕ.zero  ] +⅋ +[1+ ℕ.suc y ] = +[1+ y ]
```

Analogously, if we're adding a positive one:

```agda
  +[1+ ℕ.zero  ] +⅋ -[1+ ℕ.suc y ] = -[1+ y ]
  -[1+ ℕ.suc x ] +⅋ +[1+ ℕ.zero  ] = -[1+ x ]
```

The final case, is if we are adding a positive `ℕ.suc` to a negative `ℕ.suc`, in
which case the two cancel each other out and we add the remaining terms:

```agda
  +[1+ ℕ.suc x ] +⅋ -[1+ ℕ.suc y ] = +[1+ x ] +⅋ -[1+ y ]
  -[1+ ℕ.suc x ] +⅋ +[1+ ℕ.suc y ] = -[1+ x ] +⅋ +[1+ y ]
```

What a headache! Who knew addition could be this hard? The good news is that I
didn't have to figure this all out on my own; Agda was extremely helpful. I
simply wrote the first line, and then thought to myself whether I could solve
the problem from there. If I could, great! If I couldn't, I asked Agda to split
one of the variables for me, which generated some new, more specific cases.
Rinse and repeat until all the holes are filled and everyone is happy.

While this is the most straightforward way to write `_+_` it falls somewhat
flat. The problem is that `_+_`, as written, needs to perform significant
inspection of its arguments in order to compute the result. As a general
principle, significant inspection is an antipattern, as it will require
duplicating all of that same effort in every subsequent proof. A better
technique is to separate out the logic for subtraction of natural numbers into
its own function:

```agda
  _⊝_ : ℕ.ℕ → ℕ.ℕ → ℤ
  _⊝_ ℕ.zero ℕ.zero = +0
  _⊝_ ℕ.zero (ℕ.suc n) = -[1+ n ]
  _⊝_ (ℕ.suc m) ℕ.zero = +[1+ m ]
  _⊝_ (ℕ.suc m) (ℕ.suc n) = m ⊝ n
```

By implementing `_+_` in terms of `_⊝_`, we can factor out a significant portion
of the logic:

```agda
  infixl 5 _+_

  _+_ : ℤ → ℤ → ℤ
  (+ x)    + (+ y)    = + (x ℕ.+ y)
  (+ x)    + -[1+ y ] = x ⊝ ℕ.suc y
  -[1+ x ] + (+ y)    = y ⊝ ℕ.suc x
  -[1+ x ] + -[1+ y ] = -[1+ x ℕ.+ ℕ.suc y ]
```

This new definition of `_+_` is significantly shorter and more regular. As a
bonus, it shows the addition of positive and negative cases are both calls to
`_⊝_`, albeit with the order of the arguments flipped. This will make our lives
significantly easier when we go to prove facts about `_+_` in the next chapter.

Having implemented addition is the hard part. We can implement subtraction
trivially, via addition of the negative:

```agda
  infixl 5 _-_
  _-_ : ℤ → ℤ → ℤ
  x - y = x + (- y)
```

Last but not least, we can define multiplication, again as repeated addition.
It's a little trickier this time around, since we need to recurse on positive
and negative multiplicands, but the cases are rather simple. Multiplication by
zero is zero:


```agda
  infixl 6 _*_
  _*_ : ℤ → ℤ → ℤ
  x * +0             = +0
```

Multiplication by positive or negative one transfers the sign:

```agda
  x * +[1+ ℕ.zero  ] = x
  x * -[1+ ℕ.zero  ] = - x
```

and finally, we can perform repeated addition or subtraction:

```agda
  x * +[1+ ℕ.suc y ] = (+[1+ y ] * x) + x
  x * -[1+ ℕ.suc y ] = (-[1+ y ] * x) - x
```

Thankfully, our hard work is rewarded when the unit tests agree that we got the
right answers:

```agda
  module Tests where
    open import Relation.Binary.PropositionalEquality

    _ : - (+ 2) * - (+ 6) ≡ + 12
    _ = refl

    _ : (+ 3) - (+ 10) ≡ - (+ 7)
    _ = refl
```

This is quite a marvelous achievement. In this chapter we've defined three
number systems, in order of increasing complexity and challenge. While there are
many more number systems we could build: the rationals, the reals, the complex
numbers, to name some famous ones, we will leave it here. Instead, we will turn
our attention in the next chapter to the notion of proof, and learn how to do
better than unit tests to show our code works as expected.

