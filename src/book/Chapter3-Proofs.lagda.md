# Proof Objects {#sec:proofs}

Hidden

:   ```agda
{-# OPTIONS --allow-unsolved-metas #-}
    ```

```agda
module Chapter3-Proofs where
```


Prerequisites

:   ```agda
import Chapter2-Numbers
    ```


My first encounter with mathematical proofs was in a first-year university
algebra course, where I immediately realized I had no idea what was going on.
The reasoning that seemed perfectly convincing to me was much less so to
whomever was in charge of assigning my grade. I didn't do well in that course,
or any subsequent ones.

The problem was that I didn't know what steps needed to be justified, and which
could be taken for granted. Thankfully, doing proofs in Agda makes this
exceptionally clear---either your proof typechecks, or it doesn't. In either
case, the feedback cycle is extremely quick, and it's easy to iterate until
you're done.

In this chapter we will take our first looks at what constitutes a proof and see
how we can articulate them in Agda. In the process, we will need to learn a
little more about Agda's execution model and begin exploring the exciting world
of dependent types.


## Constructivism

It is worth noting that the mathematics in this book are not the "whole story"
of the field. You see, there are two camps in the world of math: the
*classicists* and the *constructivists.* Much like many religious sects, these
two groups have much more in common than they have distinct. In fact, the only
distinction between these two groups of truth-seekers is their opinion on the
nature of falsities.

The classicists---the vast majority---believe all mathematical statements are
partitioned those which are *true* those which are *false.* There is simply no
middle ground. This opinion certainly doesn't sound controversial, but it does
admit odd tactics for proving things. One common proof technique in the
classical camp is to show that something *can't not* exist, and therefore
deducing that it does.

Contrast the classicists with the constructivists, who trust their eyes more
than they trust logical arguments. Constructivists aren't happy knowing
something merely doesn't not exist; they'd like to see the thing for themselves.
Thus, the constructivists insist that a proof actually build the object in
question, rather than just show it must be there with no clues towards actually
finding the thing.

In general, there are two ways to mathematically show something exists. The
first way is to just build the thing, in sense "proof by doing." The other is to
show that a world without the thing would be meaningless, and thus show its
existence---in some sense---by sheer force of will, because we really *don't*
want to believe our world is meaningless.

To illustrate this difference, suppose we'd like to prove that there exists a
prime number greater than 10. Under a classical worldview, a perfectly
acceptable proof would go something like this:

1. Suppose there does not exist any prime number greater than 10.
2. Therefore, the prime factorization of every number must consist only of 2, 3,
   5, and 7.
3. If a number $n$ has a prime factor $d$, then $n + 1$ does not have have $d$ as
   a prime factor.
4. The number $2 \times 3 \times 5 \times 7 = 210$ has prime factors of 2, 3, 5,
   and 7.
5. Therefore, $210 + 1 = 211$ does not have prime factors of 2, 3, 5, or 7.
6. Therefore, 211 has no prime factors.
7. This is a contradiction, because all numbers have prime factors.
8. Therefore, there does exist a prime number greater than 10. ∎

Contrast this against a constructive proof of the same proposition:

1. 11 is divisible by no number between 2 and 10.
2. Therefore, 11 is a prime number.
3. 11 is a number greater than 10.
4. Therefore, there exists a prime number greater than 10. ∎

Classical arguments are allowed to assume the negation, show that it leads to
absurdity, and therefore refute the original negation. But constructive
arguments are *required* to build the object in question, and furthermore to
take on the burden to show that it satisfies the necessary properties. The
classicists will accept a constructive argument, while the constructivists
*insist* on one.

Under a computational setting, constructive arguments are much more compelling
than classical ones. This is because constructive arguments correspond to
objects we can hold in our hands (or, at least, in memory), while classical
arguments can come from counterfactual observations. To put it another way,
constructive arguments correspond directly to *algorithms.*


## Statements are Types; Programs are Proofs

Having studied our programming language in @sec:chapter1 and looked at some
simple mathematical objects in @sec:chapter2, let's now turn our focus towards
more fundamental mathematical ideas. When most people think of math, their minds
go immediately to numbers. But of course, mathematics is a field significantly
larger than numbers, and we will touch upon them only briefly in the remainder
of this chapter.

But if numbers are not the focus of mathematics, then what *is*? In the opinion
of this author, it's the process of clear, logical deduction around precise
ideas. Numbers are one such precise idea, but they are by no means the only.
Some common other examples are the booleans, graphs, and geometry. Some less
examples less often considered math are digital circuits, and computer programs.
Anything you can define precisely and manipulate symbolically can fall under the
purview of mathematics when done right.

In math, it's common to differentiate between *statements* and *theorems.*
Statements are claims you can make, while theorems are claims you can prove. For
example, it's a perfectly valid statement that $2 = 3$, but such a claim isn't a
theorem under any any usual definitions for 2, 3, or equality. Occasionally,
you'll also hear statements called *propositions,* but this word is amazingly
overloaded, and we will not adopt such usage.

Of particular interest to us are theorems, which by necessity are made of two
parts: a statement and a *proof* of that statement. While two mathematicians
might disagree on whether they think a statement is true, they must both agree a
theorem be true. That is the nature of a theorem, that it comes with a proof,
and a proof must be convincing in order to warrant such a name.

There is a very apt analogy to software here. It's very easy to believe a
problem can't be solved. That is, of course, until someone hands you the
algorithm that does it. The algorithm itself is a proof artifact that shows the
problem can be done, and it would be insanity to disagree in the presence of
such evidence.

It is exactly this analogy that we will exploit for the remainder of this book
in order to show the relationship between mathematics and programming. In doing
so, we will help programmers use the tools they already have, in order to to
start being productive in mathematics. But let's make the connection more
formal.

To be very explicit, our analogy equates *mathematical states* and
*types.* That is to say, any mathematical statement can be encoding as a type,
and every type can be interpreted as a mathematical statement. Furthermore,
every theorem of a statement corresponds to a *program with that type,* and
every program is a proof of the statement. As an extremely simple example, we
can say that the type `type:Bool` corresponds to the proposition "there exists a
boolean." This is not a particularly strong claim.

Under a constructive lens, we can prove the proposition merely by proving a
boolean, thus proving at least one exists. Therefore, the term `ctor:true` is a
proof of `type:Bool`.

Such a simple example doesn't provide much illumination. Let's try something
more complicated. Recall our `type:IsEven` type from @sec:even, which we can
bring back into scope:

```agda
module Example-ProofsAsPrograms where
  open Chapter2-Numbers.Exports.Naturals
    using (ℕ; IsEven)
```

Every type forms a module containing its constructors and fields, so we can open
both of `module:ℕ` and `module:IsEven` to get the relevant constructors out:

```agda
  open ℕ
  open IsEven
```

We can then form a statement asking whether zero is even by constructing the
type:

```agda
  zero-is-even : IsEven zero
```

Of course, zero *is* even, the proof of which we have seen before:

```agda
  zero-is-even = zero-even
```

Because we have successfully implemented `def:zero-is-even`, we say that
`def:zero-is-even` is a theorem, and that it a proof of `expr:IsEven zero`.

To drive the point home, we can also try asking one is an even number:

```agda
  one-is-even : IsEven (suc zero)
  one-is-even = ?
```

However, as we saw in @sec:evens, there is no way to fill this hole. Therefore,
`def:one-is-even` cannot be implemented, and therefore it is not a
theorem---even though `expr:IsEven (suc zero)` is a perfect acceptable
statement.

In the context of values (programs) and types, we will adopt some extra
terminology. We say that a type is *inhabited* if there exists at least one
value of that type. Therefore, `type:Bool` and `expr:IsEven zero` are both
inhabited, while `expr:IsEven (suc zero)` is not.

Under a constructive lens, it is exactly those statements for which we have a
proof that can be said to be true. In other words, truth is synonymous with
being inhabited.

These examples all illustrate the point: while we can always write down the type
of something we'd like to prove, we cannot always find a value with that type.
Therefore, we say that types correspond to statements, while values are proofs
of those statements. In the literature, this concept is known by the name *types
as propositions,* and as the *Curry--Howard correspondence.*

The Curry--Howard correspondence thus gives us a guiding principle for doing
constructive mathematics in a programming language. We "simply" write down the
problem, encoding the statement as a type, and then we work hard to construct a
value of that type. In doing so, we show the truth of the original problem
statement. Keeping this perspective in mind is the secret to success.


## Hard to Prove or Simply False?

Of course, this abstract discussion around the Curry--Howard isomorphism makes
the whole business seem much less messy than it is in practice. It's one thing
to discuss whether a type is inhabited, and a very different thing to actually
produce a value for a given type. Every example we've seen so far has made the
job seem trivial, but attempting to produce an inhabitant has driven many to the
brink of madness.

What's so hard here, you might wonder. The problem is, when you're not making
much process, it's hard to tell whether you're merely taking the wrong approach,
or whether the task at hand is *literally impossible.*

Of the absolute utmost importance in mathematics is the *principle of
consistency.* This is a fancy way of saying "there should be no proof of false
things." Math is a tool for exploring truths about platonic abstractions, and
being able to derive a proof of false would be devastating to the entire
endeavor. The reason we care so much about this is that falsities beget
falsities. If you ever get your hands on one, you can use it to produce a
second.

You've probably seen the classic "proof" that $1 = 2$. It goes like this:

Let $a = b$, then

$$
\begin{aligned}
& ab &= a^2 \\
\therefore \quad &  ab - b^2 &= a^2 - b^2 \\
& &= (a + b)(a - b) \\
\therefore \quad & b(a - b) &= (a + b)(a - b) \\
\therefore \quad & b &= a + b \\
& &= b + b \\
& &= 2b \\
\therefore \quad & 1 &= 2
\end{aligned}
$$

The actual flaw in reasoning here is on line 5, when we cancel $a - b$ from both
sides of the equation. Recall that $a = b$, so $a - b = 0$, and thus this is an
implicit division by zero.

To see how we can use one false proof to get another, consider now Pythagoras'
famous theorem about the side lengths of triangles:

$$
a^2 + b^2 = c^2
$$

But since we have already "proven" that $1 = 2$, we can therefore "derive" the
fact that:

$$
a + b = c
$$

Whoops! As you can see, as soon as we manage to prove something false, all bets
are off. In English, this property is known as the *principle of explosion* in
English, but you can also call it *ex falso quodlibet* if you're feeling
particularly regal. All this means is that, given a proof of false, you can
subsequently provide a proof of anything. Therefore, contradictions are *really,
really* bad, and a huge chunk of logical development (including computation
itself) has arisen from scholars discovering contradictions in less rigorous
mathematics than what we use today.

All of this is to say: it's desirable that it be very difficult to prove
something that is false. From afar, this sounds like a very good and righteous
desideratum. But when you're deep in the proof mines, having difficulties
eliciting the sought-after proof, it's often unclear whether you haven't tried
hard enough or whether the problem is impossible outright. I myself have spent
*weeks* of my life trying to prove a false statement without realizing it. I
suspect this is a necessary rite of passage.

Nevertheless, I hope you spare you from some of the toil spent wasted on a false
proposition. If you're ever finding a proof to be exceptionally hard, it's
worth taking some time out to prove the proposition for extremely simple,
concrete values. For example, when you're working with numbers, see if it holds
when everything is zero or one. Working through the easiest cases by hand will
usually point out a fundamental problem if there is one, or might alert you to
the fact that you haven't yet built enough machinery (that is, library code
around your particular problem) to make proving things easy.

Remember, you can always prove something the stupid way first, and come back
with a better proof later on if you deem necessary. In proofs as in life, "done"
is better than "perfect."


## The Equality Type {#sec:propeq}

All of this discussion about encoding statements as types is fine and dandy, but
how do we go about actually *building* these types? Usually the technique is to
construct an indexed type whose indices constrain what we can do, much like we
did with `type:IsEven`.

One of the most common mathematical statements---indeed, often synonymous with
math in school---is the *equation.* Equality is the statement that two different
objects are, and always were, just one object. There is a wide and raging debate
about exactly what equality *means,* but for the time being we will limit
ourselves to the case that the two expressions will eventually *evaluate to the
exact same tree of constructors.* This particular notion of equality is known as
*propositional equality* and is the basic notion of equality in Agda.

As I said, the word "proposition" is extremely overloaded with meanings, and
this usage has absolutely nothing to do with the idea of *propositions as types*
discussed earlier. Instead, here and everywhere in the context of Agda,
*proposition* means "inhabited by at most one value." That is, `type:Bool` is
not a proposition, because it can be constructed by either of the two booleans.
On the other hand, `expr:IsEven zero` is a proposition, because its *only* proof
is `ctor:zero-even`.

We can define propositional equality by making a type for it. The type should
relate two objects stating that they are equal. Thus it must be *indexed by
two values.* These indices correspond to the two values being related. In order
for two things to evaluate to the same constructors, they must have the same
type. And because we'd like to define propositional equality once and for all,
we will parameterize this equality type by the type of things it relates. Solving
all these constraints simultaneously gives us the following `keyword:data` type:

```agda
module Definition where
  data _≡_ {A : Set} : A → A → Set where
    refl : {x : A}
        → x ≡ x
```


Hidden

:   ```agda
  -- fix indentation for expr
    ```

Recall that the `≡` symbol is input as [`==`](AgdaMode).

The type of `ctor:refl` here, `bind:A:{x : A} → x ≡ x`, says that for any value
`x` we'd like, we know only that `x` is equal to itself. The name `ctor:refl` is
short for *reflexivity,* which is technical jargon for the property that *all
things are equal to themselves.* We shorten reflexivity to `ctor:refl` because
we end up writing this constructor *a lot.*

That's the type of `ctor:refl`, which happens to be the only constructor of
this data type. But consider the type `bind:x y:x ≡ y`---it's a statement that
`x` and `y` in fact evaluate to the same tree of constructors. Whether or not
this is actually true depends on whether the type is actually inhabited, which
it is only when `x` and `y` both compute to the same thing. It is only in this
case that we can convince Agda that `ctor:refl` is an inhabitant, because
`ctor:refl` *requires* that both of the type indices be `x`.

We'll play with this type momentarily to get a feeling for it. But first we have
a little more bookkeeping to do. In order to play nicely with standard
mathematical notation, we'd like `type:_≡_` to bind very loosely, that is to
say, to have a low precedence. Furthermore, we do not want `type:_≡_` to
associate at all, so we can use `keyword:infix` without a left or right suffix
to ensure the syntax behaves as desired.

```agda
  infix 4 _≡_
```

We have already encountered `type:_≡_` and `ctor:refl` in @sec:chapter1 where we
called them "unit tests." This was a little white-lie. In fact, what we were
doing before with our "unit tests" was proposing the equality of two terms, and
giving a proof of `ctor:refl` to show they were in fact equal.

Because Agda will automatically do as much computation and simplification as it
can, for any two concrete expressions that result in equal constructors, Agda
will convince itself of this fact. As a practical technique, we often can (and
do) write little unit tests of this form. But, as we will see in a moment, we
can use propositional equality to assert much stronger claims than unit tests
are capable of determining.

Let's play around with our equality type to get a feel for what it can do.

```agda
module Playground where
  open import Relation.Binary.PropositionalEquality
    using (_≡_; refl)

  open Chapter2-Numbers.Exports.Naturals
```

We should not be surprised that Agda can determine that two
syntactically-identical terms are equal:

```agda
  _ : suc (suc (suc zero)) ≡ suc (suc (suc zero))
  _ = refl
```

As we saw before, Agda will also expand definitions, meaning we can trivially
show that:

```agda
  _ : three ≡ suc (suc (suc zero))
  _ = refl
```

Agda can also do this if the definitions require computation, as is the case
for `def:_+_`:

```agda
  _ : three ≡ one + two
  _ = refl
```

Each of these examples is of the "unit test" variety. But perhaps you'll be
delighted to learn that we can also use propositional equality to automatically
show some algebraic identities---that is, two mathematical expressions with
variables that are always equal.

For starters, we'd like to prove the following simple identity:

$$
0 + x = x
$$

Our familiarity with math notation in situations like these can actually be a
burden to understanding. While we will readily admit the truth of this
statement, it's less clear what exactly it's saying, as what variables *are* is
often fuzzy. I like this example, because working it through helped
conceptualize things I'd been confused about for decades.

What $0 + x = x$ is really saying is that *for any $x$, it is the case that
$0 + x = x$.* Mathematicians are infuriatingly implicit about what and when they
are quantifying over, and a big chunk of internalizing math is just getting a
feel for how the quantification works.

Phrased in this way, we can think of the identity $0 + x = x$ instead as a
*function* which takes a parameter `x` and returns a proof that, for that exact
argument, `bind:x:0 + x ≡ x`. Thus:

```agda
  0+x≡x⅋ : (x : ℕ) → zero + x ≡ x
  0+x≡x⅋ = ?
```

In order to give a proof of this fact, we must bind the parameter on the left
side of the equals (in fact, we don't even need to give it a name), and can
simply give `ctor:refl` on the right side:

```agda
  0+x≡x : (x : ℕ) → zero + x ≡ x
  0+x≡x _ = refl
```

Our examples thus far seem to indicate that `type:_≡_` can automatically show
all of the equalities we'd like. But this is due only to careful planning on my
part. Try as we might, however, Agda will simply *refuse* to typecheck the
analogous identity $x + 0 = x$:

```illegal
  x+0≡x⅋ : (x : ℕ) → x + zero ≡ x
  x+0≡x⅋ _ = refl
```

complaining that:

```info
x + zero != x of type ℕ
when checking that the expression refl has type x + zero ≡ x
```

Inspecting the error message here is quite informative; Agda tells us that `x +
zero` is not the same thing as `x`. What exactly does it mean by that? In
@sec:stuckness we discussed what happens when an expression gets stuck. Recall
that Agda computes by way of matching expressions on which constructors they
evaluate to. But we defined `def:_+_` by induction on its first argument, and in
this case, the first argument is simply `x`. Thus the expression `bind:x:x +
zero` is stuck, which is why Agda can't work whether `ctor:refl` is an
acceptable constructor to use here.

We can solve this, like most other problems of stuckness, simply by pattern
matching on the stuck variable:

```agda
  x+0≡x⅋₀ : (x : ℕ) → x + zero ≡ x
  x+0≡x⅋₀ zero     = {! !}
  x+0≡x⅋₀ (suc x)  = {! !}
```

Immediately, Agda gets unstuck. Our first hole here now has type `expr:zero ≡
zero`, which is trivially solved by `ctor:refl`:

```agda
  x+0≡x⅋₁ : (x : ℕ) → x + zero ≡ x
  x+0≡x⅋₁ zero     = refl
  x+0≡x⅋₁ (suc x)  = {! !}
```

This second goal here is harder, however. Its type `bind:x:suc (x + zero) ≡ suc
x` has arisen from instantiating the original parameter at `bind:x:suc x`. Thus
we are trying to show `bind:x:suc x + zero ≡ suc x`, which Agda has reduced to
`bind:x:suc (x + zero) ≡ suc x` by noticing the leftmost argument to `def:_+_`
is a `ctor:suc` constructor.

Looking closely, this goal is almost exactly the type of `def:x+0≡x` itself,
albeit with a `ctor:suc` tacked onto either side. If we were to recurse, we
could get a proof of `bind:x:x + zero ≡ x`, which then seems plausible that we
could massage into the right shape. Let's pause on our definition of `def:x+0≡x`
for a moment, in order to work out this problem of fitting a `ctor:suc` into a
proof-shaped hole.


## Congruence

At first blush, we are trying to solve the following problem:

```agda
  postulate
    _ : (x : ℕ)
      → x + zero ≡ x
      → suc (x + zero) ≡ suc x
```


Hidden

:   ```agda
  -- fix indentation for expr
    ```


which we read as "for any number `x :` `type:ℕ`, we can transform a proof of
`bind:x:x + zero ≡ x` into a proof of `bind:x:suc (x + zero) ≡ suc x`." While
such a thing is perfectly reasonable, it feels like setting the bar too low.
Surely we should be able to show the more general solution that:


Hidden

:   ```agda
    -- fix indentation
    ```


```agda
  postulate
    _ : {x y : ℕ}
      → x ≡ y
      → suc x ≡ suc y
```


Hidden

:   ```agda
  -- fix indentation for expr
    ```


read informally as "if `x` and `y` are equal, then so too are `bind:x:suc x` and
`bind:y:suc y`." Notice that while `x` was an *explicit* parameter to the
previous formulation of this idea, we here have made it *implicit.* Since there
is no arithmetic required, Agda is therefore able to unambiguously determine
which two things we're trying to show are equal. And why do something explicitly
if the computer can figure it out on our behalf?

Phrased this way, perhaps our goals are still too narrow. Recall that
propositional equality means "these two values evaluate to identical forms,"
which is to say that, at the end of the day, they are indistinguishable.

If two things are indistinguishable, then there must not be any way that we can
distinguish between them, including looking at the result of function call.
Therefore, we can make the much stronger claim that "if `x` and `y` are equal,
then so too are `f x` and `f y` for *any function* `f`!"

Now we really cooking with gas.

This property is known as *congruence*, which again gets shortened to `def:cong`
due its frequency. The type of `def:cong` is rather involved, but most of the
work involved is binding the relevant variables.

Hidden

:   ```agda
    -- fix indentation
    ```

```agda
  cong⅋₀
      : {A B : Set}  -- ! 1
      → {x y : A}    -- ! 2
      → (f : A → B)  -- ! 3
      → x ≡ y        -- ! 4
      → f x ≡ f y    -- ! 5
  cong⅋₀ f x≡y = ?
```

The proper way to read this type is, from top to bottom:

1. For any types `A` and `B`,
2. and for any values `x` and `y`, both of type `A` , then
3. for any function `f : A → B`,
4. given a proof that `bind:x y:x ≡ y`,
5. it is the case that `bind:f x y:f x ≡ f y`.

Actually proving `def:cong` is surprisingly straightforward. We already have a
proof that `bind:x y:x ≡ y`. When we pattern match on this value, Agda is smart enough to
replace every `y` in scope with `x`, since we have already learned that `x` and
`y` are exactly the same thing. Thus, after a [MakeCase:x≡y](AgdaCmd):

```agda
  cong⅋₁
      : {A B : Set}
      → {x y : A}
      → (f : A → B)
      → x ≡ y
      → f x ≡ f y
  cong⅋₁ f refl = {! !}
```

our new goal has type `bind:f x:f x ≡ f x`, which is filled trivially by a call
to `ctor:refl`.

```agda
  cong
      : {A B : Set}
      → {x y : A}
      → (f : A → B)
      → x ≡ y
      → f x ≡ f y
  cong f refl = refl
```

You'll notice something cool has happened here. When we pattern matched on a
proof, Agda used the result as evidence, which helped it get unstuck and make
computational progress. This is an idea we will explore further in
@sec:dot-patterns.

Popping the stack, recall that we were looking for a means of completing the
following proof:

```agda
  x+0≡x⅋₂ : (x : ℕ) → x + zero ≡ x
  x+0≡x⅋₂ zero     = refl
  x+0≡x⅋₂ (suc x)  = {! !}
```

The hole here has type `bind:x:suc (x + zero) ≡ suc x`, which we can use
`def:cong` to help with. Congruence requires a function `f` that is on both
sides of the equality, which in this case means we must use `ctor:suc`.
Therefore, we can fill our hole with:

```agda
  x+0≡x⅋₃ : (x : ℕ) → x + zero ≡ x
  x+0≡x⅋₃ zero     = refl
  x+0≡x⅋₃ (suc x)  = {! cong suc !}
```

and ask Agda to [Refine](AgdaCmd), which will result in:

```agda
  x+0≡x⅋₄ : (x : ℕ) → x + zero ≡ x
  x+0≡x⅋₄ zero     = refl
  x+0≡x⅋₄ (suc x)  = cong suc {! !}
```

Notice how Agda has taken our suggestion for the hole, applied it, and left a
new hole for the remaining argument to `def:cong`. This new hole has type
`bind:x:x + zero ≡ x`, which is exactly the type of `def:x+0≡x` itself. We can
ask Agda to fill in the rest of the definition for us by invoking
[Auto](AgdaCmd):

```agda
  x+0≡x : (x : ℕ) → x + zero ≡ x
  x+0≡x zero     = refl
  x+0≡x (suc x)  = cong suc (x+0≡x x)
```

Congruence is an excellent tool for doing induction in proofs. You can do
induction as normal, but the resulting proof from the recursive step is usually
not quite be what you need. Luckily, the solution is often just a `def:cong`
away.


## Identity Elements

A common idiom in Agda's standard library are the `-identityˡ` and `-identityʳ`
functions, which are properties stating a binary operation has left- and right-
identities, respectively. An *identity* is any value which doesn't change the
result. As we have just now shown, 0 is both a right and left identity for
addition, because $x + 0 = x$ and $0 + x = x$. In order to get start getting
familiar with these idioms, we can give new our existing proofs:

```agda
  +-identityˡ : (x : ℕ) → zero + x ≡ x
  +-identityˡ = 0+x≡x

  +-identityʳ : (x : ℕ) → x + zero ≡ x
  +-identityʳ = x+0≡x
```

The superscript `l` and `r` here are input as [`^l`](AgdaMode) and [`^r`](AgdaMode),
respectively. The attentive reader might question why exactly we need
`def:+-identityˡ`, since it's fully-normalized definition is just `ctor:refl`, which is
to say that it's something Agda can work out for itself without explicitly using
`def:+-identityˡ`. While that is true, it is an *implementation detail.* If we were
to not expose `def:+-identityˡ`, the user of our proof library would be required to
understand for themselves exactly how addition is computed, which can be an
onerous mental burden. Instead, we content ourselves with exposing "trivial"
proofs like `def:+-identityˡ` with the understanding that it is the *name* of this
proof that is important, more so than its contents. Throughout your exposure to
the Agda standard library, you will find many such-named functions, and the
convention can help you find the lemmas you need without needing to dig deeply
into the implementation of the mathematical object at study.

In addition to addition, multiplication also enjoys both left and right
identities. A good exercise is to find and prove both.


Exercise

:   Find and prove a right identity for `def:_*_`:


Solution

:     ```agda
  *-identityʳ : (x : ℕ) → x * one ≡ x
  *-identityʳ zero     = refl
  *-identityʳ (suc x)  = cong suc (*-identityʳ x)
    ```


Exercise

:   Find and prove a left identity for `def:_*_`:


Solution

:     ```agda
  *-identityˡ : (x : ℕ) → one * x ≡ x
  *-identityˡ zero     = refl
  *-identityˡ (suc x)  = cong suc (+-identityʳ x)
    ```

Exercise

:   Exponentiation doesn't have notions of both left and right identities, but
    has instead only one of the two. Determine which, and prove it is an
    identity element.


Solution

:     ```agda
  ^-identityʳ : (x : ℕ) → x ^ one ≡ x
  ^-identityʳ zero     = refl
  ^-identityʳ (suc x)  = cong suc (*-identityʳ x)
    ```


## Symmetry and Involutivity

Given that we have just proven `one * x ≡ x`, how hard do you think it will be
to prove `x ≡ one * x`? The obvious idea is to try simply to reuse our
`*-identityˡ` proof, as in:

```illegal
  *-identityˡ′⅋ : (x : ℕ) → x ≡ one * x
  *-identityˡ′⅋ = *-identityˡ
```

Unfortunately, Agda is unhappy with this definition, and it complains:

```info
x + zero * x != x of type ℕ
```

This approach clearly isn't going to work. Instead, we might consider just
writing the proof again, pattern-match and all. But we notice upon trying that
the proof delegates out to `def:+-identityʳ`, which puts us in a recursive
bind---surely we shouldn't have to rewrite the entire proof hierarchy just to
switch what's on the left of the equals sign!

But a propositional equality shows that the two things on either side of an
equals sign are identical. That is, once we've pattern matched on `refl : x ≡
x`, there is no longer a distinction between the left and right sides of the
equals sign. We can exploit this fact to reverse every propositional equality
proof via `def:sym`:

```agda
  sym : {A : Set} → {x y : A} → x ≡ y → y ≡ x
  sym refl = refl
```

Rather underwhelming once you see it, isn't it? After we pattern match on
`ctor:refl`, we learn that `x` and `y` are the same thing, so our goal becomes `x ≡
x`, which we can solve with `ctor:refl`. And from there, Agda is happy to rewrite the
left side as `y`, since it knows that's just a different name for `x` anyway.

What's with the name `def:sym` anyway? It's short for *symmetry,* which is the idea
that a relation doesn't distinguish between its left and right arguments. We
shorten it to `def:sym` as always because of the sheer ubiquity with which this
proof combinator gets used.

With `def:sym`, we now have a satisfying, general-purpose tool for implementing
`*-identityˡ′`:

```agda
  *-identityˡ′ : (x : ℕ) → x ≡ one * x
  *-identityˡ′ x = sym (*-identityˡ x)
```

Because `def:sym` swaps which of its arguments is on the left and which is on the
right, we should expect that applying `def:sym` twice should get us back to where we
started. Is this so? We could try to ponder the question deeply, but instead we
remember that we're now capable of doing computer-aided mathematics, and the
more interesting question is whether we can prove it. And in fact we can! The
hardest part is laying down the type, which we'd like to work for any proof,
regardless of the types involved. Thus we must bind `A : Set` to quantify over
the type of the proof, and then we must bind `x : A` and `y : A` for the
particular arguments on either side of the equals sign. Then we're ready to get
started on the question proper, namely:

```agda
  sym-involutive
      : {A : Set} → {x y : A}
      → (p : x ≡ y)
      → sym (sym p) ≡ p
```

The proof here is simple and satisfying, and is left as an exercise to the
reader.


Exercise

:   Prove `def:sym-involutive`.


Solution

  :   ```agda
  sym-involutive refl = refl
    ```


An involution is any operation that gets you back to where you started after two
invocations. In other words, it's a self-canceling operation. For another
example we've already run into, `not : Bool → Bool` is also involutive:

```agda
  import Chapter1-Agda
  open Chapter1-Agda.Booleans

  not-involutive : (x : Bool) → not (not x) ≡ x
  not-involutive false  = refl
  not-involutive true   = refl
```

Throughout this book, we will encounter more and more algebraic properties like
involutivity, symmetry and identities. In fact, I would **strongly recommend**
jotting them down somewhere to keep as a handy cheatsheet. The road to success
as a fledgling mathematician is to remember what all of these things mean, and
to look for examples of each whenever you are in a new domain. Discovering them
allow you to reuse your entire existing vocabulary and understanding,
transplanting those ideas into the new area, which means you can hit the ground
running. Indeed, much to the surprise of traditionally-educated people,
mathematics is much more about these sorts of properties than it ever was about
numbers.


## Transitivity

Let's stop for a moment and take stock of what we've managed to accomplish thus
far in our exploration of equality proofs. We began with reflexivity, which is
being able to state equalities of the form:

$$
x = x
$$

While such a thing is of paramount important, it's fundamentally the least
interesting thing we could possibly do with equality. In the previous section,
we discussed symmetry, which allows us to transform a statement like:

$$
x = y
$$

into one "the other way around:"

$$
y = x
$$

Perhaps this is slightly more intriguing than reflexivity, but only by the
slightest of margins. Blatant in its absence, however, is the ability to
*combine* proofs. This is something you know, even if you don't know that you
know it. For example, consider the following symbolic proof:

$$
\begin{aligned}
(a + b) \times c &= a \times c + b \times c \\
&= a \times c + c \times b \\
&= c \times b + a \times c
\end{aligned}
$$

The omission of the left-hand sides of the equalities on subsequent lines is a
notional convenience, but we can explicitly elaborate it out:

$$
\begin{aligned}
(a + b) \times c &= a \times c + b \times c \\
a \times c + b \times c &= a \times c + c \times b \\
a \times c + c \times b &= c \times b + a \times c
\end{aligned}
$$

Note that the right side of each equality is identical to the left side of the
equality on the next line. This is the sort of composition of proofs we'd like
to be able to perform; namely, to glue several proofs "end to end," much like a
chain of dominoes. This notion is called *transitivity,* and we can state it
thus:

```agda
  trans
    : {A : Set} {x y z : A}
    → x ≡ y
    → y ≡ z
    → x ≡ z
```

In other words, `def:trans` takes a proof that `x ≡ y` and a proof that `y ≡ z`, and
gives us back a proof that `x ≡ z`. To prove such a thing, we take a page out of
the `def:sym` book, and pattern match on both proofs, allowing Agda to unify `z` and
`y`, before subsequently unifying `y` and `x`:

```agda
  trans refl refl = refl
```

We can use transitivity to help us prove less-fundamental properties about
things. For example, we might like to show $a ^ 1 = a + (b \times 0)$. This
isn't too tricky to do with pen and paper:

$$
\begin{aligned}
a^1 &= a \\
&= a + 0 \\
&= a + (b \times 0)
\end{aligned}
$$


```agda
  -- TODO(sandy): put these zeroes in the section on identities
  *-zeroˡ : (x : ℕ) → zero * x ≡ zero
  *-zeroˡ _ = refl

  *-zeroʳ : (x : ℕ) → x * zero ≡ zero
  *-zeroʳ zero = refl
  *-zeroʳ (suc x) = *-zeroʳ x
```

Let's write this as a proposition:


```agda
  a^1≡a+b*0⅋₋₁ : (a b : ℕ) → a ^ one ≡ a + (b * zero)
  a^1≡a+b*0⅋₋₁ a b = ?
```

Of course, we can always prove something by doing the manual work of pattern
matching on our inputs, but that approach is best avoided if at possible, as it
usually leaves you deep in the weeds. Proof by pattern matching is much akin to
programming in assembly---you can get the job done, but it requires paying
attention to much more detail than we'd like. Instead, we can prove the above
proposition out of reusable pieces that we've already developed. Because we'd
like to glue together some existing proofs, we begin with a call to `def:trans`:

```agda
  a^1≡a+b*0⅋₀ : (a b : ℕ) → a ^ one ≡ a + (b * zero)
  a^1≡a+b*0⅋₀ a b
    = trans ? ?
```

This call to `def:trans` shows up with a yellow background because we haven't yet
given Agda enough information to infer all the necessary types. This is nothing
to worry about, as our next step will sort everything out. We will follow our
"pen and paper" proof above, where our first step was that $a^1 = a$, which we
called `^-identityʳ a`:

```agda
  a^1≡a+b*0⅋₁ : (a b : ℕ) → a ^ one ≡ a + (b * zero)
  a^1≡a+b*0⅋₁ a b
    = trans (^-identityʳ a) ?
```

Our goal now has the type `a ≡ a + b * zero`, which we'd like to simplify and
implement in two steps. Thus, we use another call to `def:trans`, this time to
assert the fact that $a = a + 0$. We don't have a proof of this directly, but we
do have the opposite direction via `+-identityʳ a`. Symmetry can help us out:

```agda
  a^1≡a+b*0⅋₂ : (a b : ℕ) → a ^ one ≡ a + (b * zero)
  a^1≡a+b*0⅋₂ a b
    = trans (^-identityʳ a)
    ( trans (sym (+-identityʳ a))
            ?
    )
```

We are left with a goal with the type `a + zero ≡ a + b * zero`. While we know
that `*-zeroʳ b` could show $b \times 0 = 0$ for us, and thus that `sym (*-zeroʳ
b)` will give us $0 = b \times 0$ , we are left with the problem of getting this
evidence into the right place. Whenever you have a proof for a subexpression,
you should think `def:cong`:

```agda
  -- TODO(sandy): rewrite me with the targeting idea first, so we can avoid
  -- the unsolved metas here
  --
  -- also put in a note about picking the spot first, for exactly this reason
  a^1≡a+b*0⅋₃ : (a b : ℕ) → a ^ one ≡ a + (b * zero)
  a^1≡a+b*0⅋₃ a b
    = trans (^-identityʳ a)
    ( trans (sym (+-identityʳ a))
            (cong ? (sym (*-zeroʳ b)))
    )
```

This final hole, recall, moves the given proof to the desired place in the
expression. Here we have `a + zero` and would like to replace it with `a + b *
zero`, meaning we need to target the `ctor:zero` in our original expression.
Therefore, we must give a function that *targets* the `ctor:zero`, leaving the
remainder of the expression alone. We can introduce a function via a lambda:

```agda
  a^1≡a+b*0⅋₄ : (a b : ℕ) → a ^ one ≡ a + (b * zero)
  a^1≡a+b*0⅋₄ a b
    = trans (^-identityʳ a)
    ( trans (sym (+-identityʳ a))
            (cong (λ φ → ?) (sym (*-zeroʳ b)))
    )
```

The lambda here is input as [`Gl`](AgdaMode), while the phi is [`Gf`](AgdaMode).
A useful trick for filling in the body of `def:cong`'s targeting function is to copy
the expression you had before, and replace the bit you'd like to change with the
function's input. Thus:

```agda
  a^1≡a+b*0 : (a b : ℕ) → a ^ one ≡ a + (b * zero)
  a^1≡a+b*0 a b
    = trans (^-identityʳ a)
    ( trans (sym (+-identityʳ a))
            (cong (λ φ → a + φ) (sym (*-zeroʳ b)))
    )
```

Of course, we can rewrite `λ φ → a + φ` by "canceling" the `φ` on both sides,
which gives us the slightly terser form `a +_`. This gives rise to an
alternative implementation:

```agda
  a^1≡a+b*0′ : (a b : ℕ) → a ^ one ≡ a + (b * zero)
  a^1≡a+b*0′ a b
    = trans (^-identityʳ a)
    ( trans (sym (+-identityʳ a))
            (cong (a +_) (sym (*-zeroʳ b)))
    )
```

Throughout this book, we will use the second notation whenever the subexpression
we'd like to target is easy to get to. If it is very nested, we will opt to use
the explicit lambda instead. Using an explicit lambda always works, while we
can't always get away using short form. Both forms are equivalent, and you may
choose whichever you prefer in your own code. However, by virtue of this
presentation being a book, we are limited by physical page widths, and thus will
opt for the terser form whenever it will simplify the presentation.

Composing proofs directly via `def:trans` does indeed work, but it leaves a lot to
be desired. Namely, the proof we wrote out "by hand" looks nothing like the pile
of `def:trans` calls we ended up using to implement `a^1≡a+b*0`. Thankfully, Agda's
syntax is sufficiently versatile that we can build a miniature *domain specific
language* in order to get more natural looking proofs. We will explore this idea
in the next section.


## Mixfix Parsing

As we saw in @sec:chapter1, we can define binary operators in Agda by sticking
underscores on either side, like in `def:_+_`. You might be surprised to learn that
these underscores are a much more general feature. The underscore corresponds to
a syntactic hole, hinting to Agda's parser that the underscore is a reasonable
place to allow an expression.

To illustrate this idea we can make a *postfix* operator by prefixing our
operator with an underscore, as in the factorial function:

```agda
  _! : ℕ → ℕ
  zero   ! = one
  suc n  ! = suc n * n !  -- ! 1
```

-- TODO(sandy): is this claim true?

One important thing to note is that function application binds most tightly of
all, thus the `suc n !` at [1](Ann) is parsed `(suc n) !`, rather than the
more obvious seeming `suc (n !)`. Recall that by default, operators get
precedence 20, which is what `def:_!` gets in this case. And since we defined `def:_*_`
with precedence 7, [1](Ann) correctly parses as `suc n * (n !)`.

Sometimes it's desirable to make *prefix* operators, where the symbol comes
before the argument. While Agda parses regular functions as prefix operators,
writing an explicit underscore on the end of an identifier means we can play
with associativity. For example, while it's tedious to write `five` out of
`ctor:suc`s:

```agda
  five⅋₀ : ℕ
  five⅋₀ = suc (suc (suc (suc (suc zero))))
```

where each of these sets of parentheses is mandatory, we can instead embrace the
nature of counting in unary and define a right-associative prefix "tick mark"
(input as [`|`](AgdaMode)):

```agda
  ∣_ : ℕ → ℕ
  ∣_ = suc

  infixr 20 ∣_

  five : ℕ
  five = ∣ ∣ ∣ ∣ ∣ zero
```

The presence of `ctor:zero` here is unfortunate, but necessary. When nesting
operators like this, we always need some sort of *terminal* in
order to tell Agda we're done this expression. Therefore, we will never be able
to write "true" tick marks which are merely to be counted. However, we can
lessen the ugliness by introducing some different syntax for `ctor:zero`, as in:

```agda
  □ : ℕ
  □ = zero

  five⅋₁ : ℕ
  five⅋₁ = ∣ ∣ ∣ ∣ ∣ □
```

The square `def:□` can be input as [`sq`](AgdaMode). Whether or not this syntax is
better than our previous attempt is in the eye of the beholder. Suffice it to
say that we will always need some sort of terminal value when doing this style
of associativity to build values.

Mixfix parsing gets even more interesting, however. We can make *delimited
operators* by enclosing an underscore with syntax on either side. For example,
the mathematical notation for the floor function (integer part) is
$\lfloor{x}\rfloor$, which we can replicate in Agda:

```agda
  postulate
    ℝ : Set
    π : ℝ
    ⌊_⌋ : ℝ → ℕ

  three′ : ℕ
  three′ = ⌊ π ⌋
```

The floor bars are input via [``clL``](AgdaMode) and [clR](AgdaMode), while `type:ℝ`
is written as [`bR`](AgdaMode) and `def:π` is [`Gp`](AgdaMode). We don't dare define
the real numbers here, as they are a tricky construction and would distract from
the point.

Agda's profoundly flexible syntax means we are capable of defining many built-in
language features for ourselves. For example, many ALGOL-style languages come
with the so-called "ternary operator" which does `if..else` in an expression
context. Of course, the word "ternary" means only "three-ary", and has nothing
to do with conditional evaluation. Mixfix parsing means we can define true
ternary operators, with whatever semantics we'd like. However, just to
demonstrate the approach, we can define it here. Because both `?` and `:`
(the traditional syntax of the "ternary operator") have special meaning in Agda,
we will instead use `‽` ([`?!`](AgdaMode)) and `⦂` ([`z:`](AgdaMode)):

```agda
  _‽_⦂_ : {A : Set} → Bool → A → A → A
  false ‽ t ⦂ f = f
  true ‽ t ⦂ f = t

  infixr 20 _‽_⦂_

  _ : ℕ
  _ = not true ‽ four ⦂ one
```

Alternatively, since Agda doesn't come with an `if..else..` construct either, we
can also trivially define that:

```agda
  if_then_else_ : {A : Set} → Bool → A → A → A
  if_then_else_ = _‽_⦂_

  infixr 20 if_then_else_
```

which we can immediately use:

```agda
  _ : ℕ
  _ = if not true then four else one
```

or nest with itself:

```agda
  _ : ℕ
  _ = if not true then four
      else if true then one
      else zero
```

As another example, languages from the ML family come with a `case..of`
expression, capable of doing pattern matching on the right-hand side of an
equals sign (as opposed to Agda, where we can only do it on the left side!)
However, it's easy to replicate this syntax for ourselves:

```agda
  case_of_ : {A B : Set} → A → (A → B) → B
  case e of f = f e
```

This definition takes advantage of Agda's pattern-matching lambda, as in:

```agda
  _ : ℕ
  _ = case not true of λ
        { false  → one
        ; true   → four
        }
```

There is one small problem when doing mixfix parsing; unfortunately, we cannot
put two non-underscore tokens beside one another. For example, it might be nice
to make a boolean operator `_is equal to_`. A simple fix is to intersperse our
tokens with hyphens, as in:

```agda
  _is-equal-to_ : {A : Set} → A → A → Set
  x is-equal-to y = x ≡ y
```

which is nearly as good.

As you can see, Agda's parser offers us a great deal of flexibility, and we can
use this to great advantage when defining domain specific languages. Returning
to our problem of making `def:trans`-style proofs easier to think about, we can
explore how to use mixfix parsing to construct valid syntax more amenable to
equational reasoning.


## Equational Reasoning

Recall, we'd like to develop some syntax amenable to doing "pen and paper" style
proofs. That is, we'd like to write something in Agda equivalent to:

$$
\begin{aligned}
(a + b) \times c &= a \times c + b \times c \\
&= a \times c + c \times b \\
&= c \times b + a \times c
\end{aligned}
$$

The bits written in this syntax are equivalent to the `x` and `y` in the type `x
≡ y`. They tell us *what* is equal, but not *why.* In other words, proofs
written in the above style are missing *justification* as to *why exactly* we're
allowed to say each step of the proof follows. In order to make room, we will
use *Bird notation,* attaching justification to the equals sign:

$$
\begin{aligned}
& (a + b) \times c \\
& \quad = (\text{distributivity}) \\
& a \times c + b \times c \\
& \quad = (\text{commutativity of $\times$}) \\
& a \times c + c \times b \\
& \quad = (\text{commutativity of $+$}) \\
& c \times b + a \times c
\end{aligned}
$$

The construction of our domain specific language is a little finicky and deserve
some thought. Let's go slowly, but start with a new module:

```agda
  module ≡-Reasoning where
```

The idea here is that we will make a series of right-associative syntax
operators, in the style of our tick marks in the previous section. We will
terminate the syntax using `ctor:refl`, that is, showing that we've already proven
what we set out to. You'll often see a formal proof ended with a black square,
called a *tombstone* marker. Since proofs already end with this piece of syntax,
it's a great choice to terminate our right-associative chain of equalities.

```agda
    _∎ : {A : Set} → (x : A) → x ≡ x
    _∎ x = refl

    infix 3 _∎
```

The tombstone marker is input in Agda via [`qed`](AgdaMode). Note that the `x`
parameter here is unused in the definition, and exists only to point out exactly
which on object we'd like to show reflexivity. This gives us a convenient ending
piece, so let's now work backwards. The simplest piece of reasoning we can do is
an equality that requires no justification. If we already have the proof we'd
like, we can simply return it:

```agda
    _≡⟨⟩_ : {A : Set} → (x : A) → {y : A} → x ≡ y → x ≡ y
    x ≡⟨⟩ p = p

    infixr 2 _≡⟨⟩_
```

Again, `x` is unused in the definition, and exists only in the type. You might
think this is a good opportunity for an implicit argument, but we'd actually
*prefer* it to be visible. Recall that the justifications (that is, the proofs)
fully specify which two things we are stating are equal. The `x` arguments we've
written in `def:_≡⟨⟩_` and `def:_∎` are unnecessary for the implementations, but act as
a guide for the *human* writing the thing in the first place! These `x`s mark
the current state of the computation. Let's illustrate the point:

```agda
    _ : four ≡ suc (one + two)
    _ =
      four
        ≡⟨⟩
      two + two
        ≡⟨⟩
      suc one + two
        ≡⟨⟩
      suc (one + two)
        ∎
```

In this case, since everything is fully concrete, Agda can just work out the
fact that each of these expressions is propositionally equal to one another,
which is why we need no justifications. But you'll notice where once we had `x`
parameters, we now have a human-legible argument about which things are equal!
It can be helpful to insert explicit parentheses here to help us parse exactly
what's going on:

```agda
    _ : four ≡ suc (one + two)
    _ =
      four ≡⟨⟩
        ( two + two ≡⟨⟩
          ( suc one + two ≡⟨⟩
            ( suc (one + two) ∎ )))
```

Replacing `def:_∎` with its definition, we get:

```agda
    _ : four ≡ suc (one + two)
    _ =
      four ≡⟨⟩
        ( two + two ≡⟨⟩
          ( suc one + two ≡⟨⟩ refl ))
```

We can then replace the innermost `def:_≡⟨⟩_` with *its* definition, which you will
remember is to just return its second argument:

```agda
    _ : four ≡ suc (one + two)
    _ =
      four ≡⟨⟩
        ( two + two ≡⟨⟩ refl )
```

This process continues on and one until all of the syntax is eliminated, and we
are left with just:

```agda
    _ : four ≡ suc (one + two)
    _ = refl
```

While it seems like our notation merely ignores the equal terms, this isn't
actually true. Recall that the elided `x`s actually do appear in the type
signatures, which means these values *are* used to typecheck the whole thing.
That is, if we make an invalid step, Agda will tell us. For example, perhaps we
make an error in our proof, as in:

```illegal
    _ : four ≡ suc (one + two)
    _ =
      four
        ≡⟨⟩
      one + two  -- ! 1
        ≡⟨⟩
      suc one + two
        ∎
```

At [1](Ann) we accidentally dropped a `ctor:suc`. But, Agda is smart enough to catch
the mistake:

```info
zero != suc zero of type ℕ
when checking that the inferred type of an application
  one + two ≡ _y_379
matches the expected type
  four ≡ suc (one + two)
```

While all of this syntax construction itself is rather clever, there is nothing
magical going on here. It's all just smoke and mirrors abusing Agda's mixfix
parsing and typechecker in order to get nice notation for what we want.

Of course, `def:_≡⟨⟩_` is no good for providing justifications. Instead, we will use
the same idea, but this time leave a hole for the justification.

```agda
    _≡⟨_⟩_
        : {A : Set}
        → (x : A)
        → {y z : A}
        → x ≡ y
        → y ≡ z
        → x ≡ z
    _≡⟨_⟩_ x = trans

    infixr 2 _≡⟨_⟩_
```

`def:_≡⟨_⟩_` works exactly in the same way as `def:_≡⟨⟩_`, except that it takes a
proof justification as its middle argument, and glues it together with its last
argument as per `def:trans`. We have one piece of syntax left to introduce, and will
then play with this machinery in full.

Finally, by way of symmetry and to top things off, we will add a starting
keyword. This is not strictly necessary, but makes for nice introductory syntax
to let the reader know that an equational reasoning proof is coming up:

```agda
    begin_ : {A : Set} → {x y : A} → x ≡ y → x ≡ y
    begin_ x=y = x=y

    infix 1 begin_
```

The `def:begin_` function does nothing, it merely returns the proof given. And since
its precedence is lower than any of our other `module:≡-Reasoning` pieces, it binds
after any of our other syntax, ensuring the proof is already complete by the
time we get here. The purpose really is just for decoration.

Let's now put all of our hard work to good use. Recall the proof that originally
set us off on a hunt for better syntax:

```agda
  a^1≡a+b*0′⅋₁ : (a b : ℕ) → a ^ one ≡ a + (b * zero)
  a^1≡a+b*0′⅋₁ a b
    = trans (^-identityʳ a)
    ( trans (sym (+-identityʳ a))
            (cong (a +_) (sym (*-zeroʳ b)))
    )
```

We can now rewrite this proof in the equational reasoning style:

```agda
  a^1≡a+b*0′⅋₂ : (a b : ℕ) → a ^ one ≡ a + (b * zero)
  a^1≡a+b*0′⅋₂ a b =
    begin
      a ^ one
    ≡⟨ ^-identityʳ a ⟩
      a
    ≡⟨ sym (+-identityʳ a) ⟩
      a + zero
    ≡⟨ cong (a +_) (sym (*-zeroʳ b)) ⟩
      a + b * zero
    ∎
    where open ≡-Reasoning
```

which, for the purposes of aesthetics, we will format in this book as the
following whenever we have available line-width:

```agda
  a^1≡a+b*0′⅋₃ : (a b : ℕ) → a ^ one ≡ a + (b * zero)
  a^1≡a+b*0′⅋₃ a b = begin
    a ^ one       ≡⟨ ^-identityʳ a ⟩
    a             ≡⟨ sym (+-identityʳ a) ⟩
    a + zero      ≡⟨ cong (a +_) (sym (*-zeroʳ b)) ⟩
    a + b * zero  ∎
    where open ≡-Reasoning
```

As you can see, this is a marked improvement over our original definition. The
original implementation emphasized the proof justification---which are important
to the computer---while this one emphasizes the actual steps taken---which is
much more important to the human. Whenever you find yourself doing doing
non-ergonomic things for the sake of the computer, it's time to take a step back
as we have done here. This is an important lesson, inside Agda and out.


## Ergonomics, Associativity and Commutativity

If you tried writing out the new definition of `a^1≡a+b*0′⅋₃` by hand, you
likely didn't have fun. It's a huge amount of keystrokes in order to produce the
above code artifact. Thankfully, Agda's interactive support can help us write
out the mechanical parts of the above proof, allowing us to focus more on the
navigation than the driving.

The first thing you'll want to do is to write a macro or snippet for your editor
of choice. We're going to be typing out a lot of the following two things, and
it will save you an innumerable amount of time to write it down once and have
your text editor do it evermore. The two snippets you'll need are:

```snippet
  ≡⟨ ? ⟩
    ?
```

and

```snippet
  begin
    ?
  ≡⟨ ? ⟩
    ?
  ∎
  where open ≡-Reasoning
```

I have bound the first to [`step`](AgdaMode), and the latter to [`begin`](AgdaMode).
Let's put these to work writing something more useful. We'd like to prove that
addition is *associative,* which is to say, that it satisfies the following law:

$$
(a + b) + c = a + (b  + c)
$$

We can write this in Agda with the type:


```agda
  +-assoc⅋₀ : (x y z : ℕ) → (x + y) + z ≡ x + (y + z)
```

A quick binding of variables, induction on `x`, and obvious use of `ctor:refl` gets
us to this step:

```agda
  +-assoc⅋₀ zero     y z = refl
  +-assoc⅋₀ (suc x)  y z = ?
```

We're ready to start a reasoning block, and thus we can use our
[`begin`](AgdaMode) snippet:

```agda
  +-assoc⅋₁ : (x y z : ℕ) → (x + y) + z ≡ x + (y + z)
  +-assoc⅋₁ zero     y z = refl
  +-assoc⅋₁ (suc x)  y z = begin
    ?  ≡⟨ ? ⟩
    ?  ∎
    where open ≡-Reasoning
```

Note that I have opted to format this lemma more horizontally than the vertical
alignment you have. This is merely to make the most of our page width and save
some paper, but feel free to format however you'd like. I find the horizontal
layout to be more aesthetically pleasing, but much harder to write. Thus, when I
am proving things, I'll do them in the vertical layout, and do a second pass
after the fact to make it look prettier.

Regardless of my artisanal formatting decisions,  we can now start getting help
from Agda. Using [Solve](AgdaCmd) at the first and last holes will get Agda to
fill in the terms---the two things that eventually need to be equal:

```agda
  +-assoc⅋₂ : (x y z : ℕ) → (x + y) + z ≡ x + (y + z)
  +-assoc⅋₂ zero     y z = refl
  +-assoc⅋₂ (suc x)  y z = begin
    suc x + y + z    ≡⟨ ? ⟩
    suc x + (y + z)  ∎
    where open ≡-Reasoning
```

I always like to subsequently extend the top and bottom sides like this:

```agda
  +-assoc⅋₃ : (x y z : ℕ) → (x + y) + z ≡ x + (y + z)
  +-assoc⅋₃ zero     y z = refl
  +-assoc⅋₃ (suc x)  y z = begin
    suc x + y + z    ≡⟨⟩
    ?                ≡⟨ ? ⟩
    ?                ≡⟨⟩
    suc x + (y + z)  ∎
    where open ≡-Reasoning
```

which recall says that the newly added lines are already equal to the other side
of the `def:_≡⟨⟩_` operator. We can fill in these holes with
[Solve/Normalise](AgdaCmd), which asks Agda to fully-evaluate both holes. This
will expand as many definitions as it can while still making progress. Sometimes
it goes too far, but for our simple examples here, this will always be helpful.
The result looks like this:

```agda
  +-assoc⅋₄ : (x y z : ℕ) → (x + y) + z ≡ x + (y + z)
  +-assoc⅋₄ zero     y z = refl
  +-assoc⅋₄ (suc x)  y z = begin
    suc x + y + z      ≡⟨⟩
    suc (x + y + z)    ≡⟨ ? ⟩
    suc (x + (y + z))  ≡⟨⟩
    suc x + (y + z)    ∎
    where open ≡-Reasoning
```

This new hole is clearly a `cong suc`, which we can partially fill in, and then
invoke [Auto](AgdaCmd) to search for the remainder of the proof:

```agda
  +-assoc : (x y z : ℕ) → (x + y) + z ≡ x + (y + z)
  +-assoc zero     y z = refl
  +-assoc (suc x)  y z = begin
    suc x + y + z      ≡⟨⟩
    suc (x + y + z)    ≡⟨ cong suc (+-assoc x y z) ⟩
    suc (x + (y + z))  ≡⟨⟩
    suc x + (y + z)    ∎
    where open ≡-Reasoning
```

I quite like this approach for tackling proofs. I introduce a [`begin`](AgdaMode)
snippet, use [Solve](AgdaCmd) to fill in the top and bottom, insert new calls to
`def:_≡⟨⟩_` the top and bottom, fill them via [Solve/Normalise](AgdaCmd), and then
use [`step`](AgdaMode) to help fill in the middle.

Let's do another proof together, this time a less-trivial one. First, we will
dash out a quick lemma:

```agda
  +-suc : (x y : ℕ) → x + suc y ≡ suc (x + y)
  +-suc zero     y = refl
  +-suc (suc x)  y = cong suc (+-suc x y)
```

and now would like to show the *commutativity* of addition, which is,
symbolically, the following law:

$$
a + b = b + a
$$

By this point you should be able to put together the type, and show the zero
case.


Exercise

:   State the type of, perform induction on the first argument, and solve the
    zero case for `def:+-comm`.


Solution

:     ```agda
  +-comm⅋₀ : (x y : ℕ) → x + y ≡ y + x
  +-comm⅋₀ zero     y = sym (+-identityʳ y)
  +-comm⅋₀ (suc x)  y = ?
    ```

Let's start with a [`begin`](AgdaMode) snippet, this time filling the top and
bottom holes via [Solve/Normalise](AgdaCmd) directly:

```agda
  +-comm⅋₁ : (x y : ℕ) → x + y ≡ y + x
  +-comm⅋₁ zero     y = sym (+-identityʳ y)
  +-comm⅋₁ (suc x)  y = begin
    suc (x + y)  ≡⟨ ? ⟩
    y + suc x    ∎
    where open ≡-Reasoning
```

Here we have our choice of working top-down, or bottom up. Let's work bottom-up,
for fun. Add a [`step`](AgdaMode), which will make things temporarily go all
yellow as Agda now has too many degrees of freedom to work out what you mean:

```agda
  +-comm⅋₂ : (x y : ℕ) → x + y ≡ y + x
  +-comm⅋₂ zero     y = sym (+-identityʳ y)
  +-comm⅋₂ (suc x)  y = begin
    suc (x + y)  ≡⟨ ? ⟩
    ?            ≡⟨ ? ⟩
    y + suc x    ∎
    where open ≡-Reasoning
```

Nevertheless, we can persevere and fill in the bottom hole using our `def:+-suc`
lemma from just now:

```agda
  +-comm⅋₃ : (x y : ℕ) → x + y ≡ y + x
  +-comm⅋₃ zero     y = sym (+-identityʳ y)
  +-comm⅋₃ (suc x)  y = begin
    suc (x + y)  ≡⟨ ? ⟩
    ?            ≡⟨ sym (+-suc y x) ⟩
    y + suc x    ∎
    where open ≡-Reasoning
```

With this justification in place, we can now ask Agda to fill the remaining
term-level hole, again via [Solve/Normalise](AgdaCmd):

```agda
  +-comm⅋₄ : (x y : ℕ) → x + y ≡ y + x
  +-comm⅋₄ zero     y = sym (+-identityʳ y)
  +-comm⅋₄ (suc x)  y = begin
    suc (x + y)  ≡⟨ ? ⟩
    suc (y + x)  ≡⟨ sym (+-suc y x) ⟩
    y + suc x    ∎
    where open ≡-Reasoning
```

which makes the solution obvious:

```agda
  +-comm : (x y : ℕ) → x + y ≡ y + x
  +-comm zero     y = sym (+-identityʳ y)
  +-comm (suc x)  y = begin
    suc (x + y)  ≡⟨ cong suc (+-comm x y) ⟩
    suc (y + x)  ≡⟨ sym (+-suc y x) ⟩
    y + suc x    ∎
    where open ≡-Reasoning
```



## Facts About Natural Numbers

Often, a huge amount of the work to prove something is simply in manipulating
the expression to be of the right form so that you can apply the relevant lemma.
This is the case in `def:*-suc`, which allows us to expand a `ctor:suc` on the right side
of a multiplication term:

```agda
  *-suc : (x y : ℕ) → x * suc y ≡ x + x * y
  *-suc zero     y = refl
  *-suc (suc x)  y = begin
    suc x * suc y          ≡⟨⟩
    suc y + x * suc y      ≡⟨ cong (λ φ → suc y + φ) (*-suc x y) ⟩
    suc y + (x + x * y)    ≡⟨⟩
    suc (y + (x + x * y))
                          ≡⟨ cong suc (sym (+-assoc y x (x * y))) ⟩
    suc ((y + x) + x * y)
                ≡⟨ cong (λ φ → suc (φ + x * y)) (+-comm y x) ⟩
    suc ((x + y) + x * y)  ≡⟨ cong suc (+-assoc x y (x * y)) ⟩
    suc (x + (y + x * y))  ≡⟨⟩
    suc x + (y + x * y)    ≡⟨⟩
    suc x + (suc x * y)    ∎
    where open ≡-Reasoning
```

We are now ready to prove `def:*-comm`, one of our major results in this chapter.


Exercise

:   Prove the commutativity of multiplication of the natural numbers.


Solution

:       ```agda
  *-comm : (x y : ℕ) → x * y ≡ y * x
  *-comm zero     y = sym (*-zeroʳ y)
  *-comm (suc x)  y = begin
    suc x * y  ≡⟨⟩
    y + x * y  ≡⟨ cong (y +_) (*-comm x y) ⟩
    y + y * x  ≡⟨ sym (*-suc y x) ⟩
    y * suc x  ∎
    where open ≡-Reasoning
      ```

```agda
  *-distribʳ-+ : (x y z : ℕ) → (y + z) * x ≡ y * x + z * x
  *-distribʳ-+ x zero     z = refl
  *-distribʳ-+ x (suc y)  z = begin
    (suc y + z) * x      ≡⟨⟩
    x + (y + z) * x      ≡⟨ cong (x +_) (*-distribʳ-+ x y z) ⟩
    x + (y * x + z * x)  ≡⟨ sym (+-assoc x (y * x) (z * x)) ⟩
    (x + y * x) + z * x  ≡⟨⟩
    suc y * x + z * x    ∎
    where open ≡-Reasoning

  *-assoc : (x y z : ℕ) → (x * y) * z ≡ x * (y * z)
  *-assoc zero     y z = refl
  *-assoc (suc x)  y z = begin
    suc x * y * z        ≡⟨⟩
    (y + x * y) * z      ≡⟨ *-distribʳ-+ z y (x * y) ⟩
    y * z + (x * y) * z  ≡⟨ cong (λ φ → y * z + φ) (*-assoc x y z) ⟩
    y * z + x * (y * z)  ≡⟨⟩
    suc x * (y * z)      ∎
    where open ≡-Reasoning
```