---
suppress-bibliography: true
...

# Proof Objects {#sec:proofs}

Hidden

:   ```agda
{-# OPTIONS --allow-unsolved-metas #-}
    ```

```agda
module Chapter3-Proofs where
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


Prerequisites

:   ```agda
open import Chapter1-Agda
  using (Bool; true; false; _∨_; _∧_; not)
    ```

:   ```agda
open import Chapter2-Numbers
  using (ℕ; zero; suc)
    ```


## Constructivism

It is worth noting that the mathematics in this book are not the "whole story"
of the field. You see, there are two camps in the world of math: the
*classicists* and the *constructivists.* Much like many religious sects, these
two groups have much more in common than they have distinct. In fact, the only
distinction between these two groups of truth-seekers is their opinion on the
nature of falsities.

The classicists---the vast majority---believe all mathematical statements are
partitioned between those which are *true*, and those which are *false.* There is simply no
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
3. If a number $n$ has a prime factor $d$, then $n + 1$ does not have $d$ as
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
theorem under any usual definitions for 2, 3, or equality. Occasionally,
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
so, we will help programmers use the tools they already have, in order to
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
  open Chapter2-Numbers
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

To drive the point home, we can also try asking whether one is an even number:

```agda
  one-is-even : IsEven (suc zero)
  one-is-even = ?
```

However, as we saw in @sec:even, there is no way to fill this hole. Therefore,
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
ab &= a^2 \\
\therefore \quad ab - b^2 &= a^2 - b^2  \\
&= (a + b)(a - b)
\end{aligned}
$$

However, we can also factor $ab - b^2$ as follows:

$$
\begin{aligned}
ab - b^2 &= (a - b)b \\
&= b(a - b)
\end{aligned}
$$

in which case we know:

$$
\begin{aligned}
b(a - b) &= (a + b)(a - b) \\
\therefore \quad b &= a + b \\
&= b + b \\
&= 2b \\
\therefore \quad 1 &= 2
\end{aligned}
$$

The actual flaw in reasoning here is when we cancel $a - b$ from both sides of
the equation. Recall that $a = b$, so $a - b = 0$, and thus this is an implicit
division by zero.

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
are off. In English, this property is known as the *principle of explosion* but
you can also call it *ex falso quodlibet* if you're feeling particularly regal.
All this means is that, given a proof of false, you can subsequently provide a
proof of anything. Therefore, contradictions are *really, really* bad, and a
huge chunk of logical development (including computation itself) has arisen from
scholars discovering contradictions in less rigorous mathematics than what we
use today.

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

  open Chapter2-Numbers
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


## Congruence {#sec:cong}

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

Another way of reading the type of congruence is that it allows us to
"transport" a proof from the input-side of a function over to the output-side.

Actually proving `def:cong` is surprisingly straightforward. We already have a
proof that `bind:x y:x ≡ y`. When we pattern match on this value, Agda is smart
enough to replace every `y` in scope with `x`, since we have already learned
that `x` and `y` are exactly the same thing. Thus, after a
[MakeCase:x≡y](AgdaCmd):

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


## Identity and Zero Elements {#sec:identities}

A common algebraic structure is the idea of an *identity element*---annoyingly,
"identity" in a difference sense than in algebraic identity. An identity
element is a value which doesn't change the answer when applied as a function
argument. That's a very abstract sentence, so let's dive into it in more detail.

Consider addition. As we saw in the previous section, whenever you add zero, you
don't change the result. That is to say that zero is an identity element for the
addition function. Since $x + 0 = x$, zero is a *right identity* for addition,
and because $0 + x = x$, zero is a *left identity* too.

Identity values are tied to specific functions. Notice that *multiplication* by
zero definitely changes the result, and so zero is not an identity for
multiplication. We do, however, have an identity for multiplication: it's just
the one instead. Identities are extremely important in algebra, because spotting
one means we can simplify an expression.

In Agda, proofs about identities are often given standard names, with the
`-identityˡ` and `-identityʳ` suffixes (input as [`^l`](AgdaMode) and
[`^r`](AgdaMode) respectively.) We prepend the function name to these, so, the
proof that 0 is a left identity for `def:_+_` should be named `def:+-identityˡ`.
Therefore, let's give better names to our functions from earlier:

```agda
  +-identityˡ : (x : ℕ) → zero + x ≡ x
  +-identityˡ = 0+x≡x

  +-identityʳ : (x : ℕ) → x + zero ≡ x
  +-identityʳ = x+0≡x
```

The attentive reader might question why exactly we need `def:+-identityˡ`, since
it's fully-normalized definition is just `ctor:refl`, which is to say that it's
something Agda can work out for itself without explicitly using `def:+-identityˡ`.

While that is true, it is an implementation detail. If we were to not expose
`def:+-identityˡ`, the user of our proof library would be required to understand
for themselves exactly how addition is implemented. It doesn't seem too onerous,
but in the wild, we're dealing with much more complicated objects.

Instead, we content ourselves in exposing "trivial" proofs like
`def:+-identityˡ` with the understanding that it is the *name* of this proof
that is important. Throughout your exposure to the Agda standard library, you
will find many such-named functions, and the conventions will help you find the
theorems you need without needing to dig deeply into the each implementation.

In addition to addition, multiplication also enjoys both left and right
identities as we have seen. A good exercise is to prove both.


Exercise (Easy)

:   Prove that $1 \times a = a$


Solution

:     ```agda
  *-identityˡ : (x : ℕ) → 1 * x ≡ x
  *-identityˡ zero     = refl
  *-identityˡ (suc x)  = cong suc (+-identityʳ x)
    ```


Exercise (Easy)

:   Prove that $a \times 1 = a$


Solution

:     ```agda
  *-identityʳ : (x : ℕ) → x * 1 ≡ x
  *-identityʳ zero     = refl
  *-identityʳ (suc x)  = cong suc (*-identityʳ x)
    ```

Addition and multiplication aren't the only operations we've seen that have
identities. Both monus and exponentiation also have identities, but they are not
two-sided. For example, zero is a right identity for monus:

```agda
  ∸-identityʳ : (x : ℕ) → x ∸ 0 ≡ x
  ∸-identityʳ _ = refl
```

but it is not a left identity. As it happens, the monus operation does not have
a left identity---a fact we will prove in @sec:no-monus-id.


Exercise (Easy)

:   Find and prove an identity element for exponentiation.


Solution

:     ```agda
  ^-identityʳ : (x : ℕ) → x ^ 1 ≡ x
  ^-identityʳ zero     = refl
  ^-identityʳ (suc x)  = cong suc (*-identityʳ x)
    ```


Identities are not limited to numeric operations. For example, `ctor:false` is
both a left and right identity for `def:_∨_`, as we can show:

```agda
  ∨-identityˡ : (x : Bool) → false ∨ x ≡ x
  ∨-identityˡ _ = refl
```

```agda
  ∨-identityʳ : (x : Bool) → x ∨ false ≡ x
  ∨-identityʳ false  = refl
  ∨-identityʳ true   = refl
```


Exercise

: Prove analogous facts about the boolean AND function `def:_∧_`.


Solution

:   ```agda
  ∧-identityˡ : (x : Bool) → true ∧ x ≡ x
  ∧-identityˡ _ = refl
    ```

:   ```agda
  ∧-identityʳ : (x : Bool) → x ∧ true ≡ x
  ∧-identityʳ false  = refl
  ∧-identityʳ true   = refl
    ```


While identity elements might seem unexciting and pointless right now, but they
are an integral part for a rich computational structure that we will study in
@sec:monoids. For the time being, we will remark only that the discovery of the
number zero was a marvelous technological achievement in its day.

Beyond identities, some operations also have the notion of a *zero element*, or
*annihilator.* An annihilator is an element which dominates the computation,
forcing the return value to also be the annihilator. The most familiar example
of a zero element is literally `ctor:zero` for multiplication---whenever you
multiply by zero you get back zero! Like identities, zero elements can have a
chirality and apply to one or both sides of a binary operator. Multiplication by
zero is both a left and right zero:

```agda
  *-zeroˡ : (x : ℕ) → zero * x ≡ zero
  *-zeroˡ _ = refl
```

```agda
  *-zeroʳ : (x : ℕ) → x * zero ≡ zero
  *-zeroʳ zero = refl
  *-zeroʳ (suc x) = *-zeroʳ x
```

The name "zero element" can be misleading. Zero elements can exist for
non-numeric functions, but the potential confusion doesn't end there. Many
less type-safe languages have a notion of falsey values---that is, values which
can be implicitly converted to a boolean, and elicit false when doing so. The
number 0 a prototypical example of a falsey value, which unfortunately causes
people to equivocate between zero and false.

At risk of stating the obvious, falsey values do not exist in Agda, and more
generally should be considered a poison for the mind.

I bring up falsey values only to disassociate zero from false in your mind. In
the context of the `def:_∨_` function, it is `def:true` that is the zero
element:

```agda
  ∨-zeroˡ : (x : Bool) → true ∨ x ≡ true
  ∨-zeroˡ _ = refl
```

```agda
  ∨-zeroʳ : (x : Bool) → x ∨ true ≡ true
  ∨-zeroʳ false = refl
  ∨-zeroʳ true = refl
```

Annihilators can dramatically simplify a proof. If you can spot one lurking, you
know its existence must immediately trivialize a subexpression, reducing it to a
zero. Often recursively.


Exercise

: Find an analogous annihilator for `def:_∧_`.


Solution

:   ```agda
  ∧-zeroˡ : (x : Bool) → false ∧ x ≡ false
  ∧-zeroˡ _ = refl
    ```

:   ```agda
  ∧-zeroʳ : (x : Bool) → x ∧ false ≡ false
  ∧-zeroʳ false = refl
  ∧-zeroʳ true = refl
    ```


## Symmetry and Involutivity {#sec:involutivity}

In the previous section, we proved the elementary fact `def:*-identityˡ`,
stating that $1 \times a = a$. Given that we now have that proof under our
belts, how challenging do you expect it to be in order to prove $a = 1 \times
a$?

The obvious idea is to try simply to reuse our `def:*-identityˡ` proof, as in:

```illegal
  *-identityˡ′⅋ : (x : ℕ) → x ≡ 1 * x
  *-identityˡ′⅋ = *-identityˡ
```

Unfortunately, Agda is unhappy with this definition, and it complains:

```info
x + 0 * x != x of type ℕ
when checking that the expression *-identityˡ has type
(x : ℕ) → x ≡ 1 * x
```

Something has gone wrong here, but the error message isn't particularly
elucidating. Behind the scenes, Agda is trying to massage the type of
`def:*-identityˡ` into the type of `def:*-identityˡ′`. Let's work it through for
ourselves to see where exactly the problem arises.

Remember that we defined `type:_≡_` for ourselves, and therefore that it *can't*
have any special support from the compiler. As far as Agda is concerned
`type:_≡_` is *just some type,* and has nothing to do with equality. Anything
we'd expect to hold true of equality is therefore something we have to prove
for ourselves, rather than expect Agda to do on our behalf.

So to see the problem, we begin with the type `bind:x:1 * x ≡ x` from
`def:*-identityˡ`. Then, we try to assign a value with this type to the
definition of `def:*-identityˡ′`, which we've said has type `bind:x:x ≡ 1 *
x`. Agda notices that *these are not the same type*, and kicks off its
*unification* algorithm in an attempt to line up the types.

During unification, Agda is attempting to combine these two types:

* `bind:x:1 * x ≡ x` , and
* `bind:x:x ≡ 1 * x`

which it does by attempting to show that both left-hand sides of `type:_≡_`
compute to the same thing, and similarly for both right-hand sides. More
generally, if Agda is trying to unify `bind:a b:a ≡ b` and `bind:c d:c ≡ d`, it
will try to show that `a ~ c` and `b ~ d`, where `~` means "simplifies down to
identical syntactic forms."

Perhaps you already see where things are going wrong. Agda attempts to unify our
two propositional equality types, and in doing so, reduces down to two
unification problems. From the left-hand sides, it gets `bind:x:1 * x` `~`
`bind:x:x`, and from the right-hand sides, `bind:x:x` `~` `bind:x:1 * x`. Of
course, these unification problems are *not* syntactically identical, which is
exactly why we wanted to prove their equality in the first place.

Unfortunately, there is no way we can add `def:*-identityˡ` to some sort of
"global proof bank" and have Agda automatically solve the equality on our
behalf. Instead, we resign ourselves to the fact that we will need a different
approach to implement `def:*-identityˡ′`.

The next obvious solution is to just write out our proof of $a = 1 \times a$
again, pattern match and all. The original implementation of `def:*-identityʳ`
was, if you will recall:

```agda
  *-identityˡ⅋ : (x : ℕ) → 1 * x ≡ x
  *-identityˡ⅋ zero     = refl
  *-identityˡ⅋ (suc x)  = cong suc (+-identityʳ x)
```

If we wanted just to rewrite this proof with the propositional equality flipped
around, we notice something goes wrong:

```illegal
  *-identityˡ′⅋₀ : (x : ℕ) → x ≡ 1 * x
  *-identityˡ′⅋₀ zero     = refl
  *-identityˡ′⅋₀ (suc x)  = cong suc (+-identityʳ x)
```

```info
x + zero != x of type ℕ
when checking that the expression +-identityʳ x has type
x ≡ x + 0 * suc x
```

It's the same problem we had before, except now the error comes from our use of
`def:+-identityʳ`! This puts us in an annoyingly recursive bind; in order to
flip the arguments on either side of `def:_≡_` must we *really* reimplement
`def:*-identityˡ`, `def:+-identityʳ`, and *every proof in their transitive call
graph?*

By Newton's good grace, thankfully the answer is a resounding *no!* What we are
missing here is a conceptual piece of the puzzle. Recall that propositional
equality itself proves that the two things on either side of `def:_≡_` are in
fact just one thing. That is, once we've pattern matched on `ctor:refl`:
`bind:x y:x ≡ y`, there is no longer a distinction between `x` and `y`!

We can exploit this fact to flip any propositional equality proof, via a new
combinator `def:sym`:

```agda
  sym : {A : Set} → {x y : A} → x ≡ y → y ≡ x
  sym refl = refl
```

Rather underwhelming once you see it, isn't it? After we pattern match on
`ctor:refl`, we learn that `x` and `y` are the same thing, so our goal becomes `x ≡
x`, which we can solve with `ctor:refl`. From there, Agda is happy to rewrite the
left side as `y`, since it knows that's just a different name for `x` anyway.

Thank goodness.

Wondering what strange word `def:sym` is short for? *Symmetry* is the idea that
a relation doesn't distinguish between its left and right arguments. We'll
discuss relations in more generality in @sec:relations, but all you need to
know for now is that equality is a relation.

As usual, we shorten "symmetry" to `def:sym` due to its overwhelming ubiquity in
proofs.

Returning to the problem of `def:identityˡ′`, `def:sym` now gives us a
satisfying, general-purpose tool for its implementation:

```agda
  *-identityˡ′ : (x : ℕ) → x ≡ 1 * x
  *-identityˡ′ x = sym (*-identityˡ x)
```

Because `def:sym` swaps which of its arguments is on the left and which is on
the right, we should expect that applying `def:sym` twice should get us back to
where we started. Is this so?

We could try to ponder the question deeply, but instead we remember that we're
now capable of doing computer-aided mathematics, and the more interesting
question is whether we can prove it.

In fact we can! The hardest part is laying down the type, which we'd like to
work for any propositional equality term, regardless of the specific types
involved. Thus we must bind `A :` `type:Set` to quantify over the type of the
proof, and then we must bind `x : A` and `y : A` for the particular arguments on
either side of the equals sign:

```agda
  sym-involutive⅋
      : {A : Set} → {x y : A}
      → (p : x ≡ y) → sym (sym p) ≡ p
  sym-involutive⅋ = ?
```

The proof here is simple and satisfying, and is left as an exercise to the
reader.


Exercise (Trivial)

:   Prove `def:sym-involutive`.


Solution

  :   ```agda
  sym-involutive  : {A : Set} {x y : A}
                  → (p : x ≡ y) → sym (sym p) ≡ p
  sym-involutive refl = refl
    ```


An *involution* is any operation that gets you back to where you started after
two invocations. In other words, it's a self-canceling operation. Another
involution we've already run into is `def:not`:

```agda
  not-involutive : (x : Bool) → not (not x) ≡ x
  not-involutive false  = refl
  not-involutive true   = refl
```

Throughout this book, we will encounter more and more algebraic properties like
involutivity, symmetry, and identities elements. In fact, I would **strongly
recommend** jotting them down somewhere to keep as a handy cheat-sheet. The road
to success as a new mathematician is to simply to not get crushed under all of
the jargon. The ideas are often easy enough, but there are an awful lot of
things you need to simultaneously keep in your head.

Discovering new abstractions like these allow you to reuse your entire existing
vocabulary and understanding, transplanting those ideas into the new area, which
means you can hit the ground running. Indeed, much to the surprise of
traditionally-educated people, mathematics is much more about things like
identity elements and involutivity than it ever was about numbers.


## Transitivity {#sec:transitivity}

Proofs, much like computer programs, are usually too big to build all in one go.
Just like in software, it's preferable to build small, reusable pieces, which we
can later combine together into the desired product.

Blatant in its absence, therefore, is a means of actually composing these proofs
together. Much like how there are many ways of combining software, we also have
many ways of gluing together proofs. The most salient however is analogous to
the implicit semicolon in many procedural languages, allowing us to tack one
proof immediately onto the tail of another.

This is something you already know, even if you don't know that you know it. For
example, consider the following symbolic proof:

$$
\begin{aligned}
(a + b) \times c &= ac + bc \\
ac + bc &= ac + cb \\
ac + cb &= cb + ac
\end{aligned}
$$

This series of equations has the property that the right hand of each equation
is the same as the left hand of the subsequent line. As a notational
convenience, we therefore usually omit all but the first left hand side, as in:

$$
\begin{aligned}
(a + b) \times c &= ac + bc \\
&= ac + cb \\
&= cb + ac
\end{aligned}
$$

Finally, it's implied that only the first and last expressions in this equality
chain are relevant, with everything in between being "accounting" of a sort.
Therefore, having done the work, we can omit all of the intermediary
computation, and simply write:

$$
(a + b) \times c = cb + ac
$$

Notice how we have now constructed an equality of two rather disparate
expressions, simply by chaining together smaller equalities end on end, like
dominoes. This property of equality---that we're allowed to such a thing in the
first place---is called *transitivity,* and we can be stated as:

```agda
  trans&
    : {A : Set} {x y z : A}
    → x ≡ y
    → y ≡ z
    → x ≡ z
```


Hidden

:   ```agda
  trans& = ?
    ```



In other words, `def:trans` takes a proof that `bind:x y:x ≡ y` and a proof that
`bind:y z:y ≡ z`, and gives us back a proof that `bind:x z:x ≡ z`. In order to
prove such a thing, we take a page out of the `def:sym` book, and pattern match
on both proofs, allowing Agda to unify `z` and `y`, before subsequently unifying
`y` and `x`:


Hidden

:     ```agda
  trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
      ```


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


Let's write this as a proposition:


```agda
  a^1≡a+b*0⅋₋₁ : (a b : ℕ) → a ^ 1 ≡ a + (b * zero)
  a^1≡a+b*0⅋₋₁ a b = ?
```

Of course, we can always prove something by doing the manual work of pattern
matching on our inputs. But we'd prefer not to whenever possible, as pattern
matching leaves you deep in the weeds of implementation details. Proof by
pattern matching is much akin to programming in assembly---you can get the job
done, but it requires paying attention to much more detail than we'd like.

Instead, we'd like to prove the above proposition out of reusable pieces. In
fact, we've already proven each of the individual steps---`def:^-identityʳ`,
`def:+-identityʳ`, and `def:*-zeroʳ` correspond to the salient steps on each
line of the proof. So let's do it.

Because we'd like to glue together some existing proofs, we begin with a call to
`def:trans`:

```agda
  a^1≡a+b*0⅋₀ : (a b : ℕ) → a ^ 1 ≡ a + b * 0
  a^1≡a+b*0⅋₀ a b
    = trans ? ?
```

This call to `def:trans` shows up in a deep saffron background. Despite being
new, this is nothing to worry about; it's just Agda's way of telling us it
doesn't yet have enough information to infer all of the invisible
arguments---but our next move will sort everything out.

We will follow our "pen and paper" proof above, where our first step was that
$a^1 = a$, which we called `^-identityʳ a`:

```agda
  a^1≡a+b*0⅋₁ : (a b : ℕ) → a ^ 1 ≡ a + b * 0
  a^1≡a+b*0⅋₁ a b
    = trans (^-identityʳ a) ?
```


Hidden

:     ```agda
  -- fix indentation
      ```


Our goal now has the type `bind:a b:a ≡ a + b * zero`, which we'd like to
simplify and implement in two steps. Thus, we use another call to
`def:trans`---this time to assert the fact that $a = a + 0$. We don't have a
proof of this directly, but we do have the opposite direction via
`bind:a:+-identityʳ a`. Symmetry will help us massage our sub-proof into the
right shape:

```agda
  a^1≡a+b*0⅋₂ : (a b : ℕ) → a ^ 1 ≡ a + b * 0
  a^1≡a+b*0⅋₂ a b
    = trans (^-identityʳ a)
    ( trans (sym (+-identityʳ a))
            ?
    )
```


Hidden

:     ```agda
  -- fix indentation
      ```


We are left with a goal whose type is `bind:a b:a + zero ≡ a + b * zero`. While
we know that `bind:b:*-zeroʳ b` shows $b \times 0 = 0$, and thus that
`bind:b:sym (*-zeroʳ b)` gives $0 = b \times 0$ , we are left with the problem
of getting this evidence into the right place. Whenever you have a proof for a
subexpression, you should think `def:cong`---dropping it in place with a hole
for its first argument and your subexpression proof as its second:

```agda
  a^1≡a+b*0⅋₃ : (a b : ℕ) → a ^ 1 ≡ a + b * 0
  a^1≡a+b*0⅋₃ a b
    = trans (^-identityʳ a)
    ( trans (sym (+-identityʳ a))
            (cong ? (sym (*-zeroʳ b)))
    )
```


Hidden

:     ```agda
  -- fix indentation
      ```

Congruence is highly-parameterized, and therefore often introduces unconstrained
metas while working interactively. As before, it's nothing to worry about.

Our final hole in this implementation is a function responsible for "targeting"
a particular subexpression in the bigger hole. Recall that here we have
`bind:a:a + zero`, and we would like to rewrite `ctor:zero` as `bind:b:b *
zero`. Thus, our function should target the `ctor:zero` in the expression
`bind:a:a + zero`.

In order to do so, we must give a function that *changes* the `ctor:zero`,
leaving the remainder of our expression alone. We can introduce a function via a
lambda:

```agda
  a^1≡a+b*0⅋₄ : (a b : ℕ) → a ^ 1 ≡ a + b * 0
  a^1≡a+b*0⅋₄ a b
    = trans (^-identityʳ a)
    ( trans (sym (+-identityʳ a))
            (cong (λ φ → ?) (sym (*-zeroʳ b)))
    )
```

The lambda (`λ`) here is input as [`Gl`](AgdaMode), while the phi (`φ`) is
[`Gf`](AgdaMode). We are required to use the lambda symbol, as it's Agda syntax,
but we chose phi only out of convention---feel free to pick any identifier here
that you'd instead prefer.

A useful trick for filling in the body of `def:cong`'s targeting function is to
copy the expression you had before, and replace the bit you'd like to change
with the function's input---`φ` in our case. Thus:

```agda
  a^1≡a+b*0 : (a b : ℕ) → a ^ 1 ≡ a + b * 0
  a^1≡a+b*0 a b
    = trans (^-identityʳ a)
    ( trans (sym (+-identityʳ a))
            (cong (λ φ → a + φ) (sym (*-zeroʳ b)))
    )
```


Hidden

:     ```agda
  -- fix indentation
      ```

Like always, we can rewrite our lambda `bind:a:λ φ → a + φ` by "canceling" the
`φ` on both sides. By writing this as a section, we get the slightly terser form
`bind:a:a +_`, giving rise to a shorter implementation:

```agda
  a^1≡a+b*0′ : (a b : ℕ) → a ^ 1 ≡ a + b * 0
  a^1≡a+b*0′ a b
    = trans (^-identityʳ a)
    ( trans (sym (+-identityʳ a))
            (cong (a +_) (sym (*-zeroʳ b)))
    )
```

Throughout this book, we will use this second notation whenever the subexpression
is easy to target, choosing an explicit lambda if the subexpress is particularly
nested. Using an explicit lambda always works, but we can't always get away
using the shorter form.

That being said, both forms are equivalent, and you may choose whichever you
prefer in your own code. However, by virtue of this presentation being a book,
we are limited by physical page widths, and thus will opt for the terser form
whenever it will simplify the presentation.

Composing proofs directly via `def:trans` does indeed work, but it leaves a lot
to be desired. Namely, the proof we wrote out "by hand" looks nothing like the
pile of `def:trans` calls we ended up using to implement `def:a^1≡a+b*0`.
Thankfully, Agda's syntax is sufficiently versatile that we can build a
miniature *domain specific language* in order to get more natural looking
proofs. We will explore this idea in the next section.


## Mixfix Parsing {#sec:mixfix-parsing}

As we saw when defining binary operators like `def:_∨_` in @sec:operators, and
again when representing negative integers via `ctor:-[1+_]` in @sec:integers, we
can define interesting syntax in Agda by leaving underscores around the place.
These underscores are a very general feature for interacting with Agda's
parser---an underscore corresponds to a syntactic hole that Agda intereprets as
a good reasonable place for an expression.

To illustrate this idea we can make a *postfix* operator by prefixing our
operator with an underscore, as in the factorial function:

```agda
  _! : ℕ → ℕ
  zero   ! = 1
  suc n  ! = suc n * n !
```

which works as we'd expect:

```
  _ : 5 ! ≡ 120
  _ = refl
```

Figuring out exactly how Agda's parser manages to make `def:_!` takes some
thought. The first thing to note is that function application binds more tightly
than *anything else* in the language; thus, our definition of `def:_!` is
implicitly parsed as:

```agda
  _!⅋₀ : ℕ → ℕ
  zero     !⅋₀ = 1
  (suc n)  !⅋₀ = (suc n) * n !⅋₀
```

From here, `def:_!` behaves normally with respect to the rules of operator
precedence. By default, if you haven't given an operator an explicit fixity
declaration (see @sec:fixity for a reminder), Agda will assign it a precedence
of 20.

But `def:_*_` has a precedence of 7, which means that `def:_!` binds more
tightly than `def:_*_` does, giving us our final parse as:

```agda
  _!⅋₁ : ℕ → ℕ
  zero     !⅋₁ = 1
  (suc n)  !⅋₁ = (suc n) * (n !⅋₁)
```

Sometimes it's desirable to make *prefix* operators, where the symbol comes
before the argument. While Agda parses regular functions as prefix operators,
writing an explicit underscore on the end of an identifier means we can fiddle
with its associativity. For example, while it's tedious to write `def:five` out of
`ctor:suc`s:

```agda
  five⅋₀ : ℕ
  five⅋₀ = suc (suc (suc (suc (suc zero))))
```

where each of these sets of parentheses is mandatory. We can instead embrace the
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
to write "true" tick marks which are merely to be counted.

However, we can assuage the ugliness by introducing some new syntax for
`ctor:zero`, as in:

```agda
  □ : ℕ
  □ = zero

  five⅋₁ : ℕ
  five⅋₁ = ∣ ∣ ∣ ∣ ∣ □
```

The square `def:□` can be input as [`sq`](AgdaMode). Whether or not this syntax
is better than our previous attempt is in the eye of the beholder. Suffice it to
say that we will always need some sort of terminal value when doing this style
of associativity to build values.

Mixfix parsing gets even more interesting, however. We can make *delimited
operators* like in @sec:integers by enclosing an underscore with syntax on
either side. For example, the mathematical notation for the floor function
(integer part) is $\lfloor{x}\rfloor$, which we can replicate in Agda:

```agda
  postulate
    ℝ : Set
    π : ℝ
    ⌊_⌋ : ℝ → ℕ

  three′ : ℕ
  three′ = ⌊ π ⌋
```

The floor bars are input via [``clL``](AgdaMode) and [clR](AgdaMode), while
`type:ℝ` is written as [`bR`](AgdaMode) and `def:π` is [`Gp`](AgdaMode). We
don't dare define the real numbers here, as they are a tricky construction and
would distract from the point.

Agda's profoundly flexible syntax means we are capable of defining many built-in
language features for ourselves. To illustrate, many ALGOL-style languages come
with the so-called "ternary operator[^ternary]" which does `if..else` in an
expression context.

Mixfix parsing means we can define true ternary operators, with whatever
semantics we'd like. But let's humor ourselves and define the conditional
ternary operator for ourselves. Since both `?` and `:` (the traditional syntax
of the "ternary operator") have special meaning in Agda, we must get a little
creative with our syntax.

Thankfully, we've got all of Unicode at our fingertips, and it's not hard to
track down some alternative glyphs. Instead, we will use `‽` ([`?!`](AgdaMode))
and `⦂` ([`z:`](AgdaMode)):

[^ternary]: Of course, the word "ternary" means only "three-ary", and has
  nothing to do with conditional evaluation.

```agda
  _‽_⦂_ : {A : Set} → Bool → A → A → A
  false ‽ t ⦂ f = f
  true ‽ t ⦂ f = t

  infixr 20 _‽_⦂_

  _ : ℕ
  _ = not true ‽ 4 ⦂ 1
```

In addition, since Agda doesn't come with any `if..else..` construct, we can
also trivially define such a thing:

```agda
  if_then_else_ : {A : Set} → Bool → A → A → A
  if_then_else_ = _‽_⦂_

  infixr 20 if_then_else_
```

which we can immediately use:

```agda
  _ : ℕ
  _ = if not true then 4 else 1
```

Due to our use of `keyword:infixr`, we can also nest `def:if_then_else_` with
itself:

```agda
  _ : ℕ
  _ = if not true then 4
      else if true then 1
      else 0
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
        { false  → 1
        ; true   → 4
        }
```

There is one small problem when doing mixfix parsing; unfortunately, we cannot
put two non-underscore tokens beside one another. For example, it might be nice
to make a boolean operator `def:_is equal to_`, but this is illegal in Agda. A
simple fix is to intersperse our tokens with hyphens, as in:

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


## Equational Reasoning {#sec:propreasoning}

Recall, we'd like to develop some syntax amenable to doing "pen and paper" style
proofs. That is, we'd like to write something in Agda equivalent to:

$$
\begin{aligned}
(a + b) \times c &= ac + bc \\
&= ac + cb \\
&= cb + ac
\end{aligned}
$$

Each side of an equals sign in this notation is equivalent to either `x` or `y`
in a type `bind:x y:x ≡ y`. In the pen and paper proof, we see *what* is equal,
but not *why.* Recall that in Agda, each sub-proof has its own name that we must
explicitly `def:trans` together, and these are the sorts of "why"s we want to
track.

In other words, proofs written in the above style are missing *justification* as
to *why exactly* we're claiming each step of the proof follows. In order to make
room for these justifications, we will use *Bird notation,* which attaches them
to the equals sign:

$$
\begin{aligned}
& (a + b) \times c \\
& \quad = (\text{distributivity}) \\
& ac + bc \\
& \quad = (\text{commutativity of $\times$}) \\
& ac + cb \\
& \quad = (\text{commutativity of $+$}) \\
& cb + ac
\end{aligned}
$$

This is the syntax we will emulate in Agda, although doing so is a little
finicky and will require much thought. To pique your interested, after this
section is complete we will be able to structure the above proof in Agda as:


Hidden

:     ```agda
  module SyntaxExample where
    open import Relation.Binary.PropositionalEquality hiding (cong)
    open ≡-Reasoning
    open import Data.Nat.Properties
      ```

```illegal
    ex : (a b c : ℕ) → (a + b) * c ≡ c * b + a * c
    ex a b c = begin
      (a + b) * c    ≡⟨ *-distribʳ-+ c a b ⟩
      a * c + b * c  ≡⟨ cong (a * c +_) (*-comm b c) ⟩
      a * c + c * b  ≡⟨ +-comm (a * c) (c * b) ⟩
      c * b + a * c  ∎
```



We will begin with a new module:

```agda
  module ≡-Reasoning where
```

The idea behind building this custom syntax is that we will make a series of
right-associative syntax operators, in the style of our tick marks in the
previous section. This syntax must eventually be terminated, analogously to how
`def:∣_` had to be terminated by `def:□`. In this case, we will terminate our
syntax using `ctor:refl`, that is, showing we've proven what we set out to.

You'll often see a formal proof ended with a black square (`∎`, input as
[qed](AgdaMode)), called a *tombstone* marker. Since proofs already end with
this piece of syntax, it's a great choice to terminate our right-associative
chain of equalities.

```agda
    _∎ : {A : Set} → (x : A) → x ≡ x
    _∎ x = refl

    infix 3 _∎
```

Note that the `x` parameter here is unused in the definition, and exists only to
point out exactly for which object we'd like to show reflexivity. Having sorted
out the "end" of our syntax, let's now work backwards.

The simplest piece of reasoning we can do is an equality that requires no
justification---think different expressions which automatically compute to the
same value, like `ctor:suc zero` and `def:one`. Again `x` exists only to give a
type to our proof, so we ignore it, choosing to return the proof we've already
got:

```agda
    _≡⟨⟩_ : {A : Set} {y : A}
          → (x : A)
          → x ≡ y
          → x ≡ y
    x ≡⟨⟩ p = p

    infixr 2 _≡⟨⟩_
```

These long brackets are input as [`<`](AgdaMode) and [`>`](AgdaMode),
respectively.

It's easy to lose the forest for the trees here, so let's work through an
example. We can write a trivial little proof, showing the equality of several
different ways of writing the number 4:

```agda
    _ : 4 ≡ suc (one + two)
    _ =
      4                ≡⟨⟩
      two + two        ≡⟨⟩
      suc one + two    ≡⟨⟩
      suc (one + two)  ∎
```

In this case, since everything is fully concrete, Agda can just work out the
fact that each of these expressions is propositionally equal to one another,
which is why we need no justifications. But you'll notice where once we had `x`
and `y`s in our types, now have a human-legible argument about *which* things
are equal!

Agda successfully parses the above, but it can be helpful for own sanity to
make the parse tree explicit. Rather than use infix notation, we'll use the full
unsectioned names for both `def:_≡⟨⟩_` and `def:_∎`, and then insert all of the
parentheses:

```agda
    _ : 4 ≡ suc (one + two)
    _ = _≡⟨⟩_  4
      ( _≡⟨⟩_  (two + two)
      ( _≡⟨⟩_  (suc one + two)
      ( _∎     (suc (one + two)))))
```

Recall that the implementation of `def:_≡⟨⟩` merely returns its second argument,
so we can simplify the above to:

```agda
    _ : 4 ≡ suc (one + two)
    _ = _≡⟨⟩_  (two + two)
      ( _≡⟨⟩_  (suc one + two)
      ( _∎     (suc (one + two))))
```

Our resulting expression begins with another call to `def:_≡⟨⟩_`, so we can make
the same move again. And a third time, resulting in:

```agda
    _ : 4 ≡ suc (one + two)
    _ =  _∎ (suc (one + two))
```

Replacing `def:_∎` now with *its* definition, we finally eliminate all of our
function calls, and are left with the rather underwhelming proof:

```agda
    _ : 4 ≡ suc (one + two)
    _ = refl
```

Have I pulled a fast one on you? Did we do all of this syntactic manipulation
merely as a jape? While it seems like we've done nothing of value here, notice
what happens if we try writing down an *invalid* proof---as in:

```illegal
    _ : 4 ≡ suc (one + two)
    _ =
      4              ≡⟨⟩
      one + two      ≡⟨⟩ -- ! 1
      suc one + two  ∎
```

At [1](Ann) we accidentally wrote `def:one` instead of `expr:suc one`. But, Agda
is smart enough to catch the mistake, warning us:

```info
zero != suc zero of type ℕ
when checking that the inferred type of an application
  one + two ≡ _y_379
matches the expected type
  4 ≡ suc (one + two)
```

So whatever it is that we've built, it's doing *something* interesting. Despite
ignoring every argument, somehow Agda is still noticing flaws in our proof. How
can it do such a thing? Let's look at the definition of `def:_≡⟨⟩_` again:

```agda
    _≡⟨⟩⅋₀_ : {A : Set} {y : A}
          → (x : A)
          → x ≡ y
          → x ≡ y
    x ≡⟨⟩⅋₀ p = p
```

Despite that fact that `x` is completely ignored in the *implementation* of this
function, it does happen to be used in the *type!* The reason our last example
failed to compile is because when we fill in `x`, we're changing the type of the
proof required in the second argument. But the second argument is already
`ctor:refl`. Thus, we're asking Agda to assign a type of `expr:3 ≡ 4` to
`ctor:refl`, which it just can't do. That's where the error comes from, and
that's why `def:_≡⟨⟩_` is less trivial than it seems.

While all of this syntax construction itself is rather clever, there is nothing
magical going on here. It's all just smoke and mirrors abusing Agda's mixfix
parsing and typechecker in order to get nice notation for what we want. Of
course, `def:_≡⟨⟩_` is no good for providing justifications. Instead, we will
use the same idea, but this time leave a hole for the justification.

```agda
    _≡⟨_⟩_
        : {A : Set}
        → (x : A)
        → {y z : A}
        → x ≡ y
        → y ≡ z
        → x ≡ z
    x ≡⟨ j ⟩ p = trans j p

    infixr 2 _≡⟨_⟩_
```

Our new function `def:_≡⟨_⟩_` works exactly in the same way as `def:_≡⟨⟩_`,
except that it takes a proof justification `j` as its middle argument, and glues
it together with its last argument `p` as per `def:trans`. We'll look at an
example momentarily.

We have one piece of syntax left to introduce, and will then play with this
machinery in full.

By way of poetic symmetry (rather than by way of `def:sym`) and to top things
off, we will add a piece of syntax to indicate the beginning of a proof block.
This is not strictly necessary, but makes for nice introductory syntax to let
the reader know that an equational reasoning proof is coming up:

```agda
    begin_ : {A : Set} → {x y : A} → x ≡ y → x ≡ y
    begin_ x=y = x=y

    infix 1 begin_
```

The `def:begin_` function does nothing, it merely returns the proof given. And
since its precedence is lower than any of our other `module:≡-Reasoning` pieces,
it binds after any of our other syntax, ensuring the proof is already complete
by the time we get here. The purpose really is just for decoration, but does
serve a purpose when we define analogous machinery in the context of preorders
(@sec:preorder-reasoning.)

Let's now put all of our hard work to good use. Recall the proof that originally
set us off on a hunt for better syntax:

```agda
    a^1≡a+b*0′⅋₁ : (a b : ℕ) → a ^ 1 ≡ a + b * 0
    a^1≡a+b*0′⅋₁ a b
      = trans (^-identityʳ a)
      ( trans (sym (+-identityʳ a))
              (cong (a +_) (sym (*-zeroʳ b)))
      )
```

The equational reasoning syntax we've built gives us a much nicer story for
implementing this. Rather than work with the big explicit pile of calls to
`def:trans`, after popping out of the `module:≡-Reasoning` module, we can just
open a new reasoning block:

```agda
  a^1≡a+b*0′⅋₂ : (a b : ℕ) → a ^ 1 ≡ a + b * 0
  a^1≡a+b*0′⅋₂ a b =
    begin
      a ^ 1
    ≡⟨ ^-identityʳ a ⟩
      a
    ≡⟨ sym (+-identityʳ a) ⟩
      a + 0
    ≡⟨ cong (a +_) (sym (*-zeroʳ b)) ⟩
      a + b * 0
    ∎
    where open ≡-Reasoning  -- ! 1
```

Note that at [1](Ann) we `keyword:open` the `module:≡-Reasoning` module. This is
a local binding, which brings our machinery into scope only for the current
definition. While it is possible to `keyword:open` `module:≡-Reasoning` at the
top level, this is generally frowned upon, as there will eventually be many
other sorts of reasoning we might want to perform.

For the purposes of this book's aesthetics, whenever we have the available
line-width, we will choose to format equational reasoning blocks as:

```agda
  a^1≡a+b*0′⅋₃ : (a b : ℕ) → a ^ 1 ≡ a + b * 0
  a^1≡a+b*0′⅋₃ a b = begin
    a ^ 1      ≡⟨ ^-identityʳ a ⟩
    a          ≡⟨ sym (+-identityʳ a) ⟩
    a + 0      ≡⟨ cong (a +_) (sym (*-zeroʳ b)) ⟩
    a + b * 0  ∎
    where open ≡-Reasoning
```

You are welcome to pick whichever style you prefer; the former is easier to type
out and work with, but the latter looks prettier once the proof is all sorted.

As you can see, this is a marked improvement over our original definition. The
original implementation emphasized the proof justification---which are important
to the computer---while this one emphasizes the actual steps taken---which is
much more important to the human. Whenever you find yourself doing
non-ergonomic things for the sake of the computer, it's time to take a step back
as we have done here. This is an important lesson, inside Agda and out.


## Ergonomics, Associativity and Commutativity

If you tried writing out the new definition of `def:a^1≡a+b*0′⅋₃` by hand, you
likely didn't have fun. It's a huge amount of keystrokes in order to produce all
of the necessary Unicode, let alone what the expression looks like between each
proof rewrite. Thankfully, Agda's interactive support can help us write out the
mechanical parts of the above proof, allowing us to focus more on the navigation
than the driving.

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

I have bound the first to [`step`](AgdaMode), and the latter to
[`begin`](AgdaMode).

Let's put these to work writing something more useful. We'd like to prove that
`def:_∨_` is associative, which is to say, that it satisfies the following law:

$$
(a \vee b) \vee c = a \vee (b  \vee c)
$$

We can write this in Agda with the type:


```agda
  ∨-assoc⅋₀ : (a b c : Bool) → (a ∨ b) ∨ c ≡ a ∨ (b ∨ c)
  ∨-assoc⅋₀ = ?
```

You should be able to prove this one for yourself:

```agda
  ∨-assoc : (a b c : Bool) → (a ∨ b) ∨ c ≡ a ∨ (b ∨ c)
  ∨-assoc false  b c = refl
  ∨-assoc true   b c = refl
```


Exercise

: Also prove `def:∧-assoc`.

Solution

:   ```agda
  ∧-assoc : (a b c : Bool) → (a ∨ b) ∨ c ≡ a ∨ (b ∨ c)
  ∧-assoc false  b c = refl
  ∧-assoc true   b c = refl
    ```


Not too hard at all, is it? Let's now try the same, except this time showing
that it's addition that's associative:


```agda
  +-assoc⅋₀ : (x y z : ℕ) → (x + y) + z ≡ x + (y + z)
  +-assoc⅋₀ = ?
```

A quick binding of variables, induction on `x`, and obvious use of `ctor:refl` gets
us to this step:

```agda
  +-assoc⅋₁ : (x y z : ℕ) → (x + y) + z ≡ x + (y + z)
  +-assoc⅋₁ zero     y z = refl
  +-assoc⅋₁ (suc x)  y z = ?
```

We're ready to start a reasoning block, and thus we can use our
[`begin`](AgdaMode) snippet:

```agda
  +-assoc⅋₂ : (x y z : ℕ) → (x + y) + z ≡ x + (y + z)
  +-assoc⅋₂ zero     y z = refl
  +-assoc⅋₂ (suc x)  y z = begin
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
  +-assoc⅋₃ : (x y z : ℕ) → (x + y) + z ≡ x + (y + z)
  +-assoc⅋₃ zero     y z = refl
  +-assoc⅋₃ (suc x)  y z = begin
    suc x + y + z    ≡⟨ ? ⟩
    suc x + (y + z)  ∎
    where open ≡-Reasoning
```

I always like to subsequently extend the top and bottom of the equality with
`def:_⟨⟩_`, like this:

```agda
  +-assoc⅋₄ : (x y z : ℕ) → (x + y) + z ≡ x + (y + z)
  +-assoc⅋₄ zero     y z = refl
  +-assoc⅋₄ (suc x)  y z = begin
    suc x + y + z    ≡⟨⟩
    ?                ≡⟨ ? ⟩
    ?                ≡⟨⟩
    suc x + (y + z)  ∎
    where open ≡-Reasoning
```

which recall says that the newly added lines are already equal to the other side
of the `def:_≡⟨⟩_` operator. We can fill in these holes with
[Solve/Normalise](AgdaCmd), which asks Agda to fully-evaluate both holes,
expanding as many definitions as it can while still making progress. Sometimes
it goes too far, but for our simple examples here, this will always be helpful.
The result looks like this:

```agda
  +-assoc⅋₅ : (x y z : ℕ) → (x + y) + z ≡ x + (y + z)
  +-assoc⅋₅ zero     y z = refl
  +-assoc⅋₅ (suc x)  y z = begin
    suc x + y + z      ≡⟨⟩
    suc (x + y + z)    ≡⟨ ? ⟩
    suc (x + (y + z))  ≡⟨⟩
    suc x + (y + z)    ∎
    where open ≡-Reasoning
```

This new hole is clearly a `cong suc`, which we can partially fill in:

```agda
  +-assoc⅋₆ : (x y z : ℕ) → (x + y) + z ≡ x + (y + z)
  +-assoc⅋₆ zero     y z = refl
  +-assoc⅋₆ (suc x)  y z = begin
    suc x + y + z      ≡⟨⟩
    suc (x + y + z)    ≡⟨ cong suc ? ⟩
    suc (x + (y + z))  ≡⟨⟩
    suc x + (y + z)    ∎
    where open ≡-Reasoning
```

and then invoke [Auto](AgdaCmd) to search for the remainder of the proof:

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

I quite like this workflow when tackling proofs. I introduce a [`begin`](AgdaMode)
snippet, use [Solve](AgdaCmd) to fill in either side. Then, I add new calls to
`def:_≡⟨⟩_` on both the top and bottom and fill those in via
[Solve/Normalise](AgdaCmd). Finally, I like to add [`step`](AgdaMode) in the
middle, and look for obvious techniques to help fill in the rest.

Let's do another proof together, this time one less trivial. First, we will
dash out a quick lemma[^lemma]:

[^lemma]: A lemma is a "boring" theorem: one that we prove only because it's on
  the path to something we care more about proving. There is no technical
  distinction between lemmas and theorems, the difference is only in the mind of
  the original mathematician.


Hidden

:     ```agda
  -- fix expr
      ```


Exercise (Easy)

:   Implement  `def:+-suc` `:` `expr:(x y : ℕ) → x + suc y ≡ suc (x + y)`


Solution

:   ```agda
  +-suc : (x y : ℕ) → x + suc y ≡ suc (x + y)
  +-suc zero     y = refl
  +-suc (suc x)  y = cong suc (+-suc x y)
    ```


Given `def:+-suc`, we would now like to show the *commutativity* of addition,
which is the idea that the idea of the arguments don't matter. Symbolically, the
commutativity property of addition is written as:

$$
a + b = b + a
$$

By this point you should be able to put together the type, and show the zero
case.


Exercise (Easy)

:   State the type of, perform induction on the first argument, and solve the
    `ctor:zero` case for `def:+-comm`.


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
for fun. Add a [`step`](AgdaMode), which will make things go saffron
temporarily, since Agda now has too many degrees of freedom to work out what you
mean:

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

Since the outermost function call (`ctor:suc`) is the same on both lines, we can
invoke `def:cong`:

```agda
  +-comm⅋₅ : (x y : ℕ) → x + y ≡ y + x
  +-comm⅋₅ zero     y = sym (+-identityʳ y)
  +-comm⅋₅ (suc x)  y = begin
    suc (x + y)  ≡⟨ cong suc ? ⟩
    suc (y + x)  ≡⟨ sym (+-suc y x) ⟩
    y + suc x    ∎
    where open ≡-Reasoning
```

and the finish the proof noticing that recursion will happily fill this hole.

```agda
  +-comm : (x y : ℕ) → x + y ≡ y + x
  +-comm zero     y = sym (+-identityʳ y)
  +-comm (suc x)  y = begin
    suc (x + y)  ≡⟨ cong suc (+-comm x y) ⟩
    suc (y + x)  ≡⟨ sym (+-suc y x) ⟩
    y + suc x    ∎
    where open ≡-Reasoning
```

As you can see, equational reasoning makes proofs much more legible, and using
Agda interactively assuages most of the pain of writing equational reasoning
proofs.


## Exercises in Proof

That covers everything we'd like to say about proof in this chapter. However,
there are a few more properties about the natural numbers we'd like to show for
future chapters, and this is the most obvious place to do it. These proofs are
too hard to do simply by stacking calls to `def:trans`, and therefore gain a lot
of tractability when done with equational reasoning.

The diligent reader is encouraged to spend some time proving the results in this
section for themselves; doing so will be an excellent opportunity to practice
working with Agda and to brandish new tools.


For our first exercise, `def:suc-injective` states that we can cancel outermost
`ctor:suc` constructors in equality over the naturals:


Hidden

:     ```agda
  -- fix expr
      ```

Exercise (Trivial)

: Prove `def:suc-injective` `:` `expr:{x y : ℕ} → suc x ≡ suc y → x ≡ y`.


Solution

:   ```agda
  suc-injective : {x y : ℕ} → suc x ≡ suc y → x ≡ y
  suc-injective refl = refl
    ```


Often, a huge amount of the work to prove something is simply in manipulating
the expression to be of the right form so that you can apply the relevant lemma.
This is the case in `def:*-suc`, which allows us to expand a `ctor:suc` on the
right side of a multiplication term.

```agda
  *-suc⅋ : (x y : ℕ) → x * suc y ≡ x + x * y
  *-suc⅋ = ?
```


Exercise (Challenge)

: Prove `def:*-suc`.


Hint

: Proving `def:*-suc` requires two applications of `def:+-assoc`, as well as one
  of `def:+-comm`.


Solution

:       ```agda
  *-suc : (x y : ℕ) → x * suc y ≡ x + x * y
  *-suc zero     y = refl
  *-suc (suc x)  y = begin
    suc x * suc y
      ≡⟨⟩
    suc y + x * suc y
      ≡⟨ cong (λ φ → suc y + φ) (*-suc x y) ⟩
    suc y + (x + x * y)
      ≡⟨⟩
    suc (y + (x + x * y))
      ≡⟨ cong suc (sym (+-assoc y x (x * y))) ⟩
    suc ((y + x) + x * y)
      ≡⟨ cong (λ φ → suc (φ + x * y)) (+-comm y x) ⟩
    suc ((x + y) + x * y)
      ≡⟨ cong suc (+-assoc x y (x * y)) ⟩
    suc (x + (y + x * y))
      ≡⟨⟩
    suc x + (y + x * y)
      ≡⟨⟩
    suc x + (suc x * y) ∎
    where open ≡-Reasoning
        ```


You will not be surprised to learn that multiplication is also commutative, that
is, that:

$$
a \times b = b \times a
$$


Hidden

:     ```agda
  -- fix expr
      ```

Exercise (Medium)

:   Prove `def:*-comm` `:` `expr:(x y : ℕ) → x * y ≡ y * x`.


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

Hidden

:     ```agda
  -- fix expr
      ```


Throughout this book, we will require a slew of additional mathematical facts.
They are not particularly *interesting* facts, and none of them should surprise
you in the slightest. Nevertheless, our insistence that we build everything by
hand requires this expenditure of energy. The propositions are thus given as
exercises, in order that you might find some value in the tedium.


Exercise (Medium)

:   Prove `def:*-distribʳ-+` `:` `(` `x y z :` `type:ℕ` `)` `→ (y` `def:+` `z)`
    `def:*` `x` `type:≡` `y` `def:*` `x` `def:+` `z` `def:*` `x`.


Solution

:     ```agda
  *-distribʳ-+ : (x y z : ℕ) → (y + z) * x ≡ y * x + z * x
  *-distribʳ-+ x zero     z = refl
  *-distribʳ-+ x (suc y)  z = begin
    (suc y + z) * x      ≡⟨⟩
    x + (y + z) * x      ≡⟨ cong (x +_) (*-distribʳ-+ x y z) ⟩
    x + (y * x + z * x)  ≡⟨ sym (+-assoc x (y * x) (z * x)) ⟩
    (x + y * x) + z * x  ≡⟨⟩
    suc y * x + z * x    ∎
    where open ≡-Reasoning
      ```


Hidden

:     ```agda
  -- fix expr
      ```



Exercise (Hard)

:   Prove `def:*-distribˡ-+` `:` `(` `x y z :` `type:ℕ` `) ` `→ x` `def:*` `(y`
    `def:+` `z)` `type:≡` `x` `def:*` `y` `def:+` `x` `def:*` `z`.


Solution

:     ```agda
  *-distribˡ-+ : (x y z : ℕ) → x * (y + z) ≡ x * y + x * z
  *-distribˡ-+ x y z = begin
    x * (y + z)    ≡⟨ *-comm x _ ⟩
    (y + z) * x    ≡⟨ *-distribʳ-+ x y z ⟩
    y * x + z * x  ≡⟨ cong (_+ z * x) (*-comm y x) ⟩
    x * y + z * x  ≡⟨ cong (x * y +_) (*-comm z x) ⟩
    x * y + x * z  ∎
    where open ≡-Reasoning
      ```


Hidden

:     ```agda
  -- fix expr
      ```


Exercise (Medium)

: Prove `def:*-assoc` `:` `expr:(x y z : ℕ) → (x * y) * z ≡ x * (y * z)`.


Solution

:     ```agda
  *-assoc : (x y z : ℕ) → (x * y) * z ≡ x * (y * z)
  *-assoc zero     y z = refl
  *-assoc (suc x)  y z = begin
    suc x * y * z        ≡⟨⟩
    (y + x * y) * z      ≡⟨ *-distribʳ-+ z y (x * y) ⟩
    y * z + (x * y) * z  ≡⟨ cong (y * z +_) (*-assoc x y z) ⟩
    y * z + x * (y * z)  ≡⟨⟩
    suc x * (y * z)      ∎
    where open ≡-Reasoning
      ```

Congratulations! You made it through all of the tedious proofs about numbers. Go
and celebrate with a snack of your choice; you've earned it!


## Wrapping Up

In @sec:propeq, we defined *propositional equality,* represented by `type:_≡_`,
which we used to prove to Agda that two values are syntactically equal. We
proved that equality is reflexive, symmetric, and transitive, as well as showing
that it is congruent (preserved by functions.) Furthermore, in
@sec:propreasoning, we built a little domain-specific language in Agda for doing
equational reasoning.

All of this machinery can be found be found in the standard library under
`module:Relation.Binary.PropositionalEquality`, however, for now we will only
publicly re-export `type:_≡_` and `module:≡-Reasoning`:

```agda
open import Relation.Binary.PropositionalEquality
  using (_≡_; module ≡-Reasoning)
  public
```

For reasons that will become clear in @sec:modarith, we will export the rest of
our propositional equality tools under a new module `module:PropEq`, which will
need to be opened separately:

```agda
module PropEq where
  open Relation.Binary.PropositionalEquality
    using (refl; cong; sym; trans)
    public
```

In @sec:mixfix-parsing we discussed mixfix parsing, where we leave underscores
in the names of identifiers in order to enable more interesting syntactic forms.
As examples of mixfix identifiers, we created ``def:if_then_else_ and
`def:case_of_`, which can be found in the standard library here:

```agda
open import Data.Bool
  using (if_then_else_)
  public

open import Function
  using (case_of_)
  public
```

While discussing common flavors of proofs in @sec:identities and
@sec:involutivity, we proved many facts about `def:_∨_` and `def:_∧_`. These can
all be found under `module:Data.Bool.Properties`:

```agda
open import Data.Bool.Properties
  using  ( ∨-identityˡ  ; ∨-identityʳ
         ; ∨-zeroˡ      ; ∨-zeroʳ
         ; ∨-assoc      ; ∧-assoc
         ; ∧-identityˡ  ; ∧-identityʳ
         ; ∧-zeroˡ      ; ∧-zeroʳ
         ; not-involutive
         )
  public
```

Additionally, we tried our hand at defining many facts about the natural
numbers---all of which can be found in the standard library under
`module:Data.Nat.Properties`:

```agda
open import Data.Nat.Properties
  using  ( +-identityˡ  ; +-identityʳ
         ; *-identityˡ  ; *-identityʳ
         ; *-zeroˡ      ; *-zeroʳ
         ; +-assoc      ; *-assoc
         ; +-comm       ; *-comm
         ; ^-identityʳ
         ; +-suc         ;  suc-injective
         ; *-distribˡ-+  ; *-distribʳ-+
         )
  public
```

---

```unicodetable
ʳ U+02B3 MODIFIER LETTER SMALL R (\^r)
ˡ U+02E1 MODIFIER LETTER SMALL L (\^l)
λ U+03BB GREEK SMALL LETTER LAMDA (\Gl)
π U+03C0 GREEK SMALL LETTER PI (\Gp)
φ U+03C6 GREEK SMALL LETTER PHI (\Gf)
′ U+2032 PRIME (\')
‽ U+203D INTERROBANG (\?!)
ℕ U+2115 DOUBLE-STRUCK CAPITAL N (\bN)
ℝ U+211D DOUBLE-STRUCK CAPITAL R (\bR)
→ U+2192 RIGHTWARDS ARROW (\to)
∎ U+220E END OF PROOF (\qed)
∣ U+2223 DIVIDES (\|)
∧ U+2227 LOGICAL AND (\and)
∨ U+2228 LOGICAL OR (\or)
∸ U+2238 DOT MINUS (\.-)
≡ U+2261 IDENTICAL TO (\==)
⌊ U+230A LEFT FLOOR (\clL)
⌋ U+230B RIGHT FLOOR (\clR)
□ U+25A1 WHITE SQUARE (\sq)
⟨ U+27E8 MATHEMATICAL LEFT ANGLE BRACKET (\<)
⟩ U+27E9 MATHEMATICAL RIGHT ANGLE BRACKET (\>)
⦂ U+2982 Z NOTATION TYPE COLON (\z:)
```

