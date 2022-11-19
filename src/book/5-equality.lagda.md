# Equality

```agda
module 5-equality where

open import Data.Nat

postulate
  todo : {A : Set} → A

module Examples where
  open import Relation.Binary.PropositionalEquality

  postulate
    IO : Set → Set
    ⊤ : Set
```

While math and programming share a lot of underpinning theory, that doesn't
necessarily mean that programming, as it exists in the real world, acknowledges
this connection! As a result, a lot of the work we need to do is to unlearn bad
habits. In this chapter we will discuss the semantics around equality: what
it is, how it works, and why it's a significantly more interesting topic than
most programmers give it credit for.

For most programmers, equality is a *predicate*[^predicate] over a pair of
objects. Depending on the discipline, these objects are not required to have the
same type, but we will ensure they do in our presentation here. Thus, equality
is of the type:

[^predicate]: A function that returns a boolean.

```agda
  module Irrelevant where
    postulate
      Bool : Set


      _==_ : {A : Set} → A → A → Bool
```

Sounds good, right? Notice that already we have played a slight game of
conflation; this is not a *notion* of equality, it is a query *testing* for
equality. Related, certainly, but two very different things.


## Boolean Blindness

If testing for equality is all you have ever known, it might be hard to
appreciate its shortcomings. The biggest problem here is that the result is just
a single bit, with meaning attached *only in the mind of the original
programmer.* At best, there is an implicit relationship between storing a `true`
value from the result of calling `_==_` and my business logic knowing the two
values are equal. You can easily imagine an application like this:

1. We have a user management system, where users have accounts.
2. Users can change their own accounts, but they can't change anyone else's.
3. Except for admins, who can change anyone's account.

Now imagine a function:

```example
updateUserProfile : UserProfile → IO ⊤
```

where `IO ⊤` is the type of procedures that change the state of the world. We'd
like to ensure all calls to `updateUserProfile` are guarded by a check that the
operating user is the owner of the profile, or is an admin. The problem now is
that there is no way to enforce that equality test actually gets run. If it ever
gets accidentally dropped, our application will contain a security vulnerability
--- a bad thing by any account!

A lot of software "best practices" come down to techniques for working around
problems like this. If `updateUserProfile` always makes the check as part of its
implementation, then at least callers can't forget to check the user's
authority. But what if the code-path has already verified the user's identity?
Are we forced to do a (probably costly) second authorization to call this
function?

As you can see, it's a surprisingly pervasive problem. And it all comes down to
a problem commonly known as *boolean blindness.*

Boolean blindness is a condition of projecting highly structured information
down into a single bit, saying "yes" or "no." But of course, having a "yes" or
"no" answer is only meaningful if you know what the question was. And boolean
blindness is all about throwing away the question.

The solution, as usual, is to induce a new type to help solve our problem.
Imagine if we had a type `a ≡ b` which *asserted* that `a` and `b` were equal.
That is to say, the only way of getting a value of type `a ≡ b` is to first show
that the two values are equal. Then we could change our program above:

```agda
  postulate
    User : Set
    UserProfile : User → Set
    IsAdmin : User → Set

  data CanChangeProfile (user owner : User) : Set where
    because-admin : IsAdmin user → CanChangeProfile user owner
    because-owner : user ≡ owner → CanChangeProfile user owner

  postulate
    updateUserProfile
      : {user owner : User}
      → CanChangeProfile user owner
      → UserProfile owner
      → IO ⊤
```

We have made several changes. First, `UserProfile` is now indexed by its owner,
which sets us up to track *data provenance.* If we know at the type level who
owns the profile, we can use the full power of the type system to help us
enforce our invariants.

The other big change is that `updateUserProfile` now also requires a
`CanChangeProfile user owner` argument in order to be called. This is a new type
we've created, which witnesses a proof that `user` is allowed to change the
profile owned by `owner`. There are two ways of showing `CanChangeProfile`: the
first is we're allowed to change it because we're an admin (as *witnessed* by an
`IsAdmin` proof). Alternatively, we can show we're allowed to change the profile
because we, the active user, are the one and same as the owner of the profile.

This seems like a small change, but it solves all of our problems in one fell
swoop. Call-sites are now required to pass along a `CanChangeProfile user owner`
proof when running `updateUserProfile`, which ensures it's impossible to forget
to make the check: failure to do so will result in not having enough arguments
to call the function!

We've also worked around the difficulty of doing superfluous checks. Because
a `CanChangeProfile` is just a normal piece of data, it can be passed around,
and so we can simply use the one we already have if we've made the check
earlier.


## Propositional Equality

Now that you're convinced there is value in representing equality as a type, how
do we actually go about doing that? While there are many notions of equality
(which we will discuss in @sec:many-equalities), we will settle for the time
being with "equivalent in representation" --- that is to say, two values are
equal if they are made up of the same bits in memory (but not requiring
necessarily the same pointers!) This means that `4 ≡ 2 + 2` (because `2 + 2`
computes to `4`), but that `4 ≢ 5` (because `4` and `5` are obviously different
numbers!)

The trick is to define a type with one value parameter, and one type index:

```agda
module X where
  infix 0 _≡_
  data _≡_ {A : Set} (lhs : A) : A → Set where
```

Our clever trick is the observation that *two things are only equal if they are
the same thing!* That is, we just require the two type indices to be the same
thing:

```agda
    refl : lhs ≡ lhs
```

This makes intuitive sense: things are only equal to themselves! We use the
obscure name `refl` as a shortened form of *reflexivity*: the mathematical
property that something is equal to itself.

Let's talk a little bit more about the mathematical properties of equality.
Beyond reflexivity, we also expect an equality to satisfy *symmetry* and
*transitivity.*

Symmetry means that if I know `a ≡ b`, I'd damn well like to also know that `b
≡ a`. Since we're saying these two things are the same, it shouldn't matter
which one is on the left and which is on the right.

Transitivity means that if I know `a ≡ b` and that `b ≡ c`, I should be able to
deduce that `a ≡ c` by "following the equalities."

If our `_≡_` type above truly is an equality in the mathematical sense, we must
prove that by implementing symmetry and transitivity for it. Recall that, by way
of Curry-Howard, propositions take the form of types, and proofs come as
programs. Therefore, to prove this thing is an equality, we must give programs
that witness it does what we say!

Before diving in to the proofs, our lives will be made better if we introduce a
few variables (in the mathematical sense.) Throughout the following programs, we
will always have some set `A : Set`, and three values of `A`, named `a`, `b` and
`c`:

```agda
  variable
    A : Set
    a b c : A
```

Introducing these variables means we don't need to assert their existence
every time we'd like to get work done. We simply say `a : A` in the variable
block, and elsewhere in our program if we refer to `a`, Agda knows what we're
talking about.

Returning to the problem, we'd like to show:

```agda
  sym : a ≡ b → b ≡ a
```

that is, we'd like to transform a proof of `a ≡ b` into a proof of `b ≡ a`. How
can we possibly do this? The trick is to remember that `_≡_` is just a data
type, which is to say it has a value (`refl`) at runtime that we can simply
pattern match on. When we pattern match on it, we learn that `a` and `b` are the
same thing, which then simplifies our problem to returning a proof that `a ≡ a`.
And that, we know how to do, because that's the definition of reflexivity!

Therefore:

```agda
  sym refl = refl
```

The proof of transitivity follows a similar technique.

Exercise

:   Give a proof of

    ```agda
  trans : a ≡ b → b ≡ c → a ≡ c
    ```


Solution

:   ```agda
  trans refl refl = refl
    ```


## Unit Testing

Armed with the `_≡_` type (pronounced "propositional equality"), we are
immediately endowed with the ability to write unit tests for our programs. But
these are not exactly unit tests in the way you imagine them; these are more
documentation than they are tests. Recall that we have no means yet of showing
non-equality, therefore, any unit tests we write are *guaranteed to pass*
(assuming they compile in the first place.)

Want to show that `1 + 1` equals `2`? Easy! Write it as a type, and give the
proof as `refl`:

```agda
  _ : 1 + 1 ≡ 2
  _ = refl
```

Behind the scenes, Agda evaluates the left- and right- sides of the equality,
sees that they're equal, and thus that `refl` is a satisfactory proof of that
statement. This will always be true for *examples:* fully-fleshed out,
unparameterized expressions, which is what unit tests are. "Show that given this
input, you get that output."

Tests of this form are the ultimate in test-driven development: write them
first, and continue programming not until the tests pass, but until the program
compiles!

Rather interestingly, we can also go the other direction; that is, write part of
the proposition (type), and then give the proof as `refl`, like in the
following:

```example
  _ : 9 * 9 ≡ ?
  _ = refl
```

Here the question mark indicates a "interaction hole" which is to say, part of
the program that we haven't figured out yet. However, given the `refl` proof on
the next line, the program in its entirety is specified; the only possible thing
that can go in the hole is `81` (or some other computation that immediately
reduces to `81`.) Because the hole is completely constrained, we can just ask Agda
to fill in the blank for us via [Agda](Solve):

```agda
  _ : 9 * 9 ≡ 81
  _ = refl
```

Just to illustrate the latter point, that any other computation that results in
`81` is also OK:

```agda
  _ : 9 * 9 ≡ 80 + 1
  _ = refl
```

In general, what's happening here is that behind the scenes, Agda will fully
evaluate each term on either side of the `_≡_`, and stop only when it's
convinced the two are equal. In the case that they don't evaluate to the same
thing, you'll get a type error informing you of that fact. For example, consider
the following (false) statement:

```wrong
  _ : 2 + 2 ≡ 5
  _ = refl
```

Agda responds in kind:

```error
4 != 5 of type ℕ
when checking that the expression refl has type 2 + 2 ≡ 5
```

Couldn't be clearer.


## Simple Proofs

Equipped with our new equality types, we are capable of writing some simple
proofs. For now we will limit ourselves to facts about natural numbers, which
are infinite in size and thus not trivial, but also simple enough that our
proofs can be short enough to get a feel for how they operate. Recall the
following facts about the definition of natural numbers and addition over them:

```example
  data ℕ : Set where
    zero : ℕ
    suc : ℕ → ℕ

  _+_ : ℕ → ℕ → ℕ
  _+_ zero n = n
  _+_ (suc m) n = suc (m + n)
```

Our first, extremely trivial, proof, will be that for any number $n$, it is the
case that $0 + n = n$. Since our proofs are programs (functions), they must be
given a name. In this case, a good name is probably the fact we are trying to
show, thus let's call our function `0+n≡n`:

```agda
  0+n≡n :
```

We must now decipher the mathematical statement into the language of types. We
are now asked to show something "for any number $n$," which means the caller has
*choice* for $n$, which should remind you of a function parameter.

After we've chosen $n$, we are immediately given a proof that $0 + n = n$, which
is just an equality type. Therefore, the type of `0+n≡n` is:

```agda
    (n : ℕ) → 0 + n ≡ n
```

Recall that `0` is merely syntactic sugar for `zero`, and so we can also read
this type off as

```example
    (n : ℕ) → zero + n ≡ n
```

But this fact comes directly from the definition of `_+_`, which says:

```example
  _+_ zero n = n
```

Because this is the *definition* of addition over natural numbers, Agda will
helpful compute it away, and instead shorten our proof burden to the fact that
`n ≡ n`, which of course, is just `refl`:

```agda
  0+n≡n n = refl
```

Notice that we must first bind the `n` argument on the left side of the equality
before setting the right as `refl`. This is necessary because if we do not bind
it, we are trying to put a *function value* on the right side of the equals, and
`refl` builds equality types, *not* function types.

As you can see, proving $0 + n = n$ was so easy as to be *trivial.* You might
therefore be amazed to learn that proving $n + 0 = n$ is significantly harder.
The first theorem was easy because, in essence, Agda was smart enough to have
done the work for us. It noticed that the definition of `_+_` immediately
eliminated a zero on the left, and therefore the problem became trivial.

However, for $n + 0 = n$, this is not the case. The zero is now on the right,
but the definition of `_+_` eliminates only on the left. Of course, we could
transform this problem into the former by making use of the fact that $m + n = n
+ m$, except there's a problem: we haven't proven that yet either!

So how can we proceed? The first step, as always, is to write the type:

```agda
  n+0≡n : (n : ℕ) → n + 0 ≡ n
```

We can now write the function body, leaving a hole for the actual proof:

```example
  n+0≡n n = ?
```

Since our problem doesn't immediately reduce to `refl`, we must do something
else. But the only thing we can do is to define `n+0≡n` by cases, one for every
possible way of building a `ℕ`. Of course, there are exactly two ways, via
`zero` and via `suc`, so we can split our proof into these two cases:

```example
  n+0≡n zero = ?
  n+0≡n (suc n) = ?
```

In the first case, we now know that $n = 0$, and thus are trying to show $0 + 0
= 0$, which, like in the last proof, is immediately evident by the
left-reduction of `_+_` when its first argument is zero. Therefore, this case is
just `refl`:

```agda
  n+0≡n zero = refl
```

```example
  n+0≡n (suc m) = ?
```

What are we now trying to show? Why, `suc m + 0 ≡ suc m`. But if you look at the
definition for `_+_`, we see that `suc m + x` is in fact equal to `suc (m + x)`
(in this case, $x = 0$). So we are really looking for a proof that `suc (m + 0)
≡ suc m`. Presumably if we had a proof that $m + 0 = m$, we could transform it
into the desired proof.

But hold on, modulo the variable names, $m + 0 = m$ is exactly the thing we're
trying to prove! This sounds like a perfect opportunity to use recursion:

```agda
  n+0≡n (suc m) =
    let m+0≡m = n+0≡n m
    in todo
```

All that's left is to transform our proof `m + 0 ≡ m` into a proof `suc (m + 0)
≡ suc m`, which doesn't sound too hard. Of course, we know that for any function
`f`, if we know the inputs are equal, we must be able to deduce that the outputs
are equal too.

This fact is known as *congruence,* which we will shorten to `cong` because it's
a proof that gets used *a lot.* Let's try our hand at defining `cong`. As
always, the type:

```agda
  cong : {A B : Set} → (f : A → B) → {x y : A} → x ≡ y → f x ≡ f y
```

This type is quite involved, so let's go through it slowly. Recall that any
arguments in curly braces are inferred by Agda, so we don't need to write them
by hand.

But what we're saying, piece by piece, is this. For any two types `{A B : Set}`,
for any function `f : A → B` between those two types, for any two arguments `{x
y : A}`, if we have a proof that `x ≡ y`, we can deduce the fact that `f x ≣ f
y`.

Proving `conga` is very easy. We need only look at the definition of the input
equality, see that it's `refl`, and therefore that the result type is actually
of type `f x ≡ f x` (and is therefore also `refl`):

```agda
  cong f refl = refl
```

Equipped with `cong`, we can finally complete our proof that `n+0≡n`, by filling
in the `todo` with `cong suc m+0≡m`:

```example
  n+0≡n (suc m) =
    let m+0≡m = n+0≡n m
    in cong suc m+0≡m
```

This technique of proving a simpler thing, often recursively, and then using
`cong` to massage it back into the right shape is one of the most powerful
techniques we have for proving things "by hand."

Let's consider the case now where we'd like to prove the other direction, namely
$n = n + 0$. Seeing as we just proved $n + 0 = n$, this one should be a cake
walk. And in fact it is. Recall our discussion earlier about symmetry, that
equality always respects the fact that if $a = b$ then $b = a$. Thus, all we
need to do is construct a proof going the other direction, and call `sym` on
that:

```agda
  n≡n+0 : (n : ℕ) → n ≡ n + 0
  n≡n+0 n = sym (n+0≡n n)
```


Exercise

:   Prove

    ```agda
  m+suc : (m n : ℕ) → suc m + n ≡ m + suc n
    ```


Solution

:   ```agda
  m+suc zero n = refl
  m+suc (suc m) n = cong suc (m+suc m n)
    ```

## Equational Reasoning

```agda
module Y where
  open import Relation.Binary.PropositionalEquality

  postulate
    n≡n+0 : (n : ℕ) → n ≡ n + 0
    m+suc : (m n : ℕ) → suc m + n ≡ m + suc n
```

The proofs we have looked at so far are probably not in the style you would
expect from years of doing arithmetic and algebra on paper, where we state a
fact, and then show a series of algebraic transformations to manipulate the fact
into some other shape. Consider, for example, how we might evaluate $(2 \times
3) \times (4 + 3) \div (1 + 1)$:

$$
\begin{aligned}
& (2 \times 3) \times (4 + 3) \div (1 + 1) \\
&= 6 \times (4 + 3) \div (1 + 1) \\
&= 6 \times 7 \div (1 + 1) \\
&= 6 \times 7 \div 2 \\
&= 42 \div 2 \\
&= 41
\end{aligned}
$$

This style of proof is known as *equational reasoning,* where we break a
computation down into a series of tiny steps, both to help ourselves as the
*writers* of the proof to simplify the proof burden, but also for *readers* to
more easily skim their way through a proof. Proofs, like code, are more
important to be readable than to be writeable.

We can do equational reasoning in Agda as well, by exploiting its extremely
flexible syntax. By including `where open ≡-Reasoning` at the end of each case
of our proof, we can enter the equational reasoning environment. Once inside the
environment, we can use `begin` to start a proof, and `∎` to end it (pronounced
"tombstone", or "Q.E.D.") To illustrate a simple worked proof:

```agda
  _ : (2 * 3) * (4 + 3) ≡ 42
  _ =
    begin
      (2 * 3) * (4 + 3)
    ≡⟨⟩
      6 * (4 + 3)
    ≡⟨⟩
      6 * 7
    ≡⟨⟩
      42
    ∎
    where open ≡-Reasoning
```

Instead of using a raw `≡` sign like we do in math, we instead need these funny
`≡⟨⟩` brackets, the purpose for which will become obvious in a moment. Of
course, this is a silly proof --- Agda can work it out for us via `refl`, since
it can simply perform the entire computation. But let's try another example,
where we can't just use `refl` like in `lemma1`:

```agda
  lemma1 : (n : ℕ) → (2 * 3) * n ≡ 6 * n + 0
```

This is the sort of proof we could bash our way through by pattern matching on
`n`, but that doesn't feel very *mathematical.* Instead, it would be nicer to
carry the computation out as far as we can, and then see what we can accomplish.
Begin by stating the problem:

```agda
  lemma1 n =
    begin
      (2 * 3) * n
```

Of course, this expression computes definitionally to:

```agda
    ≡⟨⟩
      6 * n
```

All that's required now is to introduce an add-zero to the right. While we could
go through the equational work of showing that must be so, it's easier to
instead rely on work we've already done. In fact, we've already proven that $n =
n + 0$ for any $n$ --- it's in a function we wrote called `n≡n+0`. Calling that
function with `6 * n` as the argument will get us the proof we need.

However, we can't just write `≡⟨⟩ 6 * n + 0` as the next step in the proof. We
need to clarify and say *why* that is the case. We need to give a
*justification* for this step. Of course, this justification is just `n≡n+0 (6 *
n)`; we simply need to tell Agda to use this fact. The trick is to put it
*inside* of the funny `⟨` brackets `⟩`, like so:

```agda
    ≡⟨ n≡n+0 (6 * n) ⟩
      6 * n + 0
```

Finally, we have gotten to where we want to be; our goal was to show that the
initial expression was equal to `6 * n + 0`, and so we are now finished. We need
only slap on the tombstone, and open our reasoning environment:

```agda
    ∎
    where open ≡-Reasoning
```

Of course, when doing these proofs for yourself, it's common to start
"outside-in." If you wanted to prove $x = y$, you could start by writing the
following template and elaborating your work:

```example
  _ =
    begin
      x
    ≡⟨ ? ⟩
      y
    ∎
    where open ≡-Reasoning
```

Equational reasoning lets us split up the proof burden by slowly approaching the
goal, rather than coming up with it fully-fledged. Not all mathematical domains
support this style of reasoning, but it's a godsend for those which do.


## Associativity of Addition

One beloved fact about addition is that it is *associative* --- that is to say,
for any numbers $m, n, k$ we have the fact that $m + (n + k) = (m + n) + k$.
This sounds like a boring property, but comes in useful all the time. In fact,
you probably use this property without knowing it every day. Associativity is
the reason that we don't need to write brackets around repeated chains of
addition; it simply doesn't matter where you put them! Any time you add up three
numbers, you are implicitly invoking the property of associativity; otherwise,
you'd have to be much more attentive as to which numbers you stuck together
first.

Exercise

:   Prove the associativity of addition of the natural numbers. That is, give a
    program of type:


    ```agda
  +-assoc : (m n k : ℕ) → m + (n + k) ≡ (m + n) + k
    ```


Solution

:   ```agda
  +-assoc zero n k = refl
  +-assoc (suc m) n k = cong suc (+-assoc m n k)
    ```


## Commutativity of Addition

When you're ready for a challenge, try the following exercise proving the
so-called *commutativity* property of addition. We will discuss commutativity
further in the next section.

Exercise

:     Prove the following property about addition. Hint: remember that you have
      case splitting, equational reasoning, `cong`, any lemma we've already
      proven, and recursion at your disposal.

      ```agda
  m+n≡n+m : (m n : ℕ) → m + n ≡ n + m
      ```

Solution

:     ```agda
  m+n≡n+m zero n = n≡n+0 n
  m+n≡n+m (suc m) n = begin
    suc m + n    ≡⟨⟩
    suc (m + n)  ≡⟨ cong suc (m+n≡n+m m n) ⟩
    suc (n + m)  ≡⟨ m+suc n m ⟩
    n + suc m    ∎
    where open ≡-Reasoning
      ```


The previous exercise had you show the well-known property of addition that $m +
n = n + m$, known as the *commutativity of addition.* In general, a commutative
operation is one in which you can change the order of the arguments without
changing the result.

As you saw when trying to prove commutativity, this proof is by no means
trivial! And yet it's a fact all humans know (though perhaps not symbolically.)
It's a familiar notion because the idea is drilled into us in our youth, but
it's unclear *why* this fact must be true.

I like this property because it really helps drive home what a proof really is.
Of course we all know that $m + n = n + m$, but how do you actually prove it? We
can look at hundreds of examples and get a *probabilistic* understanding of the
property, and convince ourselves it's *probablay* true. But that simply isn't a
proof. And when you look at our computational definition of `_+_` which is
clearly asymmetric (favoring computation on the left hand side) it really isn't
obvious why those chains of `suc`s should actually end up being the same.

I like this proof because it forces a mental shift, from "obviously this is
true" to "how do I give a convincing argument of it?" And to me, that is at the
heart of mathematics. Of course, this is also true in programming. It's no good
to "know" how to actuate a robot to find its way around; in the process of
writing the program, you will realize there are significantly more challenges
than you thought. To quote Bertrand Russell, one of the pioneering fathers of
the logical foundation that has grown into modern constructive mathematics:

> Everything is vague to a degree you do not realize till you have tried to make
> it precise.

Amen. This is something you already appreciate as a programmer. We need now only
broaden that understanding to mathematics and to previously-informal reasoning
about software

Like associativity, commutativity is a very important property for *actually
getting work done.* When combined with associativity, we are given the ability
to arbitrarily split up addition tasks. That means, we can distribute the
problem to several works, and accumulate the individual results without any
expensive book-keeping. You will notice that commutativity and associativity are
crucial pieces of most distributed algorithms. Have you ever stopped to wonder
why all examples of the popular MapReduce programming model are about counting
words? Because the technique simply doesn't work for non-commutative or
non-associative operations. Pretty sneaky!


## Multiplication

Enough about addition. Let's briefly discuss multiplication, but will leave the
proof burden to you to show all of our desired properties about this beloved
operation.

Just like we can view addition as repeated counting, we can view multiplication
as repeated addition:

```shambple
_*_ : ℕ → ℕ → ℕ
_*_ zero n = zero
_*_ (suc m) n = n + m * n
```

This last equation is the familiar property that $(1 + m) \times n = n + m
\times n$. You'll notice a definite pattern of recursion in all of these
definitions; split the definition into cases, and then use "obvious"
mathematical facts to give the answers. Then, go back, and prove the
less-obvious facts.

Following the process

```agda
  *-zero : (n : ℕ) → n * zero ≡ zero
  *-zero zero = refl
  *-zero (suc n) = *-zero n

  *-distrib-+r : (m n k : ℕ) → (m + n) * k ≡ m * k + n * k
  *-distrib-+r zero n k = refl
  *-distrib-+r (suc m) n k =
    begin
      (suc m + n) * k
    ≡⟨⟩
      k + (m + n) * k
    ≡⟨ cong (k +_) (*-distrib-+r m n k) ⟩
      k + (m * k + n * k)
    ≡⟨ +-assoc k (m * k) (n * k) ⟩
      k + m * k + n * k
    ≡⟨⟩
      suc m * k + n * k
    ∎
    where open ≡-Reasoning

  *-suc : (m n : ℕ) → m * suc n ≡ m + m * n
  *-suc zero n = refl
  *-suc (suc m) n =
    begin
      suc m * suc n
    ≡⟨⟩
      suc (n + m * suc n)
    ≡⟨ cong (\ φ → suc (n + φ)) (*-suc m n) ⟩
      suc (n + (m + m * n))
    ≡⟨ cong suc (+-assoc n m (m * n)) ⟩
      suc (n + m + m * n)
    ≡⟨ sym (cong suc (+-assoc n m (m * n))) ⟩
      suc (n + (m + m * n))
    ≡⟨ todo ⟩
      suc (m + (n + m * n))
    ≡⟨⟩
      suc (m + suc m * n)
    ≡⟨⟩
      suc m + suc m * n
    ∎
    where open ≡-Reasoning

  *-assoc : (m n k : ℕ) → m * (n * k) ≡ (m * n) * k
  *-assoc zero n k = refl
  *-assoc (suc m) n k =
    begin
      suc m * (n * k)
    ≡⟨⟩
      n * k + m * (n * k)
    ≡⟨ cong (\ φ → n * k + φ) (*-assoc m n k) ⟩
      n * k + (m * n) * k
    ≡⟨⟩
      (n * k) + (m * n) * k
    ≡⟨ sym (*-distrib-+r n (m * n) k) ⟩
      (n + m * n) * k
    ≡⟨⟩
      (suc m * n) * k
    ∎
    where open ≡-Reasoning

  *-comm : (m n : ℕ) → m * n ≡ n * m
  *-comm zero n = sym (*-zero n)
  *-comm (suc m) n =
    begin
      suc m * n
    ≡⟨⟩
      n + m * n
    ≡⟨ cong (n +_) (*-comm m n) ⟩
      n + n * m
    ≡⟨ sym (*-suc n m) ⟩
      n * suc m
    ∎
    where open ≡-Reasoning
```






```example
  0+n≡n+0 : (n : ℕ) → 0 + n ≡ n + 0
  0+n≡n+0 n = trans (0+n≡n n) (sym (n+0≡n n))
```


## Intentional vs Extensional Equality

Based on the above examples, equality might seem like the clearest thing in the
world. This is not entirely the case, however. For numbers and booleans and
strings, the story is cut and dry, but difficulties arise when we begin to think
about more exotic types. In particular, let's take some time to discuss when two
functions are equal.

When *are* two functions equal? This is a hard problem. Consider functions `f`,
`g` and `h`:

```agda
f : ℕ → ℕ
f x = x + 2

g : ℕ → ℕ
g x = 2 * x

h : ℕ → ℕ
h x = suc (suc x)
```

Clearly functions `f` and `g` are *not* equal. But the answer is less clear as
to whether `f` and `h` are. The two functions are syntactically entirely
different, but compute the same output given the same input. If you were to draw
the plots of these two functions, they'd look identical.

But this isn't necessarily the whole story; are `bubblesort` and `mergesort`
equal functions? They both return the same outputs given the same inputs,
however, they do so in entirely different ways, and with entirely different
runtime asymptotic complexities!

Yikes. What a mess we find ourselves in.

Many programming languages sidestep the problem by comparing functions by their
pointer equality. In these cases, two functions are the same if they occur at
the same place in memory. But this is unsatisfying on many levels. First and
foremost, it is an abstraction leak. Functions are mathematical ideas,
completely separate from the hardware they run on. There exist models of
computation that don't have memory, and thus such a decision allows you to
deduce properties of the hardware you're running on --- which ought to be a
no-no. Mathematics doesn't run on any hardware; it just *is.* Equally abhorrent
in pointer equality of functions is that it means two identical, syntactically
byte-for-byte source identical functions might not compare equal, due to
unpredictable quirks of how the runtime has decided to lay out memory. This
means that a program which might work today could fail tomorrow based only on a
differing mood of the runtime. There are many ways to describe this behavior,
but neither "sane" nor "mathematical" nor even "good programming practice" are
one.

The mathematical solution to this problem is to split equality of function types
into two camps. There is a world in which `bubblesort` and `mergesort` *are* the
same function, and a world in which they are not. In the first world, we care
only that the functions map equal inputs to equal outputs. In the latter, we
require the two functions to be defined in exactly the same way. These two
approaches to equality are known as *extensional* and *intensional* equality,
respectively.

Intensionality continues to be a challenge to define. Do variable names matter?
What about no-ops? The entire thing is a boondoggle, and we will not delve
deeper into this idea.

Instead, we will worry only about extensional equality. Two functions are thus
equal if they map inputs to equal outputs. That is to say, given two functions
`f` and `g`, we'd like the following property to hold:

```agda
open import Relation.Binary.PropositionalEquality hiding (_≗_)

_≗_ : {A B : Set} → (A → B) → (A → B) → Set
_≗_ {A} f g = (a : A) → f a ≡ g a
```

We can read this as `f ≗ g` is a *type synonym* for a function that transforms
`a : A`s into proofs of equality between `f a` and `g a`.







