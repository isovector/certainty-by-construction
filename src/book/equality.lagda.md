## Equality

```agda
module equality where

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


### Boolean Blindness

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


### Propositional Equality

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


### Unit Testing

Armed with the `_≡_` type (pronounced "propositional equality"), we are
immediately endowed with the ability to write unit tests for our programs. But
these are not exactly unit tests in the way you imagine them; these are more
documentation than they are tests. Recall that we have no means yet of showing
non-equality, therefore, any unit tests we write are *guaranteed to pass*
(assuming they compile in the first place.)

Want to show that `1 + 1` equals `2`? Easy! Write it as a type, and give the
proof as `refl`:

```agda
open import Data.Nat

_ : 1 + 1 ≡ 2
_ = refl
```

Behind the scenes, Agda evaluates the left- and right- sides of the equality,
sees that they're equal, and thus that `refl` is a satisfactory proof of that
statement. This will always be true for *examples:* fully-fleshed out,
unparameterized expressions, which is what unit tests are. "Show that given this
input, you get that output."

