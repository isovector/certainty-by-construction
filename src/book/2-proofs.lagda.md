# Proofs

In this chapter we will take our first looks at what constitutes a mathematical
proof, as well as how to articulate proofs in Agda. In the process, we will need
to learn a little more about Agda's execution model and begin exploring the
exciting world of dependent types.

My first encounter with proofs was in a first-year university algebra course,
where I quickly learned I had no idea what a proof was (and had the marks to
prove it!) A proof is supposed to be a mathematical argument that other
mathematicians find convincing; my problem was, things that seemed convincing to
me were inevitably unconvincing to the professor. Perhaps you have encountered
this same problem. If so, there is good news for you in this chapter --- working
in Agda makes it exceptionally clear what constitutes a proof; either Agda is
happy with what you've written, or it isn't. In either case, the feedback cycle
is extremely quick, and it's easy to iterate until you're done.

We begin by starting a new module for the chapter, and importing the necessary
proof machinery from Agda's standard library.

```agda
module 2-proofs where

open import Relation.Binary.PropositionalEquality
```

In earlier chapters, we referred to this `PropositionalEquality` module as being
Agda's support for unit testing. This was a little white lie, that we are now
ready to come clean regarding. In fact, `PropositionalEquality` is the standard
module for doing proofs about Agda's computation model --- of which unit tests
are a very special case. For the remainder of this chapter, we will prove some
facts about the number systems we built in the last.


## Facts About Booleans

To wet our whistle, we will begin by proving some facts about booleans. Because
booleans exist in a very limited universe (there are only two of them,) the
proofs tend to be rather stupid. Nothing clever is necessary to prove facts
about booleans, we can simply enumerate every possible case and show that the
desired property holds. Of course, this strategy won't take us very far in
bigger types, but we will find it informative for the time being.

Rather than working directly over the booleans we defined in the last chapter,
we can instead use `Data.Bool` which is definition-for-definition compatable.

```agda
module Bool-Properties where
  open import Data.Bool
```

We began our exploration of booleans by defining the `not : Bool → Bool`
function which swaps between `true` and `false`. One fact we might want to show
about `not` is that it is it's own inverse, that is, applying `not` twice is the
same as not having applied it at all. This is a mathematical property known as
*involutivity,* and thus, we would like to show that `not` is involutive.

In words, the statement we'd like to prove is:

> For any boolean $x$, it is the case that `not (not x)` is equal to `x`.

We can encode this in Agda by defining `not-involutive`:

```agda
  not-involutive
      : (x : Bool)
      → not (not x) ≡ x
```

which says exactly the same thing. For any `x : Bool`, we can produce `not (not
x) ≡ x`, which is to say, a proof that `not (not x)` is equal to `x`. The `_≡_`
type comes from the `PropositionalEquality` module, and the majority of this
chapter will be our exploration in what it is and how it works.

How can we prove our desired fact? One way would be to give a proof that this is
the case when `x = true` and when `x = false`. Since there are no other options
for `x`, if we can prove both cases, the proposition must hold in general.

Proofs in Agda are no different than functions; therefore, we can define
`not-involutive` as a function that takes a single parameter, and subsequently
pattern match that parameter into its two cases:

```agda
  not-involutive false = refl
  not-involutive true  = refl
```

On the right hand side of these two clauses, we have given `refl`, which is
Agda's way of saying "it is obvious that the proof holds." Of course, it must be
obvious to *Agda* that the proof holds. The question is, why is Agda obviously
convinced in both of these cases?

Recall the definition of `not`:

```agda
  not⅋ : Bool → Bool
  not⅋ false = true
  not⅋ true = false
```

We are originally trying to show `not (not x) ≡ x`, for some `x`. In
`not-involutive`, when we subsequently pattern match on `x`, we learn what `x`
is. In the first case, we learn `x = false`, and therefore, the statement we're
trying to prove becomes `not (not false) ≡ false`. But Agda knows how to compute
`not false`, which it then reduces to the claim `not true ≡ false`. Again, Agda
knows how to compute `not true`, so it reduces further to `false ≡ false`. Such
a statement is obviously true, and so Agda is happy when we say the proof is
`refl`. The exact same argument holds when `x = true`.

The word `refl` is short for *reflexivity,* which is the mathematical word for
the idea that something is equal to itself. This is a rather indisputable fact,
to say otherwise would be to throw out the meaning of equality altogether. The
type of `refl` looks like this:

```agda
  postulate
    refl⅋ : {A : Set} {a : A} → a ≡ a
```

which is to say, for any value `x` of any type `A`, `x` is equal to itself. When
we were required to show `false ≡ false`, Agda inferred that we meant `A = Bool`
and `x = false`.

Looking back at the definition of `not-involutive`, it appears that the
right-hand side doesn't depend at all on the value of the argument. Could we
have instead gotten away by writing `not-involutive x = refl`? Unfortunately
not. We require the pattern match to get Agda "unstuck" and able to reduce the
definition of `not`.

One common idiom in Agda's standard library are the `-identityˡ` and
`-identityʳ` functions, which are properties stating a binary operation has
left- and right- identities, respectively. An *identity* is any value which
doesn't change the result. As shown in the previous chapter, `false` is an
identity for logical OR, but we can prove this fact more formally now. Behold:

```agda
  ∨-identityˡ : (x : Bool) → false ∨ x ≡ x
  ∨-identityˡ x = refl
```

What's going on here? How can the right hand side be `refl` without having
pattern matched on the left? Didn't we just have a length discussion about
exactly this? The answer comes from the definition of `_∨_`, which as you will
recall is:

```agda
  _∨⅋_ : Bool → Bool → Bool
  false ∨⅋ other = other
  true  ∨⅋ other = true
```

The first equation here states that anything of the form `false ∨ other` gets
immediately rewritten to `other`, which is exactly what's happening in
`∨-identityʳ`. Agda doesn't need us to pattern match on `x` because the
definition of `_∨_` doesn't need inspect it in order to reduce.

Contrast `∨-identityˡ` to its mirror image:

```agda
  ∨-identityʳ : (x : Bool) → x ∨ false ≡ x
  ∨-identityʳ false = refl
  ∨-identityʳ true  = refl
```

Here we are required to pattern match on `x` because `_∨_` pattern matches on
its first argument, and thus this is the only way to get Agda unstuck. This
kind of asymmetry is intrinsic to Agda's evaluation model, and thus we must be
conscious of it. As a general rule, anything you pattern match on in the
implementation is something you'll need to pattern match on in a proof. As you
become more proficient in Agda, you will start to get an eye for how to write
definitions that are optimized for ease-of-proof. For any particular function,
many definitions are possible, but they will all compute the answer differently,
and thus will have impact upon how we go about proving things.


Exercise

: State and prove `∧-identityˡ`.


Solution

:   ```agda
  ∧-identityˡ : (x : Bool) → true ∧ x ≡ x
  ∧-identityˡ x = refl
    ```


Exercise

: State and prove `∧-identityʳ`.


Solution

:   ```agda
  ∧-identityʳ : (x : Bool) → x ∧ true ≡ x
  ∧-identityʳ false = refl
  ∧-identityʳ true  = refl
    ```


Identities are especially nice properties to find when designing mathematical
objects; they act like the number 1 does when multiplying (thus the name
"identity".) Identities are useful "placeholders" in algorithms when you need a
default value, but don't have an obvious choice. We will discuss the important
roles of identities further in @sec:objects.

Another useful property for a binary operator is the notion of *associativity,*
which is a familiar fact most commonly known about arithmetic, namely:

$$
(a + b) + c = a + (b + c)
$$

That is to say, the exact placement of parentheses is unimportant for
associative operators, and for that reason, we are justified in leaving them
out, as in:

$$
a + b + c
$$

Technically such a statement is ambiguous, but the great thing about
associativity is it means the two possible parses are equal. As it happens,
`_∨_` is associative, as we can show:

```agda
  ∨-assoc : (a b c : Bool) → (a ∨ b) ∨ c ≡ a ∨ (b ∨ c)
  ∨-assoc false b c = refl
  ∨-assoc true  b c = refl
```


Exercise

: Is `_∧_` also associative? If so, prove it. If not, explain why.


Solution

:   ```agda
  ∧-assoc : (a b c : Bool) → (a ∧ b) ∧ c ≡ a ∧ (b ∧ c)
  ∧-assoc false b c = refl
  ∧-assoc true  b c = refl
    ```

We have two final properties we'd like to prove about our binary number system,
which is the fact that `_∨_` and `_∧_` are *commutative.* Commutative operators
are ones which are symmetric about their arguments. Again, this property is best
known as a fact about addition:

$$
a + b = b + a
$$

In general, a binary operator is commutative if we can swap its arguments
without changing the result. We can prove this about `_∨_` by pattern matching
on every argument:

```agda
  ∨-comm : (x y : Bool) → x ∨ y ≡ y ∨ x
  ∨-comm false false = refl
  ∨-comm false true  = refl
  ∨-comm true  false = refl
  ∨-comm true  true  = refl
```

While such a thing works, this is clearly a very tedious proof. The amount of
effort grows exponentially with the number of arguments, which feels especially
silly when the right hand side is always just `refl`. Thankfully, Agda has a
tactic for this. A *tactic* is a generic algorithm for producing a proof term;
and in this case, we're looking for the `case-bash!` tactic. Using `case-bash!`,
we can rewrite `∨-comm` as:

```agda
  ∨-comm⅋ : (x y : Bool) → x ∨ y ≡ y ∨ x
  ∨-comm⅋ = case-bash!
    -- TODO(sandy): find the right module
    where open import case-bash
```

Similarly, we can case bash our way through `∧-comm`, though if we'd like, we
can import `case-bash` into the global scope:

```agda
  open import case-bash

  ∧-comm : (x y : Bool) → x ∧ y ≡ y ∧ x
  ∧-comm = case-bash!
```

We've now had some experience proving theorems about our code. Of course, the
finiteness of the booleans has dramatically simplified the problem, requiring no
creativity in finding the proofs; indeed the fact that the computer can write
them for us via `case-bash!` is a little disheartening. Nevertheless, it's a
great opportunity to get a feel for proving in a safe environment. We'll have to
learn some new tricks if we'd like to succeed in proving things about the
natural numbers.

In the future, if you need any properties about the booleans, you don't need to
prove them for yourself; most things you could possibly want are already proven
for you under `Data.Bool.Properties`.


## Facts About Natural Numbers

```agda
module Nat-Properties where
  open import Data.Nat
```

In this section, our goal is to prove associativity and commutativity of both
addition and multiplication of natural numbers. Now that we are working in an
infinite universe, with more naturals than we can enumerate, we find ourselves
lost in the dark. Our proof knowledge learned from boolean exposure is simply
not powerful to help us here. We are going to need to learn some new tricks.

The first and most important new technique we will need is `cong`, which you
already have available to you via `PropositionalEquality`. Nevertheless, its
definition is the rather overwhelming:

```agda
  cong⅋
      : {A B : Set} {x y : A}
      → (f : A → B)
      → x ≡ y
      → f x ≡ f y
  cong⅋ f refl = refl
```

This peculiar function's name is short for *congruence,* which is the property
that functions preserve equality. That is, given some function `f`, we know that
if `x ≡ y`, then it is surely the case that `f x ≡ f y`. It has to be, because
`x` and `y` are the same thing, so the function must map the one thing to one
place. Congruence is a real workhorse in proving, as it allows us to "move" a
proof of a smaller claim into the right place in a larger theorem. We will see
an example of it shortly.

Proving associativity of multiplication over the natural numbers is a very tall
order; this is not a fact that comes lightly to us. In fact, we will need to
prove nine smaller theorems first, gradually working our way up to the eventual
goal. This is not unlike software, where we decompose hard problems into easier
problems, solve them, and then recombine the solutions. A small theorem, proven
along the way of a bigger theorem, is often called a *lemma.*

Our first lemma is `+-identityʳ`, which is to say, that 0 acts as a right
identity to addition. That is, we're looking to show the following:

```agda
  +-identityʳ : (x : ℕ) → x + 0 ≡ x
```

We begin as we did for booleans; pattern matching on the argument. If it's zero,
we're already done:

```agda
  +-identityʳ zero = refl
```

If our parameter isn't zero, then it must be `suc x` for some `x`. In this case,
our goal is refined as `suc (x + 0) ≡ suc x`, which you will notice is very
close to `x + 0 ≡ x` --- that is, the thing we're trying to prove in the first
place! Recursion is almost certainly the answer, but it's not quite the right
shape; somehow we need to pin a `suc` on both sides.

Fortunately, this is exactly what `cong` does. Recursion will give us a proof of
`x + 0 ≡ x`, which we need to somehow massage into a proof that `suc (x + 0) ≡
suc x`. Therefore, our lemma is completed as:

```agda
  +-identityʳ (suc x) = cong suc (+-identityʳ x)
```


Exercise

: Use a similar technique to prove `+-suc : (x y : ℕ) → x + suc y ≡ suc (x + y)`.


Solution

:   ```agda
  +-suc : (x y : ℕ) → x + suc y ≡ suc (x + y)
  +-suc zero y = refl
  +-suc (suc x) y = cong suc (+-suc x y)
    ```


```agda
  +-comm : (x y : ℕ) → x + y ≡ y + x
  +-comm zero y = sym (+-identityʳ y)
  +-comm (suc x) y = begin
    suc x + y    ≡⟨⟩
    suc (x + y)  ≡⟨ cong suc (+-comm x y) ⟩
    suc (y + x)  ≡⟨ sym (+-suc y x) ⟩
    y + suc x    ∎
    where open ≡-Reasoning

  +-assoc : (x y z : ℕ) → (x + y) + z ≡ x + (y + z)
  +-assoc zero y z = refl
  +-assoc (suc x) y z = begin
    (suc x + y) + z    ≡⟨⟩
    suc (x + y) + z    ≡⟨⟩
    suc ((x + y) + z)  ≡⟨ cong suc (+-assoc x y z) ⟩
    suc (x + (y + z))  ≡⟨⟩
    suc x + (y + z)    ∎
    where open ≡-Reasoning

  *-identityʳ : (x : ℕ) → x * 1 ≡ x
  *-identityʳ zero = refl
  *-identityʳ (suc x) = cong suc (*-identityʳ x)

  *-zeroʳ : (x : ℕ) → x * 0 ≡ 0
  *-zeroʳ zero = refl
  *-zeroʳ (suc x) = *-zeroʳ x

  *-suc : (x y : ℕ) → x * suc y ≡ x + x * y
  *-suc zero y = refl
  *-suc (suc x) y = begin
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

  *-comm : (x y : ℕ) → x * y ≡ y * x
  *-comm zero y = sym (*-zeroʳ y)
  *-comm (suc x) y = begin
    suc x * y  ≡⟨⟩
    y + x * y  ≡⟨ cong (y +_) (*-comm x y) ⟩
    y + y * x  ≡⟨ sym (*-suc y x) ⟩
    y * suc x  ∎
    where open ≡-Reasoning

  *-distribʳ-+ : (x y z : ℕ) → (y + z) * x ≡ y * x + z * x
  *-distribʳ-+ x zero z = refl
  *-distribʳ-+ x (suc y) z = begin
    (suc y + z) * x      ≡⟨⟩
    x + (y + z) * x      ≡⟨ cong (x +_) (*-distribʳ-+ x y z) ⟩
    x + (y * x + z * x)  ≡⟨ sym (+-assoc x (y * x) (z * x)) ⟩
    (x + y * x) + z * x  ≡⟨⟩
    suc y * x + z * x    ∎
    where open ≡-Reasoning

  *-assoc : (x y z : ℕ) → (x * y) * z ≡ x * (y * z)
  *-assoc zero y z = refl
  *-assoc (suc x) y z = begin
    suc x * y * z        ≡⟨⟩
    (y + x * y) * z      ≡⟨ *-distribʳ-+ z y (x * y) ⟩
    y * z + (x * y) * z  ≡⟨ cong (λ φ → y * z + φ) (*-assoc x y z) ⟩
    y * z + x * (y * z)  ≡⟨⟩
    suc x * (y * z)      ∎
    where open ≡-Reasoning
```

```agda
module Integer-Properties where
  import Data.Nat as ℕ
  import Data.Nat.Properties as ℕ
  import 2-numbers
  open 2-numbers.Sandbox-Integers

  neg-involutive : (x : ℤ) → - (- x) ≡ x
  neg-involutive +0 = refl
  neg-involutive +[1+ n ] = refl
  neg-involutive -[1+ n ] = refl

  +-identityˡ : (x : ℤ) → 0ℤ + x ≡ x
  +-identityˡ x = refl

  +-identityʳ : (x : ℤ) → x + 0ℤ ≡ x
  +-identityʳ (+ ℕ.zero) = refl
  +-identityʳ +[1+ x ] = refl
  +-identityʳ -[1+ x ] = refl

  *-zeroˡ : (m : ℤ) → +0 * m ≡ +0
  *-zeroˡ (+ ℕ.zero) = refl
  *-zeroˡ +[1+ ℕ.zero ] = refl
  *-zeroˡ +[1+ ℕ.suc x ] = refl
  *-zeroˡ -[1+ ℕ.zero ] = refl
  *-zeroˡ -[1+ ℕ.suc x ] = refl

  *-identityˡ : (m : ℤ) → 1ℤ * m ≡ m
  *-identityˡ (+ ℕ.zero) = refl
  *-identityˡ +[1+ ℕ.zero ] = refl
  *-identityˡ +[1+ ℕ.suc x ] =
    cong (λ φ → +[1+ ℕ.suc φ ]) (Nat-Properties.+-identityʳ x)
  *-identityˡ -[1+ ℕ.zero ] = refl
  *-identityˡ -[1+ ℕ.suc x ] =
    cong (λ φ → -[1+ ℕ.suc φ ]) (Nat-Properties.+-identityʳ x)

  open ≡-Reasoning

  +-comm : (x y : ℤ) → x + y ≡ y + x
  +-comm +0 y = sym (+-identityʳ _)
  +-comm +[1+ x ] +0 = refl
  +-comm -[1+ x ] +0 = refl
  +-comm +[1+ ℕ.suc x ] -[1+ ℕ.suc y ] = +-comm +[1+ x ] -[1+ y ]
  +-comm -[1+ ℕ.suc x ] +[1+ ℕ.suc y ] = +-comm -[1+ x ] +[1+ y ]
  +-comm +[1+ x ] +[1+ y ] = cong (λ φ → +[1+ ℕ.suc φ ]) (ℕ.+-comm x y)
  +-comm -[1+ x ] -[1+ y ] = cong (λ φ → -[1+ ℕ.suc φ ]) (ℕ.+-comm x y)
  +-comm +[1+ ℕ.zero ] -[1+ ℕ.zero ] = refl
  +-comm +[1+ ℕ.zero ] -[1+ ℕ.suc y ] = refl
  +-comm +[1+ ℕ.suc x ] -[1+ ℕ.zero ] = refl
  +-comm -[1+ ℕ.zero ] +[1+ ℕ.zero ] = refl
  +-comm -[1+ ℕ.zero ] +[1+ ℕ.suc y ] = refl
  +-comm -[1+ ℕ.suc x ] +[1+ ℕ.zero ] = refl

  postulate
    *-comm : (m n : ℤ) → m * n ≡ n * m
    +-assoc : (x y z : ℤ) → (x + y) + z ≡  x + (y + z)

  open import Data.Product

  +‿-‿zero : (m : ℕ.ℕ) → +[1+ m ] + -[1+ m ] ≡ +0
  +‿-‿zero ℕ.zero = refl
  +‿-‿zero (ℕ.suc m) = +‿-‿zero m

  -‿-‿+‿suc : (m n : ℕ.ℕ) → -[1+ ℕ.suc m ] + -[1+ n ] ≡ -[1+ m ] + -[1+ ℕ.suc n ]
  -‿-‿+‿suc ℕ.zero ℕ.zero = refl
  -‿-‿+‿suc ℕ.zero (ℕ.suc n) = refl
  -‿-‿+‿suc (ℕ.suc m) n =
    cong (λ φ → -[1+ ℕ.suc (ℕ.suc φ) ]) (sym (Nat-Properties.+-suc m n))
    where open ≡-Reasoning

  *-pos-neg : (m n : ℕ.ℕ) → +[1+ m ] * -[1+ n ] ≡ +[1+ n ] * -[1+ m ]
  *-pos-neg m ℕ.zero = sym (*-identityˡ -[1+ m ])
  *-pos-neg ℕ.zero (ℕ.suc n) =
    begin
      -[1+ ℕ.suc (n ℕ.+ 0) ]
    ≡⟨ cong (λ φ → -[1+ ℕ.suc φ ]) (Nat-Properties.+-identityʳ n) ⟩
      -[1+ ℕ.suc n ]
    ∎
    where open ≡-Reasoning
  *-pos-neg (ℕ.suc m) (ℕ.suc n) =
    begin
      +[1+ m ] * -[1+ n ] + -[1+ n ] + -[1+ ℕ.suc m ]
    ≡⟨ cong (λ φ → φ + -[1+ n ] + -[1+ ℕ.suc m ]) (*-pos-neg m n) ⟩
      +[1+ n ] * -[1+ m ] + -[1+ n ] + -[1+ ℕ.suc m ]
    ≡⟨ +-assoc (+[1+ n ] * -[1+ m ]) -[1+ n ] -[1+ ℕ.suc m ] ⟩
      +[1+ n ] * -[1+ m ] + (-[1+ n ] + -[1+ ℕ.suc m ])
    ≡⟨ cong (λ φ → +[1+ n ] * -[1+ m ] + φ) (+-comm -[1+ n ] -[1+ ℕ.suc m ]) ⟩
      +[1+ n ] * -[1+ m ] + (-[1+ ℕ.suc m ] + -[1+ n ])
    ≡⟨ cong (λ φ → +[1+ n ] * -[1+ m ] + φ) (-‿-‿+‿suc m n) ⟩
      +[1+ n ] * -[1+ m ] + (-[1+ m ] + -[1+ ℕ.suc n ])
    ≡⟨ sym (+-assoc (+[1+ n ] * -[1+ m ]) -[1+ m ] -[1+ ℕ.suc n ]) ⟩
      +[1+ n ] * -[1+ m ] + -[1+ m ] + -[1+ ℕ.suc n ]
    ∎
    where open ≡-Reasoning

  *-neg-neg : (m n : ℕ.ℕ) → -[1+ m ] * -[1+ n ] ≡ +[1+ m ] * +[1+ n ]
  *-neg-neg m ℕ.zero = refl
  *-neg-neg ℕ.zero (ℕ.suc n) = refl
  *-neg-neg (ℕ.suc m) (ℕ.suc n) =
    cong (λ φ → φ + +[1+ n ] + +[1+ ℕ.suc m ]) (*-neg-neg m n)

  -‿hom : (m n : ℕ.ℕ) → -[1+ m ] + -[1+ n ] ≡ -[1+ m ℕ.+ ℕ.suc n ]
  -‿hom ℕ.zero n = refl
  -‿hom (ℕ.suc m) n = cong (λ φ → -[1+ ℕ.suc φ ]) (sym (Nat-Properties.+-suc m n))

  *‿-‿neg : (m n : ℕ.ℕ) → ∃[ x ] +[1+ m ] * -[1+ n ] ≡ -[1+ x ]
  *‿-‿neg m ℕ.zero = m , refl
  *‿-‿neg m (ℕ.suc n) with *‿-‿neg m n
  ... | fst , snd = (fst ℕ.+ ℕ.suc m) ,
    ( begin
      -[1+ n ] * +[1+ m ] + -[1+ m ]
    ≡⟨ cong (_+ -[1+ m ]) (*-comm -[1+ n ] +[1+ m ]) ⟩
      +[1+ m ] * -[1+ n ] + -[1+ m ]
    ≡⟨ cong (_+ -[1+ m ]) snd ⟩
      -[1+ fst ] + -[1+ m ]
    ≡⟨ -‿hom fst m ⟩
      -[1+ fst ℕ.+ ℕ.suc m ]
    ∎
    )
    where open ≡-Reasoning

--   +-assoc : (x y z : ℤ) → (x + y) + z ≡  x + (y + z)
--   +-assoc +0 y z = refl
--   +-assoc +[1+ x ] +0 z = refl
--   +-assoc +[1+ x ] +[1+ y ] +0 = refl
--   +-assoc +[1+ x ] +[1+ y ] +[1+ z ] =
--     begin
--       +[1+ ℕ.suc (ℕ.suc ((x ℕ.+ y) ℕ.+ z)) ]
--     ≡⟨ cong (λ φ → +[1+ ℕ.suc φ ]) (sym (ℕ.+-suc (x ℕ.+ y) z)) ⟩
--       +[1+ ℕ.suc (x ℕ.+ y ℕ.+ ℕ.suc z) ]
--     ≡⟨ ? ⟩
--       +[1+ ℕ.suc (x ℕ.+ ℕ.suc (y ℕ.+ z)) ]
--     ∎
--   +-assoc +[1+ x ] +[1+ y ] -[1+ z ] = {! !}
--   +-assoc +[1+ x ] -[1+ y ] +0 = +-identityʳ _
--   +-assoc +[1+ x ] -[1+ y ] +[1+ z ] = {! !}
--   +-assoc +[1+ x ] -[1+ y ] -[1+ z ] = {! !}
--   +-assoc -[1+ x ] (+ ℕ.zero) (+ ℕ.zero) = {! !}
--   +-assoc -[1+ x ] (+ ℕ.zero) +[1+ z ] = {! !}
--   +-assoc -[1+ x ] (+ ℕ.zero) -[1+ z ] = {! !}
--   +-assoc -[1+ x ] +[1+ y ] +0 = +-identityʳ _
--   +-assoc -[1+ x ] +[1+ y ] +[1+ z ] = {! !}
--   +-assoc -[1+ x ] +[1+ y ] -[1+ z ] = {! !}
--   +-assoc -[1+ x ] -[1+ y ] +0 = +-identityʳ _
--   +-assoc -[1+ x ] -[1+ y ] +[1+ z ] = {! !}
--   +-assoc -[1+ x ] -[1+ y ] -[1+ z ] = {! !}

```
