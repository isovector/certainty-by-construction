## Decidability

```agda
module decidability where
```

In classical logic, there exists the so-called *law of the excluded middle*
which states "a proposition is either true or false[^excluded-middle]" The law
of the excluded middle gives rise to the familiar idea of *double-negation*,
that if we know a proposition is not false, it must therefore be true, since
there is no middle ground.

[^excluded-middle]: Implicit in this statement is that any possible middle
  ground between true or false has been excluded.

While this is certainly a desirable property, it doesn't entirely jive with our
intuitions as humans. There are loads of questions to which the honest answer
must be "we just don't know." This is not just a problem of formalization; many
problems in math and computer science simply don't have an answer. The most
famous of which is the *halting problem* which asks you for an algorithm to
decide whether a given program eventually stops, or runs forever. Of course, if
you had such an algorithm, you could write a program that computes it, negate
its answer, and feed it as input to itself. In such a case, it halts if and only
if it doesn't halt, logically flip-flopping to an infinite regress.

The halting problem is a statement we can write out mathematically. By its
existence, we must bite one of two bullets:

1. mathematics is unsuitable for dealing with problems like these
2. there is, in fact, an *included* middle

Bullet #2 is clearly the easier to stomach. Accepting this truth brings us to
the realm of *constructive mathematics* --- a world in which we can prove the
existence of things only by explicitly building one. This jives with most
programmers' sensibilities, since constructivism is necessary for computation;
you simply are unable to call a function that you haven't given the
implementation for, at least, not if you don't want your program to crash!

Let's spend a little time constructing the machinery necessary to talk about the
law of the excluded middle in Agda, and then see what alternatives are offered
to us when taking the constructivist point of view.

Under the Curry--Howard isomorphism, types are propositions, and programs are
proofs. Falsity is a property of propositions, and so we must ask ourselves,
what does it mean for a type to be false? The one goal that mathematics holds
above all others is this central tenet: **it must be impossible to prove
false.** There exist several proofs that, once you have a single proof of false
in your system, you can subsequently prove *anything.* This is clearly
unacceptable, and would turn mathematics into a field of landmines at best, and
a joke at worst. Thus, the proposition `false` is distinguished by having no
proofs.

Believe it or not, this is something we can define directly in Agda, by giving a
data type with no constructors:

```agda
data ⊥ : Set where
```

The type `⊥` now exists as something we can talk about, but, thankfully, can
never construct. So, what good is it? Since we know that anything is provable
given a falsity, we can show something is false if it can be used to construct a
value of type `⊥`. That is to say, any function which produces `⊥` must
necessarily not be callable, since it wouldn't have anything to return. Thus, we
can show `P` is false by defining a function which takes a `P` and returns a
`⊥`:

```agda
infix 3 ¬_
¬_ : Set → Set
¬ P = P → ⊥
```

`¬_` is a general purpose construction for showing its argument is false.

A note on terminology; we generally reserve the word "false" when talking about
propositions, while the term "uninhabited" is more natural when talking about
types. Henceforth, we will describe a term of type `¬ A` as being a proof that
`A` is uninhabited.

While `⊥` is the most obvious of the uninhabited types, not all uninhabited
types are so flagrant! In fact, there is no test we can perform that can
determine whether an arbitrary type is inhabited or not! Uninhabited types can
have constructors, like `Bot₁`:

```agda
module _ where
  open import Data.Nat
  open import Relation.Binary.PropositionalEquality

  data Bot₁ : Set where
    bot₁ : 1 ≡ 2 → Bot₁
```

which hypothetically *could* be constructed, if we had a proof that $1 = 2$,
which of course, we can't get. So `Bot₁` must therefore be uninhabited, but
showing that requires meta-reasoning!

In general, I can make arbitrarily complicated requirements necessary to
construct my type, requirements which may or may not be constructable. As it
happens, determining the inhabitance of a type is equivalent to the halting
problem! What a mess we find ourselves in.

Now that we have defined `¬_`, we are able to define the "law" of the excluded
middle in Agda. We will define it as a `postulate`, which adds it to the system
of things we can reason about in Agda, but at the cost of throwing away our
ability to actually compute anything that uses it.

```agda
open import Data.Sum
postulate
  lem : {A : Set} → A ⊎ ¬ A
```

As stated, `lem` says for any type `A`, we can get an arbitrary value of that
type, or a proof that having a value of that type would produce a `⊥`. While
there certainly do exist types that have this property (and `⊥` is trivially one
of them), it's a far cry from being able to do it for *every* type.

What can we do instead? Well, we could give specific functions, which are
*instantiations* of the law of the excluded middle, for specific types. The
types for which this is possible are said to be *decidable* --- that is, there
exists a *decision procedure* (an algorithm) to give a definitive yes or no for
the proposition in question. Let's build the machinery.

The most obvious construction here is a type `Dec : Set → Set`, indexed by the
type we're attempting to give a proof for. There are two ways we could build
such a type, either `yes` there is an inhabitant, or no there isn't.

```agda
module Hypothetical where
  data Dec (P : Set) : Set where
    yes : P → Dec P
    no  : ¬ P → Dec P
```

This is not quite, however, the way that the Agda standard library does things.
Instead, it reifies the above into `Reflects : Set → Bool → Set`, which indexes
whether or not the type is inhabited:

```agda
open import Data.Bool using (Bool; true; false)

data Reflects (P : Set) : Bool →  Set where
  ofʸ : ( p :   P) → Reflects P true
  ofⁿ : (¬p : ¬ P) → Reflects P false
```

and then defines `Dec` as a pair of a `Bool` and a `Reflects` over that same
boolean:

```agda
record Dec (P : Set) : Set where
  constructor _because_
  field
    does : Bool
    proof : Reflects P does
```

The reasoning here is that a large amount of time you don't actually care about
the proof, you just want to know whether the type is inhabited or not. Having
the `does` constructor lets you quickly check that, and the `Reflects` machinery
is useful for showing certain things are *always* or *never* inhabited.

However, due to some pattern synonym magic, you are able to pretend `Dec` is
implemented as we originally did, with `yes` and `no` constructors and
everything will work out fine:

```agda
pattern yes p =  true because ofʸ  p
pattern no ¬p = false because ofⁿ ¬p
```

Earlier I made the claim that, given a proof of false, we can prove anything.
We're now ready to show that fact:

```agda
⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()
```

This function has no body, because there is nothing to pattern match on; there
simply are no values of `⊥`, so Agda doesn't ask us to show the function holds
for any. Thus, given a `⊥`, we can *vacuously* produce a value of any other
type.

As our first example of decidability, we can show the equality of two natural
numbers is decidable. First, some imports:

```agda
open import Data.Nat hiding (_≟_)
open import Data.Nat.Properties hiding (_≟_)
open import Relation.Binary.PropositionalEquality

module nat-eq-decidable where
```

The type of our witness to decidability is:

```agda
  _≟_ : (x y : ℕ) → Dec (x ≡ y)
```

which we can prove by matching on both arguments. In the case they are both
zero, we're done with a resounding `yes`:

```agda
  zero ≟ zero = yes refl
```

If one argument is `zero`, and the other is `suc`, well, that's a definite `no`!
In order to produce a `no`, we must have a function that would produce a `⊥`. We
can use the same trick as we did for `⊥-elim` here. By having pattern matched on
our two arguments, Agda knows that there is no way of producing an equality
proof, and so it immediately eliminates the pattern match:

```agda
  zero ≟ suc y = no λ { () }
  suc x ≟ zero = no λ { () }
```

Finally, we come to the case where both arguments are `suc`s. The solution here,
as usual, is induction. We can ask if the two `suc`ed numbers are equal, and if
so, adjust our proof:

```agda
  suc x ≟ suc y with x ≟ y
  ... | yes p = yes (cong suc p)
```

In the case they're not, however, we can no longer play the "no pattern matches"
game. Instead, we get back a proof `¬p : ¬ x ≡ y`, which we must somehow
transform into a proof `¬ suc x ≡ suc y`:

```agda
  ... | no ¬p =
```

This seems like the sort of problem we could `cong` away, but, due to the way
the functions line up, we really need a proof `suc x ≡ suc y → x ≡ y`, and
`cong` goes the other direction. Thankfully, the standard library has our backs,
with a function aptly named `suc-injective`:

```agda
    no λ x=y → ¬p (suc-injective x=y)
```


```agda
module mod-dec (n : ℕ) where
  import setoids
  open setoids.mod-base n
  import Data.Nat.Properties as Nat
  open import Relation.Binary

  _≟_ : (x y : ℕ) → Dec (x ≈ y ⟨mod n ⟩)
  _≟_ x y with ∣ x - y ∣
  ... | yo = ?
```
