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

```agda
  ∨-identityˡ : (x : Bool) → false ∨ x ≡ x
  ∨-identityˡ x = refl

  ∨-identityʳ : (x : Bool) → x ∨ false ≡ x
  ∨-identityʳ false = refl
  ∨-identityʳ true  = refl

  ∧-identityˡ : (x : Bool) → true ∧ x ≡ x
  ∧-identityˡ x = refl

  ∧-identityʳ : (x : Bool) → x ∧ true ≡ x
  ∧-identityʳ false = refl
  ∧-identityʳ true  = refl

  ∨-assoc : (a b c : Bool) → (a ∨ b) ∨ c ≡ a ∨ (b ∨ c)
  ∨-assoc false b c = refl
  ∨-assoc true  b c = refl

  ∨-comm : (x y : Bool) → x ∨ y ≡ y ∨ x
  ∨-comm false false = refl
  ∨-comm false true  = refl
  ∨-comm true  false = refl
  ∨-comm true  true  = refl

  ∧-assoc : (a b c : Bool) → (a ∧ b) ∧ c ≡ a ∧ (b ∧ c)
  ∧-assoc false b c = refl
  ∧-assoc true  b c = refl

  ∧-comm : (x y : Bool) → x ∧ y ≡ y ∧ x
  ∧-comm false false = refl
  ∧-comm false true  = refl
  ∧-comm true  false = refl
  ∧-comm true  true  = refl

module Nat-Properties where
  open import Data.Nat

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
