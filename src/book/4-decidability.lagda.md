# Decidability

```agda
module 4-decidability where
```

In the last chapter, we thoroughly investigated the notion of doing proof in
Agda.  We defined what it means for two things to be propositionally equal,
derived relevant properties of equality, built a domain-specific language for
doing equational reasoning, and proved many facts about the natural numbers.

Perhaps you are thinking you now know all there is to know about proofs, but
this is patently false: for example, we haven't yet discussed what it means for
a notion to be false! Furthermore, everything we've built so far works only for
*statically-known* values. But is it possible that we can use dependent types in
contexts where we don't know all the values we need to work with? Maybe the
values came from the user via an interactive system. Are we forced to throw away
everything we've done and degrade our guarantees to those of a weaker
programming language?

Thankfully the answer is "no," and we will explore the ideas no. In addition, we
will also get our hands dirty modeling and proving facts about objects that feel
significantly more *computer science-y.* After all, these techniques are
applicable outside of the ivory tower, too!


## Negation

Recall that we've now seen how to express that two values are (propositionally)
equal, via the `_≡_` type, proven via `refl`. We'd now like to determine a means
of discussing *inequality!*

Perhaps you might think we can make a slight tweak to the `_≡_` construction.
While `refl : x ≡ x`, perhaps we could try something along the lines of:

```agda
module Sandbox-Inequality where
  data _≢_ {A : Set} : A → A → Set where
    ineq : {x y : A} → x ≢ y
```

Unfortunately, this approach does not---and in fact, cannot---work. While we've
attempted to assert that `x` and `y` are inequal by virtue of being different
bindings of `A`, Agda gives us no guarantees that they are *distinct* values of
`A`! It's like if you write a function:

$$
(x, y) \mapsto x + y
$$

Here, $x$ and $y$ are different *variables,* but that doesn't mean I can't
*evaluate* this function at $x = y = 2$. Therefore, this approach is a dead-end,
and we will need to find an alternative means.

Recall the *principle of explosion,* the property of a contradictory system,
which states that "from false, anything is possible." This gives us a hint as to
how we might go about encoding an inequality. Rather than treating it as such,
we can instead rewrite $x \neq y$ as "$x = y$ is false."

Let's give it a go. First, rather than importing our hand-rolled natural numbers
from the previous sections, we can import them from the standard library. Don't
worry, the interface is identical to the ones we built, so there will be no
surprises in doing this:

```agda
open import Data.Nat
  using (ℕ; zero; suc)
```

We will also need to import propositional equality, which we can also get from
the standard library. This too has an identical interface, so we're safe to do
so:

```agda
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; module ≡-Reasoning)
```

With these out of the way, we can get started on our new attempt at the
principle of explosion. The idea being, in order to show that some proposition
`P` is false, we must be able to generate anything we'd like, of any type we'd
like. We can model this as:

```agda
module Sandbox-Explosion where
  False : Set → Set₁  -- ! 1
  False P = P → {A : Set} → A
```

You'll notice at [1](Ann) that the type of `False` is `Set → Set₁`, which is a
feature of Agda's type system we haven't yet covered, but will later this
chapter. For the time being, pretend this says `Set → Set`. We can now try to
find a proof that 2 is not equal to three, as per:

```agda
  2≠3⅋₀ : False (2 ≡ 3)
  2≠3⅋₀ = ?
```

Since `False` expands to a function type, we can (rather unintuitively) do a
[MakeCase:](AgdaCmd) here to get a *parameter* of type `2 ≡ 3`:

```agda
  2≠3⅋₁ : False (2 ≡ 3)
  2≠3⅋₁ x = {! !}
```

Asking Agda to [MakeCase:x](AgdaCmd) here produces a strange result:

```agda
  2≠3 : False (2 ≡ 3)
  2≠3 ()
```

What has happened is that Agda noticed that *there are no constructors for `2 ≡
3`,* and thus that this function cannot actually be called, because there is no
argument you can give it that would typecheck. Since the whole thing is moot
anyway, Agda doesn't require us to write an implementation of this function, and
allows us to get away with an *absurd pattern match,* which is the name for
those empty parentheses and the lack of an equals sign.

By virtue of having written a definition of `2≠3` that typechecks, we have
successfully proven the fact that two is not equal to three. Mission
accomplished! Nevertheless, while this is an absolutely valid encoding, it's not
how we usually write propositional negation in Agda. For that, we need the empty
type.


## Bottom

While it's acceptable to use the principle of explosion directly, there is a
simpler way of encoding the problem, namely by "factoring out" the pieces.
Rather than showing all contradictions lead to explosion, we can instead say all
contradictions lead to a specific type, and then show that all values of that
type lead to explosion. The resulting machinery means you can always use the
principle of explosion if you'd like, but in practice means your type signatures
and negative proofs become simpler to work with.

The "pre-explosive" type we'll work with is called the *bottom* type, written
`⊥` and input as `\bot`. It's definition is short and sweet:

```agda
data ⊥ : Set where
```

That's it. There are no constructors for `⊥`. Besides a slightly different type
signature, we can show `2≠3` with an identical proof, this time using bottom:

```agda
2≠3 : 2 ≡ 3 → ⊥
2≠3 ()
```

Why does this work? Recall the definition of a function: for any input in the
domain, it maps it to an element in the codomain. But there are no elements in
bottom, so any function whose codomain is bottom cannot possibly be a function
unless its *domain* also has no elements. Otherwise, the function would have
elements in the domain with nowhere to map them to in the codomain.

By this argument, any function we can successfully define which maps into bottom
necessarily constrains at least one of its parameters to also have no elements.

We still need to show that an element of `⊥` leads to the principle of
explosion, which is another easy proof:

```agda
⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()
```

Mathematically, proofs of this flavor are called *vacuously true.* Which is to
say, they are true only because they depend on a contradiction in the first
place. Nevertheless, we can give a vacuous proof that all bottom elements (of
which there are none in the first place) are equal:

```agda
⊥-unique : {x y : ⊥} → x ≡ y
⊥-unique {x} = ⊥-elim x
```

We have now shown that bottom is a satisfactory definition of false, and that
functions into bottom are therefore a good definition of the falseness of their
input type considered as a proposition. Hence, we can define `¬_`, which states
that a given proposition is false:

```agda
open import Level
  using (Level)

¬_ : {ℓ : Level} → Set ℓ → Set ℓ
¬ P = P → ⊥
infix 3 ¬_
```

and then define inequality:

```agda
_≢_ : {A : Set} → A → A → Set
x ≢ y = ¬ x ≡ y
```

```agda
≢-sym : {A : Set} {x y : A} → x ≢ y → y ≢ x
≢-sym x≠y y=x = x≠y (sym y=x)

Transitive : {A : Set} → (A → A → Set) → Set
Transitive {A} _≈_ = {x y z : A} → x ≈ y → y ≈ z → x ≈ z


no-≢-trans : ¬ ({A : Set} → Transitive {A} _≢_)
no-≢-trans ≢-trans = ≢-trans {A = ℕ} 2≠3 (≢-sym 2≠3) refl
```

```agda
data Dec (P : Set) : Set where
  yes : P  → Dec P
  no : ¬ P → Dec P


open import Data.Nat
  using (ℕ; zero; suc)

open import Relation.Binary.PropositionalEquality

_≟ℕ_ : (x y : ℕ) → Dec (x ≡ y)
zero ≟ℕ zero = yes refl
zero ≟ℕ suc y = no λ ()
suc x ≟ℕ zero = no λ ()
suc x ≟ℕ suc y with x ≟ℕ y
... | yes x=y = yes (cong suc x=y)
... | no  x≠y = no λ { refl → x≠y refl }

DecidableEquality : (A : Set) → Set
DecidableEquality A = (x y : A) → Dec (x ≡ y)

_≟ℕ′_ : DecidableEquality ℕ
_≟ℕ′_ = _≟ℕ_



data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

data _∈_ {A : Set} (a : A) : List A → Set where
  here : {xs : List A} → a ∈ (a ∷ xs)
  there : {x : A} → {xs : List A} → a ∈ xs → a ∈ (x ∷ xs)

decide-membership
    : {A : Set}
    → DecidableEquality A
    → (a : A)
    → (xs : List A)
    → Dec (a ∈ xs)
decide-membership _≟_ a [] = no λ ()
decide-membership _≟_ a (x ∷ xs)
  with a ≟ x
... | yes refl = yes here
... | no a≠x
  with decide-membership _≟_ a xs
... | yes a∈xs = yes (there a∈xs)
... | no ¬a∈xs = no λ { here → a≠x refl
                      ; (there a∈xs) → ¬a∈xs a∈xs
                      }


data All {A : Set} (P : A → Set) : List A → Set where
  [] : All P []
  _∷_ : {x : A} {xs : List A} → P x → All P xs → All P (x ∷ xs)

decide-all
    : {A : Set} {P : A → Set}
    → (p? : (a : A) → Dec (P a))
    → (xs : List A)
    → Dec (All P xs)
decide-all p? [] = yes []
decide-all p? (x ∷ xs)
  with p? x
... | no ¬px = no λ { (px ∷ _) → ¬px px }
... | yes px
  with decide-all p? xs
... | yes all = yes (px ∷ all)
... | no ¬all = no λ { (_ ∷ all) → ¬all all }


record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

infixr 4 _,_

_×_ : Set → Set → Set
A × B = Σ A (λ _ → B)


filter
    : {A : Set} {P : A → Set}
    → ((x : A) → Dec (P x))
    → (xs : List A)
    → Σ (List A) (All P)
filter p? [] = [] , []
filter p? (x ∷ xs)
  with p? x  | filter p? xs
...  | yes p | ls , all = (x ∷ ls) , (p ∷ all)
...  | no ¬p | ls , all = ls , all



weaken
    : {A : Set} {P : A → Set} {Q : A → Set} {ls : List A}
    → (P→Q : {a : A} → P a → Q a)
    → All P ls
    → All Q ls
weaken Q→P [] = []
weaken Q→P (x ∷ xs) = Q→P x ∷ weaken Q→P xs


filter′
    : {A : Set} {P : A → Set}
    → ((x : A) → Dec (P x))
    → (xs : List A)
    → Σ (List A) λ l → All P l × All (_∈ xs) l
filter′ p? [] = [] , [] , []
filter′ p? (x ∷ xs)
  with p? x | filter′ p? xs
... | yes p | ls , all-P , all-in
    = (x ∷ ls) , p ∷ all-P , here ∷ weaken there all-in
... | no ¬p | ls , all-P , all-in
    = ls , all-P , weaken there all-in



```
