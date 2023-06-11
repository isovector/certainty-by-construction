# Countability

```agda
{-# OPTIONS --allow-unsolved-metas #-}

module 9-countability where

open import Data.Nat hiding (_⊔_)
```

In this chapter we will discuss the notion of *countability* --- a general
toolkit for reasoning about sets and types, as well as classifying infinities.
Many sets have a finite number of elements, and thus, they are easy to count.

But before we get too far ahead of ourselves, we will first need to look at a
sort of "restricted" numbers. So far we have used only the natural numbers,
of which there are an infinite number. But sometimes we'd like to limit the
numbers we have available; for example, when indexing from a vector, we'd like
to limit the possible indices to be less than the length of the vector, and
therefore we can completely avoid runtime bounds checking.

> TODO(sandy): check the next sentence

The sets of numbers we are interested in are called the *finite numbers.* We can
use a natural number to index these sets, restricting the elements to be
strictly less than this index. More concretely, we can build the type `Fin`:

```agda
module Ex where
  data Fin : ℕ → Set where
    zero : {n : ℕ} → Fin (suc n)
    suc  : {n : ℕ} → Fin n → Fin (suc n)
```

A `Fin (suc n)` contains exactly `n` values, that is, it contains the numbers $0
\dots n$. This the number of inhabitants you'd expect, but be careful to not
have an off-by-one error, since we begin counting at 0. An interesting corollary
of this fact is that `Fin 0` contains zero inhabitants.

Rather than defining `Fin` ourselves, we will merely import it from the standard
library, and get a good deal of extra machinery along in the deal for free.

```agda
open import Data.Fin hiding (_+_)
```

You are encouraged to dig around in this module and its re-exports to see what
is available when working with `Fin`s.

To quickly illustrate the vector lookup example, just to give you a flavor of
how we can use `Fin`s. It's not a very involved bit of code:

```agda
module Ex₂ where
  open import Data.Vec using (Vec; _∷_; [])

  lookup : {A : Set} {n : ℕ} → Vec A n → Fin n → A
  lookup (x ∷ v) zero = x
  lookup (x ∷ v) (suc n) = lookup v n
```

Our `lookup` function bears witness to the fact that if we know the size of our
vector, we can always safely pull an element out of it without worry. There is
no bound-checking necessary, because the type of `Fin` ensures we can't ask for
an index outside of the vector. We will use `Fin`s again shortly in our
discussion of countability.


## Finite Types

```agda
open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import 8-iso

open import Data.Bool
open import Data.Sum renaming (map to ⊎-map)
open import Data.Product renaming (map to ×-map)

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; setoid; isEquivalence)

private instance
  Fin-equiv : {n : ℕ} → Equivalent lzero (Fin n)
  Equivalent._≋_ Fin-equiv = _≡_
  Equivalent.equiv (Fin-equiv {n}) = isEquivalence

  ⊎-equiv
      : {c₁ c₂ ℓ₁ ℓ₂ : Level}
        {A : Set c₁} ⦃ _ : Equivalent ℓ₁ A ⦄
        {B : Set c₂} ⦃ _ : Equivalent ℓ₂ B ⦄
      → Equivalent (ℓ₁ ⊔ ℓ₂) (A ⊎ B)
  ⊎-equiv = ?

  ×-equiv
      : {c₁ c₂ ℓ₁ ℓ₂ : Level}
        {A : Set c₁} ⦃ _ : Equivalent ℓ₁ A ⦄
        {B : Set c₂} ⦃ _ : Equivalent ℓ₂ B ⦄
      → Equivalent (ℓ₁ ⊔ ℓ₂) (A × B)
  ×-equiv = ?
```

Given a set `A` and a setoid over it:

```agda
module _ {c ℓ : Level} (A : Set c) ⦃ _ : Equivalent ℓ A ⦄ where
```

we say that `A` is (finitely) countable if it has a finite number of values. But
how can we formalize this statement? One way is to state the number of values
`A` has, and then *prove it* by showing a bijection between `A` and `Fin` of
that number. Written as a record:

```agda
  record Countable : Set (c ⊔ lsuc ℓ) where
    field
      cardinality : ℕ
      proof : A ↔ Fin cardinality
```

The mathematicians are partial to using surrounding bars to give the size of
something, which we can add for their benefit as a member of the record via
`∣_∣`:

```agda
    ∣_∣ : ℕ
    ∣_∣ = cardinality
```

We can close the module, and now open `Countable` and `_↔_` to get ready to show
that `Bool` is finite.

```agda
open Countable
open _↔_
```

Exercise

:   Show `Bool` is countable.


Solution

:   ```agda
countable-Bool : Countable Bool
cardinality countable-Bool = 2
to           (proof countable-Bool) false      = zero
to           (proof countable-Bool) true       = suc zero
from         (proof countable-Bool) zero       = false
from         (proof countable-Bool) (suc x)    = true
left-inv-of  (proof countable-Bool) false      = refl
left-inv-of  (proof countable-Bool) true       = refl
right-inv-of (proof countable-Bool) zero       = refl
right-inv-of (proof countable-Bool) (suc zero) = refl
to-cong      (proof countable-Bool) _≡_.refl   = refl
from-cong    (proof countable-Bool) _≡_.refl   = refl
    ```

One interesting fact about finite sets is that if two sets have the same
cardinality, they are isomorphic. This is easy to show by simply composing their
isomorphisms into `Fin cardinality`:

```agda
module _ {c₁ c₂ ℓ₁ ℓ₂ : Level}
         (A : Set c₁) ⦃ _ : Equivalent ℓ₁ A ⦄ (A-count : Countable A)
         (B : Set c₂) ⦃ _ : Equivalent ℓ₂ B ⦄ (B-count : Countable B) where

  ↔-card
      : ∣ A-count ∣ ≡ ∣ B-count ∣
      → A ↔ B
  ↔-card _≡_.refl =
    ↔-trans
      (A-count .proof)
      (↔-sym (B-count .proof))
```

Another interesting thing to prove is that `_⊎_` justifies the little plus-sign
in its symbol because it corresponds to the addition of inhabitants. That is, if
`A` has cardinality $m$ and `B` has cardinality $n$, then `A ⊎ B` has
cardinality $m + n$. This is not a particularly hard thing to show, especially
when you discover `join` and `splitAt` from `Data.Fin` which exactly witness the
math we'd like to perform to deliver the first $m$ elements to the left, and the
last $n$ to the right. The function `join` in particular has type `∀ m n → Fin m
⊎ Fin n → Fin (m ℕ.+ n)`, and `splitAt` is its inverse.

Thus in order to show the countability of `A ⊎ B`, we must first map our
underling countability proofs over our terms, and then `join` them together into
the right shape.

```agda
  ⊎-card : Countable (A ⊎ B)
  cardinality ⊎-card = ∣ A-count ∣ + ∣ B-count ∣
  to (proof ⊎-card) x =
    join ∣ A-count ∣
         ∣ B-count ∣
         (⊎-map (to (proof A-count))
              (to (proof B-count)) x)
  from (proof ⊎-card) x =
    ⊎-map (from (proof A-count))
          (from (proof B-count))
          (splitAt ∣ A-count ∣ x)
  left-inv-of (proof ⊎-card) x = {! !}
  right-inv-of (proof ⊎-card) = {! !}
  to-cong (proof ⊎-card) x = {! !}
  from-cong (proof ⊎-card) = {! !}
```

There is a dual fact to this one, namely that `_×_` forms the product of
cardinalities of its argument sets. This time, the magical functions in
`Data.Fin` are `remQuot` and `combine`.

```agda
  open import Data.Product

  ×-card : Countable (A × B)
  cardinality ×-card = ∣ A-count ∣ * ∣ B-count ∣
  to (proof ×-card) (a , b) =
    combine
      (to (proof A-count) a)
      (to (proof B-count) b)
  from (proof ×-card) x =
    ×-map
      (from (proof A-count))
      (from (proof B-count))
      (remQuot ∣ B-count ∣ x)
  left-inv-of (proof ×-card) = {! !}
  right-inv-of (proof ×-card) = {! !}
  to-cong (proof ×-card) = {! !}
  from-cong (proof ×-card) = {! !}
```

And since we have `A` and its setoid in scope right now, we will define
`CountablyInfinite` for later.

```agda
CountablyInfinite : {c ℓ : Level} (A : Set c) ⦃ _ : Equivalent ℓ A ⦄ → Set (c ⊔ lsuc ℓ)
CountablyInfinite A = A ↔ ℕ
```

