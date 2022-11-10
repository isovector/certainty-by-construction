## Quotients

```agda
module setoids where
open import Data.Nat
open import Data.Nat.Properties
```

Let's return to the perennial issue: when are two things equal to one another?
We've discussed *propositional equality,* that is, that two things are equal
when they are defined in exactly the same way. We've also looked at
*constructions over equality,* which allow us to derive new notions of equality
out of others, like we did with function extensionality. But in this chapter we
will discuss the notion of *quotients* --- that is, asserting by fiat that two
non-propositionally-equal things are in fact, equal.

A favorite example of quotienting for mathematicians are the so-called "ring of
natural numbers modulo $n$," more tersely written as $\mathbb{N}/n\mathbb{N}$.
But what is this ring? This ring is the mathematical way of saying "clock
addition" --- that is, we pick some $n$, maybe $n = 12$ for an example, and say
that whenever our arithmetic gets to $n$ it overflows back to 0. This is the
peculiar fact that, on an analog clock, we have the fact that $11 + 2 = 1
(\text{mod} 12)$.

How can we formalize this idea? Well, if we'd like to show $a = b (\text{mod}
n)$, we would like to find two multiples of $n$ that we can use to equate the
two. That is to say, we need to find $x, y : ℕ$ such that $a + xn = b + yn$.

The definition almost rolls off the tongue:

```agda
module _ where
  open import Relation.Binary.PropositionalEquality

  infix 4 _≈_⟨mod_⟩
  data _≈_⟨mod_⟩ (a b n : ℕ) : Set where
    ≈-mod
      : (x y : ℕ)
      → a + x * n ≡ b + y * n  -- ! 1
      → a ≈ b ⟨mod n ⟩
```

Notice that we use propositional equality at [1](Ann) to assert that we're
witnessing the fact that these two expressions *really are the same!* But that's
merely an implementation detail.

We can now show that our clock example works as expected:

```agda
  _ : 11 + 2 ≈ 1 ⟨mod 12 ⟩
  _ = ≈-mod 0 1 refl
```

Pretty nice, if you ask me.

My claim is that our use of the `≈` in `_≈_⟨mod_⟩` is valid; this relationship
truly is an equivalence relation --- that is to say, it's interchangeable with
equality, and behaves in an identical manner, mathematically speaking. Recall
that to show an equivalence relationship, we need to show the relation satisfies
reflexivity, symmetry, and transitivity. As usual, we can reify these
constraints into a record, parameterized by a relation:

```agda
module _ where
  private variable
    A : Set
    a b c : A

  record IsEquivalence (_≈_ : A → A → Set) : Set where
    field
      refl : a ≈ a
      sym : a ≈ b → b ≈ a
      trans : a ≈ b → b ≈ c → a ≈ c
```

Let's now show that `_≈_⟨mod_⟩` forms an equivalence relation. We begin by
binding a few helper variables:

```agda
module _ where
  open import Relation.Binary.PropositionalEquality

  private
    variable
      n : ℕ
      a b c d : ℕ
```

Show `refl` is trivial --- the two numbers are already equal:

```agda
  mod-refl : a ≈ a ⟨mod n ⟩
  mod-refl = ≈-mod 0 0 refl
```

Symmetry is also simple; we just need to swap around which multiples are which,
and fiddle the equality proof correspondingly:

```agda
  mod-sym : a ≈ b ⟨mod n ⟩ → b ≈ a ⟨mod n ⟩
  mod-sym (≈-mod x y p) = ≈-mod y x (sym p)
```

Transitivity, however, is significantly more involved. Before diving into the
implementation, let's work out the solution "on paper" first, where we can more
more quickly and require less formality in justifying our steps.

We can set up the problem as given $a, b, c, x, y, z, w : ℕ$, we have a series
of simultaneous equations:

$$
a + xn = b + yn \\
b + zn = c + wn
$$

We'd like to eliminate the $b$ term, so we can solve both sides for $b$:

$$
a + xn - yn = b = c + wn - zn
$$

Recall, however, that we're working over the natural numbers, which do not have
a satisfactory implementation of subtraction. So we'd prefer to phrase the
problem only in addition, which we can do by moving the negative terms to the
other side:

$$
a + xn + zn = c + wn + yn
$$

and all that's left to do is to factor out the $n$:

$$
a + (x + z)n = c + (w + y)n
$$

This gives us our desired multiples of $n$ for implementing transitivity:

```agda
  mod-trans : a ≈ b ⟨mod n ⟩ → b ≈ c ⟨mod n ⟩ → a ≈ c ⟨mod n ⟩
  mod-trans {a} {b} {n} {c} (≈-mod x y pxy)  (≈-mod z w pzw) =
    ≈-mod (x + z) (w + y)
```

And all that's left is to carry out the proof we performed above. This is not
hard, but requires a good amount of symbolic manipulation. It's left as an
exercise to the reader.


Exercise

:   Finish the proof that `mod-trans` requires to show the two terms are equal.


Solution

:   ```agda
      (
      begin
        a + (x + z) * n      ≡⟨ cong (a +_) (*-distribʳ-+ n x z) ⟩
        a + (x * n + z * n)  ≡⟨ sym (+-assoc a (x * n) (z * n)) ⟩
        (a + x * n) + z * n  ≡⟨ cong (_+ z * n) pxy ⟩
        (b + y * n) + z * n  ≡⟨ +-assoc b (y * n) (z * n) ⟩
        b + (y * n + z * n)  ≡⟨ cong (b +_) (+-comm (y * n) (z * n)) ⟩
        b + (z * n + y * n)  ≡⟨ sym (+-assoc b (z * n) (y * n)) ⟩
        (b + z * n) + y * n  ≡⟨ cong (_+ y * n) pzw ⟩
        c + w * n + y * n    ≡⟨ +-assoc c (w * n) (y * n) ⟩
        c + (w * n + y * n)  ≡⟨ sym (cong (c +_) (*-distribʳ-+ n w y)) ⟩
        c + (w + y) * n      ∎
      )
    where open ≡-Reasoning
    ```


We are now satisfied that `_≈_⟨mod_⟩` is indeed an equivalence relationship.
All that's left is to bundle everything together into an `IsEquivalence`:

```agda
  mod-equiv : IsEquivalence (_≈_⟨mod n ⟩)
  IsEquivalence.refl mod-equiv = mod-refl
  IsEquivalence.sym mod-equiv = mod-sym
  IsEquivalence.trans mod-equiv = mod-trans
```

Before we go further discussing equality, let's also come up with a few theorems
about modular arithmetic. One nice one is that we can perform `_≡_`-equality on
both sides of the `_≈_⟨mod_⟩` equality, as shown by `mod-subst`:

```agda
  mod-subst
    : a ≡ c
    → b ≡ d
    → a ≈ b ⟨mod n ⟩
    → c ≈ d ⟨mod n ⟩
  mod-subst refl refl x = x
```

Another thing that's trivial to show is the fact that $0 ≈ n (\text{mod} n)$:

```agda
  0≈n : {n : ℕ} → 0 ≈ n ⟨mod n ⟩
  0≈n = ≈-mod 1 0 refl
```

It's also nice to show that addition is cancellative inside of `_≈_⟨mod_⟩`,
for which we can use the corresponding lemma about natural numbers,
`+-cancelˡ-≡`:

```agda
  mod-+-cancelˡ
      : (c a b : ℕ)
      → c + a ≈ c + b ⟨mod n ⟩
      → a ≈ b ⟨mod n ⟩
  mod-+-cancelˡ {n} c a b (≈-mod x y p) =
    ≈-mod x y ((+-cancelˡ-≡ c)
      (
      begin
        c + (a + x * n)  ≡⟨ sym (+-assoc c a (x * n)) ⟩
        (c + a) + x * n  ≡⟨ p ⟩
        c + b + y * n    ≡⟨ +-assoc c b (y * n) ⟩
        c + (b + y * n)  ∎
      ))
    where open ≡-Reasoning
```

A helpful lemma is that we can move terms between pairs of additions:

```agda
  swizzle
      : (a b c d : ℕ)
      → (a + b) + (c + d) ≡ (a + c) + (b + d)
  swizzle a b c d =
    begin
      (a + b) + (c + d)  ≡⟨ +-assoc a b (c + d) ⟩
      a + (b + (c + d))  ≡⟨ sym (cong (a +_) (+-assoc b c d)) ⟩
      a + ((b + c) + d)  ≡⟨ cong (\ φ → a + (φ + d)) (+-comm b c) ⟩
      a + ((c + b) + d)  ≡⟨ cong (a +_) (+-assoc c b d) ⟩
      a + (c + (b + d))  ≡⟨ sym (+-assoc a c (b + d)) ⟩
      (a + c) + (b + d)  ∎
    where open ≡-Reasoning
```

And finally, as our main theorem of this section, we can show that `_≈_⟨mod_⟩`
preserves addition:

```agda
  +-homo-mod
      : a ≈ b ⟨mod n ⟩
      → c ≈ d ⟨mod n ⟩
      → a + c ≈ b + d ⟨mod n ⟩
  +-homo-mod {a} {b} {n} {c} {d} (≈-mod x y pxy) (≈-mod z w pzw) =
    ≈-mod (x + z) (y + w)
      (
      begin
        (a + c) + (x + z) * n
      ≡⟨ cong ((a + c) +_) (*-distribʳ-+ n x z) ⟩
        (a + c) + (x * n + z * n)
      ≡⟨ swizzle a c (x * n) (z * n) ⟩
        (a + x * n) + (c + z * n)
      ≡⟨ cong₂ _+_ pxy pzw ⟩
        (b + y * n) + (d + w * n)
      ≡⟨ swizzle b (y * n) d (w * n) ⟩
        (b + d) + (y * n + w * n)
      ≡⟨ sym (cong ((b + d) +_) (*-distribʳ-+ n y w)) ⟩
        b + d + (y + w) * n
      ∎
      )
    where open ≡-Reasoning
```


Exercise

:   Define `mod-trans` in terms of `mod-+-cancelˡ`, `mod-subst` and
    `+-homo-mod`.


Solution

:   ```agda
  mod-trans2 : a ≈ b ⟨mod n ⟩ → b ≈ c ⟨mod n ⟩ → a ≈ c ⟨mod n ⟩
  mod-trans2 {a} {b} {c = c} a=b b=c =
    mod-+-cancelˡ b a c
      (mod-subst (+-comm a b) refl
        (+-homo-mod a=b b=c))
    ```


### Setoids

While it may seem like we've taken a long detour from our original goal of
talking about equality, we are now ready to tackle *setoids* in their full
glory. A setoid is a bundled binary relation alongside a proof that it's an
equivalence relationship. By putting all of these things together, we're
rewarded by the Agda standard library with setoid reasoning: syntax for doing
"equational" reasoning over our objects.

```agda
  private
    open import Relation.Binary
    mod-setoid : (n : ℕ) → Setoid _ _
    Setoid.Carrier (mod-setoid n) = ℕ
    Setoid._≈_ (mod-setoid n) = _≈_⟨mod n ⟩
    IsEquivalence.refl (Setoid.isEquivalence (mod-setoid n)) = mod-refl
    IsEquivalence.sym (Setoid.isEquivalence (mod-setoid n)) = mod-sym
    IsEquivalence.trans (Setoid.isEquivalence (mod-setoid n)) = mod-trans

  module mod-reasoning (n : ℕ) where
    open import Relation.Binary.Reasoning.Setoid (mod-setoid n) public
```

Our `Setoid` record is just the following:

```agda
record Setoid : Set₁ where
  infix 4 _≈_
  field
    Carrier : Set
    _≈_ : Carrier → Carrier → Set
    isEquivalence : IsEquivalence _≈_
open Setoid
```

and it's trivial to show now that `_≈_⟨mod_⟩` forms a setoid:

```agda
mod-setoid : ℕ → Setoid
Carrier (mod-setoid n) = ℕ
_≈_ (mod-setoid n) = _≈_⟨mod n ⟩
isEquivalence (mod-setoid n) = mod-equiv
```

Finally, we've now built the reasoning structure around which we can write
proofs about `_≈_⟨mod_⟩` significantly more directly than we have been able to
thus far.

For example, let's show the following fact:

```agda
module _ {n : ℕ} where
  open IsEquivalence (mod-equiv {n})

  0≈a*n : (a : ℕ) → 0 ≈ a * n ⟨mod n ⟩
```

Rather than faff about with `x` and `y` such that they multiply against `n` to
equal the left and right sides, we can now use our setoid reasoning to abstract
away the awkward details. We begin by pattern matching on `a`; the zero case is
trivial:

```agda
  0≈a*n zero = refl
```

Otherwise, it's time to `open mod-reasoning n` and get to work. We are trying to
show `0 ≈ suc a * n ⟨mod n ⟩`, so setoid reasoning lets us begin with 0:

```agda
  0≈a*n (suc a) =
    begin
      0
```

which is definitionally equal (via everyday propositional equality `≡⟨⟩`) to $0
+ 0$:

```agda
    ≡⟨⟩
      0 + 0
```
We can now use `≈⟨_⟩` as admitted by our setoid to give a `_≈_⟨mod_⟩`
justification as to why the two things are equal:

```agda
    ≈⟨ +-homo-mod 0≈n (0≈a*n a) ⟩
      n + a * n
```

And then, finally, another propositional equality justification to show that
we've completed the proof:

```agda
    ≡⟨⟩
      suc a * n
    ∎
    where
      open mod-reasoning n
```

