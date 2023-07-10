# Isomorphisms

```agda
{-# OPTIONS --allow-unsolved-metas #-}

module 7-isos where
```

In this chapter we will discuss when are two *types* the same, in essence,
looking for a suitable notion of equality for types themselves. Surprisingly,
this is not merely an exercise in learning obscure facts---the theory here gives
rise to some incredibly powerful techniques in programming, like automatic
asymptotic-improvement for many classes of algorithms. In order to motivate the
techniques involved, we will first discuss the countability of a type, develop a
robust mechanism for operating with equal type, and finally explore applications
of these techniques.


## Finite Numbers

Although we have spent an eternity discussing different sorts of numbers, we
have one final variety to define and work though. These are the *finite
numbers,* which, unlike the infinity of the natural numbers, are bounded in the
largest number they can represent. Finite numbers are all around us, from the 64
bit integers (of which the biggest representable number is
18446744073709551615), to the numbers we should be using to index arrays---after
all, the safest way to avoid a bounds check at runtime is to ensure the number
you're trying to index against is guaranteed to be less than the length of the
array in question.

Contrasting the 64 bit integer use-case against the array bounds use-case is
informative, in that in the latter, we might not know exactly what the biggest
representable number should be. Rather than doing the usual thing and defining
completely different types for `Word8`, `Word16`, `Word32`, etc., we can instead
make a single type constructor for all finite numbers, indexed by how many
distinct numbers it can represent. We'll call this type `type:Fin`, and would
like the property that `type:Fin 2` has exactly two values, while `type:Fin 13`
has 13. By picking absurdly large values of `n`, we can use `type:Fin n` to
represent the machine words, and instead by using `n` in a dependent way, we can
ensure it matches the length of an array. We will look at examples of both of
these use cases in a moment, but first we must define the type.

```agda
open import Data.Nat as ℕ using (ℕ)
private variable
  m n : ℕ


module Definition-Fin where
  data Fin : ℕ → Set where
    zero  : Fin (ℕ.suc n)
    suc   : Fin n → Fin (ℕ.suc n)  -- ! 1
```

`type:Fin`, like `type:ℕ`, is a unary encoding of the natural numbers, but you
will notice that each of its constructors produces a `type:Fin` indexed by a
`ctor:ℕ.suc`. Agda technically doesn't require use to use a fully qualified
`ctor:ℕ.suc` here, instead we could simply use `ctor:suc`, but it helps to
differentiate against the `type:Fin`-valued `ctor:suc` defined at [1](Ann).

Because each data constructor is indexed by `ctor:ℕ.suc`, there is simply no way
to build a `type:Fin 0`, which is consistent with our desideratum that `type:Fin
n` have $n$ distinct values. Every time we invoke `ctor:suc`, however, we lose
some "capacity" in the index, until we are eventually *forced* to use
`ctor:zero`. Because every time we use `ctor:suc`, we lose a `ctor:ℕ.suc` in the
index, we are allowed to call `ctor:suc` exactly $n - 1$ times before we are
required to call `ctor:zero`. And it is exactly this `ctor:zero` which explains
the discrepancy between the $n - 1$ potential calls to `ctor:suc` and the $n$
values that `type:Fin n` is promised to have. It's just like how the biggest
number we can store in a byte is 255, even though there are 256 values in a
byte---we just have to remember to count zero!

To illustrate that this all works, we can give the five values of `Fin 5`:

```agda
  module Examples where
    0f 1f 2f 3f 4f : Fin 5
    0f = zero
    1f = suc zero
    2f = suc (suc zero)
    3f = suc (suc (suc zero))
    4f = suc (suc (suc (suc zero)))
```

In an attempt to continue the pattern, we can try:

```illegal
    5f : Fin 5
    5f = suc (suc (suc (suc (suc zero))))
```

but Agda instead insists that this is not allowed:

```info
(ℕ.suc _n_37) != ℕ.zero of type ℕ
when checking that the expression zero has type Fin 0
```

Therefore, we can conclude that `type:Fin` behaves as we'd like it to.

Of course, we can always forget the index, and transform a `type:Fin` into a
`type:ℕ`:

```agda
  toℕ : Fin n → ℕ
  toℕ zero     = ℕ.zero
  toℕ (suc x)  = ℕ.suc (toℕ x)
```

Rather than using our own definition for the remainder of this chapter, we will
instead import an equivalently-defined version from the standard library:

```agda
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc)
```

## Finites for Vector Lookup

Functional programming usually eschews arrays, because they are *non-inductive*
(that is, not built from smaller copies of themselves) data structures. Instead,
we prefer to use linked lists, which are equivalently good, up to some
definition of equivalence that pays no attention to matters of performance on
a traditional Von Neumann architecture computer. However, that notion of
equivalence *does* include notions of program correctness and composition of
reasoning.

Vectors are a version of linked lists whose type is annotated with the number of
elements in the list. Thus, vectors are an excellent stand-in for arrays when
considered as contiguous blocks of memory which must be allocated somewhere. The
definition of a vector is straightforward---every time you stick an element in,
we increase its length type index:

```agda
open import Level
  renaming (zero to lzero; suc to lsuc; _⊔_ to _⊔l_)

private variable
  ℓ : Level

module Example-Vectors where
  data Vec (A : Set ℓ) : ℕ → Set ℓ where
    []   : Vec A 0
    _∷_  : A → Vec A n → Vec A (suc n)
  -- TODO(sandy): check this precedence
  infixr 4 _∷_
```

Extracting the length of a vector is very easy; simply take the index and return
it:

```agda
  private variable
    A : Set ℓ

  length : Vec A n → ℕ
  length {n = n} _ = n
```

However, most relevant to our previous discussion about the finite numbers, we
can use a `type:Fin` to extract a single element from the vector. By indexing
the `type:Vec` and the `type:Fin` by the same `n`, we can ensure that it's a
type error to request a value beyond the bounds of the array:

```agda
  lookup : Vec A n → Fin n → A
  lookup (a ∷ as) zero      = a
  lookup (a ∷ as) (suc ix)  = lookup as ix
```

To illustrate this function, we can show that it works as expected:

```agda
  open import Data.Char
  open import Relation.Binary.PropositionalEquality
    using (_≡_; refl)

  _ : lookup ('a' ∷ 'b' ∷ 'c' ∷ []) (suc zero) ≡ 'b'
  _ = refl
```

As a quick note, `def:lookup` is known in more traditional, ALGOL-like
languages, as `def:_[_]`:

```agda
  _[_] : Vec A n → Fin n → A
  _[_] = lookup

  _ : ('a' ∷ 'b' ∷ 'c' ∷ []) [ suc (suc zero) ] ≡ 'c'
  _ = refl
```

## Characteristic Functions

An interesting realization is that the `def:lookup` completely characterizes the
`type:Vec` type. Another way of saying that is that there is exactly as much
information in `type:Vec` as there is in this alternative definition of
`type:Vec′`:

```agda
  Vec′ : Set ℓ → ℕ → Set ℓ
  Vec′ A n = Fin n → A
```

Given this definition, we have alternative implementations of `def:length′` and
`def:lookup′`:

```agda
  length′ : Vec′ A n → ℕ
  length′ {n = n} _ = n

  lookup′ : Vec′ A n → Fin n → A
  lookup′ f ix = f ix
```

Despite these definitions, you are probably not yet convinced that `type:Vec`
and `type:Vec′` are equivalent, and will remain so until I have put forth a
convincing proof. This is good skepticism, and the sort of thing we'd like to
foster. Nevertheless, I can present a proof that these two definitions of
vectors are equivalent---namely, by giving a function which transform one
type to the other, and a second function which goes the other direction. Going
the one way is easy, it's just `def:lookup`:

```agda
  toVec′ : Vec A n → Vec′ A n
  toVec′ = lookup
```

The other direction is slightly more subtle, and requires pattern matching on
the size of the vector:

```agda
  open import Function using (_∘_)

  fromVec′ : Vec′ A n → Vec A n
  fromVec′ {n = zero}   v = []
  fromVec′ {n = suc n}  v = v zero ∷ fromVec′ (v ∘ suc)  -- ! 1
```

You'll notice at [1](Ann), we must stick a call to `ctor:suc` in before we
invoke `v`. This is a common idiom when doing induction with data structures
represented as functions, which we will briefly discuss in the next section.
-- TODO(sandy): add a section ref. For the time being, it suffices to note that
in effect, this composition automatically adds one to any index that is looked
up in `v`---in essence, chopping off the 0th element, since it can no longer be
referenced.

To complete our proof, we must finally show that `def:fromVec′` and `def:toVec′`
are *inverses* of one another. That is, for any given vector, we should be able
to go to and fro(m), ending up exactly where we started. If we can do so for
every possible `type:Vec` and every possible `type:Vec′`, we have shown that
every vector can be encoded as either type, and thus that they are both equally
good representations of vectors. When we are working with `type:Vec` directly,
it suffices to show propositional equality:

```agda
  from∘to : (v : Vec A n) → fromVec′ (toVec′ v) ≡ v
  from∘to [] = refl
  from∘to (x ∷ v)
    rewrite from∘to v = refl
```

The other direction is slightly harder, since we do not have propositional
equality for function types. Instead, we can show the extensional equality of
the two `type:Vec′`s---that they store the same value at every possible index:

```agda
  to∘from
      : (v : Vec′ A n) → (ix : Fin n)
      → toVec′ (fromVec′ v) ix ≡ v ix
  to∘from v zero      = refl
  to∘from v (suc ix)  = to∘from (v ∘ suc) (ix)
```

This completes the proof that `def:fromVec′` and `def:toVec′` are inverses of
one another, and therefore, that `type:Vec` and `type:Vec′` are equivalent
types. Because `type:Vec′` is just the type of `def:lookup` curried with the
vector you'd like to look at, we say that `def:lookup` is the *characteristic
function.*

As we will see later in this chapter, the existence of a characteristic function
(in this sense) is exactly what defines the concept of "data structure" in the
first place.


## Isomorphisms

The argument presented above---that two types are equivalent if we can transform
between them without losing any information---is completely general, and goes by
the name *isomorphism.* We can bundle the whole proof argument together into a
record---although in doing so, we will generalize from propositional equality to
using setoids. The setoids add some cruft, but their added generality will
quickly come in handy. First, we can define the type itself, as a relation
between two setoids:

```agda
open import Relation.Binary
  using (Setoid; _Preserves_⟶_)

private variable
  c₁ c₂ c₃ c₄ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

record Iso
      (s₁ : Setoid c₁ ℓ₁)
      (s₂ : Setoid c₂ ℓ₂)
      : Set (c₁ ⊔l c₂ ⊔l ℓ₁ ⊔l ℓ₂) where
  constructor iso
```

Still inside the definition, we will publicly open our setoids, giving them
canonical names that we can use in later fields of `type:Iso`:

```agda
  open Setoid s₁ using ()
      renaming (Carrier to A; _≈_ to _≈₁_)
      public
  open Setoid s₂ using ()
      renaming (Carrier to B; _≈_ to _≈₂_)
      public
```

Now for our fields, which package up all the pieces of the proof that we gave
when showing the two equivalent types for vectors. In addition, since we're now
working with setoids, we must show that `field:to` and `field:from` preserve the
relevant equalities:

```agda
  field
    to   : A → B
    from : B → A
    from∘to≈id  : (x : A) → from (to x) ≈₁ x
    to∘from≈id  : (x : B) → to (from x) ≈₂ x
    to-cong    : to    Preserves _≈₁_ ⟶ _≈₂_
    from-cong  : from  Preserves _≈₂_ ⟶ _≈₁_
```

One last thing that we'll pack inside the definition of `type:Iso` are
facilities for using setoid reasoning over both `s₁` and `s₂`, which we will
name `module:A-Reasoning` and `module:B-Reasoning`---corresponding to the types
`A` and `B` for the respective carriers.

```agda
  module A-Reasoning where
    open import Relation.Binary.Reasoning.Setoid s₁
      public
  module B-Reasoning where
    open import Relation.Binary.Reasoning.Setoid s₂
      public
```

While `type:Iso` is a good name for the record, and especially when doing
copattern matching---it's not the name that mathematicians normally use for this
concept. Instead, they go with `def:_↔_` (input as [`<->`](AgdaMode).)

```agda
_↔_ = Iso
```

Before we go on to say too much more about isomorphisms, we can first show that
`type:Vec` and `type:Vec′` are indeed isomorphic to one another. After a little
import wrangling:

```agda
open import Relation.Binary.PropositionalEquality
  using ()
  renaming (setoid to prop-setoid)

import 6-structures
open 6-structures.Sandbox-Monoids
  using (≗-setoid)

open Iso

module _ where
  open Example-Vectors

  open Relation.Binary.PropositionalEquality using (refl; _≡_)
  open import Function using (_∘_)
```

we are now ready to show `def:vec-iso`, which states there is an isomorphism
between the propositional equality setoid on `type:Vec` and the `def:≗-setoid`
equality over `type:Vec′`. This proof is mostly trivial, since we've already
done the heavy lifting. However, showing `field:from-cong` takes some effort
(and a lemma, defined immediately after in a `keyword:where` block) since it
doesn't automatically fall out from computation.

```agda
  vec-iso
      : {A : Set c₁}
      → prop-setoid (Vec A n) ↔ ≗-setoid (Fin n) (prop-setoid A)
  to          vec-iso                     = lookup
  from        vec-iso                     = fromVec′
  from∘to≈id  vec-iso                     = from∘to
  to∘from≈id  vec-iso                     = to∘from
  to-cong     vec-iso refl a              = refl
  from-cong   (vec-iso {A = A}) {x} {y} f = lemma _ x y f
```

In order to show the `def:lemma`, we must prove that every element in
`def:fromVec′` of `x` is equal to every element of the same on `y`. This is done
via induction on `n`, and proceeds methodically:

```agda
    where
      lemma
          : ∀ n → (x y : Fin n → A)
          → (f : ∀ a → x a ≡ y a)
          → fromVec′ x ≡ fromVec′ y
      lemma zero x y f = refl
      lemma (suc n) x y f
        rewrite f zero
        rewrite lemma n (x ∘ suc) (y ∘ suc) (f ∘ suc)
          = refl
```


## Isomorphisms Form an Equivalence Relation

I have been implicitly claiming that isomorphism is a good notion of equality
for types. We will now justify that, by showing that isomorphisms do indeed form
an equivalence relation. Reflexivity is trivial, because we need to map a type
to itself in both directions:

```agda
private variable
  s₁ : Setoid c₁ ℓ₁
  s₂ : Setoid c₂ ℓ₂
  s₃ : Setoid c₃ ℓ₃
  s₄ : Setoid c₄ ℓ₄

open import Relation.Binary using (Reflexive; Symmetric; Transitive)
open import Function using (id; _∘_)

↔-refl : s₁ ↔ s₁
↔-refl {s₁ = s} =
  iso id id (λ x → Setoid.refl s) (λ x → Setoid.refl s) id id
```

Showing symmetry requires us only to change which function we're calling
`field:to` and which we're calling `field:from`:

```agda
↔-sym : s₁ ↔ s₂ → s₂ ↔ s₁
↔-sym (iso to from from∘to≈id to∘from≈id to-cong from-cong)
  = iso from to to∘from≈id from∘to≈id from-cong to-cong
```

Transitivity is more work than the other two cases, but it's not much harder
conceptually. The trick is merely to compose the two `field:to` fields together,
and the two `field:from` together, and then find the right invocation of the
laws to show that these new compositions are also lawful.

```agda
module _ where
  open Iso

  ↔-trans : s₁ ↔ s₂ → s₂ ↔ s₃ → s₁ ↔ s₃
  to    (↔-trans f g) = to g ∘ to f
  from  (↔-trans f g) = from f ∘ from g
  from∘to≈id (↔-trans f g) x = begin
    from f (from g (to g (to f x)))  ≈⟨ from-cong f (from∘to≈id g _) ⟩
    from f (to f x)                  ≈⟨ from∘to≈id f x ⟩
    x                                ∎
    where open A-Reasoning f
  to∘from≈id (↔-trans f g) x = begin
    to g (to f (from f (from g x)))  ≈⟨ to-cong g (to∘from≈id f _) ⟩
    to g (from g x)                  ≈⟨ to∘from≈id g x ⟩
    x                                ∎
    where open B-Reasoning g
  to-cong    (↔-trans f g) x≈y = to-cong    g (to-cong    f x≈y)
  from-cong  (↔-trans f g) x≈y = from-cong  f (from-cong  g x≈y)
```

These three proofs together show that `type:_↔_` is indeed an equivalence
relation, although we must restrict the levels on both sides to be the same in
order for the standard machinery to agree with this fact:

```agda
open Relation.Binary using (IsEquivalence)

↔-equiv : IsEquivalence (_↔_ {c₁ = c₁} {ℓ₁ = ℓ₁})
IsEquivalence.refl   ↔-equiv = ↔-refl
IsEquivalence.sym    ↔-equiv = ↔-sym
IsEquivalence.trans  ↔-equiv = ↔-trans
```


## Countable Types


```agda
open import Data.Fin using (Fin; zero; suc)

module Sandbox-Finite where
  _Has_Elements : Setoid c₁ ℓ₁ → ℕ → Set (c₁ ⊔l ℓ₁)
  s Has cardinality Elements = s ↔ prop-setoid (Fin cardinality)
```

```agda
  open import Data.Bool using (Bool; true; false)
  open Iso

  open Relation.Binary.PropositionalEquality
    hiding ([_])

  bool-is-2 : prop-setoid Bool Has 2 Elements
  to    bool-is-2 false       = zero
  to    bool-is-2 true        = suc zero
  from  bool-is-2 zero        = false
  from  bool-is-2 (suc zero)  = true
  from∘to≈id bool-is-2 false       = refl
  from∘to≈id bool-is-2 true        = refl
  to∘from≈id bool-is-2 zero        = refl
  to∘from≈id bool-is-2 (suc zero)  = refl
  to-cong    bool-is-2 refl = refl
  from-cong  bool-is-2 refl = refl
```

From which we can immediately derive the fact that any two types with the same
number of elements are isomorphic to one another:

```agda
  fin-iso : s₁ Has n Elements → s₂ Has n Elements → s₁ ↔ s₂
  fin-iso i₁ i₂ = ↔-trans i₁ (↔-sym i₂)
```

```agda
  open Data.Nat using (_*_; _+_)

  open import Data.Product using (_×_; _,_; proj₁; proj₂)
  import Data.Product as ×
  open import Data.Fin using (combine; remQuot)
  open import Data.Fin.Properties

  open import Data.Product.Relation.Binary.Pointwise.NonDependent
    using (×-setoid)

  ×-preserves-↔ : s₁ ↔ s₂ → s₃ ↔ s₄ → ×-setoid s₁ s₃ ↔ ×-setoid s₂ s₄
  to    (×-preserves-↔ s t) = ×.map (to s) (to t)
  from  (×-preserves-↔ s t) = ×.map (from s) (from t)
  from∘to≈id (×-preserves-↔ s t) (x , y) =
    from∘to≈id s x , from∘to≈id t y
  to∘from≈id (×-preserves-↔ s t) (x , y) =
    to∘from≈id s x , to∘from≈id t y
  to-cong    (×-preserves-↔ s t) = ×.map (to-cong s) (to-cong t)
  from-cong  (×-preserves-↔ s t) = ×.map (from-cong s) (from-cong t)

  *-fin
      : prop-setoid (Fin (m * n))
      ↔ ×-setoid (prop-setoid (Fin m)) (prop-setoid (Fin n))
  to          *-fin = remQuot _
  from        *-fin (fst , snd)  = combine fst snd
  from∘to≈id  (*-fin {m = m}) x  = combine-remQuot {m} _ x
  to∘from≈id  *-fin (x , y) with remQuot-combine x y
  ... | p = cong proj₁ p , cong proj₂ p
  to-cong *-fin refl = refl , refl
  from-cong *-fin (refl , refl) = refl

  ×-fin : s₁ Has m Elements → s₂ Has n Elements
        → ×-setoid s₁ s₂ Has m * n Elements
  ×-fin fin₁ fin₂ = ↔-trans (×-preserves-↔ fin₁ fin₂) (↔-sym *-fin)
```

```agda
  open import Data.Sum.Relation.Binary.Pointwise
    using (⊎-setoid; ⊎-refl; inj₁; inj₂; ≡⇒Pointwise-≡)

  open Data.Fin using (splitAt; join)
  open import Data.Sum
  import Data.Sum as +

  ⊎-preserves-↔ : s₁ ↔ s₂ → s₃ ↔ s₄ → ⊎-setoid s₁ s₃ ↔ ⊎-setoid s₂ s₄
  to    (⊎-preserves-↔ s t) = +.map (to s) (to t)
  from  (⊎-preserves-↔ s t) = +.map (from s) (from t)
  from∘to≈id (⊎-preserves-↔ s t) (inj₁ x) = inj₁ (from∘to≈id s x)
  from∘to≈id (⊎-preserves-↔ s t) (inj₂ y) = inj₂ (from∘to≈id t y)
  to∘from≈id (⊎-preserves-↔ s t) (inj₁ x) = inj₁ (to∘from≈id s x)
  to∘from≈id (⊎-preserves-↔ s t) (inj₂ y) = inj₂ (to∘from≈id t y)
  to-cong (⊎-preserves-↔ s t) (inj₁ x) = inj₁ (to-cong s x)
  to-cong (⊎-preserves-↔ s t) (inj₂ x) = inj₂ (to-cong t x)
  from-cong (⊎-preserves-↔ s t) (inj₁ x) = inj₁ (from-cong s x)
  from-cong (⊎-preserves-↔ s t) (inj₂ x) = inj₂ (from-cong t x)

  +-fin
      : prop-setoid (Fin (m + n))
      ↔ ⊎-setoid (prop-setoid (Fin m)) (prop-setoid (Fin n))
  to    +-fin = splitAt _
  from  +-fin = join _ _
  from∘to≈id (+-fin {m = m})  = join-splitAt m _
  to∘from≈id +-fin x          = ≡⇒Pointwise-≡ (splitAt-join _ _ x)
  to-cong    +-fin refl        = ⊎-refl refl refl
  from-cong  +-fin (inj₁ refl) = refl
  from-cong  +-fin (inj₂ refl) = refl

  ⊎-fin : s₁ Has m Elements → s₂ Has n Elements
        → ⊎-setoid s₁ s₂ Has m + n Elements
  ⊎-fin fin₁ fin₂ = ↔-trans (⊎-preserves-↔ fin₁ fin₂) (↔-sym +-fin)

```


## Sigma Types


## Exponent Laws

```agda
open import Data.Unit
  using (⊤; tt)

open Setoid


_¹ : (s : Setoid c₁ ℓ₁) → s ↔ ≗-setoid ⊤ s
to          (s ¹) x _   = x
from        (s ¹) f     = f tt
from∘to≈id  (s ¹) x     = refl s
to∘from≈id  (s ¹) x tt  = refl s
to-cong     (s ¹) x tt  = x
from-cong   (s ¹) f     = f tt

open import Data.Product using (_×_; _,_)

private variable
  a b : Level
  X : Set a
  Y : Set b

open import Function using (flip)

flip-iso
  : (s : Setoid c₁ ℓ₁)
  → ≗-setoid X (≗-setoid Y s) ↔ ≗-setoid Y (≗-setoid X s)
to          (flip-iso s)       = flip
from        (flip-iso s)       = flip
from∘to≈id  (flip-iso s) f x y = refl s
to∘from≈id  (flip-iso s) f x y = refl s
to-cong     (flip-iso s) f     = flip f
from-cong   (flip-iso s) f     = flip f

hmm
  : (s : Setoid c₁ ℓ₁)
  → ≗-setoid (X × Y) s ↔ ≗-setoid X (≗-setoid Y s)
to          (hmm s) f x y      = f (x , y)
from        (hmm s) f (x , y)  = f x y
from∘to≈id  (hmm s) f xy       = refl s
to∘from≈id  (hmm s) f x y      = refl s
to-cong     (hmm s) f x y      = f (x , y)
from-cong   (hmm s) f (x , y)  = f x y

open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Data.Product.Relation.Binary.Pointwise.NonDependent
  using (×-setoid)

hmm2
  : (s : Setoid c₁ ℓ₁)
  → ≗-setoid (X ⊎ Y) s
      ↔ ×-setoid (≗-setoid X s) (≗-setoid Y s)
to    (hmm2 s) f  = (λ x → f (inj₁ x) )
                  , (λ y → f (inj₂ y))
from  (hmm2 s) (fx , fy) (inj₁ x) = fx x
from  (hmm2 s) (fx , fy) (inj₂ y) = fy y
from∘to≈id  (hmm2 s) f (inj₁ x) = refl s
from∘to≈id  (hmm2 s) f (inj₂ y) = refl s
to∘from≈id  (hmm2 s) fxfy  = (λ x → refl s)
                           , (λ y → refl s)
to-cong     (hmm2 s) f = (λ x → f (inj₁ x))
                       , (λ y → f (inj₂ y))
from-cong   (hmm2 s) (fx , fy) (inj₁ x) = fx x
from-cong   (hmm2 s) (fx , fy) (inj₂ y) = fy y


open Data.Nat using (_^_)
open Sandbox-Finite

-- TODO(sandy): this is not for an arbitrary setoid iso in the codomain
→-preserves-↔
    : s₁ ↔ s₂ → s₃ ↔ s₄
    → ≗-setoid (s₁ .Carrier) s₃ ↔ ≗-setoid (s₂ .Carrier) s₄
to (→-preserves-↔ s t) f = to t ∘ f ∘ from s
from (→-preserves-↔ s t) f = from t ∘ f ∘ to s
from∘to≈id (→-preserves-↔ s t) f x =
  begin
    from t (to t (f (from s (to s x))))
  ≈⟨ from∘to≈id t _ ⟩
    f (from s (to s x))
  ≈⟨ ? ⟩
    f x
  ∎
  where open A-Reasoning t
to∘from≈id (→-preserves-↔ s t) f x = {! !}
to-cong (→-preserves-↔ s t) f x = to-cong t (f (from s x))
from-cong (→-preserves-↔ s t) f x = from-cong t (f (to s x))

open Example-Vectors using (Vec; []; _∷_)

module _ where
  import Relation.Binary.PropositionalEquality as ≡

  vec-fin₀
    : ∀ {A : Set c₁} → prop-setoid (Vec A 0) Has 1 Elements
  to vec-fin₀ [] = zero
  from vec-fin₀ zero = []
  from∘to≈id vec-fin₀ [] = ≡.refl
  to∘from≈id vec-fin₀ zero = ≡.refl
  to-cong vec-fin₀ ≡.refl = ≡.refl
  from-cong vec-fin₀ ≡.refl = ≡.refl

  vec-rep
      : prop-setoid (Vec (s₁ .Carrier) (suc n))
        ↔ ×-setoid s₁ (prop-setoid (Vec (s₁ .Carrier) n))
  to vec-rep (x ∷ xs) = x , xs
  from vec-rep (x , xs) = x ∷ xs
  from∘to≈id vec-rep (x ∷ xs) = ≡.refl
  to∘from≈id (vec-rep {s₁ = s}) (x , xs) = refl s , ≡.refl
  to-cong (vec-rep {s₁ = s}) ≡.refl = refl s , ≡.refl
  from-cong (vec-rep {s₁ = s}) (fst , ≡.refl) = {! !}


  vec-fin
    : s₁ Has m Elements
    → prop-setoid (Vec (s₁ .Carrier) n) Has (m ^ n) Elements
  vec-fin {n = zero} s = vec-fin₀
  vec-fin {n = suc n} s
    = ↔-trans (vec-rep)
    ( ↔-trans (×-preserves-↔ s (vec-fin s))
    ( (↔-sym *-fin) ))

→-fin : s₁ Has m Elements → s₂ Has n Elements
      → ≗-setoid (s₁ .Carrier) s₂ Has (n ^ m) Elements
→-fin s t
  = ↔-trans (→-preserves-↔ s t)
      (↔-trans (↔-sym vec-iso) (vec-fin ↔-refl))
```


## Automatic Memoization

