# Isomorphisms

Hidden

:   ```agda
{-# OPTIONS --allow-unsolved-metas #-}
    ```

```agda
module Chapter8-Isomorphisms where
```


As we near the end of this book, we now turn our focus towards our final
theoretical topic: *isomorphisms*---the question of when two types are
equivalent. In essence, then, we will find ourselves looking for a suitable
notation of equality over types themselves. Rather surprisingly, this is not
moot exercise in learning obscure and arcane trivia, as the theory gives rise to
some incredibly powerful programming techniques.

Like many notions of equality we have studied thus far, isomorphisms do not
preserve *everything* between two types. Of particular interest to us, is that
isomorphic types usually have dramatically different computational
behavior---and the knowledgeable practitioner can exploit this differential. In
this chapter, we will focus on the theory, saving its real-world usage as a case
study for our final chapter. There we will wield our newfound powers to
dramatically simplify the problem of dynamic programming, in essence, acquiring
learning how to improve algorithmic asymptotics for free.

Isomorphisms are *everywhere* in programming, whether we're aware of them or
not. Usually they're completely invisible until you learn where to look.
The existence of an isomorphism is what we're grasping for when we serialize a
data structure to disk, and read it back again later, expecting to get the same
thing back. There is an implicit isomorphism we unwittingly invoke when we
multiply matrices to do 3D graphics programming---in that we forget there is a
difference between operations in 3D space and the inscrutable arrays of numbers
we use to encode them.

Before you learn to look for them, isomorphisms just feel like harmless
equivocation between two different things that feel the same. Functions on a
computer *are* just pointers to a series of instructions, aren't they? Numbers
*are* just their binary representations, right? As we have seen throughout this
book, numbers at least *are* much more than their binary representations.

In all of these cases, we are mentally invoking the idea that these two
disparate things are similar enough that it's safe to think of one as the other.
Usually this equivalence is much less sound than we'd like, and is the source of
nearly all non-trivial software bugs. Problems arise when our mental model of a
system doesn't correspond exactly with the system itself.


Prerequisites

:   ```agda
open import Chapter1-Agda
  using (Bool; true; false; _×_; uncurry)
    ```

:   ```agda
open import Chapter2-Numbers
  using (ℕ; zero; suc; _+_; _*_; _^_; Maybe; just; nothing)
    ```

:   ```agda
open import Chapter3-Proofs
  renaming (module PropEq to ≡)
    ```

:   ```agda
open import Chapter4-Relations
    ```

:   ```agda
open import Chapter5-Modular-Arithmetic
  using (equiv-to-preorder; ≡-is-equivalence; refl; sym; trans)
    ```

:   ```agda
open import Chapter6-Decidability
  using (⊥)
    ```

:   ```agda
open import Chapter7-Structures
  hiding (length)
    ```

Hidden

:   ```agda
postulate
  exercise-for-the-reader : {ℓ : Level} {A : Set ℓ} → A
-- FIX
    ```

## Finite Numbers

Although we have spent an eternity discussing different sorts of numbers, we
will need one final flavor---the *finite numbers.*  These, unlike the infinity
of the naturals, are bounded in the largest number they can represent.

Finite numbers are all around us. The sixty four wires inside of your computer
use voltages to encode numbers, and no matter how hard you `ctor:suc`, you're
eventually going to run out of encodable numbers on your hardware. A sixty-fifth
wire won't come along out of nowhere just because you need it! Of course, we can
simulate bigger numbers by working on them in chunks, but at any one time, the
biggest number a computer can ever work with is $2^{64}-1$.

Unwittingly, we (conceptually) use finite numbers when we index arrays. The
array has a length, and it's illegal to lookup something in the array using a
number bigger than that length. Different languages have different solutions to
this problem, but the most elegant one is to prevent it from happening in the
first place---that is, to use a type more precise than simply `type:ℕ`.

Contrasting the 64 bit integer case against the array bounds case is
informative, in that in the latter, we might not know exactly what the biggest
representable number should be. Rather than doing the usual thing and defining
completely different types for 8-bit numbers, and 16-bit numbers, and so on, we
can instead make a single type for *all* finite numbers, indexed by how many
distinct numbers it can represent.

We'll call this type `type:Fin`, and would like the property that `type:Fin 2`
has exactly two values, while `type:Fin 13` has 13. By picking absurdly large
values of `n`, we can use `type:Fin n` to represent the machine words, and
instead by using `n` in a dependent way, we can ensure it matches the length of
an array. We will look at examples of both of these use cases in a moment, but
first we must define the type.

```agda
module Definition-Fin where
  data Fin : ℕ → Set where
    zero  : {n : ℕ} → Fin (ℕ.suc n)
    suc   : {n : ℕ} → Fin n → Fin (ℕ.suc n)
```

`type:Fin`, like `type:ℕ`, is a unary encoding of the natural numbers, but you
will notice that each of its constructors now produces a `type:Fin` indexed by a
`ctor:ℕ.suc`. Agda technically doesn't require use to use a fully qualified
`ctor:ℕ.suc` here, but it helps to visually differentiate which `ctor:suc` comes
from `type:Fin` and which from `ℕ`.

Because each data constructor is indexed by `ctor:ℕ.suc`, there is simply no way
to build a `type:Fin 0`---consistent with our desideratum that `type:Fin n` have
$n$ distinct values. Note that every time we invoke `ctor:suc`, we must give a
*smaller* `type:Fin` as an argument. In essence, this means give up some of our
finite "capacity". Eventually, the innermost argument will have type `type:Fin
1`, for which the only constructor is `ctor:zero`.

It is exactly this `ctor:zero` which explains the discrepancy between the $n -
1$ potential calls to `ctor:suc` and the $n$ values that `type:Fin n` is
promised to have. It's just like how the biggest number we can store in a byte
is 255, even though there are 256 values in a byte---we just have to remember to
count `ctor:zero`!

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

but Agda instead insists that such a thing is not allowed:

```info
(ℕ.suc _n_37) != ℕ.zero of type ℕ
when checking that the expression zero has type Fin 0
```

Therefore, we can conclude that `type:Fin` behaves as we'd like. Of course, we
can always opt to forget the index, transforming a `type:Fin` into a `type:ℕ` in
the process:

```agda
  toℕ : {n : ℕ} → Fin n → ℕ
  toℕ zero     = ℕ.zero
  toℕ (suc x)  = ℕ.suc (toℕ x)
```

As usual, rather than giving our own definition for `type:Fin`, we will instead
import it from the standard library:

```agda
open import Data.Fin
  using (Fin; zero; suc)
```


## Vectors and Finite Bounds

You are likely familiar with arrays as a data structure for storing a constant
number of elements. Arrays are characterized by random access to their elements,
and being contiguously laid-out in memory.

Already this definition should raise some alarm bells. Discussion of memory
placement is something we should be fundamentally disinterested in; it's an
arbitrary property of the computing machines we happen to have today, but it's
not of any real importance to what computation *actually is.* Worse, arrays are
non-inductive, in that we can't easily built a larger one out of a smaller one,
because the continuous-memory condition means we will probably need to
reallocate and copy the contents.

Instead, we turn our attention to a related, but significantly-better-behaved
notion: the *vector.* Vector are data structures for storing a constant number
of elements, which, importantly, and unlike arrays, are inductive. Their
inductivity means vectors play nicely in a mathematical setting, and, when kept
at a constant size, provide an excellent model for arrays in contemporary
hardware.

The definition of a vector is completely, straightforward---every time you stick
an element in, just  increase its length:

```agda
private variable
  ℓ : Level
  m n : ℕ

module Definition-Vectors where
  data Vec (A : Set ℓ) : ℕ → Set ℓ where
    []   : Vec A 0
    _∷_  : A → Vec A n → Vec A (suc n)
  infixr 5 _∷_
```

Of course, rather than define this type ourselves, we will take it from the
standard library:

```agda
open import Data.Vec
  using (Vec; []; _∷_)
```
The `type:ℕ` index of `type:Vec` thus stores the length of the vector, which is
to say, the number of elements inside of it. Therefore, we can "compute" the
length of a vector just by taking its index and returning it:

```agda
module Example-Vectors where
  private variable
    A : Set ℓ

  length : Vec A n → ℕ
  length {n = n} _ = n
```

More interestingly however is that we can give a precise type to looking up an
element by using a `type:Fin` as the index type. By indexing the `type:Vec` and
the `type:Fin` by the same `n`, we can ensure that it's a type error to request
a value beyond the bounds of the array:

```agda
  lookup : Vec A n → Fin n → A
  lookup (a  ∷ _)   zero      = a
  lookup (_  ∷ as)  (suc ix)  = lookup as ix
```

To illustrate this function, we can show that it works as expected:

```agda
  _ : lookup (6 ∷ 3 ∷ 5 ∷ []) (suc (suc zero)) ≡ 5
  _ = refl
```

We are almost ready to discuss isomorphisms, but first we must come up with a
different representation for vectors, in order to subsequently show that the two
notions are in fact "the same." To that end, we now turn our attention to
characteristic functions.


## Characteristic Functions

An interesting realization is that the `def:lookup` completely characterizes the
`type:Vec` type. Another way of saying that is that there is exactly as much
information in `type:Vec` as there is in this alternative definition of
`type:Vec′`:

```agda
  Vec′ : Set ℓ → ℕ → Set ℓ
  Vec′ A n = Fin n → A
```

Given this definition, we can give alternative implementations of the vector
constructors:

```agda
  []′ : Vec′ A 0
  []′ ()

  _∷′_ : A → Vec′ A n → Vec′ A (suc n)
  (a ∷′ v) zero      = a
  (a ∷′ v) (suc ix)  = v ix
```

and also alternative definitions of the vector eliminators:

```agda
  length′ : Vec′ A n → ℕ
  length′ {n = n} _ = n

  lookup′ : Vec′ A n → Fin n → A
  lookup′ f ix = f ix
```

Despite these definitions, you are probably not yet convinced that `type:Vec`
and `type:Vec′` are equivalent, and will remain dubious until I have put forth a
convincing proof. This is good skepticism. Nevertheless, I can present a proof
that these two definitions of vectors are equivalent---namely, by giving a
function which transform one type to the other, and a second function which goes
the other direction. Going the one way is easy; it's just `def:lookup`:

```agda
  toVec′ : Vec A n → Vec′ A n
  toVec′ = lookup
```

The other direction is slightly more subtle, and requires pattern matching on
the size of the vector:

```agda
  fromVec′ : Vec′ A n → Vec A n
  fromVec′ {n = zero}   v = []
  fromVec′ {n = suc n}  v = v zero ∷ fromVec′ (v ∘ suc)  -- ! 1
```

You'll notice at [1](Ann), we must stick a call to `ctor:suc` in before we
invoke `v`. This is a common idiom when doing induction with data structures
represented as functions; the general rule is that the domain of functions works
"backwards." If you make the argument bigger---like we're doing here---the
resulting image of the function is *smaller.*[^profunctor] For the time being,
it suffices to note that in effect, this composition automatically adds one to
any index that is looked up in `v`---in essence, chopping off the 0th element,
since it can no longer be referenced.

[^profunctor]: If this idea seems strange to you, you can quickly gain some
  intuition by fooling around with a graphing calculator. And if you're
  interested in why exactly functions behave this way, the relevant research
  keyword is that functions are *contravariant* in their domain.

To complete our proof, we must finally show that `def:fromVec′` and `def:toVec′`
are *inverses* of one another. That is, for any given vector, we should be able
to go to and fro(m)---ending up exactly where we started. If we can do so for
every possible `type:Vec` and every possible `type:Vec′`, we will have shown
that every vector can be encoded as either type, and thus that they are both
equally good representations of vectors.

When we are working with `type:Vec` directly, it suffices to show propositional
equality:

```agda
  fromVec′∘toVec′ : (v : Vec A n) → fromVec′ (toVec′ v) ≡ v
  fromVec′∘toVec′ [] = refl
  fromVec′∘toVec′ (x ∷ v)
    rewrite fromVec′∘toVec′ v
      = refl
```

Recall that we do not have a notion of propositional equality for functions.
While we could reach immediately for a setoid, for our purposes we can instead
show functional extensionality of the vectors-represented-as-functions---proving
that the two representations store the same value at every index:

```agda
  toVec′∘fromVec′
      : (v : Vec′ A n)
      → toVec′ (fromVec′ v) ≗ v
  toVec′∘fromVec′ v zero      = refl
  toVec′∘fromVec′ v (suc ix)  = toVec′∘fromVec′ (v ∘ suc) (ix)
```

This completes the proof that `def:fromVec′` and `def:toVec′` are inverses of
one another, and therefore, that `type:Vec` and `type:Vec′` are equivalent
types. Because `type:Vec′` is just the type of `def:lookup` curried with the
vector you'd like to look at, we say that `def:lookup` is the *characteristic
function.*

As we will see, the existence of a characteristic function (in this sense) is
exactly what defines the concept of "data structure" in the first place.


## Isomorphisms

The argument presented above---that two types are equivalent if we can transform
between them without losing any information---is completely general, and is what
we have been alluding to all this time by the name *isomorphism.*

We can bundle the whole proof argument together into a record---although in
doing so, we will generalize from propositional equality to using setoids. The
setoids add some cruft, but their added generality will quickly come in handy.
First, we can define the type itself, as a relation between two setoids:

```agda
private variable
  c₁ c₂ c₃ c₄ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

record Iso
      (s₁ : Setoid c₁ ℓ₁)
      (s₂ : Setoid c₂ ℓ₂)
      : Set (c₁ ⊔ c₂ ⊔ ℓ₁ ⊔ ℓ₂) where
  constructor iso
```

Working with multiple setoids at once is painful, so we will take a moment to
open `s₁` and `s₂`, projecting out and renaming their respective fields:

```agda
  open Setoid s₁ using ()
      renaming (Carrier to A; _≈_ to _≈₁_)
      public
  open Setoid s₂ using ()
      renaming (Carrier to B; _≈_ to _≈₂_)
      public
```

The fields of our `type:Iso` now must package up all the pieces of the proof
that we gave above: a pair of functions which convert between the two
representations, and a pair of proofs that these conversions are in fact
inverses of one another. And of course, since we're now dealing with setoids, we
must also show that the conversion functions respect congruence. All together
then, we have the following six fields:

```agda
  field
    to   : A → B
    from : B → A
    from∘to  : (x : A) → from (to x) ≈₁ x
    to∘from  : (x : B) → to (from x) ≈₂ x
    to-cong    : {x y : A} → x ≈₁ y → to x ≈₂ to y
    from-cong  : {x y : B} → x ≈₂ y → from x ≈₁ from y
```

One final thing that we'll pack inside the definition of `type:Iso` is
equational reasoning machinery for both sides of the isomorphism, which we will
name `module:A-Reasoning` and `module:B-Reasoning`---corresponding to the types
`A` and `B` of the respective carriers.

```agda
  module A-Reasoning where
    open Preorder-Reasoning (Setoid.isPreorder s₁)
      public

  module B-Reasoning where
    open Preorder-Reasoning (Setoid.isPreorder s₂)
      public
```

While `type:Iso` is a good name for the record, and especially when doing
copattern matching---it's not the name that mathematicians normally use for this
concept. Therefore, we will define a binary operator for `type:Iso`: `def:_≅_`
(input as [`~=`](AgdaMode).)

```agda
_≅_ = Iso
open Iso
```

Before we go on to say too much more about isomorphisms, we can first build
`def:vec-iso`, which formalizes our argument earlier that there is indeed an
isomorphism between `type:Vec` and its characteristic function `def:lookup`.

Recall that isomorphisms are defined over setoids, which means we must lift
`def:lookup` into the `type:_⇒_` setoid. The proof is mostly trivial, since
we've already done all the heavy lifting. However, we will first need one lemma,
which applies a function over a `type:Fn` (which, recall, is the notion of
equivalence for the `type:_⇒_` setoid.) While we could generalize the type
further, the following will be sufficient for our needs:

```agda
module _ where
  Fn-map
    : {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃}
    → (f : A → B)
    → Fn (prop-setoid B) (prop-setoid C)
    → Fn (prop-setoid A) (prop-setoid C)
  Fn-map f x = fn (Fn.func x ∘ f) (Fn.cong x ∘ ≡.cong f)
```

Finally, we can show `def:vec-iso`:

```agda
  open Example-Vectors

  vec-iso
      : {A : Set c₁}
      → prop-setoid (Vec A n)
      ≅ (prop-setoid (Fin n) ⇒ prop-setoid A)
  Fn.func (to vec-iso v) = lookup v
  Fn.cong (to vec-iso v) = ≡.cong (lookup v)
  from vec-iso = fromVec′ ∘ Fn.func
  from∘to vec-iso v rewrite fromVec′∘toVec′ v = refl
  to∘from vec-iso v {ix}  ≡.refl = toVec′∘fromVec′ (Fn.func v) ix
  to-cong vec-iso ≡.refl  ≡.refl = refl
  from-cong (vec-iso {n = zero}) _ = refl
  from-cong (vec-iso {n = suc n}) {v₁} {v₂} vi≡vj
    rewrite vi≡vj {x = zero} refl
    rewrite from-cong  vec-iso {Fn-map suc v₁} {Fn-map suc v₂}  -- ! 1
                       (vi≡vj ∘ ≡.cong suc)
      = refl
```

The complications at [1](Ann) requiring `def:Fn-map` are due to us needing to
show the congruence of two *completely different* functions when doing the
recursive case in `field:from-cong`. In essence, we must chop off the head of
both vector-as-a-functions, and unfortunately, Agda isn't smart enough to
determine this on its own.

Having successfully shown `def:vec-iso`, and thus gotten our first taste of an
isomorphism, we are now ready to investigate them more thoroughly.


## Equivalence on Isomorphisms

Thus far, I have been claiming that isomorphism is a good notion of equality
between types, but without any real evidence to back it up. We will now prove
just that, by showing isomorphisms do indeed form an equivalence
relation---which recall, is the "interface" of equality. First, we will need a
slew of setoids in scope:

```agda
private variable
  s₁ : Setoid c₁ ℓ₁
  s₂ : Setoid c₂ ℓ₂
  s₃ : Setoid c₃ ℓ₃
  s₄ : Setoid c₄ ℓ₄
```

Showing reflexivity is trivial; we need only map the carrier of a setoid to
itself:

```agda
≅-refl : s₁ ≅ s₁
≅-refl {s₁ = s} =
  iso id id (λ x → Setoid.refl s) (λ x → Setoid.refl s) id id
```

Symmetry is not much harder, in that it requires us only to rename which
function we're calling `field:to` and which we're calling `field:from`. Writing
it all out is a bit of a pain, but there is no conceptual difficulty:

```agda
≅-sym : s₁ ≅ s₂ → s₂ ≅ s₁
≅-sym (iso  f₁  f₂  id₁  id₂  cong₁  cong₂)
     = iso  f₂  f₁  id₂  id₁  cong₂  cong₁
```

Showing transitivity is more work than the other two cases, but again, there
isn't any challenge conceptually. The trick is merely to compose the two
`field:to` fields together, and the two `field:from` together, and then find the
right invocation of the laws to show that these new compositions are also
lawful.

```agda
module _ where
  open Iso

  ≅-trans : s₁ ≅ s₂ → s₂ ≅ s₃ → s₁ ≅ s₃
  to    (≅-trans f g) = to    g ∘ to    f
  from  (≅-trans f g) = from  f ∘ from  g
  from∘to (≅-trans f g) x = begin
    from f (from g (to g (to f x)))  ≈⟨ from-cong f (from∘to g _) ⟩
    from f (to f x)                  ≈⟨ from∘to f x ⟩
    x                                ∎
    where open A-Reasoning f
  to∘from (≅-trans f g) x = begin
    to g (to f (from f (from g x)))  ≈⟨ to-cong g (to∘from f _) ⟩
    to g (from g x)                  ≈⟨ to∘from g x ⟩
    x                                ∎
    where open B-Reasoning g
  to-cong    (≅-trans f g) x≈y = to-cong    g (to-cong    f x≈y)
  from-cong  (≅-trans f g) x≈y = from-cong  f (from-cong  g x≈y)
```

Together, these three proofs show that `type:_≅_` does indeed form an
equivalence relation. Unfortunately, the standard machinery doesn't allow our
levels to vary on either side of the equivalence, so we must unify them:

```agda
≅-equiv : IsEquivalence (_≅_ {c₁ = c₁} {ℓ₁ = ℓ₁})
IsPreorder.refl   (IsEquivalence.isPreorder ≅-equiv) = ≅-refl
IsPreorder.trans  (IsEquivalence.isPreorder ≅-equiv) = ≅-trans
IsEquivalence.sym ≅-equiv = ≅-sym
```

This restriction on the levels of our isomorphisms means that `type:≅-equiv`
will rarely be of use to us for doing equational reasoning. Nevertheless,
having shown that isomorphisms do indeed form an equivalence relation should
make us feel much better about treating them as the right choice for equality
between types.

Finally, it will often come in handy to be able to construct an isomorphism out
of theorems we've already proven. For this, we can use `def:≅-prop` which merely
wraps up a pair of propositionally-inverse functions.

```agda
≅-prop
    : {A : Set ℓ₁} {B : Set ℓ₂}
    → (f : A → B) → (g : B → A)
    → f ∘ g ≗ id
    → g ∘ f ≗ id
    → prop-setoid A ≅ prop-setoid B
to         (≅-prop f g f∘g=id g∘f=id) = f
from       (≅-prop f g f∘g=id g∘f=id) = g
from∘to    (≅-prop f g f∘g=id g∘f=id) = g∘f=id
to∘from    (≅-prop f g f∘g=id g∘f=id) = f∘g=id
to-cong    (≅-prop f g f∘g=id g∘f=id) = ≡.cong f
from-cong  (≅-prop f g f∘g=id g∘f=id) = ≡.cong g
```


## Finite Types

Now that we have a suitable definition for, and motivation behind, isomorphisms,
let's explore some circumstances by which they arise. One particularly fruitful
way to think about isomorphisms is that they correspond to a relabeling of each
of the elements, renaming elements in one of the carriers to names from the
other. When exactly can we do this? Whenever there are the same number of
elements in both types!

In fact, we can use this idea to *define* the notion of finite types---that is,
types with a finite number of elements---by showing an isomorphism *into*
`type:Fin`. By using some cute syntax, we can define `type:_Has_Elements`, which
we will use to say `s` `type:Has` `n` `type:Elements` to prove there are
exactly `n` distinguished elements in the setoid `s`. Incidentally, this number
of distinguished elements is also known as the *cardinality* of the
type[^quotient].

[^quotient]: Technically, the number of the elements in the type, *quotiented by
  the setoid,* but we will play a little fast and loose with the terminology for
  ease of reading.

```agda
module Sandbox-Finite where
  _Has_Elements : Setoid c₁ ℓ₁ → ℕ → Set (c₁ ⊔ ℓ₁)
  s Has cardinality Elements =
    s ≅ prop-setoid (Fin cardinality)

  -- FIX
```

We therefore know by definition (and reflexivity) that `bind:n:Fin n` has `n`
elements:

```agda
  fin-fin : {n : ℕ} → prop-setoid (Fin n) Has n Elements
  fin-fin = ≅-refl
```

Let's try a (slightly) less trivial example, and show that `type:Bool` has
exactly two elements. Rather surprisingly, this is significantly more tedious
than we might expect:

```agda
  open Iso

  bool-fin : prop-setoid Bool Has 2 Elements
  to         bool-fin false       = zero
  to         bool-fin true        = suc zero
  from       bool-fin zero        = _  -- ! 1
  from       bool-fin (suc zero)  = _
  from∘to    bool-fin false       = refl
  from∘to    bool-fin true        = refl
  to∘from    bool-fin zero        = refl
  to∘from    bool-fin (suc zero)  = refl
  to-cong    bool-fin ≡.refl      = refl
  from-cong  bool-fin ≡.refl      = refl
```

Notice that at [1](Ann), we have opted to let Agda infer the inverse function.
It's able to do so because it knows that `field:from∘to` is `def:refl`, and
therefore the result of `field:from` is already fully determined.

While we don't need an isomorphism to convince ourselves that `type:Bool` does
indeed have two elements, this machinery already holds water, and we can use it
to do real work. An immediate corollary of `type:_Has_Elements` is any two types
with the same cardinality must necessarily be isomorphic to one another:

```agda
  fin-iso
    : s₁  Has n Elements
    → s₂  Has n Elements
    → s₁ ≅ s₂
  fin-iso s₁ s₂ = ≅-trans s₁ (≅-sym s₂)
```


## Algebraic Data Types

As exciting as it is to show that there are *definitely* two booleans, one
can't help but feel a bit underwhelmed by the difficulty of the process. Are we
doomed to write giant isomorphisms for every type we care about? Is there
nothing more compositional that we can instead reach for? Indeed, many types can
be automatically disassembled into more compositional pieces.

If we forget about dependent types for the time being, the types we can build
are known as the *algebraic data types,* and correspond closely with types that
we care about as data (as opposed to types we care about as proofs.) The idea is
that we can decompose any algebraic data type, and rebuild it out of some
combination of `type:⊤`, `type:⊥`, `type:_⊎_` and `type:_×_`.

We haven't yet discussed `type:⊤`---pronounced "unit type"---because it's
neither a particularly value-ful nor valuable type, having only one inhabitant,
`ctor:tt`. The definition of `type:⊤` ([top](AgdaMode)) looks like this:

```agda
  module ⊤-Definition where
    record ⊤ : Set where
      constructor tt

  open import Data.Unit
    using (⊤; tt)
```

The unit type doesn't come into play much in Agda, but is more useful in
languages that permit side effects. A function which returns `type:⊤` is
therefore one which you are invoking *solely* for its side effects. Compared to
the expressivity of types we have become familiar with in Agda, such a dearth of
information is a hard world to return to. Nevertheless, we will find a use for
`type:⊤` in Agda momentarily.

Recall the definition of `type:Bool`:


```agda
  data Bool⅋ : Set where
    false  : Bool⅋
    true   : Bool⅋
```

How can we decompose this definition into a generic representation by way of
some combination of our algebraic data constructors, `type:⊤`, `type:⊥`,
`type:_⊎_` and `type:_×_`? Notice that `ctor:false` and `ctor:true` contain no
information, they are only arbitrary labels for two distinct elements of type
`type:Bool`. What's important is that we can create them *ex nihilo*---that is
to say, without needing to give any arguments to build them---and that we have a
*choice* between the two.

Whenever we have a choice between two types, we can model it with `type:_⊎_`.
And what's our choice between? It's between two constructors with no information
whatsoever, which is exactly the property that `type:⊤` also satisfies.
Therefore, we should be able to find an isomorphism between `type:Bool` and
`type:⊤ ⊎ ⊤`.

```agda
  open import Data.Sum using (_⊎_; inj₁; inj₂)
```

Exercise (Easy)

: Show the isomorphism between `type:Bool` and `type:⊤ ⊎ ⊤`.


Solution

:       ```agda
  generic-bool : prop-setoid Bool ≅ prop-setoid (⊤ ⊎ ⊤)
  to        generic-bool false  = inj₁  tt
  to        generic-bool true   = inj₂  tt
  from      generic-bool (inj₁  tt) = false
  from      generic-bool (inj₂  tt) = true
  from∘to   generic-bool false  = refl
  from∘to   generic-bool true   = refl
  to∘from   generic-bool (inj₁  tt) = refl
  to∘from   generic-bool (inj₂  tt) = refl
  to-cong   generic-bool ≡.refl = refl
  from-cong generic-bool ≡.refl = refl
        ```

Of course, it feels like we've traded needing to write an annoying isomorphism
into `expr:Fin 2` with an annoying isomorphism into `type:⊤ ⊎ ⊤`, but this is
not quite right. Importantly, isomorphisms between types and their generic
representations are canonical, and languages with good support for polytypic
programming can often synthesize these canonical isomorphisms on your behalf.
While Agda does have support for polytypic programming, its interface at time of
writing leaves much to be desired, and so nobody has actually implemented this
feature, although nothing but elbow grease is lacking.

Nevertheless, it's important to understand the generic representations of
algebraic data types. Even if the language you're working it can't synthesize
machinery to convert between the type and its generic representation, you can
always choose to work directly on the generic side if you'd like to write
programs that are polymorphic on the *shape* of types.

For our next trick, we will show the equivalence of a `keyword:data` constructor
which takes parameters, and a record of those same fields. Consider two
definitions of a `type:Ratio`:

```agda
  data Ratio⅋ : Set where
    mkRatio : (numerator : ℕ) → (denominator : ℕ) → Ratio⅋
```

and

```agda
  record Ratio : Set where
    constructor mkRatio
    field
      numerator    : ℕ
      denominator  : ℕ
```

Surely you will agree that these two types are equivalent. Therefore, we do not
need to consider the case of `keyword:data` constructors with parameters
separately from the problem of how can we give a generic representation for
records. As you might expect, all we need to do is combine each field by means
of `type:_×_`. And thus, the generic representation of `type:Ratio` is `type:ℕ
× ℕ`.

Exercise (Easy)

: Show the isomorphism between `type:Ratio` and `type:ℕ × ℕ`.


Solution

:       ```agda
  generic-ratio : prop-setoid Ratio ≅ prop-setoid (ℕ × ℕ)
  to        generic-ratio (mkRatio n d)  = n , d
  from      generic-ratio (n , d)        = mkRatio n d
  from∘to   generic-ratio (mkRatio n d)  = refl
  to∘from   generic-ratio (n , d)        = refl
  to-cong   generic-ratio ≡.refl         = refl
  from-cong generic-ratio ≡.refl         = refl
        ```

And there you have it! All non-dependent types you can define for yourself can
be decomposed into some combination of `type:⊤`, `type:⊥`, `type:_⊎_`, and
`type:_×_`. If your type was defined via `keyword:data`, use `type:_⊎_` to
differentiate between its constructors, and treat each constructor as if it were
a record. For records, conjoin each field with `type:_×_`.

You might be wondering why `type:⊥` is in this list, and it's because nothing
prevents you from defining a type with no constructors, in which case the only
isomorphism you can give is to `type:⊥`.


Exercise (Easy)

: Recall the definition of `type:List`:

:   ```agda
  data List⅋ (A : Set ℓ) : Set ℓ where
    []   : List⅋ A
    _∷_  : A → List⅋ A → List⅋ A
  -- FIX
    ```

:   Show an isomorphism between `bind:A:List A` and `bind:A:⊤ ⊎ (A × List A)`


Solution

:       ```agda
  generic-list  : {A : Set ℓ}
                → prop-setoid (List A)
                ≅ prop-setoid (⊤ ⊎ (A × List A))
  to         generic-list []        = inj₁  tt
  to         generic-list (x ∷ xs)  = inj₂  (x , xs)
  from       generic-list (inj₁  x)          = []
  from       generic-list (inj₂  (x , xs))   = x ∷ xs
  from∘to    generic-list []         = refl
  from∘to    generic-list (x ∷ xs)   = refl
  to∘from    generic-list (inj₁  x)  = refl
  to∘from    generic-list (inj₂  x)  = refl
  to-cong    generic-list ≡.refl     = refl
  from-cong  generic-list ≡.refl     = refl
        ```


As you can see from this example, the isomorphism between an algebraic data type
and its generic representation is completely automatic and entirely
uninteresting. Therefore, it's a great candidate for code generation, and we are
justified in our decision to not think much more about how exactly to get our
hands on these generic representations.

In the next section we will give `type:_Has_Elements` implementations for each
of the generic type constructors, through which we can automatically get the
same for any algebraic type we care about.


## The Algebra of Algebraic Data Types

The name "algebraic data types" is rather apt, in that there is indeed an
algebra over these types. It's not a particularly exciting algebra, in that all
it does is count the number of inhabitants of each type. But as we will see, not
only is the collection well named, so too is each of the types.

Let's first bash out the easy cases, namely that `type:⊥` has zero elements, and
that the unit type `type:⊤` has one. *Unit* type. *One* element. Get it?

```agda
  ⊥-fin : prop-setoid ⊥ Has 0 Elements
  to        ⊥-fin ()
  from      ⊥-fin ()
  from∘to   ⊥-fin ()
  to∘from   ⊥-fin ()
  to-cong   ⊥-fin ≡.refl = refl
  from-cong ⊥-fin ≡.refl = refl

  ⊤-fin : prop-setoid ⊤ Has 1 Elements
  to        ⊤-fin _     = zero
  from      ⊤-fin _     = tt
  from∘to   ⊤-fin _     = refl
  to∘from   ⊤-fin zero  = refl
  to-cong   ⊤-fin _     = refl
  from-cong ⊤-fin _     = refl
```

Showing the isomorphisms into `type:Fin` for `type:_×_` and `type:_⊎_` are a
little harder, but it's only because we'd like to make the definitions more
general than being over `def:prop-setoid`.

As a first step, we will show that products and coproducts preserve
isomorphisms. That is, we can map isomorphisms component-wise over products and
coproducts in the obvious way---just apply the transformation on one side, while
leaving the other as it was. Thus, given two isomorphisms, we can construct an
isomorphism between the product setoid given by `def:×-preserves-≅`:

```agda
  import Data.Product as ×
  open Setoid-Renaming

  ×-preserves-≅
    : s₁ ≅ s₂
    → s₃ ≅ s₄
    → ×-setoid s₁ s₃ ≅ ×-setoid s₂ s₄
  to    (×-preserves-≅ s t) = ×.map (to s)    (to t)
  from  (×-preserves-≅ s t) = ×.map (from s)  (from t)
  from∘to (×-preserves-≅ s t) (x , y) = from∘to s x , from∘to t y
  to∘from (×-preserves-≅ s t) (x , y) = to∘from s x , to∘from t y
  to-cong    (×-preserves-≅ s t) = ×.map (to-cong s)    (to-cong t)
  from-cong  (×-preserves-≅ s t) = ×.map (from-cong s)  (from-cong t)
```

In order to get back to the land of `def:prop-setoid`s, we can show a further
isomorphism, which is that a pair setoid of types is equivalent to a
propositional of pairs. That is to say, we *homomorphism* between `def:×-setoid`
and `def:prop-setoid`, as shown by `def:×-prop-homo`:

```agda
  ×-prop-homo
      :  {A : Set ℓ₁} {B : Set ℓ₂}
      →  ×-setoid (prop-setoid A) (prop-setoid B)
         ≅ prop-setoid (A × B)
  to         ×-prop-homo = id
  from       ×-prop-homo = id
  from∘to    ×-prop-homo _ = refl , refl
  to∘from    ×-prop-homo _ = refl
  to-cong    ×-prop-homo (≡.refl , ≡.refl) = refl
  from-cong  ×-prop-homo ≡.refl = refl , refl
```

Similarly, we can give the same treatment to `type:_⊎_`, as in
`def:⊎-preserves-≅`:

```agda
  import Data.Sum as ⊎
  open import Data.Sum using (_⊎_; inj₁; inj₂)

  ⊎-preserves-≅
      : s₁ ≅ s₂
      → s₃ ≅ s₄
      → ⊎-setoid s₁ s₃ ≅ ⊎-setoid s₂ s₄
  to         (⊎-preserves-≅ s t)           = ⊎.map (to s)    (to t)
  from       (⊎-preserves-≅ s t)           = ⊎.map (from s)  (from t)
  from∘to    (⊎-preserves-≅ s t) (inj₁ x)  = inj₁  (from∘to s x)
  from∘to    (⊎-preserves-≅ s t) (inj₂ y)  = inj₂  (from∘to t y)
  to∘from    (⊎-preserves-≅ s t) (inj₁ x)  = inj₁  (to∘from s x)
  to∘from    (⊎-preserves-≅ s t) (inj₂ y)  = inj₂  (to∘from t y)
  to-cong    (⊎-preserves-≅ s t) (inj₁ x)  = inj₁  (to-cong s x)
  to-cong    (⊎-preserves-≅ s t) (inj₂ x)  = inj₂  (to-cong t x)
  from-cong  (⊎-preserves-≅ s t) (inj₁ x)  = inj₁  (from-cong s x)
  from-cong  (⊎-preserves-≅ s t) (inj₂ x)  = inj₂  (from-cong t x)
```

and then again show a homomorphism between `def:⊎-setoid` and `def:prop-setoid`:

```agda
  ⊎-prop-homo
      :  {A : Set ℓ₁} {B : Set ℓ₂}
      →  ⊎-setoid (prop-setoid A) (prop-setoid B)
         ≅ prop-setoid (A ⊎ B)
  to        ⊎-prop-homo = id
  from      ⊎-prop-homo = id
  to∘from   ⊎-prop-homo _ = refl
  from∘to   ⊎-prop-homo (inj₁  x) = inj₁  refl
  from∘to   ⊎-prop-homo (inj₂  y) = inj₂  refl
  to-cong   ⊎-prop-homo (inj₁  ≡.refl)     = refl
  to-cong   ⊎-prop-homo (inj₂  ≡.refl)     = refl
  from-cong ⊎-prop-homo {inj₁  x} ≡.refl   = inj₁ refl
  from-cong ⊎-prop-homo {inj₂  y} ≡.refl   = inj₂ refl
```

Given two finite numbers, we can combine them in either of two every-day
familiar ways. The first, familiar to anyone who has ever counted on their
fingers, is to consider one `type:Fin` the continuation of the other. For
example, even though our hands only have five fingers a piece, we can still
count to ten by enumerating one to five on our left hand, and then six to ten on
our right. By generalizing our number of fingers, and interpreting which hand
as a sum type, we can show this "reinterpretation" of a sum of two `type:Fin`s
via `def:join`.

```agda
  open Data.Fin using (inject+; raise)

  module Join-SplitAt where
    join : Fin m ⊎ Fin n → Fin (m + n)
    join {n = n} (inj₁ x) = inject+ n x
    join {m = m} (inj₂ y) = raise m y
```

Of course, we can undo this transformation as well, via `def:splitAt`:

```agda
    splitAt : ∀ m → Fin (m + n) → Fin m ⊎ Fin n
    splitAt zero     x        = inj₂ x
    splitAt (suc m)  zero     = inj₁ zero
    splitAt (suc m)  (suc x)  = ⊎.map₁ suc (splitAt m x)
```

These two functions, `def:join` and `def:splitAt`, are in fact inverses of one
another, although we leave the proof as an exercise to the reader. If the reader
cannot be bothered and would like simply to move on, they can find the relevant
proofs under `module:Data.Fin.Properties` as `def:join-splitAt` and
`def:splitAt-join`.

The "there and back again" nature of `def:join` and `def:splitAt` should remind
you of an isomorphism, and indeed, there is such an isomorphism given by
`def:join-splitAt-iso`:

```agda
  open Data.Fin using (splitAt; join)

  join-splitAt : (m n : ℕ) → (i : Fin (m + n)) → join m n (splitAt m i) ≡ i
  join-splitAt = exercise-for-the-reader

  splitAt-join : (m n : ℕ) → (i : Fin m ⊎ Fin n) → splitAt m (join m n i) ≡ i
  splitAt-join = exercise-for-the-reader

  join-splitAt-iso
      : prop-setoid (Fin (m + n))
      ≅ prop-setoid (Fin m ⊎ Fin n)
  to         join-splitAt-iso = splitAt _
  from       join-splitAt-iso = join _ _
  from∘to    (join-splitAt-iso {m = m})  = join-splitAt m _
  to∘from    join-splitAt-iso x          = splitAt-join _ _ x
  to-cong    join-splitAt-iso ≡.refl = refl
  from-cong  join-splitAt-iso ≡.refl = refl
```

Where there is a mathematical object for coproducts, there is usually one
lurking just around the corner describing an analogous idea for products. Here
is no exception; we do indeed have an analogous construction for products, and
one no less familiar. Recall that in our everyday arabic numerals, we have
exactly ten unique digits, ranging from 0 to 9. These ten possibilities are
easily modeled by an application of `type:Fin`, and allow us to denote ten
different values.

But observe what happens when we put two of these digits beside one another---we
are now able to range between the numbers 00 and 99, of which there are one
hundred. You of course, will not be surprised by this fact, but it's interesting
to see the theoretical underpinning as to why our positional numbering system
works. We can show this reinpretation via `def:combine`:

```agda
  module Combine-RemQuot where
    combine : Fin m → Fin n → Fin (m * n)
    combine          zero     y = inject+ _ y
    combine {n = n}  (suc x)  y = raise n (combine x y)
```

and its inverse via the awkwardly named `def:remQuot` (short for
"remainder/quotient")

```agda
    remQuot : (n : ℕ) → Fin (m * n) → Fin m × Fin n
    remQuot {m = suc m} n x with splitAt n x
    ... | inj₁ l = zero , l
    ... | inj₂ r = ×.map₁ suc (remQuot {m} n r)
```

Again, showing that these are in fact inverses of one another is left as an
exercise as the reader. Again again, the necessary proofs can be found in
`module:Data.Fin.Properties` under the obvious names should the reader be
disinterested in improving their proof skills. Armed with everything, we can
indeed show an isomorphism between a product of `def:Fin`s and a `def:Fin` of
products, as in `def:combine-remQuot-iso`:

```agda
  open import Data.Fin using (combine; remQuot)

  combine-remQuot
    : {n : ℕ}
    → (k : ℕ)
    → (i : Fin (n * k))
    → uncurry combine (remQuot {n} k i) ≡ i
  combine-remQuot = exercise-for-the-reader

  remQuot-combine
    : {n k : ℕ}
    → (x : Fin n)
    → (y : Fin k)
    → remQuot k (combine x y) ≡ (x , y)
  remQuot-combine = exercise-for-the-reader

  combine-remQuot-iso
      : prop-setoid (Fin (m * n))
      ≅ (prop-setoid (Fin m × Fin n))
  to         combine-remQuot-iso = remQuot _
  from       combine-remQuot-iso (fst , snd)  = combine fst snd
  from∘to    (combine-remQuot-iso {m = m}) x  = combine-remQuot {m} _ x
  to∘from    combine-remQuot-iso (x , y)  = remQuot-combine x y
  to-cong    combine-remQuot-iso ≡.refl   = refl
  from-cong  combine-remQuot-iso ≡.refl   = refl
```

At long last, we are now ready to show that coproducts add the cardinalities of
their injections. The trick is to map both finite isomorphisms across the
`type:_⊎_`, and then invoke `def:join-splitAt-iso`, as in the following:

```agda
  ⊎-fin : s₁ Has m Elements → s₂ Has n Elements
        → ⊎-setoid s₁ s₂ Has m + n Elements
  ⊎-fin fin₁ fin₂
    = ≅-trans  (⊎-preserves-≅ fin₁ fin₂)
    ( ≅-trans  ⊎-prop-homo
               (≅-sym join-splitAt-iso))
```

We can do a similar trick to show that `type:_×_` multiplies the cardinalities
of its projections, albeit invoking `def:×-preserves-≅` and
`def:combine-remQuot-iso` instead:

```agda
  ×-fin : s₁ Has m Elements → s₂ Has n Elements
        → ×-setoid s₁ s₂ Has m * n Elements
  ×-fin fin₁ fin₂
    = ≅-trans  (×-preserves-≅ fin₁ fin₂)
    ( ≅-trans  ×-prop-homo
               (≅-sym combine-remQuot-iso))
```


## Monoids On Sets

```agda
  open Monoid
  ips-setoid : Setoid _ _
  Carrier ips-setoid = Set
  _≈_ ips-setoid x y = prop-setoid x ≅ prop-setoid y
  refl′ (pre (equiv ips-setoid)) = ≅-refl
  trans′ (pre (equiv ips-setoid)) = ≅-trans
  sym′ (equiv ips-setoid) = ≅-sym

  ×-⊤-monoid : Monoid _ _
  setoid ×-⊤-monoid = ips-setoid
  _∙_ ×-⊤-monoid = _×_
  ε ×-⊤-monoid = ⊤
  assoc ×-⊤-monoid x y z = ≅-prop ×.assocʳ′ ×.assocˡ′ refl refl
  identityˡ ×-⊤-monoid x = ≅-prop ×.proj₂ (tt ,_) refl refl
  identityʳ ×-⊤-monoid x = ≅-prop ×.proj₁ (_, tt) refl refl
  ∙-cong ×-⊤-monoid h k = ≅-trans (≅-sym ×-prop-homo) (≅-trans (×-preserves-≅ h k) ×-prop-homo)

  ⊎-⊥-monoid : Monoid _ _
  setoid ⊎-⊥-monoid = ips-setoid
  _∙_ ⊎-⊥-monoid = _⊎_
  ε ⊎-⊥-monoid = ⊥
  assoc ⊎-⊥-monoid x y z = ≅-prop ⊎.assocʳ ⊎.assocˡ (λ { (inj₁ x) → refl
                                                       ; (inj₂ (inj₁ x)) → refl
                                                       ; (inj₂ (inj₂ y)) → refl })
                                                    λ { (inj₁ (inj₁ x)) → refl
                                                      ; (inj₁ (inj₂ y)) → refl
                                                      ; (inj₂ y) → refl }
  identityˡ ⊎-⊥-monoid x = ≅-prop (λ { (inj₂ y) → y }) inj₂ (λ { x₁ → refl }) λ { (inj₂ y) → refl }
  identityʳ ⊎-⊥-monoid x = ≅-prop (λ { (inj₁ y) → y }) inj₁ (λ { x₁ → refl }) λ { (inj₁ y) → refl }
  ∙-cong ⊎-⊥-monoid {x = x} {y} {z} {w} h k = ≅-trans (≅-sym ⊎-prop-homo) (≅-trans (⊎-preserves-≅ h k) ⊎-prop-homo)
```


## Functions as Exponents {#sec:exponents}

In a non-dependent world, we have three interesting type formers---products,
coproducts, and functions. Having looked already at the first two, we now turn
our attention to the cardinalities of functions.

First, we note that there exists a more interesting setoid over functions than
the `def:≗-setoid` that we have been considering thus far. We need a setoid over
functions which preserves all equalities in the domain into the codomain. This
is a property we have seen already a thousand times, it's known as congruence.
Thus, we need a setoid over congruent functions. Given such a thing, it's easy
(though rather verbose) to show that it preserves isomorphisms:

```agda
open Setoid
  hiding (refl; sym; trans; Carrier; _≈_)

→-preserves-≅
    : s₁ ≅ s₂ → s₃ ≅ s₄
    → (s₁ ⇒ s₃) ≅ (s₂ ⇒ s₄)
Fn.func  (to (→-preserves-≅ s t) f) = to t       ∘ Fn.func f ∘ from s
Fn.cong  (to (→-preserves-≅ s t) f) = to-cong t  ∘ Fn.cong f ∘ from-cong s
Fn.func  (from (→-preserves-≅ s t) f) = from t ∘ Fn.func f ∘ to s
Fn.cong  (from (→-preserves-≅ s t) f) = from-cong t ∘ Fn.cong f ∘ to-cong s
from∘to (→-preserves-≅ s t) f {x} {y} a = begin
  from t (to t (Fn.func f (from s (to s x))))  ≈⟨ from∘to t _ ⟩
  Fn.func f (from s (to s x))                  ≈⟨ Fn.cong f (from∘to s x) ⟩
  Fn.func f x                                  ≈⟨ Fn.cong f a ⟩
  Fn.func f y                                  ∎
  where open A-Reasoning t
to∘from (→-preserves-≅ s t) f {x} {y} a = begin
  to t (from t (Fn.func f (to s (from s x))))  ≈⟨ to∘from t _ ⟩
  Fn.func f (to s (from s x))                  ≈⟨ Fn.cong f (to∘from s x) ⟩
  Fn.func f x                                  ≈⟨ Fn.cong f a ⟩
  Fn.func f y                                  ∎
  where open B-Reasoning t
to-cong (→-preserves-≅ {s₁ = s₁} s t) {g} {h} f {x} {y} a = begin
  to t (Fn.func g (from s x)) ≈⟨ to-cong t (Fn.cong g (from-cong s a)) ⟩
  to t (Fn.func g (from s y)) ≈⟨ to-cong t (f (refl ⦃ isEquivalence s₁ ⦄)) ⟩
  to t (Fn.func h (from s y)) ∎
  where open B-Reasoning t hiding (refl)
from-cong (→-preserves-≅ {s₂ = s₂} s t) {g} {h} f {x} {y} a = begin
  from t (Fn.func g (to s x)) ≈⟨ from-cong t (Fn.cong g (to-cong s a)) ⟩
  from t (Fn.func g (to s y)) ≈⟨ from-cong t (f (refl ⦃ isEquivalence s₂ ⦄)) ⟩
  from t (Fn.func h (to s y)) ∎
  where open A-Reasoning t hiding (refl)
```

Now, given a setoid over elements, we can construct a setoid over vectors where
the elements are considered pointwise. That is, two vectors are equal only when
each of their elements are equal. Under such a setoid, it's easy to see that if
the vector has length $n$ and the element-wise setoid has cardinality $k$, the
cardinality of the possible vectors is $k^n$. Why is this? Because each of the
$n$ elements can be one of $k$ distinct possibilities. Combinatorially
therefore, we have the following:

$$
\underbrace{k \times k \times \cdots \times k}_{\text{$n$ times}} = k^n
$$

We can prove this in three parts; first by showing that a vector of length zero
has cardinality one:

```agda
module _ (s : Setoid c₁ ℓ₁) where
  open Setoid s

  data Vec-Pointwise
      : (n : ℕ) → Rel (Vec Carrier n) ℓ₁ where
    []   :  Vec-Pointwise zero [] []
    _∷_  :  {n : ℕ} {x y : Carrier}
            {xs ys : Vec (Carrier) n}
          →  x ≈ y
          →  Vec-Pointwise n xs ys
          →  Vec-Pointwise (suc n) (x ∷ xs) (y ∷ ys)

  open Setoid-Renaming
    hiding (Carrier)

  vec-equiv : IsEquivalence (Vec-Pointwise n)
  refl′ (pre vec-equiv) {[]} = []
  refl′ (pre vec-equiv) {x ∷ xs} = refl s ∷ refl vec-equiv
  trans′ (pre vec-equiv) [] [] = []
  trans′ (pre vec-equiv) (xy ∷ xys) (yz ∷ yzs)
    = trans s xy yz ∷ trans vec-equiv xys yzs
  sym′ vec-equiv [] = []
  sym′ vec-equiv (x ∷ xs) = sym s x ∷ sym vec-equiv xs

  vec-setoid : ℕ → Setoid _ _
  Carrier (vec-setoid n) = Vec Carrier n
  _≈_ (vec-setoid n) = Vec-Pointwise n
  isEquivalence (vec-setoid n) = vec-equiv

instance
  vec-setoid-inst
    : {c ℓ : Level} {n : ℕ}
    → ⦃ s : Setoid c ℓ ⦄
    → Setoid c ℓ
  vec-setoid-inst {n = n} ⦃ s ⦄ = vec-setoid s n

  vec-equiv-inst
    : {c ℓ : Level} {n : ℕ}
    → ⦃ s : Setoid c ℓ ⦄
    → IsEquivalence (Vec-Pointwise s n)
  vec-equiv-inst ⦃ s ⦄ = vec-equiv s

vec-prop-homo
  : {A : Set ℓ}
  → prop-setoid (Vec A n) ≅ vec-setoid (prop-setoid A) n
to vec-prop-homo v = v
from vec-prop-homo v = v
from∘to vec-prop-homo x = ≡.refl
to∘from vec-prop-homo [] = []
to∘from vec-prop-homo (_ ∷ _) = refl ∷ refl
to-cong vec-prop-homo ≡.refl = refl
from-cong (vec-prop-homo) [] = ≡.refl
from-cong vec-prop-homo (≡.refl ∷ as)
  rewrite from-cong vec-prop-homo as
    = refl


open Sandbox-Finite

module _ {s₁ : Setoid c₁ ℓ₁} where
  private instance
    _ = s₁
    _ = s₁ .isPreorder
    _ = s₁ .isEquivalence

  vec-fin₀ : vec-setoid s₁ 0 Has 1 Elements
  to         vec-fin₀ []      = zero
  from       vec-fin₀ zero    = []
  from∘to    vec-fin₀ []      = []
  to∘from    vec-fin₀ zero    = refl
  to-cong    vec-fin₀ []      = refl
  from-cong  vec-fin₀ ≡.refl  = refl
```

Then, by showing a lemma that is there an isomorphism between `type:Vec A (suc
n)` and `type:A × Vec A n`:

```agda
  vec-rep : vec-setoid s₁ (suc n) ≅ ×-setoid s₁ (vec-setoid s₁ n)
  to vec-rep    (x ∷  xs) = x ,  xs
  from vec-rep  (x ,  xs) = x ∷  xs
  from∘to       (vec-rep) (x ∷  xs) = refl ∷  refl
  to∘from       (vec-rep) (x ,  xs) = refl ,  refl
  to-cong       (vec-rep) (x ∷  xs) = x ,  xs
  from-cong     (vec-rep) (x ,  xs) = x ∷  xs
```

We can combine these two facts into the desired proof that vectors have an
exponential cardinality:

```agda
  vec-fin
    : s₁ Has m Elements
    → vec-setoid s₁ n Has (m ^ n) Elements
  vec-fin {n = zero}   s = vec-fin₀
  vec-fin {n = suc n}  s
    = ≅-trans  vec-rep
    ( ≅-trans  (×-preserves-≅ s (vec-fin s))
    ( ≅-trans  ×-prop-homo
               (≅-sym combine-remQuot-iso)))
```

And now, to tie everything together, we can show that functions themselves also
have an exponential cardinality. This is a straightforward application of
`def:→-preserves-≅`, `def:vec-iso` and `vec-fin`. In essence, we transform our
function `A → B` into a function `Fin m → Fin n`, and then use the
characteristic function of vectors to reinterpret that function as a vector of
length `m`. Finally, we know the cardinality of such a vector, as shown just now
by `def:vec-fin`.

```agda
→-fin : s₁ Has m Elements → s₂ Has n Elements
      → (s₁ ⇒ s₂) Has (n ^ m) Elements
→-fin s t
  = ≅-trans (→-preserves-≅ s t)
  ( ≅-trans (≅-sym vec-iso)
   (≅-trans vec-prop-homo
            (vec-fin ≅-refl)))
```


## Wrapping Up

```agda
open import Data.Vec
  using (Vec; []; _∷_; lookup)
  public

-- TODO(sandy): write about me!
open import Data.Sum
  using (_⊎_; inj₁; inj₂)
  public

open import Data.Fin
  using (Fin; zero; suc; toℕ)
  public

open Sandbox-Finite public
```

