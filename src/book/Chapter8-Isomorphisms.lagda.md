# Isomorphisms

Hidden

:   ```agda
{-# OPTIONS --allow-unsolved-metas #-}
    ```

```agda
module Chapter8-Isomorphisms where
```

Prerequisites

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
open import Chapter7-Structures
  hiding (length)
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
private variable
  ℓ : Level

module Definition-Vectors where
  data Vec (A : Set ℓ) : ℕ → Set ℓ where
    []   : Vec A 0
    _∷_  : A → Vec A n → Vec A (suc n)
  infixr 5 _∷_
```

As usual, rather than defining this type ourselves, we will use the equivalent
definition from the standard library:

```agda
open import Data.Vec
  using (Vec; []; _∷_)

module Example-Vectors where
```

Now, given a vector, we can easily extract its length, simply by taking the
index and returning it:

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
  _ : lookup (6 ∷ 3 ∷ 5 ∷ []) (suc zero) ≡ 3
  _ = refl
```

As a quick note, `def:lookup` is known in more traditional, ALGOL-like
languages, as `def:_[_]`:

```agda
  _[_] : Vec A n → Fin n → A
  _[_] = lookup

  _ : (6 ∷ 3 ∷ 5 ∷ []) [ suc (suc zero) ] ≡ 5
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
  fromVec′∘toVec′ : (v : Vec A n) → fromVec′ (toVec′ v) ≡ v
  fromVec′∘toVec′ [] = refl
  fromVec′∘toVec′ (x ∷ v)
    rewrite fromVec′∘toVec′ v = refl
```

The other direction is slightly harder, since we do not have propositional
equality for function types. Instead, we can show the extensional equality of
the two `type:Vec′`s---that they store the same value at every possible index:

```agda
  toVec′∘fromVec′
      : (v : Vec′ A n) → (ix : Fin n)
      → toVec′ (fromVec′ v) ix ≡ v ix
  toVec′∘fromVec′ v zero      = refl
  toVec′∘fromVec′ v (suc ix)  = toVec′∘fromVec′ (v ∘ suc) (ix)
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
private variable
  c₁ c₂ c₃ c₄ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

record Iso
      (s₁ : Setoid c₁ ℓ₁)
      (s₂ : Setoid c₂ ℓ₂)
      : Set (c₁ ⊔ c₂ ⊔ ℓ₁ ⊔ ℓ₂) where
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
    from∘to  : (x : A) → from (to x) ≈₁ x
    to∘from  : (x : B) → to (from x) ≈₂ x
    to-cong    : {x y : A} → x ≈₁ y → to x ≈₂ to y
    from-cong  : {x y : B} → x ≈₂ y → from x ≈₁ from y
```

One last thing that we'll pack inside the definition of `type:Iso` are
facilities for using setoid reasoning over both `s₁` and `s₂`, which we will
name `module:A-Reasoning` and `module:B-Reasoning`---corresponding to the types
`A` and `B` for the respective carriers.

```agda
  module A-Reasoning where
    open Preorder-Reasoning (IsEquivalence.isPreorder (Setoid.isEquivalence s₁))
      public
  module B-Reasoning where
    open Preorder-Reasoning (IsEquivalence.isPreorder (Setoid.isEquivalence s₂))
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

open Iso

module _ where
  open Example-Vectors

  open import Function using (_∘_)
```

we are now ready to show `def:vec-iso`, which states there is an isomorphism
between the `type:vec-setoid` over `type:Vec` and the function setoid `type:_⇨_`
over `type:Vec′`. This proof is mostly trivial, since we've already done the
heavy lifting. However, showing `field:from-cong` takes some effort (and a
lemma, defined immediately after in a `keyword:where` block) since it doesn't
automatically fall out from computation.

-- TODO(sandy): setoids chapter should discuss vec-setoid and the pointwise
-- helpers


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
    setoid→preorder : {c ℓ : Level} → ⦃ s : Setoid c ℓ ⦄ → IsPreorder (s .Setoid._≈_)
    setoid→preorder ⦃ s ⦄ = IsEquivalence.isPreorder (Setoid.isEquivalence s)

    vec-setoid-inst : {c ℓ : Level} → {n : ℕ} → ⦃ s : Setoid c ℓ ⦄ → Setoid c ℓ
    vec-setoid-inst {n = n} ⦃ s ⦄ = vec-setoid s n

    prop-setoid-inst : {c : Level} {A : Set c} → Setoid c c
    prop-setoid-inst {A = A} = prop-setoid A

  open Setoid-Renaming
    hiding (Carrier)


  pointwise→≡ : ∀ {ℓ} {A : Set ℓ} {xs ys} → Vec-Pointwise (prop-setoid A) n xs ys → xs ≡ ys
  pointwise→≡ [] = refl
  pointwise→≡ (≡.refl ∷ xs)
    rewrite pointwise→≡ xs = refl

  -- TODO(sandy): true of any setoid
  ≡→pointwise : ∀ {ℓ} {A : Set ℓ} {xs ys} → xs ≡ ys → Vec-Pointwise (prop-setoid A) n xs ys
  ≡→pointwise x rewrite x = refl′ (pre (vec-equiv (prop-setoid _)))


  vec-iso
      : {A : Set c₁}
      → vec-setoid (prop-setoid A) n
      ↔ (prop-setoid (Fin n) ⇒ prop-setoid A)
  Fn.func (to vec-iso x) = lookup x
  Fn.cong (to vec-iso x) = ≡.cong (lookup x)
  from vec-iso = fromVec′ ∘ Fn.func
  from∘to (vec-iso {A = A}) x
    rewrite fromVec′∘toVec′ x = refl′ (pre (vec-equiv (prop-setoid A)))
  to∘from vec-iso x {n} ≡.refl = toVec′∘fromVec′ (Fn.func x) n
  to-cong vec-iso x ≡.refl rewrite pointwise→≡ x = refl
  from-cong (vec-iso {n = zero}) {x} {y} f = refl′ (pre (vec-equiv (prop-setoid _)))
  from-cong (vec-iso {n = suc n}) {x} {y} f
    = f refl
    ∷ from-cong (vec-iso {n = n})
        { fn (Fn.func x ∘ suc) (Fn.cong x ∘ ≡.cong suc) }
        { fn (Fn.func y ∘ suc) (Fn.cong y ∘ ≡.cong suc) }
        (f ∘ ≡.cong suc)
```

In order to show the `def:lemma`, we must prove that every element in
`def:fromVec′` of `x` is equal to every element of the same on `y`. This is done
via induction on `n`, and proceeds methodically:

With our first taste of isomorphism, we are now ready to investigate them more
thoroughly and learn about their properties.


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

↔-refl : s₁ ↔ s₁
↔-refl {s₁ = s} =
  iso id id (λ x → Setoid.refl s) (λ x → Setoid.refl s) id id
```

Showing symmetry requires us only to change which function we're calling
`field:to` and which we're calling `field:from`:

```agda
↔-sym : s₁ ↔ s₂ → s₂ ↔ s₁
↔-sym (iso to from from∘to to∘from to-cong from-cong)
  = iso from to to∘from from∘to from-cong to-cong
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
  from∘to (↔-trans f g) x = begin
    from f (from g (to g (to f x)))  ≈⟨ from-cong f (from∘to g _) ⟩
    from f (to f x)                  ≈⟨ from∘to f x ⟩
    x                                ∎
    where open A-Reasoning f
  to∘from (↔-trans f g) x = begin
    to g (to f (from f (from g x)))  ≈⟨ to-cong g (to∘from f _) ⟩
    to g (from g x)                  ≈⟨ to∘from g x ⟩
    x                                ∎
    where open B-Reasoning g
  to-cong    (↔-trans f g) x≈y = to-cong    g (to-cong    f x≈y)
  from-cong  (↔-trans f g) x≈y = from-cong  f (from-cong  g x≈y)
```

These three proofs together show that `type:_↔_` is indeed an equivalence
relation, although we must restrict the levels on both sides to be the same in
order for the standard machinery to agree with this fact:

```agda
↔-equiv : IsEquivalence (_↔_ {c₁ = c₁} {ℓ₁ = ℓ₁})
IsPreorder.refl   (IsEquivalence.isPreorder ↔-equiv) = ↔-refl
IsPreorder.trans  (IsEquivalence.isPreorder ↔-equiv) = ↔-trans
IsEquivalence.sym ↔-equiv = ↔-sym
```


## Finite Types

One of the most immediate things we can do with isomorphisms is to enumerate the
number of inhabitants of types. Types for which this is possible are known as
*finite* types, because they have a finite number of inhabitants.

We can show a type is finite by giving an isomorphism into `type:Fin`. The index
on `type:Fin` is called the *cardinality* of the type, and we will give a mixfix
definition for finite types by way of `type:_Has_Elements`:

```agda
open import Data.Fin using (Fin; zero; suc)

module Sandbox-Finite where
  _Has_Elements : Setoid c₁ ℓ₁ → ℕ → Set (c₁ ⊔ ℓ₁)
  s Has cardinality Elements = s ↔ prop-setoid (Fin cardinality)
```

As a simple (although admittedly tedious) example of `type:_Has_Elements`, we
can show that `type:Bool` has two inhabitants:

```agda
  open import Data.Bool using (Bool; true; false)
  open Iso


  bool-fin : prop-setoid Bool Has 2 Elements
  to         bool-fin false       = zero
  to         bool-fin true        = suc zero
  from       bool-fin zero        = false
  from       bool-fin (suc zero)  = true
  from∘to    bool-fin false       = refl
  from∘to    bool-fin true        = refl
  to∘from    bool-fin zero        = refl
  to∘from    bool-fin (suc zero)  = refl
  to-cong    bool-fin ≡.refl        = refl
  from-cong  bool-fin ≡.refl        = refl
```

While we don't need an isomorphism to convince ourselves that `type:Bool` does
indeed have two elements, the machinery is in fact useful. One immediate
corollary of `type:_Has_Elements` is any two types with the same cardinality
must necessarily be isomorphic to one another:

```agda
  fin-iso : s₁ Has n Elements → s₂ Has n Elements → s₁ ↔ s₂
  fin-iso i₁ i₂ = ↔-trans i₁ (↔-sym i₂)
```

In fact, it is exactly this treatment as finite types that gives product and
sum types their respective names. Product types have cardinality equal
to the product of the cardinalities of their projection types, while sum types
*add* their constituent cardinalities. Proving these facts requires a few
lemmas, which are interesting in their own right, and thus we will dawdle on our
way to the main result.


First, we will show that products and coproducts preserve isomorphisms. That is,
we can map isomorphisms component-wise over products and coproducts in the
obvious way---just apply the transformation on one side, while leaving the other
as it was. Thus, given two isomorphisms, we can construct an isomorphism between
the product setoid given by `def:×-preserves-↔`:

```agda
  open import Data.Product using (_×_; _,_; proj₁; proj₂)
  import Data.Product as ×
  open Setoid-Renaming

--   record -×- (s₁ : Setoid c₁ ℓ₁) (s₂ : Setoid c₂ ℓ₂) : Set where
--     field
--       ≈-proj₁ :
  ×-setoid : Setoid c₁ ℓ₁ → Setoid c₂ ℓ₂ → Setoid _ _
  Carrier (×-setoid s₁ s₂) = s₁ .Carrier × s₂ .Carrier
  _≈_ (×-setoid s₁ s₂) (a₁ , b₁) (a₂ , b₂)
    = s₁ ._≈_ a₁ a₂
    × s₂ ._≈_ b₁ b₂
  refl′ (pre (equiv (×-setoid s₁ s₂)))
    = Setoid.refl s₁ , Setoid.refl s₂
  trans′ (pre (equiv (×-setoid s₁ s₂))) (a₁₂ , b₁₂) (a₂₃ , b₂₃)
    = Setoid.trans s₁ a₁₂ a₂₃ , Setoid.trans s₂ b₁₂ b₂₃
  sym′ (equiv (×-setoid s₁ s₂)) (a , b)
    = Setoid.sym s₁ a , Setoid.sym s₂ b

  ×-preserves-↔ : s₁ ↔ s₂ → s₃ ↔ s₄ → ×-setoid s₁ s₃ ↔ ×-setoid s₂ s₄
  to    (×-preserves-↔ s t) = ×.map (to s) (to t)
  from  (×-preserves-↔ s t) = ×.map (from s) (from t)
  from∘to (×-preserves-↔ s t) (x , y) =
    from∘to s x , from∘to t y
  to∘from (×-preserves-↔ s t) (x , y) =
    to∘from s x , to∘from t y
  to-cong    (×-preserves-↔ s t) = ×.map (to-cong s) (to-cong t)
  from-cong  (×-preserves-↔ s t) = ×.map (from-cong s) (from-cong t)
```

Similarly, we can give the same treatment to `type:_⊎_`, as in
`def:⊎-preserves-↔`:

```agda
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  import Data.Sum as +

  data ⊎-Pointwise (s₁ : Setoid c₁ ℓ₁) (s₂ : Setoid c₂ ℓ₂)
      : Rel (s₁ .Carrier ⊎ s₂ .Carrier) (ℓ₁ ⊔ ℓ₂) where
    inj₁  : {x y : s₁ .Carrier}
          → _≈_ s₁ x y → ⊎-Pointwise s₁ s₂ (inj₁ x) (inj₁ y)
    inj₂  : {x y : s₂ .Carrier}
          → _≈_ s₂ x y → ⊎-Pointwise s₁ s₂ (inj₂ x) (inj₂ y)

  ⊎-equiv : IsEquivalence (⊎-Pointwise s₁ s₂)
  refl′ (pre (⊎-equiv {s₁ = s₁})) {inj₁ x} = inj₁ (Setoid.refl s₁)
  refl′ (pre (⊎-equiv {s₂ = s₂})) {inj₂ y} = inj₂ (Setoid.refl s₂)
  trans′ (pre (⊎-equiv {s₁ = s₁})) (inj₁ x=y) (inj₁ y=z)
    = inj₁ (trans′ (pre (equiv s₁)) x=y y=z)
  trans′ (pre (⊎-equiv {s₂ = s₂})) (inj₂ x=y) (inj₂ y=z)
    = inj₂ (trans′ (pre (equiv s₂)) x=y y=z)
  sym′ (⊎-equiv {s₁ = s₁}) (inj₁ x) = inj₁ (sym′ (equiv s₁) x)
  sym′ (⊎-equiv {s₂ = s₂}) (inj₂ x) = inj₂ (sym′ (equiv s₂) x)

  ⊎-setoid : Setoid c₁ ℓ₁ → Setoid c₂ ℓ₂ → Setoid _ _
  Carrier (⊎-setoid s₁ s₂) = s₁ .Carrier ⊎ s₂ .Carrier
  _≈_ (⊎-setoid s₁ s₂) = ⊎-Pointwise s₁ s₂
  equiv (⊎-setoid s₁ s₂) = ⊎-equiv

  ⊎-preserves-↔ : s₁ ↔ s₂ → s₃ ↔ s₄ → ⊎-setoid s₁ s₃ ↔ ⊎-setoid s₂ s₄
  to         (⊎-preserves-↔ s t)           = +.map (to s) (to t)
  from       (⊎-preserves-↔ s t)           = +.map (from s) (from t)
  from∘to    (⊎-preserves-↔ s t) (inj₁ x)  = inj₁ (from∘to s x)
  from∘to    (⊎-preserves-↔ s t) (inj₂ y)  = inj₂ (from∘to t y)
  to∘from    (⊎-preserves-↔ s t) (inj₁ x)  = inj₁ (to∘from s x)
  to∘from    (⊎-preserves-↔ s t) (inj₂ y)  = inj₂ (to∘from t y)
  to-cong    (⊎-preserves-↔ s t) (inj₁ x)  = inj₁ (to-cong s x)
  to-cong    (⊎-preserves-↔ s t) (inj₂ x)  = inj₂ (to-cong t x)
  from-cong  (⊎-preserves-↔ s t) (inj₁ x)  = inj₁ (from-cong s x)
  from-cong  (⊎-preserves-↔ s t) (inj₂ x)  = inj₂ (from-cong t x)
```

Given two finite numbers, we can combine them in either of two every-day
familiar ways. The first, familiar to anyone who has ever counted on their
fingers, is to consider one `type:Fin` the continuation of the other. For
example, even though our hands only have five fingers a piece, we can still
count to ten by enumerating one to five on our left hand, and then six to ten on
our right. By generalizing our number of fingers, and interpretting which hand
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
    splitAt (suc m)  (suc x)  = +.map₁ suc (splitAt m x)
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
  open import Data.Fin.Properties

  join-splitAt-iso
      : prop-setoid (Fin (m + n))
      ↔ ⊎-setoid (prop-setoid (Fin m)) (prop-setoid (Fin n))
  to         join-splitAt-iso = splitAt _
  from       join-splitAt-iso = join _ _
  from∘to    (join-splitAt-iso {m = m}) = join-splitAt m _
  to∘from    join-splitAt-iso x = {! !} -- ≡⇒Pointwise-≡ (splitAt-join _ _ x)
  to-cong    join-splitAt-iso ≡.refl        = refl′ (pre (equiv (⊎-setoid (prop-setoid (Fin _)) (prop-setoid (Fin _)))))
  from-cong  join-splitAt-iso (inj₁ ≡.refl) = ≡.refl
  from-cong  join-splitAt-iso (inj₂ ≡.refl) = ≡.refl
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

and its inverse via the awkwardly named `def:remQuot (short for
"remainder/quotient")

```agda
    open import Data.Nat.Properties

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

  combine-remQuot-iso
      : prop-setoid (Fin (m * n))
      ↔ ×-setoid (prop-setoid (Fin m)) (prop-setoid (Fin n))
  to       combine-remQuot-iso              = remQuot _
  from     combine-remQuot-iso (fst , snd)  = combine fst snd
  from∘to  (combine-remQuot-iso {m = m}) x  = combine-remQuot {m} _ x
  to∘from  combine-remQuot-iso (x , y) with remQuot-combine x y
  ... | p = ≡.cong proj₁ p , ≡.cong proj₂ p
  to-cong    combine-remQuot-iso ≡.refl           = ≡.refl , ≡.refl
  from-cong  combine-remQuot-iso (≡.refl , ≡.refl)  = ≡.refl
```

At long last, we are now ready to show that coproducts add the cardinalities of
their injections. The trick is to map both finite isomorphisms across the
`type:_⊎_`, and then invoke `def:join-splitAt-iso`, as in the following:

```agda
  ⊎-fin : s₁ Has m Elements → s₂ Has n Elements
        → ⊎-setoid s₁ s₂ Has m + n Elements
  ⊎-fin fin₁ fin₂
    = ↔-trans (⊎-preserves-↔ fin₁ fin₂) (↔-sym join-splitAt-iso)
```

We can do a similar trick to show that `type:_×_` multiplies the cardinalities
of its projections, albeit invoking `def:×-preserves-↔` and
`def:combine-remQuot-iso` instead:

```agda
  ×-fin : s₁ Has m Elements → s₂ Has n Elements
        → ×-setoid s₁ s₂ Has m * n Elements
  ×-fin fin₁ fin₂
    = ↔-trans (×-preserves-↔ fin₁ fin₂) (↔-sym combine-remQuot-iso)
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
open Setoid-Renaming
  hiding (Carrier)

open import Data.Product using (_,_)

open import Function.Equality
  using (_⇨_)
  renaming (_⟨$⟩_ to func; cong to fcong)

→-preserves-↔
    : s₁ ↔ s₂ → s₃ ↔ s₄
    → (s₁ ⇒ s₃) ↔ (s₂ ⇒ s₄)
Fn.func   (to (→-preserves-↔ s t) f) = to t ∘ Fn.func f ∘ from s
Fn.cong  (to (→-preserves-↔ s t) f) = to-cong t ∘ Fn.cong f ∘ from-cong s
Fn.func   (from (→-preserves-↔ s t) f) = from t ∘ Fn.func f ∘ to s
Fn.cong  (from (→-preserves-↔ s t) f) = from-cong t ∘ Fn.cong f ∘ to-cong s
from∘to (→-preserves-↔ s t) f {x} {y} a = begin
  from t (to t (Fn.func f (from s (to s x))))  ≈⟨ from∘to t _ ⟩
  Fn.func f (from s (to s x))                  ≈⟨ Fn.cong f (from∘to s x) ⟩
  Fn.func f x                                  ≈⟨ Fn.cong f a ⟩
  Fn.func f y                                  ∎
  where open A-Reasoning t
to∘from (→-preserves-↔ s t) f {x} {y} a = begin
  to t (from t (Fn.func f (to s (from s x))))  ≈⟨ to∘from t _ ⟩
  Fn.func f (to s (from s x))                  ≈⟨ Fn.cong f (to∘from s x) ⟩
  Fn.func f x                                  ≈⟨ Fn.cong f a ⟩
  Fn.func f y                                  ∎
  where open B-Reasoning t
to-cong (→-preserves-↔ {s₁ = s₁} s t) {g} {h} f {x} {y} a = begin
  to t (Fn.func g (from s x)) ≈⟨ to-cong t (Fn.cong g (from-cong s a)) ⟩
  to t (Fn.func g (from s y)) ≈⟨ to-cong t (f (refl′ (pre (equiv s₁)))) ⟩
  to t (Fn.func h (from s y)) ∎
  where open B-Reasoning t
from-cong (→-preserves-↔ {s₂ = s₂} s t) {g} {h} f {x} {y} a = begin
  from t (Fn.func g (to s x)) ≈⟨ from-cong t (Fn.cong g (to-cong s a)) ⟩
  from t (Fn.func g (to s y)) ≈⟨ from-cong t (f (refl′ (pre (equiv s₂)))) ⟩
  from t (Fn.func h (to s y)) ∎
  where open A-Reasoning t
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
open Sandbox-Finite

module _ where
  vec-fin₀ : vec-setoid s₁ 0 Has 1 Elements
  to         vec-fin₀ []                 = zero
  from       vec-fin₀ zero               = []
  from∘to    vec-fin₀ []                 = []
  to∘from    vec-fin₀ zero               = ≡.refl
  to-cong    vec-fin₀ []                 = ≡.refl
  from-cong  (vec-fin₀ {s₁ = s}) ≡.refl  = refl′ (pre (equiv (vec-setoid s 0)))
```

Then, by showing a lemma that is there an isomorphism between `type:Vec A (suc
n)` and `type:A × Vec A n`:

```agda
  vec-rep
      : vec-setoid s₁ (suc n)
        ↔ ×-setoid s₁ (vec-setoid s₁ n)
  to vec-rep    (x ∷ xs)                     = x , xs
  from vec-rep  (x , xs)                     = x ∷ xs
  from∘to       (vec-rep {s₁ = s}) (x ∷ xs)  = refl s ∷ refl′ (pre (equiv (vec-setoid s _)))
  to∘from       (vec-rep {s₁ = s}) (x , xs)  = refl s , refl′ (pre (equiv (vec-setoid s _)))
  to-cong       (vec-rep {s₁ = s}) (x ∷ xs)  = x , xs
  from-cong     (vec-rep {s₁ = s}) (x , xs)  = x ∷ xs
```

We can combine these two facts into the desired proof that vectors have an
exponential cardinality:

```agda
  vec-fin
    : s₁ Has m Elements
    → vec-setoid s₁ n Has (m ^ n) Elements
  vec-fin {n = zero}   s = vec-fin₀
  vec-fin {n = suc n}  s
    = ↔-trans vec-rep
    ( ↔-trans (×-preserves-↔ s (vec-fin s))
              (↔-sym combine-remQuot-iso))
```

And now, to tie everything together, we can show that functions themselves also
have an exponential cardinality. This is a straightforward application of
`def:→-preserves-↔`, `def:vec-iso` and `vec-fin`. In essence, we transform our
function `A → B` into a function `Fin m → Fin n`, and then use the
characteristic function of vectors to reinterpret that function as a vector of
length `m`. Finally, we know the cardinality of such a vector, as shown just now
by `def:vec-fin`.

```agda
  →-fin : s₁ Has m Elements → s₂ Has n Elements
        → (s₁ ⇒ s₂) Has (n ^ m) Elements
  →-fin s t
    = ↔-trans (→-preserves-↔ s t)
    ( ↔-trans (↔-sym vec-iso)
              (vec-fin ↔-refl))
```


## Isomorphisms for Program Optimization

While counting cardinalities is fun and all, it can be easy to miss the forest
for the trees. Why might J. Random Hacker care about isomorphisms? Perhaps the
most salient application of theory I have ever seen is the use of isomorphism to
*automatically improve* an algorithms runtime by an asymptotic factor.

How can such a thing be possible? The answer lies in the observation that while
meaning is preserved by isomorphism, computational properties are not. Most
obviously, several algorithms for sorting lists have been famously studied. Each
of these algorithms has type `Vec A n → Vec A n` (and are thus isomorphic to one
another via `def:↔-refl`.) But as we know, bubble sort performs significantly
worse than merge sort does. It is the exploitation of exactly this sort of
observation that we can use to automatically improve our algorithms.

At a high level, the goal is to find an alternative representation of our
function as some other type---some other type which has more desirable
computational properties. As an illustration, every cache layer ever put in
front of a computation is an unprincipled attempt towards this end. The common
dynamic programming approach of memoizing partial results in an
appropriately-sized array is another example.

But caching of results is not the only possible way we can exploit an
isomorphism over a function. The somewhat-esoteric *trie* data structure is
commonly used for filtering big lists of strings (known, for obvious reasons, as
a dictionary) by a prefix. The idea behind tries is to break each word in the
list into a linked list of its characters, each pointing at the next, and then
to merge each of these linked lists into one big tree structure. The root node
then has one child for every possible starting letter in the set of words.
Moving to any particular branch necessarily filters away all of the words which
*don't* start with that letter. We can treat our new node as the root, and
recurse---this time, the node has children only for the possible *second*
letters of words in the dictionary that begin with the prefix of nodes you've
already traversed.

It's a clever encoding scheme that allows for an incremental refinement of a
dictionary, and this incremental refinement is exactly the sort of computational
property we're looking to exploit in our isomorphisms out of functions. When you
step back and think about the characteristic function of the trie, you see that
really all it is answering is the question "does this string exist in the
dictionary?"---or, put another way, it is any function of type `String → Bool`.

Exploiting isomorphisms is an excellent way of coming up with clever data
structures like tries, without the necessity that oneself be clever in the first
place. It's a great hack for convincing colleagues of your keen
computer-science mind. And the canonical isomorphisms given by a types'
cardinalities is an excellent means of exploring which isomorphisms actually
exist in order to exploit.

As a silly example, let's consider functions out of `type:Bool` and into some
arbitrary type `A`. We therefore know that such a thing has cardinality equal to
the cardinality of `A` squared. Using the notation $\abs{A}$ to mean "the
cardinality of `A`", we know that these functions have cardinality $\abs{A}^2$.
But from school arithmetic, such a thing is also equal to
$\abs{A}\times\abs{A}$---which doesn't take much imagination to interpret as a
pair.

And this isn't surprising when we stop to think about it; we can replace any
function `Bool → A` with `A × A` because we only need to store two `A`s---the
one resulting from `ctor:false`, and the other which comes from `ctor:true`.
There are no other `type:Bool`s to which we can apply the function, and thus
there are no other `A`s that can be produced.

Of course, this is a silly example. I did warn you. But it serves to illustrate
an important point, that through these isomorphisms we can transport the
entirety of our knowledge about discrete mathematics into the realm of
programming. In fact, if we know that two natural numbers are equal, we can use
that fact to induce an isomorphism:


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

