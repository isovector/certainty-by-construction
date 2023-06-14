# Setoids

```agda
module 6-setoids where

open import Level using (Level)
  renaming (suc to lsuc; _⊔_ to _⊔l_)
```

In this chapter, we will discuss many more notions of equality, many of which
are directly relevant to programming. For example, we might not care if two
file names are exactly equal; merely that they're equal up to case
insensitivity. Or that two binary trees are equal if they contain the same
elements. Propositional equality is capable only of dealing with two objects
which are syntactically equal, but is of absolutely no use to us for these more
common cases. Who knew equality could be such a messy business?


## Intentional vs Extensional Equality

We will begin our exploration into equality with the example of functions. When
are two functions equal? The answer is not very cut and dry. This is a hard
problem. Consider functions `def:ex₁`, `def:ex₂` and `def:ex₃`:

```agda
module Sandbox-IntensionalExtensional where
  open import Data.Nat
    using (ℕ; _+_;  _*_)
  open ℕ

  ex₁ : ℕ → ℕ
  ex₁ x = x + 2

  ex₂ : ℕ → ℕ
  ex₂ x = 2 * x

  ex₃ : ℕ → ℕ
  ex₃ x = suc (suc x)
```

Clearly functions `def:ex₁` and `def:ex₂` are *not* equal. But the answer is less
clear as to whether `def:ex₁` and `def:ex₃` are. The two functions are syntactically
entirely different, but compute the same output given the same input. If you
were to draw the plots of these two functions, they'd look identical.

But this isn't necessarily the whole story; are bubble sort and merge sort
the same function? They both return the same outputs given the same inputs,
however, they do so in entirely different ways, and with entirely different
computational behaviors. What a mess we find ourselves in.

Many programming languages sidestep the problem by comparing functions by their
pointer equality. In these cases, two functions are the same if they occur at
the same place in memory. But this is unsatisfying on many levels. First and
foremost, it is an abstraction leak. Functions are mathematical ideas,
completely separate from the hardware they run on. There exist models of
computation that don't have memory, and thus such a decision allows you to
deduce properties of the hardware you're running on---which ought to be a
no-no. Mathematics doesn't run on any hardware; it just *is.* Equally abhorrent
in pointer equality of functions is that it means two identical, syntactically
byte-for-byte source identical functions might not compare equal, due to
unpredictable quirks of how the runtime has decided to lay out memory. This
means that a program which might work today could fail tomorrow based only on a
differing mood of the runtime. There are many ways to describe this behavior,
but neither "sane" nor "mathematical" nor even "good programming practice" are
one.

The solution to this problem is to split equality of function types into two
camps. The mathematicians take a stand and say that yes, bubble sort and merge
sort *are* the same function. The computer scientists argue that no, they are
not. In the first world, we care only that the functions map equal inputs to
equal outputs. In the latter, we require the two functions to be defined in
exactly the same way. These two approaches to equality are known as
*extensional* and *intensional* equality, respectively.

Intensionality continues to be a challenge to define. Do variable names matter?
What about no-ops? The entire question is a quagmire, and we will not delve
deeper into this idea here.

Instead, we will worry only about extensional equality. Two functions are thus
equal if they map inputs to equal outputs. That is to say, given two functions
`f` and `g`, we'd like the following property to hold:

```agda
  open import Relation.Binary.PropositionalEquality hiding (_≗_)
  open import Relation.Binary using (Rel)

  _≗_
      : {a b : Level} {A : Set a} {B : A → Set b}  -- ! 1
      → Rel ((x : A) → B x) _ -- ! 2
  _≗_ f g = ∀ x → f x ≡ g x
```

The type here is rather involved, where we have made `B` a type dependent on `A`
at [1](Ann), and then made both `f` and `g` pass their argument to `B` for their
output at [2](Ann). A more intuitive type for `def:_≗_` is:

```type
_≗_ : {A B : Set} → Rel (A → B) _
```

but the extra generality means we can use `def:_≗_` with indexed types and
dependent functions as well. This doesn't matter most of the time, but will lead
to obscure problems if you are not mindful of it.

Given the definition of `def:_≗_`, we can show that `def:ex₁` and `def:ex₃` are
indeed extensionally equal:

```agda
  open import Data.Nat.Properties
    using (+-comm)

  ex₁≗ex₃ : ex₁ ≗ ex₃
  ex₁≗ex₃ zero = refl
  ex₁≗ex₃ (suc x) = cong suc (+-comm x 2)
```

The curious reader might wonder whether `def:_≗_` forms a preorder or an
equivalence relation. In fact it does, given simply by fanning out the argument
to both functions and then using the underling equivalence on `type:_≡_`. Once
you know the trick, it's not very difficult to show on paper, but doing it in
Agda requires jumping through a couple of hoops.

We'd like to bind `A` and `B` once and for all as implicit variables, and then
show that `def:_≗_` is `type:Reflexive`, `type:Symmetric` and `type:Transitive`.
Unfortunately, `def:_≗_` has too many implicit variables for Agda to figure out
the types involved on its own. Thus in order to avoid unsolved metas, we must
explicitly give some types to `type:Reflexive` et al.,

Due to a technical quirk with how Agda handles implicits defined via
`keyword:variable`, it's rather more verbose to do our usual thing here. So
rather than defining our implicits in a `keyword:variable` block, we will
instead construct a private module and add the implicits as parameters to that.
The exact details aren't of importance here, but the dedicated student is
encouraged to repeat this section on their own using a `keyword:variable` block
and see for themself what goes wrong.

```agda
  module _ {a b : Level} {A : Set a} {B : A → Set b} where
```

With our implicits now in scope, we can define an alias for dependent functions:

```agda
    private
      Fn : Set _
      Fn = (x : A) → B x
```

and now show that `def:_≗_` is `type:Reflexive` when its `A` parameter is
instantiated at `type:Fn`:

```agda
    open import Relation.Binary
      using (Reflexive; Symmetric; Transitive; IsEquivalence)

    ≗-refl : Reflexive {A = Fn} _≗_
    ≗-refl x = refl
```

With the `type:Fn` trick sorted out, it's not very hard to define symmetry or
transitivity---just apply the extensional equality, and perform the underlying
operation on the result:

```agda
    ≗-sym : Symmetric {A = Fn} _≗_
    ≗-sym f≗g a = sym (f≗g a)

    ≗-trans : Transitive {A = Fn} _≗_
    ≗-trans f≗g g≗h a = trans (f≗g a) (g≗h a)
```

Therefore `def:_≗_` is an equivalence relation:

```agda
    ≗-equiv : IsEquivalence {A = Fn} _≗_
    IsEquivalence.refl   ≗-equiv = ≗-refl
    IsEquivalence.sym    ≗-equiv = ≗-sym
    IsEquivalence.trans  ≗-equiv = ≗-trans
```


## Function Extensionality

If you are working in more of a mathematical domain (as opposed to a
computational one), you might want to postulate *function extensionality*: the
notion that extensionally equal functions are in fact *propositionally equal.*
As we have seen, this doesn't make sense when computation is your main goal, but
if you are simply modeling the world, it's an extremely convenient thing to have
around. We can postulate `def:fun-ext` as follows:

```agda
  postulate
    fun-ext
        : {a b : Level} {A : Set a} {B : A → Set b}
        → {f g : (x : A) → B x}
        → f ≗ g → f ≡ g
```

Function extensionality doesn't exist in the standard library; while Agda is
compatible with it, it can be neither proven nor disproven in Agda, and
therefore you must be the one to decide whether or not it holds.

Given `def:fun-ext`, we can trivially lift our proof `def:ex₁≗ex₃` into a proof
that the two functions are propositionally equal:

```agda
  ex₁≡ex₃ : ex₁ ≡ ex₃
  ex₁≡ex₃ = fun-ext ex₁≗ex₃
```

Of course, you don't need to postulate `def:fun-ext`; you can always work
directly with extensional equality itself, instantiating it to get whatever
proof of equality you actually need. But the ergonomics around `def:fun-ext` can
dramatically improve the story, if you're willing to give up on computability
for it.


## Equality of Binary Trees

We would like to give a definition of equality for binary trees such that they
contain the same elements in the same order, but not necessarily that the tree
structure itself is identical. This happens to be a rather interesting example
which generalizes well, and in exploring it we will discover a new construction
over equality.

One flaw with writing a book in the literate style is that sometimes material
must be presented out of order so that the whole thing can compile. And so,
before we look at equality of binary trees, we must first construct a little
combinator. The `def:on` function is given as follows:

```agda
module _ where
  open import Level using (Level; _⊔_)

  private variable
    a b c ℓ : Level
    A : Set a
    B : Set b
    C : Set c

  on : (B → B → C) → (A → B) → A → A → C
  on _∙_ f a₁ a₂ = f a₁ ∙ f a₂
```

We can use `def:on` to conveniently run `f` on both arguments, and then use
`_∙_` to combine both results. It's often used to compare two objects under a
certain perspective. For example, we could check whether two people match, not
by comparing them for equality, but by comparing their fingerprints for
equality. This might be written as `on _≟_ fingerprint`.

You will not be surprised to learn that given a equivalence relation over some
type `B`, we can build an equivalence relation over `A` assuming we are given a
"fingerprinting" function `f : A → B`. In the jargon, this *quotients* `A` by
`f`. First, bring everything into scope as module parameters:

```agda
  open import Relation.Binary
  module Sandbox-Quotient
      {a b ℓ : Level} {B : Set b} {_≈_ : Rel B ℓ}
      {A : Set a} (f : A → B) (≈-equiv : IsEquivalence _≈_) where
```

We can then build the relation quotiented by `f`:

```agda
    _≈/f_ : Rel A ℓ
    _≈/f_ = on _≈_ f
```

and then show that `def:_≈/f_` is an equivalence relation:

```agda
    ≈/f-equiv : IsEquivalence _≈/f_
    IsEquivalence.refl   ≈/f-equiv = IsEquivalence.refl ≈-equiv
    IsEquivalence.sym    ≈/f-equiv = IsEquivalence.sym ≈-equiv
    IsEquivalence.trans  ≈/f-equiv = IsEquivalence.trans ≈-equiv
```

Showing `def:≈/f-equiv` is rather annoying, in that we must copattern match and
then define each as a projection out of `≈-equiv`. This seems as though it's
equivalent to the following definition:

```illegal
    ≈/f-equiv⅋ : IsEquivalence _≈/f_
    ≈/f-equiv = ≈-equiv
```

which it would be, if Agda could figure out the necessary unification.
Unfortunately, it cannot, and thus we must do the hard work of projecting out
each field ourselves. Alas.

You will notice that `module:Sandbox-Quotient` is a very general result, and has
absolutely nothing to do with binary trees. What it really allows us to do is to
transform some type for which we don't have an equivalence relation into another
type in which we do. But not to bury the lede, we can follow through with the
remainder of the binary tree example. First, a new module, and some imports to
get our binary trees from @sec:decidability back into scope:


```agda
module Example-BinaryTrees where
  import 4-decidability
  open 4-decidability.BinaryTrees
```

We now need a fingerprinting function to quotient our trees by. Recall that we'd
like to throw away the nesting structure of the tree, keeping only the contents
and the order. We could do that by transforming our binary trees into *normal
form*---finding some invariant that we hold true, such as ensuring every
`ctor:branch` has `ctor:empty` as its left tree. Making such a transformation
would ensure that our non-propositional notion of equality could be show via
propositional equality proper. This is the right idea, but sounds hard to get
right. Instead, we note that any binary tree with subtrees in only one direction
is not *binary* whatsoever, and reduces to a linked list.

It brings me distinct pleasure to have made it this far into a functional
programming book without having talked about linked lists. But the time is now.
Rather than dwelling on them, we assume the reader now has enough technical
proficiency in Agda (and familiarity with computing) to understand the following
presentation of linked lists without commentary. We first define the type
itself:

```agda
  data List (A : Set) : Set where
    []   : List A
    _∷_  : A → List A → List A
  infixr 4 _∷_
```

Next, we give concatenation for lists:

```agda
  _++_ : {A : Set} → List A → List A → List A
  [] ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ xs ++ ys

  infixr 4 _++_
```

We are now able to fingerprint our binary trees by giving a left-to-right
traversal, collecting the results into a linked list:

```agda
  contents : {A : Set} → BinTree A → List A
  contents empty = []
  contents (branch l a r) = contents l ++ a ∷ contents r
```

-- TODO(sandy): fix the original definition of `≡-equiv` so we can just import
-- it here instead of postulating it

```agda
  open import Relation.Binary using (Rel; IsEquivalence)
  open import Relation.Binary.PropositionalEquality
    using (_≡_; refl; _≢_)

  postulate
    ≡-equiv : {A : Set} → IsEquivalence {A = A} _≡_
```

We can now demonstrate our quotienting machinery by building two example trees:

```agda
  module _ where
    open import Data.Nat

    ex₁ : BinTree ℕ
    ex₁ = branch (leaf 1) 2 (leaf 3)

    ex₂ : BinTree ℕ
    ex₂ = branch (branch (leaf 1) 2 empty) 3 empty
```

It's clear that `def:ex₁` and `def:ex₂` are not *propositionally* equal, as
illustrated thusly:

```agda
    ex₁≠ex₂ : ex₁ ≢ ex₂
    ex₁≠ex₂ = λ ()
```

but the two do have the same elements in the same order, and thus we can show
they are equal under quotienting by `def:contents`:

```agda
    open Sandbox-Quotient (contents {ℕ}) ≡-equiv
      renaming (_≈/f_ to _≈ᴮ_)

    ex₁≈ᴮex₂ : ex₁ ≈ᴮ ex₂
    ex₁≈ᴮex₂ = refl
```

Et voila! A thing of rare beauty.


## Setoids

Let's look again at the definition of `module:Sandbox-Quotient`.

```agda
  module Sandbox-Quotient⅋
      {a b ℓ : Level} {B : Set b} {_≈_ : Rel B ℓ}
      {A : Set a} (f : A → B) (≈-equiv : IsEquivalence _≈_) where
```

You'll notice that this is quite a lot of boilerplate required in order to get
everything into scope. We need `b : Level` and `ℓ : Level` around so that we can
properly scope `B : Set b`, in order to scope `_≈_ : Rel B ℓ`, all so that we
can show that `_≈_` is an equivalence relation. In fact, this is such a common
grouping of objects that we often *bundle* them together into a single object
known as a *setoid.* The definition is given thusly:

```agda
  module Sandbox-Setoids where
    record Setoid (c ℓ : Level) : Set (lsuc (c ⊔l ℓ)) where
      field
        Carrier        : Set c
        _≈_            : Rel Carrier ℓ
        isEquivalence  : IsEquivalence _≈_

      open IsEquivalence isEquivalence public
```

By bundling these three fields together, we can more easily pass an equivalence
relationship around. To illustrate this, we can rewrite our module definition of
`module:Sandbox-Quotient⅋₁`:


```agda
  open Sandbox-Setoids

  module Sandbox-Quotient⅋₁
      {a b ℓ : Level} (B-setoid : Setoid b ℓ) {A : Set a}
      (f : A → Setoid.Carrier B-setoid)  -- ! 1
      where
    open Setoid B-setoid renaming (Carrier to B)  -- ! 2
```

The salient change here is that we no longer have `B` in scope; thus we must
reference it via `Setoid.Carrier B-setoid` at [1](Ann), and can bring it back
into scope at [2](Ann) by opening the `B-setoid` record and renaming
`field:Carrier`.

The vast entirety of Agda's standard library is based around setoid
rather than propositional equality. Thankfully, there is a canonical means of
turning propositional equality into setoid equality, given via `def:setoid`,
which merely recognizes the fact that propositional equality is itself a setoid:

```agda
  open import Relation.Binary.PropositionalEquality as PropEq
    using (_≡_)

  open Setoid

  setoid : Set → Setoid _ _
  Carrier (setoid A) = A
  _≈_ (setoid A) = PropEq._≡_
  IsEquivalence.refl   (isEquivalence (setoid A)) = PropEq.refl
  IsEquivalence.sym    (isEquivalence (setoid A)) = PropEq.sym
  IsEquivalence.trans  (isEquivalence (setoid A)) = PropEq.trans
```

However, we will not use our own definition of either `type:Setoid` or
`def:setoid` in the remainder of this book. Due to the prevalence of setoids in
the standard library, we will get significantly more interoperability by
importing the usual definition. But don't worry; it's defined identically to
what we have here.

```agda
open import Relation.Binary
  using (Setoid)
open import Relation.Binary.PropositionalEquality
  using (setoid)
```

Setoids are useful only as an interface for abstracting a notion of equality.
That means, when you're working in a particular domain, like we were in modular
arithmetic, you don't need them. But whenever you'd like to build an abstract,
parameterized structure that enforces laws, you ought to use a setoid to ensure
maximum reusability of your concept.

```agda
open import Relation.Binary
  using (Rel; IsEquivalence)

module Setoid-Examples where
  open import Level using (Level; _⊔_)
  open import Relation.Binary using (Setoid)
  open import Relation.Binary.PropositionalEquality using (setoid)
  open Setoid

  module _ where
    open Sandbox-IntensionalExtensional

    ext-setoid
        : {ℓa ℓb : Level}
        → (A : Set ℓa)
        → (B : A → Set ℓb)
        → Setoid _ _
    Setoid.Carrier        (ext-setoid A B) = (a : A) → B a
    Setoid._≈_            (ext-setoid A B) = _≗_
    Setoid.isEquivalence  (ext-setoid A B) = ≗-equiv

  open import Data.Nat using (ℕ)

  module _ {ℓ : Level} (A : Set ℓ) {n : ℕ} where
    open import Data.Vec

    length-setoid : Setoid _ _
    Carrier length-setoid = _
    _≈_ length-setoid = _
    isEquivalence length-setoid = ≈/f-equiv
      where
        open Sandbox-Quotient
            (length {A = A} {n = n})
            (Setoid.isEquivalence (setoid _))

    head-setoid : Setoid _ _
    Carrier head-setoid = _
    _≈_ head-setoid = _
    isEquivalence head-setoid = ≈/f-equiv
      where
        open Sandbox-Quotient
            (head {A = A} {n = n})
            (Setoid.isEquivalence (setoid _))

```

