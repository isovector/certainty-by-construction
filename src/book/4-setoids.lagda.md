# Setoids

```agda
module 4-setoids where
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
  open import Level using (Level; _⊔_)
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
  open import Relation.Binary
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


## Modular Arithmetic

All of the equivalences we have looked at thus far have been combinators on
existing equivalences. And of course, we have also seen propositional equality,
but it's reasonable to wonder whether any of this actually "cashes out" in the
real world. In this section, we will look into a familiar way of quotienting the
natural numbers, and see just how much leg work this common vocabulary can do
for us.

A favorite example of quotienting for mathematicians are the so-called "ring of
natural numbers modulo $n$," more tersely written as $\mathbb{N}/n\mathbb{N}$.
But what is this ring? This ring is the mathematical way of saying "clock
addition"---that is, we pick some $n$, maybe $n = 12$ for an example, and say
that whenever our arithmetic gets to $n$ it overflows back to 0. This is the
peculiar fact that, on an analog clock, we have the fact that $11 + 2 = 1$. Of
course, this is a blatant misuse of the equals symbol, so instead we write
$11 + 2 = 1 \text{(mod 12)}$.

How can we formalize this idea of modular arithmetic? Well, if we'd like to show
$a = b \text{(mod }n\text{)}$, we would like to find two multiples of $n$ that we can
use to equate the two. That is to say, we need to find $x, y : ℕ$ such that $a +
xn = b + yn$.


```agda
open import Data.Nat using (ℕ; _+_; _*_)

module ModularArithmetic where
  open import Relation.Binary.PropositionalEquality
    using (_≡_; refl)

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

-- TODO(sandy): what does it mean that this is only an impl detail?

We can now show that our clock example works as expected:

```agda
  _ : 11 + 2 ≈ 1 ⟨mod 12 ⟩
  _ = ≈-mod 0 1 refl
```

Of course, it's quite a mouthful to stick in the `⟨mod_⟩` part every time, so we
can make a new module and subsequent relation in which we hold the modulus
constant:

```agda
module ℕ/nℕ (n : ℕ) where
  open ModularArithmetic public
  open import Relation.Binary
    using (Rel)

  infix 4 _≈_
  _≈_ : Rel ℕ _
  _≈_ = _≈_⟨mod n ⟩
```

As it happens, `type:_≈_` forms an equivalence relation. Showing reflexivity and
symmetry is simple enough:

```agda
  open import 4-relations
  -- TODO(sandy): would be nice to have section numbers for modules
  open Relation.Binary using (Reflexive; Symmetric; Transitive; IsEquivalence)

  module _ where
    open import Relation.Binary.PropositionalEquality

    ≈-refl : Reflexive _≈_
    ≈-refl = ≈-mod 0 0 refl

    ≈-sym : Symmetric _≈_
    ≈-sym (≈-mod x y p) = ≈-mod y x (sym p)
```

However, the transitivity of `type:_≈_` is a significantly harder thing to
demonstrate. Before diving into the implementation, let's work out the solution
"on paper" first, where we can more more quickly and require less formality in
justifying our steps. To set up the problem, given `a ≈ b` and `b ≈ c`, and
would like to show `a ≈ c`. This looks simple enough, but the short types
involved here pack quite a punch. Recall that what `a ≈ b` really means is that
we have two numbers `x y : ℕ`, such that

$$
a + xn = b + yn
$$

Similarly for `b ≈ c` we have two more numbers `z w : ℕ` such that

$$
b + zn = c + wn
$$

In order to show `type: Transitive _≈_`, we therefore must find two more numbers
`i j : ℕ` such that the following equation holds:

$$
a + in = c + jn
$$

Solving this requires some simultaneous manipulation of the first two equations:

$$
\begin{aligned}
a + xn &= b + yn \\
b + zn &= c + wn
\end{aligned}
$$

We'd like to eliminate the $b$ term, so we can solve both equations for $b$:

$$
\begin{aligned}
a + xn - yn &= b + yn \\
b &= c + wn - zn
\end{aligned}
$$

which then allows us to combine the two equations:

$$
a + xn - yn = b = c + wn - zn
$$

and therefore we have:

$$
a + xn - yn = c + wn - zn
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

This gives us our desired numbers `i j : ℕ` for transivity, namely $i = x + z$
and $j = w + y$.

```agda
    ≈-trans : Transitive _≈_
    ≈-trans {a} {b} {c} (≈-mod x y pxy) (≈-mod z w pzw) =
      ≈-mod (x + z) (w + y)
```

And now for the hard part---we must give a *proof* that these are in fact the
right numbers. Most of the work involved is algebraic manipulation, shuffling
the terms around such that we can apply `pxy` and then `pzw`. Inlining the
algebraic manipulation is a huge amount of effort, so instead we will use two
as-of-yet-undefined lemmas that do the heavy lifting.

```agda
      ( begin
        a + (x + z) * n      ≡⟨ lemma₁ a n x z ⟩
        (a + x * n) + z * n  ≡⟨ cong (_+ z * n) pxy ⟩
        (b + y * n) + z * n  ≡⟨ lemma₂ b (y * n) (z * n) ⟩
        (b + z * n) + y * n  ≡⟨ cong (_+ y * n) pzw ⟩
        c + w * n + y * n    ≡⟨ sym (lemma₁ c n w y) ⟩
        c + (w + y) * n      ∎
      )
      where
        open ≡-Reasoning
```

Here, `lemma₁` distributes `* n` over the addition, and reassociate everything
so it's in the right shape for `pxy`. Meanwhile, `lemma₂` applies the
commutativity of addition across a pair of parentheses.

Rather than go through the effort of proving these lemmas for ourselves, we can
turn to the ring solver, and ask it to do the heavy lifting on our behalf.
First, we must bring the ring solver into scope:

```agda
        open import Data.Nat.Solver
        open +-*-Solver
```

and then we can get our two lemmas by invoking `solve` with the number of
variables in the expression, and a syntactic representation of the problem we'd
like solved:

```agda
        lemma₁ = solve 4
          (λ a n x z → a :+ (x :+ z) :* n := (a :+ x :* n) :+ z :* n)
          refl

        lemma₂ = solve 3
          (λ b i j → (b :+ i) :+ j := (b :+ j) :+ i)
          refl
```

The ring solver is a fantastic tool for automating away tedious, symbolic proofs
of this form. Of course, we could have proven these lemmas by hand, but they are
uninteresting and error-prone. And, after all, why do something by hand when
it's automateable? What's amazing is that the ring solver is just standard Agda
library code; it's nothing you couldn't have written for yourself. And indeed,
we will drill into exactly this problem in @sec:ringsolving.

Anyway, now that we have reflexivity, symmetry, and transitivity, we now know
that `type:_≈_` is an equivalence relation.

```agda
  ≈-equiv : IsEquivalence _≈_
  IsEquivalence.refl   ≈-equiv = ≈-refl
  IsEquivalence.sym    ≈-equiv = ≈-sym
  IsEquivalence.trans  ≈-equiv = ≈-trans
```

Additionally, we can use this fact to get equational reasoning syntax for free,
via our `module:PreorderReasoning` module from @sec:preorderreasoning.

```agda
  module ≈-Reasoning where
    open Sandbox-Orderings

    ≈-preorder : IsPreorder _≈_
    IsPreorder.refl   ≈-preorder = ≈-refl
    IsPreorder.trans  ≈-preorder = ≈-trans

    open IsEquivalence ≈-equiv using (sym) public
    open PreorderReasoning ≈-preorder public
```

As you've seen, it's quite a lot of work to prove anything about `_≈_⟨mod_⟩`;
whenever we'd like to do anything, we need to construct two numbers `x` and `y`,
and then prove the underlying equality holds. While this is OK for trivial
propositions, things like `mod-trans` are nearly overwhelming. You can imagine
how much effort it would be to prove anything of actual *substance* in this
domain. Mathematicians hate number crunching as much, if not more, than anyone
else, so surely they are not doing all this work by hand, are they? How can we
simplify our workload?

The answer, is setoids.


## Setoids

While it may seem like we've taken a long detour from our original goal of
talking about equality, we are now ready to tackle *setoids* in their full
glory. A setoid is a bundled binary relation alongside a proof that it's an
equivalence relationship. By putting all of these things together, we're
rewarded by the Agda standard library with setoid reasoning: syntax for doing
"equational" reasoning over our objects. This reasoning lets us operate at a
much higher level than we could when we were constructing pairs of numbers and
proofs between them.

```agda
open import Relation.Binary
  using (Rel; IsEquivalence)

module Sandbox-Setoids where
  open import Level
    using (Level; _⊔_)
    renaming (suc to lsuc)
  record Setoid (c ℓ : Level) : Set (lsuc c ⊔ lsuc ℓ) where
    field
      Carrier        : Set c
      _≈_            : Rel Carrier ℓ
      isEquivalence  : IsEquivalence _≈_

    open IsEquivalence isEquivalence public

```

Our `Setoid` record merely needs to bundle the underlying set with its
equivalence relation (and a proof that that relation is in fact an equivalence
relation!)

Given this, it's trivial to show now that `_≈_⟨mod_⟩` forms a setoid:

```agda
  mod-setoid : ℕ → Setoid _ _
  mod-setoid n = record
    { Carrier        = ℕ
    ; _≈_            = _≈_
    ; isEquivalence  = ≈-equiv
    }
    where open ℕ/nℕ n

  open import Relation.Binary.PropositionalEquality as PropEq
    using (_≡_)

  open Setoid

  setoid : ∀ {ℓ} (A : Set ℓ) → Setoid _ _
  Carrier (setoid A) = A
  _≈_ (setoid A) = _≡_
  IsEquivalence.refl (isEquivalence (setoid A)) = PropEq.refl
  IsEquivalence.sym (isEquivalence (setoid A)) = PropEq.sym
  IsEquivalence.trans (isEquivalence (setoid A)) = PropEq.trans
```

```agda

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

We're almost ready to build some interesting proofs; but we're going to need to
define a few more trivial ones first. But let's start proving some properties
about `_≈_⟨mod_⟩` in a new module:

```agda
module mod-properties (n : ℕ) where
  open ℕ/nℕ n
```

We'll still need propositional equality for a few things, but the setoid
infrastructure is meant to be a mostly drop-in replacement for propositional
equality, and so we will import it qualified:

Let's prove two more fact "by hand", the fact that $0 = n (\text{mod} n)$:

```agda
  import Relation.Binary.PropositionalEquality as PropEq
  open import Data.Nat
  open import Data.Nat.Properties

  0≈n : 0 ≈ n
  0≈n = ≈-mod 1 0 PropEq.refl
```

and the fact that we can `cong suc` onto proofs about `_≈_⟨mod_⟩`. While this
sounds obvious, it doesn't hold for most functions! Most functions do not
preserve setoid equality, so it's very exciting to find ones that do. To
illustrate this point, consider the function `4 *_`, which doesn't preserve
equality whenever, for example, $n = 5$.

```agda
  mod-suc-cong : {a b : ℕ} → a ≈ b → suc a ≈ suc b
  mod-suc-cong (≈-mod x y p) = ≈-mod x y (PropEq.cong suc p)
```

Now that our setoid infrastructure is bought and paid for, and also that we have
a few primitive lemmas to work with, we're ready to begin proving things about
modular arithmetic in earnest. We can open the `mod-reasoning` module to enable
setoid reasoning throughout the rest of the current module.

```agda
  open ≈-Reasoning
```

Let's begin by proving the following theorem:

```agda
  +-zero-mod : (a b : ℕ) → a ≈ 0 → a + b ≈ b
```

We can proceed in two cases, by splitting on `b`. In the zero case, we need to
show `a + zero ≈ zero ⟨mod n⟩`. Like when we did reasoning over propositional
equality, we `begin`:

```agda
  +-zero-mod a zero a≈0 =
    begin
      a + zero
```

and we still have access to propositional equality rewriting:

```agda
    ≡⟨ +-identityʳ a ⟩
      a
```

However, now that we have setoid reasoning enable, we can also do *setoid
rewriting* via the `≈⟨_⟩` operator. We have an `a` and want `zero`, and
conveniently, already have a proof that `a ≈ 0 ⟨mod n⟩`, so we can just apply it:

```agda
    ≈⟨ a≈0 ⟩
      zero
    ∎
```

You can see already how much nicer this style of reasoning is, compared with our
old method of building the `_≈_⟨mod_⟩` term directly.

We also need to show the `suc b` case, presented without further commentary.

```agda
  +-zero-mod a (suc b) a≈0 = begin
    a + suc b    ≡⟨ +-suc a b ⟩
    suc a + b    ≡⟨⟩
    suc (a + b)  ≈⟨ mod-suc-cong (+-zero-mod a b a≈0) ⟩
    suc b        ∎
```

Let's hoist another theorem about natural numbers that will come in handy: the
fact that `suc` is injective.

```agda
  mod-suc-injective
    : {a b : ℕ} → suc a ≈ suc b → a ≈ b
  mod-suc-injective (≈-mod x y p) =
    ≈-mod x y (suc-injective p)
```

We're now ready to show a major result, the fact that `_≈_⟨mod_⟩` preserves
addition. Congruence proofs like this are the real workhorses of getting real
mathematics done, so it's exciting that we're able to build it.

```agda
  +-cong₂-mod
      : {a b c d : ℕ}
      → a ≈ b
      → c ≈ d
      → a + c ≈ b + d
```

We can begin by case splitting on `a`. The zero case is straightforward, making
use of our previous lemma `+-zero-mod`:

```agda
  +-cong₂-mod {zero} {b} {c} {d} pab pcd = begin
    c         ≈⟨ pcd ⟩
    d         ≈⟨ sym (+-zero-mod b d (sym pab)) ⟩
    b + d     ∎
```

In the `suc a` case, we can now case split on `b`. The zero case is equally
straightforward:

```agda
  +-cong₂-mod {suc a} {zero} {c} {d} pab pcd = begin
    suc a + c  ≈⟨ +-zero-mod (suc a) c pab ⟩
    c          ≈⟨ pcd ⟩
    d          ∎
```

And all that's left is the non-zero cases, in which we can hand the problem over
to induction, using `mod-suc-cong` and `mod-suc-injective` to manipulate our
proofs back into the right shape.

```agda
  +-cong₂-mod {suc a} {suc b} {c} {d} pab pcd =
      mod-suc-cong (+-cong₂-mod (mod-suc-injective pab) pcd)
```

`+-cong₂-mod` is quite a marvel of a theorem, especially when you consider
needing to build this proof term by hand. Let's take a moment to appreciate what
we've accomplished here, by reasoning our way through how we would have solved
the problem naively.

Our parameters to `+-cong₂-mod` work out to two equations:

$$
a + xn = b + yn \\
c + zn = d + wn
$$

and we are tasked with finding $p$ and $q$ such that the following holds:

$$
(a + c) + pn = (b + d) + qn
$$

The solution is to add the two original equations together, point-wise:

$$
a + xn + c + zn = b + yn + d + wn
$$

and then group like terms:

$$
(a + c) + xn + zn = (b + d) + yn + wn
$$

of which we can then factor out an $n$ term:

$$
(a + c) + (x + z)n = (b + d) + (y + w)n
$$

giving us the solutions $p = x + z$ and $q = y + w$. So far so good, but now we
are tasked with building this equality term given the original equations. It's
not hard, but it's a consider amount of work. But the worst part is that this
reasoning is at a lower level than we'd like to be operating; we want to be
thinking about modular arithmetic, not juggling equations!

We'll prove two more facts about modular arithmetic, one in service of the
other. We can show that modular multiplication by zero results in zero:

```agda
  *-zero-mod : (a b : ℕ) → b ≈ 0 → a * b ≈ 0
  *-zero-mod zero b x = refl
  *-zero-mod (suc a) b x = begin
    suc a * b  ≡⟨⟩
    b + a * b  ≈⟨ +-cong₂-mod x (*-zero-mod a b x) ⟩
    0          ∎
```

And at long last, we can show that modular arithmetic is also congruent over
multiplication, via `*-cong₂-mod`:

```agda
  *-cong₂-mod
      : {a b c d : ℕ}
      → a ≈ b
      → c ≈ d
      → a * c ≈ b * d
  *-cong₂-mod {zero} {b} {c} {d} a=b c=d = begin
    zero * c  ≡⟨⟩
    zero      ≈⟨ sym (*-zero-mod d b (sym a=b)) ⟩
    d * b     ≡⟨ *-comm d b ⟩
    b * d     ∎
  *-cong₂-mod {suc a} {zero} {c} {d} a=b c=d = begin
    suc a * c  ≡⟨ *-comm (suc a) c ⟩
    c * suc a  ≈⟨ *-zero-mod c (suc a) a=b ⟩
    zero       ≡⟨⟩
    zero * d   ∎
  *-cong₂-mod {suc a} {suc b} {c} {d} a=b c=d = begin
    suc a * c  ≡⟨⟩
    c + a * c
      ≈⟨ +-cong₂-mod c=d (*-cong₂-mod (mod-suc-injective a=b) c=d) ⟩
    d + b * d  ≡⟨⟩
    suc b * d  ∎
```

While the proof of `*-cong₂-mod` is still quite involved, again, it's worth
considering the problem in its more "raw" form. Given:

$$
a + xn = b + yn \\
c + zn = d + wn
$$

we are looking for $p$ and $q$ such that the following holds:

$$
ac + pn = bd + qn
$$

The solution again is analogous to solving for `+-cong₂-mod`, except in this
case we must multiply the two sides of our equations, resulting in the hairy
solutions:

$$
p = cx + az + xzn \\
q = dy + bw + ywn
$$

Convincing Agda of the equality of these terms is on the order of 50 algebraic
manipulations; most of it being gentle massaging of the expression into
something you can `cong` one proof over, and then massaging it into a form on
which you can `cong` the other.

All in all, setoids have bought us a great deal of algebraic power. We've used
them to manage working over an equivalence relation, showing how we can quotient
over values that are not *literally* equal to one another, but still operate in
a context that allows us to work as if they were. The only real loss here is
that `cong` no longer holds for all functions, and that we must prove it holds
whenever we'd like to use that fact. This is a limitation more of Agda's type
theory than it is of mathematics; in the latter, it's perfectly acceptable to
define a quotient relationship that holds by fiat. It is only in our
computational context that we are required to *show* that functions cannot
observe the difference between quotiented values.

On the other hand, the rigor afforded to us by doing mathematics in a rich type
theory is what has driven so much of the recent study of equality. When you're
doing mathematics by pen and paper, it's easy to be sloppy about what equality
actually *means.* The setoid approach can be paraphrased as "whenever you define
a set, you must also define what equality means over it."


## Constructions on Setoids

By virtue of being first-class objects, setoids are *values* that we can pass
as parameters, and return from functions. That means there's an entire set of
combinators we can use for building setoids out of other things. For example,
given a type, we can trivially construct a setoid using propositional equality:

```agda
module _ where
  import Relation.Binary.PropositionalEquality as PropEq

  open Relation.Binary
    using (Setoid)
  open Setoid using (Carrier; _≈_; isEquivalence)

  setoid : Set → Setoid _ _
  Carrier (setoid A) = A
  _≈_ (setoid A) = PropEq._≡_
  IsEquivalence.refl (isEquivalence (setoid A)) = PropEq.refl
  IsEquivalence.sym (isEquivalence (setoid A)) = PropEq.sym
  IsEquivalence.trans (isEquivalence (setoid A)) = PropEq.trans
```

