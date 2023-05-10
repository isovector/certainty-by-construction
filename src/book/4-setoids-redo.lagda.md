# Structured Sets

```agda
module 4-setoids-redo where
```

One exceptionally common notion in mathematics is the notion of a "set equipped
with some structure." In this chapter, we will discuss what this means, how to
build such things, and look at several extremely distinct examples.

The first thing to take note of, however, is that when mathematicians say "set,"
very rarely do they mean *set* as in, *set theory.* What they really mean is
"some collection of elements," or even just some *type.* While set theory comes
with a great deal of axiomization for constructing sets and not shooting oneself
in the foot with them, it is worth realizing that almost no working
mathematicians use set theory when they actually get down to work. Even if
they're explicitly talking about sets.

A second point worthy of our discussion is that even though mathematicians give
their definitions of mathematical objects in terms of sets, they are not really
thinking about sets. As Buzzard points out, a group is defined in modern
textbooks as a non-empty set satisfying the group axioms. However, group theory
was invented eighty years before set theory. The definitions given are correct,
but post-hoc and sorted out after the fact. This can cause extreme
disorientation to the computer scientist, who must construct things from smaller
pieces, while the mathematicians build the big thing first and figure out how to
decompose it later.

-- TODO(sandy): cite kevin ^

Bear this in mind as we work through our examples; mathematical constructions
which might seem insane when taken at face value often make much more sense when
reconsidered in this context.


## Binary Relations

One common variety of structured set is the *relation,* which, in the canon, is
used to categorize disparate things like functions, equalities, orderings, and
set membership, to name a few. Let's begin with the mathematical definition, and
decompile it into something more sensible for our purposes.

> A binary relation `_R_` over sets $X$ and $Y$ is a subset of the Cartesian
> product $X \times Y$.

As we saw when discussing proofs, subsets are best encoded in Agda as functions
into `Set`. Taken at face value, this would give us the following type for a
relation:

```agda
open import Data.Product using (_×_)

postulate
  _ : {A B : Set} → A × B → Set
```

We can do slightly better however, by recalling the curry/uncurry isomorphism
(@sec:curry), splitting the explicit Cartesian product into two arguments:

```agda
  _ : {A B : Set} → A → B → Set
```

A fully-fledged solution here must be level polymorphic, since many of the
relations we'd like to be able to encode will be over higher-level sets. There
are actually three levels required here, one for `A`, another for `B`, and a
third for the resulting `Set`. Thus, we come up with our final definition as
`REL`:

```agda
open import Level
  using (Level; _⊔_)
  renaming (zero to lzero; suc to lsuc)

module Sandbox-Relations where
  private variable
    a b ℓ : Level

  REL : Set a → Set b → (ℓ : Level) → Set (a ⊔ b ⊔ lsuc ℓ)
  REL A B ℓ = A → B → Set ℓ
```

This `REL` is the type of *heterogeneous* relations, that is, relationships
between two distinct sets. The most salient relationship of this sort is the
usual way that functions are defined as mathematical objects---namely, as a
relation between the input and output types. Thus, we can assert that `f` is a
function by building a relation $R$ such that if $x R y$ then $f x = y$. It's
roundabout and non-computable, but such is often the case when dealing with
mathematics:

```agda
  module Example₂ where
    open import Relation.Binary.PropositionalEquality
      using (_≡_)

    IsFunction
        : {A : Set a} {B : Set b}
        → (f : A → B)
        → REL A B _
    IsFunction f A B = ∀ x y → f x ≡ y
```

Of course, this definition is somewhat cheating, since we already have a
function to begin with, and are just using it to construct a particular
relation.







```agda

  Rel : Set a → (ℓ : Level) → Set (a ⊔ lsuc ℓ)
  Rel A ℓ = A → A → Set ℓ

  module Example₁ where
    data _≡⅋₀_ {A : Set a} : A → A → Set a where
      refl : {x : A} → x ≡⅋₀ x

    data _≡_ {A : Set a} : Rel A a where
      refl : {x : A} → x ≡ x

  import Data.Nat as ℕ
  open ℕ using (ℕ)

  _≤⅋₀_ : Rel ℕ lzero
  _≤⅋₀_ = ℕ._≤_

  _≤_ : Rel ℕ _
  _≤_ = ℕ._≤_

  -- REL : Set a → Set b → (ℓ : Level) → Set (a ⊔ b ⊔ lsuc ℓ)
  -- REL A B ℓ = A → B → Set ℓ

  private variable
    A : Set a
    B : Set b

  Reflexive : Rel A ℓ → Set _
  Reflexive _~_ =
    ∀ {x} → x ~ x

  Symmetric : Rel A ℓ → Set _
  Symmetric _~_ =
    ∀ {x y} → x ~ y → y ~ x

  Transitive : Rel A ℓ → Set _
  Transitive _~_ =
    ∀ {x y z} → x ~ y → y ~ z → x ~ z

  record IsEquivalence {A : Set a} (_~_ : Rel A ℓ) : Set (a ⊔ ℓ) where
    field
      refl : Reflexive _~_
      sym : Symmetric _~_
      trans : Transitive _~_

  record IsPreorder {A : Set a} (_~_ : Rel A ℓ) : Set (a ⊔ ℓ) where
    field
      refl : Reflexive _~_
      trans : Transitive _~_

  record IsEquivalence⅋ {A : Set a} (_~_ : Rel A ℓ) : Set (a ⊔ ℓ) where
    field
      is-preorder : IsPreorder _~_
      sym : Symmetric _~_

    open IsPreorder is-preorder public

  module Example₃ where
    import Relation.Binary.PropositionalEquality
      as PropEq
    open PropEq using (_≡_)

    open IsEquivalence

    ≡-equiv : IsEquivalence {A = A} _≡_
    refl ≡-equiv = PropEq.refl
    trans ≡-equiv = PropEq.trans
    sym ≡-equiv = PropEq.sym

  module Reasoning {_~_ : Rel A ℓ} (~-preorder : IsPreorder _~_) where
    open IsPreorder ~-preorder public

    _∎ : (x : A) → x ~ x
    _∎ x = refl
    infix 3 _∎

    import Relation.Binary.PropositionalEquality
      as PropEq
    open PropEq using (_≡_)

    begin_ : {x y : A} → x ~ y → x ~ y
    begin_ x~y = x~y
    infix 1 begin_

    _≡⟨⟩_ : (x : A) → {y : A} → x ≡ y → x ≡ y
    x ≡⟨⟩ p = p
    infixr 2 _≡⟨⟩_

    _≡⟨_⟩_ : (x : A) → ∀ {y z} → x ≡ y → y ~ z → x ~ z
    _ ≡⟨ PropEq.refl ⟩ y~z = y~z
    infixr 2 _≡⟨_⟩_

    _≈⟨_⟩_ : (x : A) → ∀ {y z} → x ~ y → y ~ z → x ~ z
    _ ≈⟨ x~y ⟩ y~z = trans x~y y~z
    infixr 2 _≈⟨_⟩_

  module ≤-Reasoning where
    import Data.Nat.Properties as ℕ
    ≤-preorder : IsPreorder (_≤_)
    IsPreorder.refl ≤-preorder = ℕ.≤-refl
    IsPreorder.trans ≤-preorder = ℕ.≤-trans

    open Reasoning ≤-preorder
      renaming (_≈⟨_⟩_ to _≤⟨_⟩_)
      public


open import Data.Nat
import Relation.Binary.PropositionalEquality
  as PropEq
open PropEq using (_≡_; module ≡-Reasoning; cong)

module ModularArithmetic where
  infix 4 _≈_⟨mod_⟩
  data _≈_⟨mod_⟩ (a b n : ℕ) : Set where
    ≈-mod
      : (x y : ℕ)
      → a + x * n ≡ b + y * n  -- ! 1
      → a ≈ b ⟨mod n ⟩

open ModularArithmetic

_ : 11 + 2 ≈ 1 ⟨mod 12 ⟩
_ = ≈-mod 0 1 PropEq.refl

module ℕ/nℕ (n : ℕ) where
  open Sandbox-Relations

  infix 4 _≈_
  _≈_ : Rel ℕ _
  _≈_ = _≈_⟨mod n ⟩

  private variable
    a b c d : ℕ


  ≈-refl : Reflexive _≈_
  ≈-refl = ≈-mod 0 0 PropEq.refl

  ≈-sym : Symmetric _≈_
  ≈-sym (≈-mod x y p) = ≈-mod y x (PropEq.sym p)

  open import Data.Nat.Solver

  ≈-trans : Transitive _≈_
  ≈-trans {a} {b} {c} (≈-mod x y pxy) (≈-mod z w pzw) =
    ≈-mod (x + z) (w + y) ( begin
      a + (x + z) * n      ≡⟨ lemma₁ ⟩
      (a + x * n) + z * n  ≡⟨ cong (_+ z * n) pxy ⟩
      (b + y * n) + z * n  ≡⟨ lemma₂ ⟩
      (b + z * n) + y * n  ≡⟨ cong (_+ y * n) pzw ⟩
      c + w * n + y * n    ≡⟨ lemma₃ ⟩
      c + (w + y) * n      ∎
    )
    where
      open ≡-Reasoning
      open +-*-Solver

      lemma₁ = solve 4
        (λ a n x z → a :+ (x :+ z) :* n
                  := (a :+ x :* n) :+ z :* n)
        PropEq.refl a n x z

      lemma₂ = solve 4
        (λ b n y z → (b :+ y :* n) :+ z :* n
                  := (b :+ z :* n) :+ y :* n)
        PropEq.refl b n y z

      lemma₃ = solve 4
        (λ c n w y → c :+ w :* n :+ y :* n
                  := c :+ (w :+ y) :* n)
        PropEq.refl c n w y

  ≈-equiv : IsEquivalence _≈_
  IsEquivalence.refl ≈-equiv = ≈-refl
  IsEquivalence.sym ≈-equiv = ≈-sym
  IsEquivalence.trans ≈-equiv = ≈-trans

  module ≈-Reasoning where
    ≈-preorder : IsPreorder _≈_
    IsPreorder.refl ≈-preorder = ≈-refl
    IsPreorder.trans ≈-preorder = ≈-trans

    open IsEquivalence ≈-equiv using (sym) public
    open Reasoning ≈-preorder public


  +-cong₂-mod : a ≈ b → c ≈ d → a + c ≈ b + d
  +-cong₂-mod {zero} {b} {c} {d} a=b c=d =
    begin
      zero + c
    ≡⟨ PropEq.refl ⟩
      c
    ≈⟨ c=d ⟩
      d
    ≈⟨ ? ⟩
      b + d
    ∎
    where open ≈-Reasoning
  +-cong₂-mod {suc a} {b} {c} {d} a=b c=d = {! !}




```
