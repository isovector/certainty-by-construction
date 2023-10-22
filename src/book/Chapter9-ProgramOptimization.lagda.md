# Program Optimization

Hidden

:   ```agda
{-# OPTIONS --allow-unsolved-metas #-}
    ```

```agda
module Chapter9-ProgramOptimization where
```

The purpose of theory is not satisfying idle curiosities; instead it is to make
short work of otherwise difficult problems. In this final chapter, we will turn
our gaze towards a difficult problem in computing---dynamic programming---and
see how our new theoretical understanding completely eliminates the challenges.
Since dynamic programming often improves algorithmic complexity asymptotically,
solving it is therefore equivalent to program optimization, and doing it
automatically demonstrates a total understanding of the problem space.

As is fitting for a capstone, this chapter has a great number of dependencies in
concepts:

Prerequisites

:   ```agda
open import Chapter1-Agda
  using (_×_; _,_; proj₁; proj₂)
    ```

:   ```agda
open import Chapter2-Numbers
  using (ℕ; zero; suc; _+_; _*_)
    ```

:   ```agda
open import Chapter3-Proofs
  using (_≡_; case_of_; module PropEq)
open PropEq
  using (refl; cong)
    ```

:   ```agda
open import Chapter4-Relations
  using (Level; _⊔_; lsuc; Σ)
    ```

:   ```agda
open import Chapter6-Decidability
  using (Dec; yes; no)
    ```

:   ```agda
open import Chapter7-Structures
  using (id; _∘_; const; _≗_; prop-setoid; Setoid; ⊎-setoid; ×-setoid)
    ```

:   ```agda
open import Chapter8-Isomorphisms
  using ( Iso; _≅_; ≅-refl; ≅-sym; ≅-trans; ⊎-fin; fin-iso; ×-fin
        ; Vec; []; _∷_; lookup; Fin; zero; suc; _⊎_; inj₁; inj₂
        ; _Has_Elements; ⊎-prop-homo; ×-prop-homo)
    ```


## Why Can This Be Done?

Computing is a practical means to an end. One of the greatest tragedies in our
field is the muddled thinking that arises from conflating "what do we want to do"
from "how should we do it." But confusion exists only in our minds, and never in
reality. Because dynamic programming is an often-confusing solution to a class
of problems, we will likely learn more by studying the class of problems than we
will the offered solution.

Dynamic programming is helpful for problems with a great deal of overlapping
subproblems. This notion of subproblems arises from the algorithmic concept of
*divide and conquer,* which you will note is also muddled thinking---it too
confuses the question with a means of answering it.

At the end of the day, all computing reduces down to sampling functions at
finitely many points. Seen through this lens, dynamic programming is a technique
which makes functions less expensive to repeatedly sample, by caching their
results somewhere convenient.

This is the true nature of dynamic programming---as a technique, it is nothing
more than thinking about problems inductively, and memoizing that induction. By
virtue of being the sort of person who would read this book, you are clearly
already capable of thinking compositionally, and so all we have left is to
tackle the problem of memoization.

Why should we expect to be able to make progress on this problem? As seen in
@sec:exponents, we proved an isomorphism between functions on finite domains and
vectors. Indeed, it is exactly this vector which is most-often used as a caching
data structure when doing dynamic programming by hand. Figuring out exactly how
to index such a structure is often less clear and requires much fiddling in the
absence of explicit isomorphisms.

Note however that an effective memoization strategy is dependent on the problem.
This "one big vector" isn't necessarily always the best choice. If you know that
you need to sample the entire function space, you might as well just sample the
whole function into a table. But if sampling the function is sufficiently
expensive and you have no guarantee you'll need all of its image, you might
prefer to memoize the function at only those points necessary.

For functions with large input spaces, it would be quite wasteful to allocate a
table large enough to memoize the whole function, and proceed to only cache a
handful of points in it. Therefore, we conclude that different memoization
strategies must result in different caching data structures. And in fact, this
class of memoization strategies grows *fast*---corresponding to every possible
way of splitting the input space into contiguous chunks. Some examples of
different memoization strategies for a function with 8 points are visualized in
@fig:t8, @fig:t8by1, @fig:2x2x2, and @fig:complex, to give you a taste of how
these data structures could look.

-- TODO(sandy): remove mention of figures


There is no one-size-fits-all memoization strategy, so our eventual solution to
this problem must be polymorphic over all possible strategies.

~~~~ {design=code/Languages/Tree.hs label="Table of Pointers to Values" #fig:t8by1}
And 8 (Table 1)
~~~~

~~~~ {design=code/Languages/Tree.hs label="Binary Tree" #fig:2x2x2}
Or (Or (Or (Table 1) (Table 1)) (Or (Table 1) (Table 1))) (Or (Or (Table 1) (Table 1)) (Or (Table 1) (Table 1)))
~~~~

~~~~ {design=code/Languages/Tree.hs label="Something More Complicated" #fig:complex}
Or (Or (Table 3) (And 2 (Table 1))) (And 3 (Table 1))
~~~~

It certainly feels like we have our work cut out for us, doesn't it? Thankfully,
the task is less monumental than it seems. The hardest part is simply organizing
the problem, and our theory will guide us the rest of the way.


## Shaping the Cache

Our first order of business is to find a means of describing our desired
memoization strategy, which in turn means to find a way of describing the data
type we will use to cache results.

Note that while there are many variations on the theme, we are looking for the
*building blocks* of these cache shapes. It is undeniable that we must be able to
support a flat vector of contiguous results. Another means of building caching
structures is to combine two *different* shapes together. And our final means is
direct composition---that is, we'd like to nest one memoization strategy inside
another. In essence, this composition means we are no longer caching values, but
instead caching *caches of values.*

Rather surprisingly, these are all the shape combinators we need in order to
build any cache we'd like. We'll see some more examples soon, but in the
meantime, we can write `type:Shape` in Agda:

```agda
data Shape : Set where
  num    : ℕ → Shape
  plus   : Shape → Shape → Shape
  times  : Shape → Shape → Shape
-- FIX
```

The names of these constructors, while not what we'd expect, are certainly
suggestive. Nevertheless `bind:n:num n` corresponds to a table of `n` elements.
We will use `ctor:plus` to combine two caches "side by side", while `ctor:times`
will describe composing one cache inside of another. To get a feel for how
`type:Shape` describes data structures, let's look at a few examples.

The simplest cache imaginable is just a vector, which we can represent via
`ctor:num`. In @fig:t8 we see what a table of 8 elements looks like, noting that
the filled squares represent places to cache results.

~~~~ {design=code/Languages/Tree.hs label="A cache described by `expr:num 8`" #fig:t8}
Table 8
~~~~




```agda
∣_∣ : Shape → ℕ
∣ num    m    ∣ = m
∣ plus   m n  ∣ = ∣ m  ∣ +  ∣ n ∣
∣ times  m n  ∣ = ∣ m  ∣ *  ∣ n ∣


Ix : Shape → Set
Ix (num n)      = Fin n
Ix (times m n)  = Ix m × Ix n
Ix (plus  m n)  = Ix m ⊎ Ix n

open import Relation.Nullary.Decidable.Core
  using (map′)
open import Data.Fin using (_≟_)
open import Data.Sum.Properties
  using (inj₁-injective; inj₂-injective)

Ix-dec : {sh : Shape} → (ix₁ ix₂ : Ix sh) → Dec (ix₁ ≡ ix₂)
Ix-dec {num _} ix₁ ix₂ = ix₁ ≟ ix₂
Ix-dec {times _ _} (a₁ , b₁) (a₂ , b₂)
  with Ix-dec a₁ a₂ | Ix-dec b₁ b₂
... | yes refl | yes refl = yes refl
... | yes refl | no not-eq = no (not-eq ∘ cong proj₂)
... | no not-eq | yes refl = no (not-eq ∘ cong proj₁)
... | no not-eq | no _ = no (not-eq ∘ cong proj₁)
Ix-dec {plus _ _} (inj₁ x₁) (inj₁ x₂)
  = map′ (cong inj₁) inj₁-injective (Ix-dec x₁ x₂)
Ix-dec {plus _ _} (inj₁ x₁) (inj₂ y₂) = no λ ()
Ix-dec {plus _ _} (inj₂ y₁) (inj₁ x₂) = no λ ()
Ix-dec {plus _ _} (inj₂ y₁) (inj₂ y₂)
  = map′ (cong inj₂) inj₂-injective (Ix-dec y₁ y₂)

open Iso
  using (to; from; from∘to; to∘from; to-cong; from-cong)

shape-fin : (sh : Shape) → prop-setoid (Ix sh) Has ∣ sh ∣ Elements
shape-fin (num x)      = ≅-refl
shape-fin (plus m n)   = ≅-trans  (≅-sym ⊎-prop-homo)
                                  (⊎-fin (shape-fin m) (shape-fin n))
shape-fin (times m n)  = ≅-trans  (≅-sym ×-prop-homo)
                                  (×-fin (shape-fin m) (shape-fin n))

private variable
  ℓ ℓ₁ ℓ₂ : Level


-,_ : {A : Set ℓ₁} → {a : A} → {B : A → Set ℓ₂} → B a → Σ A B
-,_ {a = a} b = a , b

tabulate : {n : ℕ} {A : Set ℓ} → (Fin n → A) → Vec A n
tabulate {n = zero}   f = []
tabulate {n = suc n}  f = f zero ∷ tabulate (f ∘ suc)

lookup∘tabulate
  : {n : ℕ} {A : Set ℓ}
  → (f : Fin n → A)
  → (i : Fin n)
  → lookup (tabulate f) i ≡ f i
lookup∘tabulate f zero    = refl
lookup∘tabulate f (suc i) = lookup∘tabulate (f ∘ suc) i


data Trie (B : Set ℓ) : Shape → Set ℓ where
  miss  : {sh : Shape} → Trie B sh
  table : {n : ℕ} → Vec B n → Trie B (num n)
  or    : {m n : Shape} → Trie B m → Trie B n → Trie B (plus m n)
  and   : {m n : Shape} → Trie (Trie B n) m → Trie B (times m n)


private variable
  B : Set ℓ
  sh m n : Shape
  t₁ : Trie B m
  t₂ : Trie B n
  f : Ix sh → B

mutual
  MemoTrie : {B : Set ℓ} {sh : Shape} → (Ix sh → B) → Set _
  MemoTrie {B = B} {sh = sh} f = Σ (Trie B sh) (Memoizes f)

  data Memoizes {B : Set ℓ}  : {sh : Shape}
                             → (f : Ix sh → B)
                             → Trie B sh
                             → Set ℓ where
    miss : {f : Ix sh → B}
         → Memoizes f miss
    table : {n : ℕ} {f : Ix (num n) → B}
          → Memoizes f (table (tabulate f))
    or : {f : Ix (plus m n) → B}
      → Memoizes (f ∘ inj₁) t₁
      → Memoizes (f ∘ inj₂) t₂
      → Memoizes f (or t₁ t₂)
    and : {f : Ix (times m n) → B}
          {t : Trie (Trie B n) m}
        → (f2 : (ix : Ix m) → MemoTrie (f ∘ (ix ,_)))
        → t ≡ proj₁ (to-trie {f = f} f2)
        → Memoizes f (and t)

  to-trie
      : {m n : Shape}
      → {f : Ix (times m n) → B}
      → (f2 : (ix : Ix m) → Σ (Trie B n) (Memoizes (f ∘ (ix ,_))))
      → MemoTrie (proj₁ ∘ f2)
  to-trie {m = num x} f2 = -, table
  to-trie {m = plus m m₁} f2
    with to-trie (f2 ∘ inj₁) | to-trie (f2 ∘ inj₂)
  ... | t₁ , mt₁ | t₂ , mt₂ = -, or mt₁ mt₂
  to-trie {m = times m m₁} f2 = -, and (λ i → to-trie λ j → f2 (i , j)) refl


subget-is-memo
  : {fst : Trie B n}
  → (x : Ix m)
  → Memoizes (f ∘ (x ,_)) fst
  → ((ix : Ix m) → MemoTrie (f ∘ (ix ,_)))
  → MemoTrie f
subget-is-memo x subtrmem mts = -, and (λ ix →
  case Ix-dec ix x of λ
    { (yes refl) → -, subtrmem
    ; (no z) → mts ix
    }
  ) refl

get′
  : {t : Trie B sh}
  → Memoizes f t
  → Ix sh
  → B × MemoTrie f
get′ {sh = num x} miss a =
  let t = _
   in lookup t a , table t , table
get′ {sh = plus m n} miss (inj₁ x)
  with get′ miss x
... | b , fst , snd = b , or fst miss , or snd miss
get′ {sh = plus m n} miss (inj₂ y)
  with get′ miss y
... | b , fst , snd = b , or miss fst , or miss snd
get′ {sh = times m n} {f = f} miss (x , y)
  with get′ { f = f ∘ (x ,_) } miss y
... | b , subtr , subtr-memo
  with get′ { f = const subtr } miss x
... | b2 , tr , tr-memo
    = b , subget-is-memo x subtr-memo λ { ix → -, miss }
get′ {sh = num _} {t = table t} table a = lookup t a , table t , table
get′ {sh = plus m n} (or l r) (inj₁ x)
  with get′ l x
... | b , fst , snd = b , or fst _ , or snd r
get′ {sh = plus m n} (or l r) (inj₂ y)
  with get′ r y
... | b , fst , snd = b , or _ fst , or l snd
get′ {sh = times m n} (and mts _) (x , y) with mts x
... | _ , subtrmem
  with get′ subtrmem y
... | b , _ , _ = b , subget-is-memo x subtrmem mts

get′-is-fn
    : {sh : Shape} {t : Trie B sh} {f : Ix sh → B}
    → (mt : Memoizes f t)
    → proj₁ ∘ get′ mt ≗ f
get′-is-fn {sh = num _}     miss x         = lookup∘tabulate _ x
get′-is-fn {sh = plus _ _}  miss (inj₁ x)  = get′-is-fn miss x
get′-is-fn {sh = plus _ _}  miss (inj₂ y)  = get′-is-fn miss y
get′-is-fn {sh = times _ _} miss (x , y)   = get′-is-fn miss y
get′-is-fn {sh = num _}     table x        = lookup∘tabulate _ x
get′-is-fn {sh = plus _ _}  (or mt mt₁) (inj₁ x)  = get′-is-fn mt x
get′-is-fn {sh = plus _ _}  (or mt mt₁) (inj₂ y)  = get′-is-fn mt₁ y
get′-is-fn {sh = times _ _} (and mts _) (x , y)   = get′-is-fn (proj₂ (mts x)) y

module _ {A : Set} (sh : Shape) (sized : prop-setoid A Has ∣ sh ∣ Elements) (f : A → B) where
  A≅Ix : prop-setoid A ≅ prop-setoid (Ix sh)
  A≅Ix = fin-iso sized (shape-fin sh)

  f′ = f ∘ Iso.from (A≅Ix)

  get : MemoTrie f′ → A → B × MemoTrie f′
  get (_ , memo) = get′ memo ∘ (Iso.to A≅Ix)


----


tsize : Shape
tsize = times (num 2) (plus (num 1) (num 1))

--tfun : ⌊ tsize ⌋ → ℕ
--tfun (Fin.zero , inj₁ x) = 1
--tfun (Fin.zero , inj₂ y) = 2
--tfun (Fin.suc Fin.zero , inj₁ x) = 3
--tfun (Fin.suc Fin.zero , inj₂ y) = 4


--test : Σ ℕ (λ x → Σ (Trie ℕ (times (num 2) (plus (num 1) (num 1)))) (Memoizes tfun))
--test = get′ miss (Fin.suc Fin.zero , inj₁ zero)

--test2 : proj₁ (proj₂ test) ≡ and (table (miss Vec.∷ or (table (3 Vec.∷ Vec.[])) miss Vec.∷ Vec.[]))
--test2 = refl

```



