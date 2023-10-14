# Program Optimization

Hidden

:   ```agda
{-# OPTIONS --allow-unsolved-metas #-}
    ```

```agda
module Chapter9-ProgramOptimization where
```

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
  using (id; _∘_; const; _≗_; prop-setoid; Setoid)
    ```

:   ```agda
open import Chapter8-Isomorphisms
  using (Iso; _↔_; ↔-refl; ↔-sym; ↔-trans; ⊎-fin; ⊎-setoid; fin-iso; ×-fin; ×-setoid; Vec; []; _∷_; lookup; Fin; zero; suc; _⊎_; inj₁; inj₂; _Has_Elements)
    ```

```agda
data Shape : Set where
  num   : ℕ → Shape
  plus  : Shape → Shape → Shape
  times : Shape → Shape → Shape

∣_∣ : Shape → ℕ
∣ num  x      ∣ = x
∣ plus   x y  ∣ = ∣ x  ∣ +  ∣ y ∣
∣ times  x y  ∣ = ∣ x  ∣ *  ∣ y ∣


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
shape-fin (num x) = ↔-refl
shape-fin (plus m n) = ↔-trans (↔-sym ⊎-prop-homo) (⊎-fin (shape-fin m) (shape-fin n))
shape-fin (times m n) = ↔-trans (↔-sym ×-prop-homo) (×-fin (shape-fin m) (shape-fin n))

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
  MemoTrie {B = B} {sh = sh}  f = Σ (Trie B sh) (Memoizes f)

  data Memoizes {B : Set ℓ} : {sh : Shape} → (f : Ix sh → B) → Trie B sh → Set ℓ where
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

get-is-fn : ∀ {sh : Shape} {t} {f : Ix sh → B} → (mt : Memoizes f t) → proj₁ ∘ get′ mt ≗ f
get-is-fn {sh = num _}     miss x = lookup∘tabulate _ x
get-is-fn {sh = plus _ _}  miss (inj₁ x) = get-is-fn miss x
get-is-fn {sh = plus _ _}  miss (inj₂ y) = get-is-fn miss y
get-is-fn {sh = times _ _} miss (fst , snd) = get-is-fn miss snd
get-is-fn {sh = num _}     table x = lookup∘tabulate _ x
get-is-fn {sh = plus _ _}  (or mt mt₁) (inj₁ x) = get-is-fn mt x
get-is-fn {sh = plus _ _}  (or mt mt₁) (inj₂ y) = get-is-fn mt₁ y
get-is-fn {sh = times _ _} (and mts _) (fst , snd) = get-is-fn (proj₂ (mts fst)) snd

module _ {A : Set} (sh : Shape) (sized : prop-setoid A Has ∣ sh ∣ Elements) (f : A → B) where
  A↔Ix : prop-setoid A ↔ prop-setoid (Ix sh)
  A↔Ix = fin-iso sized (shape-fin sh)

  f′ = f ∘ Iso.from (A↔Ix)

  get : MemoTrie f′ → A → B × MemoTrie f′
  get (_ , memo) = get′ memo ∘ (Iso.to A↔Ix)


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



