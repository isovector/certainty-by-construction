# Program Optimization

Hidden

:   ```agda
{-# OPTIONS --allow-unsolved-metas #-}
    ```

```agda
module Chapter9-ProgramOptimization where
```

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
  using (_∘_; const; _≗_; prop-setoid; Setoid)
    ```

:   ```agda
open import Chapter8-Isomorphisms
  using (Iso; _↔_; ↔-refl; ↔-sym; ↔-trans; ⊎-fin; ⊎-setoid; ×-fin; ×-setoid; Vec; []; _∷_; lookup; Fin; zero; suc; _⊎_; inj₁; inj₂; _Has_Elements)
    ```

```agda
data Size : Set where
  num   : ℕ → Size
  plus  : Size → Size → Size
  times : Size → Size → Size

∣_∣ : Size → ℕ
∣ num  x      ∣ = x
∣ plus   x y  ∣ = ∣ x  ∣ +  ∣ y ∣
∣ times  x y  ∣ = ∣ x  ∣ *  ∣ y ∣


⌊_⌋ : Size → Set
⌊ num x      ⌋ = Fin x
⌊ times x y  ⌋ = ⌊ x ⌋ ×  ⌊ y ⌋
⌊ plus  x y  ⌋ = ⌊ x ⌋ ⊎  ⌊ y ⌋

Ix : Size → Set
Ix = ⌊_⌋

⌊⌋-setoid : Size → Setoid _ _
⌊⌋-setoid (num x) = prop-setoid (Fin x)
⌊⌋-setoid (plus m n) = ⊎-setoid (⌊⌋-setoid m) (⌊⌋-setoid n)
⌊⌋-setoid (times m n) = ×-setoid (⌊⌋-setoid m) (⌊⌋-setoid n)

size-fin : (sz : Size) → ⌊⌋-setoid sz Has ∣ sz ∣ Elements
size-fin (num x) = ↔-refl
size-fin (plus m n) = ⊎-fin (size-fin m) (size-fin n)
size-fin (times m n) = ×-fin (size-fin m) (size-fin n)

open import Data.Fin using (_≟_)

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

open import Relation.Nullary.Decidable.Core
  using (map′)
open import Data.Sum.Properties
  using (inj₁-injective; inj₂-injective)

⌊⌋dec : {sz : Size} → (ix₁ ix₂ : ⌊ sz ⌋) → Dec (ix₁ ≡ ix₂)
⌊⌋dec {num _} ix₁ ix₂ = ix₁ ≟ ix₂
⌊⌋dec {times _ _} (a₁ , b₁) (a₂ , b₂)
  with ⌊⌋dec a₁ a₂ | ⌊⌋dec b₁ b₂
... | yes refl | yes refl = yes refl
... | yes refl | no not-eq = no (not-eq ∘ cong proj₂)
... | no not-eq | yes refl = no (not-eq ∘ cong proj₁)
... | no not-eq | no _ = no (not-eq ∘ cong proj₁)
⌊⌋dec {plus _ _} (inj₁ x₁) (inj₁ x₂)
  = map′ (cong inj₁) inj₁-injective (⌊⌋dec x₁ x₂)
⌊⌋dec {plus _ _} (inj₁ x₁) (inj₂ y₂) = no λ ()
⌊⌋dec {plus _ _} (inj₂ y₁) (inj₁ x₂) = no λ ()
⌊⌋dec {plus _ _} (inj₂ y₁) (inj₂ y₂)
  = map′ (cong inj₂) inj₂-injective (⌊⌋dec y₁ y₂)


data Trie (B : Set ℓ) : Size → Set ℓ where
  miss  : {sz : Size} → Trie B sz
  table : {n : ℕ} → Vec B n → Trie B (num n)
  or    : {m n : Size} → Trie B m → Trie B n → Trie B (plus m n)
  and   : {m n : Size} → Trie (Trie B n) m → Trie B (times m n)


private variable
  B : Set ℓ
  sz m n : Size
  t₁ : Trie B m
  t₂ : Trie B n
  f : Ix sz → B

mutual
  MemoTrie : {B : Set ℓ} {sz : Size} → (Ix sz → B) → Set _
  MemoTrie {B = B} {sz = sz}  f = Σ (Trie B sz) (Memoizes f)

  data Memoizes {B : Set ℓ} : {sz : Size} → (f : Ix sz → B) → Trie B sz → Set ℓ where
    miss : {f : Ix sz → B}
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
      : {m n : Size}
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
  case ⌊⌋dec ix x of λ
    { (yes refl) → -, subtrmem
    ; (no z) → mts ix
    }
  ) refl

get′
  : {t : Trie B sz}
  → Memoizes f t
  → Ix sz
  → B × MemoTrie f
get′ {sz = num x} miss a =
  let t = _
   in lookup t a , table t , table
get′ {sz = plus m n} miss (inj₁ x)
  with get′ miss x
... | b , fst , snd = b , or fst miss , or snd miss
get′ {sz = plus m n} miss (inj₂ y)
  with get′ miss y
... | b , fst , snd = b , or miss fst , or miss snd
get′ {sz = times m n} {f = f} miss (x , y)
  with get′ { f = f ∘ (x ,_) } miss y
... | b , subtr , subtr-memo
  with get′ { f = const subtr } miss x
... | b2 , tr , tr-memo
    = b , subget-is-memo x subtr-memo λ { ix → -, miss }
get′ {sz = num _} {t = table t} table a = lookup t a , table t , table
get′ {sz = plus m n} (or l r) (inj₁ x)
  with get′ l x
... | b , fst , snd = b , or fst _ , or snd r
get′ {sz = plus m n} (or l r) (inj₂ y)
  with get′ r y
... | b , fst , snd = b , or _ fst , or l snd
get′ {sz = times m n} (and mts _) (x , y) with mts x
... | _ , subtrmem
  with get′ subtrmem y
... | b , _ , _ = b , subget-is-memo x subtrmem mts

get-is-fn : ∀ {sz : Size} {t} {f : Ix sz → B} → (mt : Memoizes f t) → proj₁ ∘ get′ mt ≗ f
get-is-fn {sz = num _}     miss x = lookup∘tabulate _ x
get-is-fn {sz = plus _ _}  miss (inj₁ x) = get-is-fn miss x
get-is-fn {sz = plus _ _}  miss (inj₂ y) = get-is-fn miss y
get-is-fn {sz = times _ _} miss (fst , snd) = get-is-fn miss snd
get-is-fn {sz = num _}     table x = lookup∘tabulate _ x
get-is-fn {sz = plus _ _}  (or mt mt₁) (inj₁ x) = get-is-fn mt x
get-is-fn {sz = plus _ _}  (or mt mt₁) (inj₂ y) = get-is-fn mt₁ y
get-is-fn {sz = times _ _} (and mts _) (fst , snd) = get-is-fn (proj₂ (mts fst)) snd

module _ {A : Set} (sz : Size) (sized : prop-setoid A Has ∣ sz ∣ Elements) (f : A → B) where
  postulate
    A↔Ix : prop-setoid A ↔ prop-setoid (Ix sz)

  f′ = f ∘ Iso.from (A↔Ix)

  get : MemoTrie f′ → A → B × MemoTrie f′
  get (_ , memo) = get′ memo ∘ (Iso.to A↔Ix)


----


--tsize : Size
--tsize = times (num 2) (plus (num 1) (num 1))

--tfun : ⌊ tsize ⌋ → ℕ
--tfun (Fin.zero , inj₁ x) = 1
--tfun (Fin.zero , inj₂ y) = 2
--tfun (Fin.suc Fin.zero , inj₁ x) = 3
--tfun (Fin.suc Fin.zero , inj₂ y) = 4


--test : Σ ℕ (λ x → Σ (Trie ℕ (times (num 2) (plus (num 1) (num 1)))) (Memoizes tfun))
--test = get′ miss (Fin.suc Fin.zero , inj₁ zero)

--test2 : proj₁ (proj₂ test) ≡ and (table (miss Vec.∷ or (table (3 Vec.∷ Vec.[])) miss Vec.∷ Vec.[]))
--test2 = refl
--```



