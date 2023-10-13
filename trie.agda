module trie where

open import Data.Nat using (ℕ; _+_; _*_)

data Size : Set where
  num   : ℕ → Size
  plus  : Size → Size → Size
  times : Size → Size → Size

∣_∣ : Size → ℕ
∣ num  x      ∣ = x
∣ plus   x y  ∣ = ∣ x  ∣ +  ∣ y ∣
∣ times  x y  ∣ = ∣ x  ∣ *  ∣ y ∣

open import Function using (case_of_)
open import Data.Fin using (Fin; _≟_; zero)
open import Data.Product
open import Data.Sum

open import Agda.Primitive
  using (Level; lsuc; _⊔_)

private variable
  c₁ c₂ c ℓ ℓ₁ ℓ₂ : Level

open import Relation.Binary.PropositionalEquality

⌊_⌋ : Size → Set
⌊ num x      ⌋ = Fin x
⌊ times x y  ⌋ = ⌊ x ⌋ ×  ⌊ y ⌋
⌊ plus  x y  ⌋ = ⌊ x ⌋ ⊎  ⌊ y ⌋

open import Data.Vec using (Vec; lookup; tabulate)
open import Relation.Nullary
open import Relation.Unary hiding (⌊_⌋; _∈_)

open import Function using (_∘_; const)
open import Relation.Nullary.Decidable.Core using (map′)
open import Data.Sum.Properties

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


open import Data.Vec.Properties using (lookup∘tabulate)

data Trie (B : Set ℓ) : Size → Set ℓ where
  miss  : {sz : Size} → Trie B sz
  table : {n : ℕ} → Vec B n → Trie B (num n)
  or    : {m n : Size} → Trie B m → Trie B n → Trie B (plus m n)
  and   : {m n : Size} → Trie (Trie B n) m → Trie B (times m n)

mutual
  data Memoizes {B : Set ℓ} : {sz : Size} → (f : ⌊ sz ⌋ → B) → Trie B sz → Set ℓ where
    miss : ∀ {sz} {f : ⌊ sz ⌋ → B}
         → Memoizes f miss
    table : ∀ {n} {f : ⌊ num n ⌋ → B}
          → Memoizes f (table (tabulate f))
    or : ∀ {m n t₁ t₂} {f : ⌊ plus m n ⌋ → B}
      → Memoizes (f ∘ inj₁) t₁
      → Memoizes (f ∘ inj₂) t₂
      → Memoizes f (or t₁ t₂)
    and : ∀ {m n} {f : ⌊ times m n ⌋ → B} {t}
        → (f2 : (ix : ⌊ m ⌋) → Σ (Trie B n) (Memoizes (f ∘ (ix ,_))))
        → t ≡ proj₁ (to-trie {f = f} f2)
        → Memoizes f (and t)

  to-trie
      : {B : Set ℓ} {m n : Size}
      → {f : ⌊ times m n ⌋ → B}
      → (f2 : (ix : ⌊ m ⌋) → Σ (Trie B n) (Memoizes (f ∘ (ix ,_))))
      → Σ (Trie (Trie B n) m) (Memoizes (proj₁ ∘ f2))
  to-trie {m = num x} f2 = -, table
  to-trie {m = plus m m₁} f2
    with to-trie (f2 ∘ inj₁) | to-trie (f2 ∘ inj₂)
  ... | t₁ , mt₁ | t₂ , mt₂ = -, or mt₁ mt₂
  to-trie {m = times m m₁} f2 = -, and (λ i → to-trie λ j → f2 (i , j)) refl


subget-is-memo
  : ∀ {B : Set ℓ} {m n} {f : ⌊ times m n ⌋ → B} {fst : Trie B n}
  → (x : ⌊ m ⌋)
  → Memoizes (f ∘ (x ,_)) fst
  → ((ix : ⌊ m ⌋) → Σ (Trie B n) (Memoizes (f ∘ (ix ,_))))
  → Σ (Trie B (times m n)) (Memoizes f)
subget-is-memo x subtrmem mts = -, and (λ ix →
  case ⌊⌋dec ix x of λ
    { (yes refl) → -, subtrmem
    ; (no z) → mts ix
    }
  ) refl

get
  : {B : Set ℓ} (sz : Size) {f : ⌊ sz ⌋ → B} {t : Trie B sz}
  → Memoizes f t
  → (a : ⌊ sz ⌋)
  → B × Σ (Trie B sz) (Memoizes f)
get (num x) miss a =
  let t = _
   in lookup t a , table t , table
get (plus m n) miss (inj₁ x)
  with get m miss x
... | b , fst , snd = b , or fst miss , or snd miss
get (plus m n) miss (inj₂ y)
  with get n miss y
... | b , fst , snd = b , or miss fst , or miss snd
get (times m n) {f} miss (x , y)
  with get n { f = f ∘ (x ,_) } miss y
... | b , subtr , subtr-memo
  with get m { f = const subtr } miss x
... | b2 , tr , tr-memo
    = b , subget-is-memo x subtr-memo λ { ix → -, miss }
get .(num _) {t = table t} table a = lookup t a , table t , table
get (plus m n) (or l r) (inj₁ x)
  with get m l x
... | b , fst , snd = b , or fst _ , or snd r
get (plus m n) (or l r) (inj₂ y)
  with get n r y
... | b , fst , snd = b , or _ fst , or l snd
get (times m n) (and mts _) (x , y) with mts x
... | _ , subtrmem
  with get n subtrmem y
... | b , _ , _ = b , subget-is-memo x subtrmem mts


get-is-fn : ∀ {sz : Size} {ℓ₂} {B : Set ℓ₂} {t} {f : ⌊ sz ⌋  → B} → (mt : Memoizes f t) → proj₁ ∘ get sz mt ≗ f
get-is-fn {num _}     miss x = lookup∘tabulate _ x
get-is-fn {plus _ _}  miss (inj₁ x) = get-is-fn miss x
get-is-fn {plus _ _}  miss (inj₂ y) = get-is-fn miss y
get-is-fn {times _ _} miss (fst , snd) = get-is-fn miss snd
get-is-fn {num _}     table x = lookup∘tabulate _ x
get-is-fn {plus _ _}  (or mt mt₁) (inj₁ x) = get-is-fn mt x
get-is-fn {plus _ _}  (or mt mt₁) (inj₂ y) = get-is-fn mt₁ y
get-is-fn {times _ _} (and mts _) (fst , snd) = get-is-fn (proj₂ (mts fst)) snd


--


tsize : Size
tsize = times (num 2) (plus (num 1) (num 1))

tfun : ⌊ tsize ⌋ → ℕ
tfun (Fin.zero , inj₁ x) = 1
tfun (Fin.zero , inj₂ y) = 2
tfun (Fin.suc Fin.zero , inj₁ x) = 3
tfun (Fin.suc Fin.zero , inj₂ y) = 4


test : Σ ℕ (λ x → Σ (Trie ℕ (times (num 2) (plus (num 1) (num 1)))) (Memoizes tfun))
test = get tsize (miss {f = tfun}) (Fin.suc Fin.zero , inj₁ zero)

test2 : proj₁ (proj₂ test) ≡ and (table (miss Vec.∷ or (table (3 Vec.∷ Vec.[])) miss Vec.∷ Vec.[]))
test2 = refl

