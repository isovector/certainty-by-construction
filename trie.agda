module trie where

open import Data.Nat using (ℕ; _+_; _*_)

data Size : Set where
  num   : ℕ → Size
  times : Size → Size → Size
  plus  : Size → Size → Size

∣_∣ : Size → ℕ
∣ num  x      ∣ = x
∣ times  x y  ∣ = ∣ x  ∣ *  ∣ y ∣
∣ plus   x y  ∣ = ∣ x  ∣ +  ∣ y ∣

open import Data.Fin
open import Data.Product
  renaming (map to ×map)
open import Data.Sum hiding (map; map₂)

open import Relation.Binary
open import Level

private variable
  c₁ c₂ c ℓ ℓ₁ ℓ₂ : Level

record Iso
      (s₁ : Setoid c₁ ℓ₁)
      (s₂ : Setoid c₂ ℓ₂)
      : Set (c₁ ⊔ c₂ ⊔ ℓ₁ ⊔ ℓ₂) where
  constructor iso

  open Setoid s₁ using ()
      renaming (Carrier to A; _≈_ to _≈₁_)
      public
  open Setoid s₂ using ()
      renaming (Carrier to B; _≈_ to _≈₂_)
      public

  field
    to   : A → B
    from : B → A
    from∘to  : (x : A) → from (to x) ≈₁ x
    to∘from  : (x : B) → to (from x) ≈₂ x
    to-cong    : {x y : A} → x ≈₁ y → to x ≈₂ to y
    from-cong  : {x y : B} → x ≈₂ y → from x ≈₁ from y

open Iso

private variable
  c₃ ℓ₃ : Level
  s₁ : Setoid c₁ ℓ₁
  s₂ : Setoid c₂ ℓ₂
  s₃ : Setoid c₃ ℓ₃

postulate
  ↔-sym : Iso s₁ s₂ → Iso s₂ s₁
  ↔-trans : Iso s₁ s₂ → Iso s₂ s₃ → Iso s₁ s₃


open import Relation.Binary.PropositionalEquality
  renaming (setoid to prop-setoid)
  hiding ([_])

_Has_Elements : Setoid c₁ ℓ₁ → ℕ → Set (c₁ ⊔ ℓ₁)
s Has cardinality Elements = Iso s (prop-setoid (Fin cardinality))

⌊_⌋ : Size → Set
⌊ num x      ⌋ = Fin x
⌊ times x y  ⌋ = ⌊ x ⌋ ×  ⌊ y ⌋
⌊ plus  x y  ⌋ = ⌊ x ⌋ ⊎  ⌊ y ⌋

postulate
  size-fin : (s : Size) → prop-setoid ⌊ s ⌋ Has ∣ s ∣ Elements

open import Data.Vec using (Vec; lookup; tabulate; _[_]≔_; replicate)
open import Relation.Nullary
open import Relation.Unary hiding (⌊_⌋; _∈_)

open import Function using (flip; _∘_; const; id)
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


open import Data.Maybe
open import Data.Vec.Properties

module Trie where

  data Trie (B : Set ℓ) : Size → Set ℓ where
    miss  : {sz : Size} → Trie B sz
    table : {sz : Size} → Vec B ∣ sz ∣ → Trie B sz
    or    : {m n : Size} → Trie B m → Trie B n → Trie B (plus m n)
    and   : {m n : Size} → Trie (Trie B n) m → Trie B (times m n)

  private variable
    sz m n : Size
    X : Set ℓ
    tr₁ : Trie X m
    tr₂ : Trie X n
    b : X
    ix ix₁ ix₂ : X


  data _∈_ {B : Set ℓ}
      : {sz : Size}
      → ⌊ sz ⌋ × B
      → Trie B sz
      → Set ℓ
      where
    tabled
      : ∀ {t}
      → lookup t (to (size-fin sz) ix) ≡ b
      → (ix , b) ∈ table t
    inj₁
      : (ix , b) ∈ tr₁
      → (inj₁ ix , b) ∈ or tr₁ tr₂
    inj₂
      : (ix , b) ∈ tr₂
      → (inj₂ ix , b) ∈ or tr₁ tr₂
    both
      : (ix₂ , b)   ∈ tr₂
      → (ix₁ , tr₂) ∈ tr₁
      → ((ix₁ , ix₂) , b) ∈ and tr₁

  theb : ∀ {B : Set ℓ} {sz : Size} {t : Trie B sz} {a : ⌊ sz ⌋} {b : B} → (a , b) ∈ t → B
  theb {b = b} _ = b

  same
    : {B : Set ℓ} {sz : Size} {t : Trie B sz}
    → {a : ⌊ sz ⌋} {b₁ b₂ : B}
    → (a , b₁) ∈ t
    → (a , b₂) ∈ t
    → b₁ ≡ b₂
  same (tabled x) (tabled y)
    rewrite x = y
  same (inj₁ p₁) (inj₁ p₂) = same p₁ p₂
  same (inj₂ p₁) (inj₂ p₂) = same p₁ p₂
  same (both p₁ p₃) (both p₂ p₄)
    rewrite same p₃ p₄ = same p₁ p₂

  mtlookup
    : {B : Set ℓ} {sz : Size}
    → (tr : Trie B sz)
    → (a : ⌊ sz ⌋)
    → Dec (Σ B (λ b → (a , b) ∈ tr))
  mtlookup miss a = no λ ()
  mtlookup {sz = sz} (table x) a
    = yes (lookup x (to (size-fin sz) a) , tabled refl)
  mtlookup (or tr₁ tr₂) (inj₁ x)
    = map′ (map₂ inj₁) (λ { (b , inj₁ p) → b , p }) (mtlookup tr₁ x)
  mtlookup (or tr₁ tr₂) (inj₂ y)
    = map′ (map₂ inj₂) (λ { (b , inj₂ p) → b , p }) (mtlookup tr₂ y)
  mtlookup (and tr) (fst , snd)
    with mtlookup tr fst
  ... | no not-in = no λ { (fst , both snd snd₁) → not-in (_ , snd₁) }
  ... | yes (t , mt∈tr) =
    map′
      (map₂ λ nb∈t → both nb∈t mt∈tr)
      (λ { (b , both tr′ mb∈tr′)
        → b
        , subst (λ φ → _ ∈ φ) (same mb∈tr′ mt∈tr) tr′ })
      (mtlookup t snd)

  undec : {P : Set ℓ₁} {R : Set ℓ₂} → (P → R) → (¬ P → R) → Dec P → R
  undec to ¬to = [ to , ¬to ] ∘ fromDec

  insert
    : {B : Set ℓ} {sz : Size}
    → Trie B sz
    → (a : ⌊ sz ⌋) → (f : ⌊ sz ⌋ → B)
    → Σ (Trie B sz) (λ t → (a , f a) ∈ t)
  insert {sz = sz} miss a f =
    let s   = size-fin sz
        f′  = f ∘ from s in
    table (tabulate f′) , tabled (begin
      lookup (tabulate f′) (to s a)  ≡⟨ lookup∘tabulate f′ _ ⟩
      f (from s (to s a))            ≡⟨ cong f (from∘to s a) ⟩
      f a                            ∎
    )
    where open ≡-Reasoning
  insert {sz = sz} (table t) a f =
    let ix = to (size-fin sz) a in
    table (t [ ix ]≔ f a) , tabled (lookup∘updateAt ix t)
  insert (or tr₁ tr₂) (inj₁ x) f
    = ×map (flip or tr₂) inj₁ (insert tr₁ x (f ∘ inj₁))
  insert (or tr₁ tr₂) (inj₂ y) f
    = ×map (or tr₁) inj₂ (insert tr₂ y (f ∘ inj₂))
  insert {sz = times m n} (and tr₁) (x , y) f
    with insert
          (undec proj₁ (const miss) (mtlookup tr₁ x))
          y
          (f ∘ (x ,_))
  ... | (tr₂ , fxy∈tr₂)
      = ×map and (both fxy∈tr₂) (insert tr₁ x (const tr₂))

  insert-ok
    : {B : Set ℓ} {sz : Size}
    → {t : Trie B sz}
    → {a a′ : ⌊ sz ⌋} → {f : ⌊ sz ⌋ → B}
    → a ≢ a′
    → (a , f a) ∈ t
    → (a , f a) ∈ proj₁ (insert t a′ f)
  insert-ok {sz = sz} {t = table t} {a} {a′} {f} a≢a′ (tabled a∈t) = tabled (
    let
      ixa = to (size-fin sz) a
      ixa′ = to (size-fin sz) a′
    in
    begin
      lookup (t [ ixa′ ]≔ f a′) (to (size-fin sz) a)
    ≡⟨ lookup∘updateAt′ ixa ixa′ (a≢a′ ∘ {! !}) t ⟩
      lookup t (to (size-fin sz) a)
    ≡⟨ a∈t ⟩
      f a
    ∎
    )
    where open ≡-Reasoning
  insert-ok {t = or _ _} {inj₁ _} {inj₁ x} a≢a′ (inj₁ a∈t) =
    inj₁ (insert-ok (a≢a′ ∘ cong inj₁) a∈t)
  insert-ok {t = or _ _} {inj₁ _} {inj₂ y} a≢a′ (inj₁ a∈t) =
    inj₁ a∈t
  insert-ok {t = or _ _} {inj₂ _} {inj₁ x} a≢a′ (inj₂ a∈t) =
    inj₂ a∈t
  insert-ok {t = or _ _} {inj₂ _} {inj₂ y} a≢a′ (inj₂ a∈t) =
    inj₂ (insert-ok (a≢a′ ∘ cong inj₂) a∈t)
  insert-ok {t = and t} {fst , snd} {fst₁ , snd₁} a≢a′ (both a∈t a∈t₁) = {! !}


record MemoTrie {A : Set ℓ₁} {B : Set ℓ₂} (f : A → B) : Set (ℓ₁ ⊔ ℓ₂) where
  field
    factoring : Size
    a-fin : prop-setoid A Has ∣ factoring ∣ Elements
    trie : Trie.Trie B factoring

  a↔sz : Iso (prop-setoid A) (prop-setoid ⌊ factoring ⌋)
  a↔sz = ↔-trans a-fin (↔-sym (size-fin factoring))

  field
    actually-in : ∀ a b → (a , b) Trie.∈ trie → b ≡ f (from a↔sz a)


open MemoTrie
open Function using (case_of_)


get : ∀ {A : Set ℓ₁} {B : Set ℓ₂} {f : A → B} → MemoTrie f → A → MemoTrie f × B
get {f = f} mt a
  with Trie.mtlookup (trie mt) (to (a↔sz mt) a)
... | yes (b , _) = mt , b
... | no not-in
  with Trie.insert (trie mt) (to (a↔sz mt) a) (f ∘ from (a↔sz mt)) in eq
... | tr′ , b∈tr′ = record
  { MemoTrie mt
  ; trie = tr′
  ; actually-in =
      -- whats the proof here?
      -- we want to show it wasn't already in here
      -- and then extend the env with this
      λ { a′ b a′b∈tr′ →
          -- check if the index is the one we just inserted
          let a≟a′ = ⌊⌋dec (to (a↔sz mt) a) a′
           in case a≟a′ of λ
                -- if yes, we can show we just inserted it
                { (yes a≡a′) →
                     Trie.same (subst (λ φ → (φ , b) Trie.∈ _) (sym a≡a′) a′b∈tr′)
                               (subst (λ φ → (_ , f (from (a↔sz mt) φ)) Trie.∈ tr′) a≡a′ b∈tr′)

                -- if not, we can show it was already in there
                ; (no a≢a′) →
                    let eq′ = sym (cong proj₁ eq) in {! !}
                }
        }
  } , Trie.theb b∈tr′

get-is-fn : ∀ {A : Set ℓ₁} {B : Set ℓ₂} {f : A → B} → (mt : MemoTrie f) → proj₂ ∘ get mt ≗ f
get-is-fn {f = f} mt a
  with Trie.mtlookup (trie mt) (to (a↔sz mt) a)
... | yes (b , pr) = begin
  b                                    ≡⟨  actually-in mt _ _ pr  ⟩
  f (from (a↔sz mt) (to (a↔sz mt) a))  ≡⟨ cong f (from∘to (a↔sz mt) a) ⟩
  f a                                  ∎
  where open ≡-Reasoning

... | no not-in
  with Trie.insert (trie mt) (to (a↔sz mt) a) (f ∘ from (a↔sz mt))
... | tr′ , b∈tr′ = cong f (from∘to (a↔sz mt) a)


