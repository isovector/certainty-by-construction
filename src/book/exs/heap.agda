module exs.heap {K : Set} (_≤ₖ_ : K → K → Set) where


module ok where
  open import Data.Nat

  private variable
    d n : ℕ
    d₁ n₁ d₂ n₂ : ℕ
    dl dr dl₁ dr₁ dl₂ dr₂ : ℕ

  data 2^_≡_ : ℕ → ℕ → Set where
    2^0 : 2^ 0 ≡ 1
    2^n : 2^ d ≡ n → 2^ (suc d) ≡ (2 * n)

  open import Relation.Binary.PropositionalEquality

  data Size : Set where
    void : Size
    tree : ℕ → ℕ → Size

  mutual
    data Heap : ℕ → Set where
      empty : Heap 0
      leaf : (k : K) → Heap 1
      left1 : (k : K) → (l : Heap 1) → k ≤ₖ min l → Heap 2
      left : (k : K) → (l : Heap (suc (suc d))) → (r : Heap (suc d)) → k ≤ₖ min l → k ≤ₖ min r → Heap (suc (suc (suc d)))
      both : (k : K) → (l r : Heap (suc d)) → k ≤ₖ min l → k ≤ₖ min r → Heap (suc (suc d))

    min : Heap (suc d) → K
    min (leaf k) = k
    min (left1 k x x₁) = k
    min (left k x x₁ x₂ x₃) = k
    min (both k x x₁ x₂ x₃) = k

  last : Heap (suc d) → K
  last (leaf k) = k
  last (left1 k l x₁) = last l
  last (left k l r x₂ x₃) = last l
  last (both k l r x₂ x₃) = last r


--   bubble-up : Heap d → Heap d
--   bubble-up empty = empty
--   bubble-up (leaf k) = leaf k
--   bubble-up (left1 k (leaf k₁) x₁) = {! !}
--   bubble-up (left k x x₁ x₂ x₃) = {! !}
--   bubble-up (both k x x₁ x₂ x₃) = {! !}


module BinomialHeap {o r} {A : Set o} {_<_ : A → A → Set r} where
  open import Agda.Primitive
  open import Data.Sum
  open import Relation.Binary.PropositionalEquality
  open import Data.Nat using (ℕ; suc; _+_; _*_)

  _≤_ : A → A → Set (o ⊔ r)
  x ≤ y = x < y ⊎ x ≡ y

  data DVec {ℓ : Level} (A : ℕ → Set ℓ) : ℕ → Set ℓ where
    [_] : A 0 → DVec A 0
    _∷_ : {n : ℕ} → A (suc n) → DVec A n → DVec A (suc n)

  data BinomialTree (bound : A) : ℕ → Set (o ⊔ r) where
    leaf : (x : A) → bound ≤ x → BinomialTree bound 0
    node : ∀ {n} → (x : A) → bound ≤ x → DVec (BinomialTree x) n → BinomialTree bound (suc n)

  mergeTree : ∀ {b n} → BinomialTree b n → BinomialTree b n → BinomialTree b (suc n)
  mergeTree (leaf a1 b≤a1) (leaf a2 b≤a2) = node {! !} {! !} [ leaf {! !} {! !} ]
  mergeTree (node a1 b≤a1 dv1) (node a2 b≤a2 dv2) = node a1 b≤a1 (node a2 ? dv2 ∷ dv1)

  postulate
    bot : A
    a : A
    bot≤ : {a : A} → bot ≤ a
    refl≤ : {a : A} → a ≤ a

  -- ex : BinomialTree bot 2
  -- ex = node {! !} {! !} (node {! !} {! !} [ leaf {! !} {! !} ] ∷ [ leaf {! !} {! !} ])

--   data BinomialChildren bound where
--     done : BinomialTree bound 0 → BinomialChildren bound 0
--     cons : ∀ {n} → BinomialTree bound (suc n) → BinomialChildren bound n → BinomialChildren bound (suc n)

  data Bin : Set where
    ⟨⟩ : Bin
    𝟙_ : Bin → Bin
    𝟘_ : Bin → Bin

  digits : Bin → ℕ
  digits ⟨⟩ = 0
  digits (𝟙 x) = suc (digits x)
  digits (𝟘 x) = suc (digits x)

  open import Data.Bool
  open import Data.Product

  bsuc-helper : Bin → Bool × Bin
  bsuc-helper ⟨⟩ = true , ⟨⟩
  bsuc-helper (𝟙 x) with bsuc-helper x
  ... | false , snd = false , 𝟙 snd
  ... | true , snd = true , 𝟘 snd
  bsuc-helper (𝟘 x) with bsuc-helper x
  ... | false , snd = false , 𝟘 snd
  ... | true , snd = false , 𝟙 snd

  bsuc : Bin → Bin
  bsuc x with bsuc-helper x
  ... | false , snd = snd
  ... | true , snd = 𝟙 snd

--   msd-is-𝟙 : (b : Bin) → ∃[ b' ] bsuc b ≡ 𝟙 b'
--   msd-is-𝟙 ⟨⟩ = ⟨⟩ , refl
--   msd-is-𝟙 (𝟙 b) = {! !}
--   msd-is-𝟙 (𝟘 b) = {! !}


  data BinomialHeap : Bin → Set (o ⊔ r) where
    empty : BinomialHeap ⟨⟩
    cons : ∀ {b} → (bound : A) → BinomialTree bound (digits b) → BinomialHeap b → BinomialHeap (𝟙 b)
    skip : ∀ {b} → BinomialHeap b → BinomialHeap (𝟘 b)

--   insert : ∀ {b} → A → BinomialHeap b → BinomialHeap (bsuc b)
--   insert {⟨⟩} a h = {! !}
--   insert {𝟙 b} a h = {! !}
--   insert {𝟘 b} a h = {! !}

module heap2 where
  open import Data.Nat hiding (_≤_)
  open import Data.Product

  data Complete : Set where
    comp incomp : Complete

  module _ {A : Set} where
    data Heap : Complete → ℕ → Set where
      empty : Heap incomp 0
      one : A → Heap comp 0
      left : ∀ {n} → A → Heap incomp (suc n) → Heap comp n → Heap incomp (suc (suc n))
      right : ∀ {n} → A → Heap comp n → Heap incomp n → Heap incomp (suc n)
      full : ∀ {n} → A → Heap comp n → Heap comp n → Heap comp (suc n)

    open import Relation.Binary.Definitions
    open import Relation.Binary.PropositionalEquality

    postulate
      _≤_ : A → A → Set
      ≤-cmp : Trichotomous _≡_ _≤_
      a : A

    _ : Heap incomp 2
    _ = left {! !} (right {! !} (one {! !}) empty) (one {! !})

--     sink : ∀ {c n} → Heap c n → Heap c n
--     sink empty = empty
--     sink (one x) = one x
--     sink (left k (left x ll lr) r) with ≤-cmp k x
--     ... | tri> ¬a ¬b c = left x (sink (left k ll lr)) r
--     ... | _ = left k (left x ll lr) r
--     sink (left k (right x ll lr) r) = {! !}
--     sink (right k l (left x rl rr)) = {! !}
--     sink (right k l (right x rl rr)) = {! !}
--     sink (right k (one x) empty) = {! !}
--     sink (full k l (one x)) = {! !}
--     sink (full k l (full x rl rr)) = {! !}

module heap3 {A : Set} where
  open import Relation.Binary.Definitions
  open import Relation.Binary.PropositionalEquality
  open import Data.Product
  open import Data.Sum
  open import Data.Nat hiding (_≤_)

  postulate
    _≤_ : A → A → Set
    ≤-cmp : Trichotomous _≡_ _≤_
    a b : A
    refl≤ : {a : A} → a ≤ a
    a≤b : a ≤ b

  data Heap : A → ℕ → Set where
    ⟨_⟩ : (a : A) → Heap a 1
    _≤⟨_⟩_ : {bound : A} {n : ℕ} → (a : A) → a ≤ bound → Heap bound n → Heap a (suc n)

  infixr 5 _≤⟨_⟩_

  x : Heap a 3
  x = a ≤⟨ a≤b ⟩ b ≤⟨ refl≤ ⟩ ⟨ b ⟩

  insert : {b : A} {n : ℕ} → (a : A) → Heap b n → Heap a (suc n) ⊎ Heap b (suc n)
  insert {b} a ⟨ .b ⟩ with ≤-cmp a b
  ... | tri< a≤b _ _  = inj₁ (a ≤⟨ a≤b ⟩ ⟨ b ⟩ )
  ... | tri≈ _ refl _ = inj₁ (a ≤⟨ refl≤ ⟩ ⟨ b ⟩ )
  ... | tri> _ _ b≤a  = inj₂ (b ≤⟨ b≤a ⟩ ⟨ a ⟩ )
  insert {b} a (.b ≤⟨ x₁ ⟩ x₂) with ≤-cmp a b
  ... | tri< a≤b _ _  = inj₁ (a ≤⟨ a≤b ⟩ b ≤⟨ x₁ ⟩ x₂ )
  ... | tri≈ _ refl _ = inj₁ (a ≤⟨ refl≤ ⟩ b ≤⟨ x₁ ⟩ x₂ )
  ... | tri> _ _ b≤a with insert a x₂
  ... | inj₁ fst      = inj₂ (b ≤⟨ b≤a ⟩ fst)
  ... | inj₂ fst      = inj₂ (b ≤⟨ x₁ ⟩ fst)

  Heap' : ℕ → Set
  Heap' n = ∃[ b ] Heap b n

  insert' : ∀ {n} → A → Heap' n → Heap' (suc n)
  insert' a (_ , h) with insert a h
  ... | inj₁ h' = -, h'
  ... | inj₂ h' = -, h'




