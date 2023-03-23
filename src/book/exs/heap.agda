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
  open import Data.Nat using (ℕ; suc)

  _≤_ : A → A → Set (o ⊔ r)
  x ≤ y = x < y ⊎ x ≡ y

  data BinomialTree (bound : A) : ℕ → Set (o ⊔ r)
  data BinomialChildren (bound : A) : ℕ → Set (o ⊔ r)

  data BinomialTree bound where
    leaf : (x : A) → bound ≤ x → BinomialTree bound 0
    node : ∀ {n} → (x : A) → bound ≤ x → BinomialChildren x n → BinomialTree bound (suc n)

  data BinomialChildren bound where
    done : BinomialTree bound 0 → BinomialChildren bound 0
    cons : ∀ {n} → BinomialTree bound (suc n) → BinomialChildren bound n → BinomialChildren bound (suc n)

  data Bin : Set where
    ⟨⟩ : Bin
    _𝟙 : Bin → Bin
    _𝟘 : Bin → Bin

  digits : Bin → ℕ
  digits = ?


  data BinomialHeap : Bin → Set (o ⊔ r) where
    empty : BinomialHeap ⟨⟩
    cons : ∀ {b bound} → BinomialTree bound (digits b) → BinomialHeap b → BinomialHeap (b 𝟙)
    skip : ∀ {b} → BinomialHeap b → BinomialHeap (b 𝟘)
