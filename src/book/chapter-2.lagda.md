## Decidability

```agda

open import chapter-1 hiding (ℕ)

module chapter-2 where

module crap where

  data BST {A : Set} (_≤_ : A → A → Bool) : Set where
    leaf : BST _≤_
    node : BST _≤_ → A → BST _≤_ → BST _≤_

  insert : {A : Set} {_≤_ : A → A → Bool} → A → BST _≤_ → BST _≤_
  insert a leaf = node leaf a leaf
  insert {_≤_ = _≤_} a (node l a' r) with a ≤ a'
  ... | ff = node (insert a l) a' r
  ... | tt = node l a' (insert a r)

  has : {A : Set} {_≤_ : A → A → Bool} → A → BST _≤_ → Bool
  has x leaf = ff
  has {_≤_ = _≤_} x (node l a r) with x ≤ a | a ≤ x
  ... | ff | _ = has x l
  ... | tt | ff = has x r
  ... | tt | tt = tt

  open import Relation.Binary.PropositionalEquality

  module _ {A : Set} {_≤_ : A → A → Bool} where

    open import Data.Product

    postulate
      ≤-refl : (a : A) → a ≤ a ≡ tt

    -- insert-has : (x : A) → (t : BST _≤_) → has x (insert x t) ≡ tt
    -- insert-has x leaf rewrite ≤-refl x = refl
    -- insert-has x (node l a r) with x ≤ a | a ≤ x
    -- ... | ff | ff = {! !}
    -- ... | ff | tt = {! !}
    -- ... | tt | z = {! !}

open import Relation.Binary.PropositionalEquality

data Tri {A : Set} (_≤_ : A → A → Set) : A → A → Set where
  lt : {x y : A} → {{x ≤ y}} → Tri _≤_ x y
  eq : {x y : A} → {{x ≡ y}} → Tri _≤_ x y
  gt : {x y : A} → {{y ≤ x}} → Tri _≤_ x y

module better (A : Set) (_≤_ : A → A → Set) (tri : (x y : A) → Tri _≤_ x y) where

  data Extend : Set where
    -∞ : Extend
    val : A → Extend
    +∞ : Extend

  data _≤E_ : Extend → Extend → Set where
    -∞≤ : {hi : Extend} → -∞ ≤E hi
    ≤-lift : {lo hi : A} → {lo ≤ hi} → val lo ≤E val hi
    val≤+∞ : {lo : A} → val lo ≤E +∞
    +∞≤+∞ : +∞ ≤E +∞

  instance

    inst--∞≤ : {hi : Extend} → -∞ ≤E hi
    inst--∞≤ = -∞≤

    inst-≤-lift : {lo hi : A} → {{lo ≤ hi}} → val lo ≤E val hi
    inst-≤-lift {{x}} = ≤-lift {_} {_} {x}

    inst-val≤+∞ : {lo : A} → val lo ≤E +∞
    inst-val≤+∞ = val≤+∞

    inst-+∞≤+∞ : +∞ ≤E +∞
    inst-+∞≤+∞ = +∞≤+∞



  data BST : Extend → Extend → Set where
    leaf : {lo hi : Extend} → {{lo ≤E hi}} → BST lo hi
    node : {lo hi : Extend} → (v : A) → BST lo (val v) → BST (val v) hi → BST lo hi



  insert : {lo hi : Extend} → (v : A) → {{lo ≤E val v}} → {{val v ≤E hi}} → BST lo hi → BST lo hi
  insert v leaf = node v leaf leaf
  insert v (node n l r) with tri v n
  ... | lt = node n (insert v l) r
  ... | eq = node n l r
  ... | gt = node n l (insert v r)


module test where
  open import Data.Nat
  open import Data.Nat.Properties

  open import Data.Sum

  tri : (x y : ℕ) → Tri _≤_ x y
  tri x y with ≤-total x y
  ... | inj₁ p1 = lt {{p1}}
  ... | inj₂ p2 = gt {{p2}}

  open better ℕ _≤_ tri

  instance
    instance-z≤ : {hi : ℕ} → 0 ≤ hi
    instance-z≤ = z≤n

    instance-s≤ : {m n : ℕ} → {{m ≤ n}} → suc m ≤ suc n
    instance-s≤ {{p}} = s≤s p

  _ : BST -∞ +∞
  _ = node 7 (node 3 leaf (node 5 (leaf) leaf)) (node 7 leaf (node 100 leaf leaf))




```
