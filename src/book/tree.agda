-- TECH TREE
--
-- classical math gets things backwards
--    contradiction cannot exist, therefore if you have one, your premise must be false
-- constructive math:
--    false *is the SAME THING* as implying a contradiction
--
-- similar but with very different takeaways
--
-- how to show a contradiction
-- how to show falsity
-- working with these things

module tree where

open import Relation.Binary.PropositionalEquality

open import Relation.Nullary
open import Relation.Unary

module Ok where
  open import Data.Nat using (ℕ; zero; suc)
  open import Data.Nat.Properties using (suc-injective)

  _≟_ : (x y : ℕ) → Dec (x ≡ y)
  zero ≟ zero = yes refl
  zero ≟ suc y = no λ { () }
  suc x ≟ zero = no λ { () }
  suc x ≟ suc y with x ≟ y
  ... | yes x=y = yes (cong suc x=y)
  ... | no ¬x=y = no λ sx=sy → ¬x=y (suc-injective sx=sy)

data Tree (A : Set) : Set where
  leaf : A → Tree A
  branch : Tree A -> Tree A -> Tree A

open import Data.Nat
open import Data.Nat.Properties

private variable
  A : Set

depth : Tree A → ℕ
depth (leaf x) = 0
depth (branch l r) = suc (depth l ⊔ depth r)

data Balanced : Tree A → Set where
  leaf-bal : {x : A} → Balanced (leaf x)
  branch-bal
      : {l r : Tree A}
      → depth l ≡ depth r
      → Balanced l
      → Balanced r
      → Balanced (branch l r)

test : Tree ℕ
test = branch (branch (leaf 5) (leaf 6)) (branch (leaf 2) (leaf 10))

test₂ : Tree ℕ
test₂ = branch (branch (leaf 5) (leaf 6)) (leaf 2 )

_ : Balanced test
_ = branch-bal refl (branch-bal refl leaf-bal leaf-bal) (branch-bal refl leaf-bal leaf-bal)

balanced? : (tree : Tree A) → Dec (Balanced tree)
balanced? (leaf x) = yes leaf-bal
balanced? (branch l r) with depth l ≟ depth r
balanced? (branch l r) | yes same-depth with balanced? l
balanced? (branch l r) | yes same-depth | yes bl with balanced? r
balanced? (branch l r) | yes same-depth | yes bl | yes br = yes (branch-bal same-depth bl br)
balanced? (branch l r) | yes same-depth | yes bl | no ¬br = no λ { (branch-bal _ _ br) → ¬br br }
balanced? (branch l r) | yes same-depth | no ¬bl = no λ { (branch-bal _ bl _) → ¬bl bl }
balanced? (branch l r) | no different-depth = no λ { (branch-bal d _ _) → different-depth d }

meta : Dec (Dec A) → Dec A
meta (yes x) = x
meta (no x) = no λ { a → x (yes a) }

pure : A → Dec A
pure a = yes a

fmap : {A B : Set} → (A → B) → (B → A) → Dec A → Dec B
fmap f _ (yes a) = pure (f a)
fmap _ f (no ¬a) = no λ { b → ¬a (f b) }


data Bounds : Set where
  -∞ : Bounds
  #  : ℕ → Bounds
  +∞ : Bounds

data _≤∞_ : Bounds → Bounds → Set where
  -∞≤n : {n : Bounds}         → -∞  ≤∞ n
  n≤n :  {a b : ℕ}    → a ≤ b → # a ≤∞ # b
  n≤+∞ : {n : ℕ}              → # n ≤∞ +∞
  +∞≤+∞ :                        +∞ ≤∞ +∞

instance
  -∞≤ : {n : Bounds} → -∞ ≤∞ n
  -∞≤ = -∞≤n

  #≤# : {a b : ℕ} → {{a ≤ b}} → # a ≤∞ # b
  #≤# {{a≤b}} = n≤n a≤b

  z≤ : {n : ℕ} → 0 ≤ n
  z≤ = z≤n

  s≤ : {a b : ℕ} → {{a ≤ b}} → suc a ≤ suc b
  s≤ {{a≤b}} = s≤s a≤b

  x≤+∞ : {n : ℕ} → # n ≤∞ +∞
  x≤+∞ = n≤+∞

  ∞≤+∞ : +∞ ≤∞ +∞
  ∞≤+∞ = +∞≤+∞

∞-trans : {a b c : Bounds} → a ≤∞ b → b ≤∞ c → a ≤∞ c
∞-trans -∞≤n y          = -∞≤n
∞-trans (n≤n x) (n≤n y) = n≤n (≤-trans x y)
∞-trans (n≤n x) n≤+∞    = n≤+∞
∞-trans n≤+∞ +∞≤+∞      = n≤+∞
∞-trans +∞≤+∞ +∞≤+∞     = +∞≤+∞

data BST : Bounds → Bounds → Set where
  empty : {b t : Bounds} → {{b ≤∞ t}} → BST b t
  branch : {lb rt : Bounds}
         → (n : ℕ)
         → (l : BST lb (# n))
         → (r : BST (# n) rt)
         → BST lb rt

yo : BST -∞ +∞
yo = branch 5
      (branch 4 empty empty)
      (empty)


