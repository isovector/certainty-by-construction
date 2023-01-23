module sets where

open import Function using (_∘_)
open import 8-iso
open import Data.Sum renaming (_⊎_ to infixr 80 _⊎_)
open import Data.Nat
open import Data.Fin using (Fin)
import Data.Fin.Properties
open import Function.Equality using (_⟨$⟩_)
open import Relation.Binary.PropositionalEquality
open import Agda.Primitive using (Level; lzero; lsuc)
open import Relation.Binary using (Setoid)

instance
  fin-equiv : {n : ℕ} → Equivalent lzero (Fin n)
  Equivalent._≋_ fin-equiv = _≡_
  Equivalent.equiv fin-equiv = Setoid.isEquivalence (setoid (Fin _))


record IsFinite {ℓ : Level} (A : Set) {{_ : Equivalent ℓ A}} : Set (lsuc ℓ) where
  field
    card : ℕ
    is-finite : A ↔ Fin card

open IsFinite
open _↔_

module _ {ℓ : Level} (A : Set) {{_ : Equivalent ℓ A}} where
  #∣_∣ : IsFinite A → ℕ
  #∣_∣ = IsFinite.card

  mkIsFinite : {n : ℕ} → A ↔ Fin n → IsFinite A
  card (mkIsFinite {n = n} x) = n
  is-finite (mkIsFinite {n = n} x) = x


--   bijection-sum : {A B A' B' : Set} → A ↔ B → A' ↔ B' → A ⊎ A' ↔ B ⊎ B'
--   bijection-sum ab a'b' =
--     inverse
--       (Data.Sum.map (ab .to)   (a'b' .to))
--       (Data.Sum.map (ab .from) (a'b' .from))
--       (λ { (inj₁ x) → cong inj₁ (ab   .left-inv-of x)
--         ; (inj₂ y) → cong inj₂ (a'b' .left-inv-of y)
--         })
--       (λ { (inj₁ x) → cong inj₁ (ab   .right-inv-of x)
--         ; (inj₂ y) → cong inj₂ (a'b' .right-inv-of y)
--         })

--   open import Data.Product renaming (_×_ to infixr 80 _×_)

--   bijection-prod : {A B A' B' : Set} → A ↔ B → A' ↔ B' → A × A' ↔ B × B'
--   bijection-prod ab a'b' =
--     inverse
--       (Data.Product.map (ab .to)   (a'b' .to))
--       (Data.Product.map (ab .from) (a'b' .from))
--       (λ { (x , y) → cong₂ _,_ (ab .left-inv-of x)  (a'b' .left-inv-of y) })
--       (λ { (x , y) → cong₂ _,_ (ab .right-inv-of x) (a'b' .right-inv-of y) })

--   fin-sum : {m n : ℕ} → Fin m ⊎ Fin n ↔ Fin (m + n)
--   fin-sum {m} {n} =
--     inverse
--       (Data.Fin.join m n)
--       (Data.Fin.splitAt m)
--       (Data.Fin.Properties.splitAt-join m n)
--       (Data.Fin.Properties.join-splitAt m n)

--   fin-prod : {m n : ℕ} → Fin m × Fin n ↔ Fin (m * n)
--   fin-prod {m} {n} =
--     inverse
--       (uncurry Data.Fin.combine)
--       (Data.Fin.remQuot n)
--       (uncurry Data.Fin.Properties.remQuot-combine)
--       (Data.Fin.Properties.combine-remQuot {n = m} n)

--   finite-sum : {A B : Set} → IsFinite A → IsFinite B → IsFinite (A ⊎ B)
--   card (finite-sum a b) = #∣ a ∣ + #∣ b ∣
--   is-finite (finite-sum a b) =
--     let sum = bijection-sum (is-finite a) (is-finite b)
--     in ↔-trans sum fin-sum

--   finite-prod : {A B : Set} → IsFinite A → IsFinite B → IsFinite (A × B)
--   card (finite-prod a b) = #∣ a ∣ * #∣ b ∣
--   is-finite (finite-prod a b) =
--     let prod = bijection-prod (is-finite a) (is-finite b)
--     in ↔-trans prod fin-prod
