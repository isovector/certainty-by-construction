module sets where

open import Function using (_∘_; _$_)
open import propisos
open import Data.Sum renaming (_⊎_ to infixr 80 _⊎_)
open import Data.Nat hiding (_≟_)
open import Data.Nat.Properties using (*-comm)
open import Data.Fin using (Fin; _≟_; zero; suc; inject₁)
import Data.Fin.Properties
open import Function.Equality using (_⟨$⟩_)
open import Relation.Binary.PropositionalEquality
open import Agda.Primitive using (Level; lzero; lsuc)
open import Relation.Binary using (Setoid)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (map′)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Data.Vec
open import Data.Vec.Membership.Propositional
open import Data.Vec.Relation.Unary.Any
open import Data.Vec.Relation.Unary.Unique.Propositional
open import Data.Vec.Relation.Unary.Unique.Propositional.Properties
open import Data.Product renaming (_×_ to infixr 80 _×_)

record IsFinite {ℓ : Level} (A : Set ℓ) : Set ℓ where
  field
    card : ℕ
    is-fin : A ↔ Fin card

  #∣_∣ : ℕ
  #∣_∣ = card

  open _↔_ is-fin

  dec-finite : DecidableEquality A
  dec-finite x y =
    map′
      (λ x=y → begin
        x            ≡⟨ sym (left-inv-of x) ⟩
        from (to x)  ≡⟨ cong from x=y  ⟩
        from (to y)  ≡⟨ left-inv-of y ⟩
        y            ∎
      )
      (cong to)
      (to x ≟ to y)
    where open ≡-Reasoning

  elements : Vec A card
  elements = tabulate from

  elements-unique : Unique elements
  elements-unique = tabulate⁺
      (λ {x} {y} x=y → begin
        x            ≡⟨ sym (right-inv-of x) ⟩
        to (from x)  ≡⟨ cong to x=y ⟩
        to (from y)  ≡⟨ right-inv-of y ⟩
        y            ∎
      )
    where open ≡-Reasoning

without : ∀ {ℓ} {A : Set ℓ} {n : ℕ} → (a : A) → (v : Vec A (suc n)) → a ∈ v → Vec A n
without a (_ ∷ vs) (here px) = vs
without a (v ∷ vs) (there x@(here _)) = v ∷ without a vs x
without a (v ∷ vs) (there x@(there _)) = v ∷ without a vs x

ne-pairs : ∀ {ℓ} {A : Set ℓ} {n : ℕ} → (Vec A (suc (suc n))) → Vec (A × A) (suc (suc n) * suc n)
ne-pairs v =
  concat $ mapWith∈ v λ {i} i∈els →
    Data.Vec.map (i ,_) (without i v i∈els)

record IsNonemptyFinite {ℓ : Level} (A : Set ℓ) : Set ℓ where
  constructor nonempty-fin
  field
    finite : IsFinite A
    card-pred : ℕ
    card-is-card : IsFinite.card finite ≡ suc card-pred

  open IsFinite finite public

  ne-elements : Vec (A × A) (card * card-pred)
  ne-elements with card in eq₁ | card-pred | card-is-card
  ... | suc c | zero | r rewrite *-comm c zero = []
  ... | suc .(suc p) | suc p | refl =
      ne-pairs $ subst (Vec A) eq₁ elements
    where open ≡-Reasoning

open import Data.Bool using (Bool; false; true)

open _↔_

from-pred
  : {ℓ : Level}
  → {A : Set ℓ}
  → (ne : IsNonemptyFinite A)
  → Fin (IsNonemptyFinite.card-pred ne)
  → A
from-pred ne x
  = from (IsNonemptyFinite.is-fin ne)
  $ subst Fin (sym (IsNonemptyFinite.card-is-card ne))
  $ inject₁ x


bool-fin : IsFinite Bool
IsFinite.card bool-fin = 2
to (IsFinite.is-fin bool-fin) false = zero
to (IsFinite.is-fin bool-fin) true = suc zero
from (IsFinite.is-fin bool-fin) zero = false
from (IsFinite.is-fin bool-fin) (suc zero) = true
left-inv-of (IsFinite.is-fin bool-fin) false = refl
left-inv-of (IsFinite.is-fin bool-fin) true = refl
right-inv-of (IsFinite.is-fin bool-fin) zero = refl
right-inv-of (IsFinite.is-fin bool-fin) (suc zero) = refl

fin-fin : {n : ℕ} → IsFinite (Fin n)
IsFinite.card (fin-fin {n}) = n
IsFinite.is-fin (fin-fin {n}) = ↔-refl


bijection-sum : {A B A' B' : Set} → A ↔ B → A' ↔ B' → A ⊎ A' ↔ B ⊎ B'
bijection-sum ab a'b' =
  inverse
    (Data.Sum.map (ab .to)   (a'b' .to))
    (Data.Sum.map (ab .from) (a'b' .from))
    (λ { (inj₁ x) → cong inj₁ (ab   .left-inv-of x)
      ; (inj₂ y) → cong inj₂ (a'b' .left-inv-of y)
      })
    (λ { (inj₁ x) → cong inj₁ (ab   .right-inv-of x)
      ; (inj₂ y) → cong inj₂ (a'b' .right-inv-of y)
      })

bijection-prod : {A B A' B' : Set} → A ↔ B → A' ↔ B' → A × A' ↔ B × B'
bijection-prod ab a'b' =
  inverse
    (Data.Product.map (ab .to)   (a'b' .to))
    (Data.Product.map (ab .from) (a'b' .from))
    (λ { (x , y) → cong₂ _,_ (ab .left-inv-of x)  (a'b' .left-inv-of y) })
    (λ { (x , y) → cong₂ _,_ (ab .right-inv-of x) (a'b' .right-inv-of y) })

fin-sum : {m n : ℕ} → Fin m ⊎ Fin n ↔ Fin (m + n)
fin-sum {m} {n} =
  inverse
    (Data.Fin.join m n)
    (Data.Fin.splitAt m)
    (Data.Fin.Properties.splitAt-join m n)
    (Data.Fin.Properties.join-splitAt m n)

fin-prod : {m n : ℕ} → Fin m × Fin n ↔ Fin (m * n)
fin-prod {m} {n} =
  inverse
    (uncurry Data.Fin.combine)
    (Data.Fin.remQuot n)
    (uncurry Data.Fin.Properties.remQuot-combine)
    (Data.Fin.Properties.combine-remQuot {n = m} n)

open IsFinite

finite-sum : {A B : Set} → IsFinite A → IsFinite B → IsFinite (A ⊎ B)
card (finite-sum a b) = #∣ a ∣ + #∣ b ∣
is-fin (finite-sum a b) =
  let sum = bijection-sum (is-fin a) (is-fin b)
  in ↔-trans sum fin-sum

finite-prod : {A B : Set} → IsFinite A → IsFinite B → IsFinite (A × B)
card (finite-prod a b) = #∣ a ∣ * #∣ b ∣
is-fin (finite-prod a b) =
  let prod = bijection-prod (is-fin a) (is-fin b)
  in ↔-trans prod fin-prod

