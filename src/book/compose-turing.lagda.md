```agda
module compose-turing where

open import np-complete1
open import Data.Sum
open import Data.Product
open import Data.Product.Properties
open import Relation.Nullary using (yes; no)
open import Data.Empty using (⊥-elim)

open TuringMachine
open import Relation.Binary.PropositionalEquality

open import sets

module _ {Q₁ Q₂ Γ₁ Γ₂ : Set}
         (tm₁ : TuringMachine Γ₁ Q₁)
         (tm₂ : TuringMachine Γ₂ Q₂) where

  private variable
    i : Γ₁ ⊎ Γ₂
    i₁ i₁' : Γ₁
    i₂ i₂' : Γ₂

    q : Q₁ × Q₂
    q₁ q₁' : Q₁
    q₂ q₂' : Q₂

    d : MoveDirection

  data ×δ : (Q₁ × Q₂) × (Γ₁ ⊎ Γ₂)
          → ((Q₁ × Q₂) × (Γ₁ ⊎ Γ₂) × MoveDirection)
          → Set where
    run₁ : δ tm₁ (q₁ , i₁) (q₁' , i₁' , d)
         → ×δ ((q₁ , q₂) , inj₁ i₁) ((q₁' , q₂) , inj₁ i₁' , d)
    run₂ : δ tm₂ (q₂ , i₂) (q₂' , i₂' , d)
         → ×δ ((q₁ , q₂) , inj₂ i₂) ((q₁ , q₂') , inj₂ i₂' , d)

  data ×H : (Q₁ × Q₂) × (Γ₁ ⊎ Γ₂) → Set where
    halted₁ : H tm₁ (q₁ , i₁) → ×H ((q₁ , q₂) , inj₁ i₁)
    halted₂ : H tm₂ (q₂ , i₂) → ×H ((q₁ , q₂) , inj₂ i₂)


  ×-tm : TuringMachine (Γ₁ ⊎ Γ₂) (Q₁ × Q₂)
  δ ×-tm = ×δ

  δ-dec ×-tm ((q₁ , q₂) , inj₁ i) ((q₁' , q₂') , inj₁ i' , d)
    with δ-dec tm₁ (q₁ , i) (q₁' , i' , d)
  ... | no z = no λ { (run₁ x) → z x }
  ... | yes z with _≟Q_ tm₂ q₂ q₂'
  ... | yes refl = yes (run₁ z )
  ... | no z = no λ { (run₁ x) → z refl }
  δ-dec ×-tm ((q₁ , q₂) , inj₁ i) ((q₁' , q₂') , inj₂ i' , d) = no λ ()
  δ-dec ×-tm ((q₁ , q₂) , inj₂ i) ((q₁' , q₂') , inj₁ i' , d) = no λ ()
  δ-dec ×-tm ((q₁ , q₂) , inj₂ i) ((q₁' , q₂') , inj₂ i' , d)
    with δ-dec tm₂ (q₂ , i) (q₂' , i' , d)
  ... | no z = no λ { (run₂ x) → z x }
  ... | yes z with _≟Q_ tm₁ q₁ q₁'
  ... | yes refl = yes (run₂ z )
  ... | no z = no λ { (run₂ x) → z refl }

  δ-deterministic ×-tm ((q₁ , q₂) , inj₁ i₁) (run₁ x₁) (run₁ x₂) =
    let p = δ-deterministic tm₁ (q₁ , i₁) x₁ x₂
        p₁ = ,-injectiveˡ p
        p₂ = ,-injectiveˡ (,-injectiveʳ p)
        p₃ = ,-injectiveʳ (,-injectiveʳ p)
     in begin
      _  ≡⟨ cong (λ φ → (φ , _) , _ , _) p₁ ⟩
      _  ≡⟨ cong (λ φ → _ , inj₁ φ , _) p₂ ⟩
      _  ≡⟨ cong (λ φ → _ , _ , φ) p₃ ⟩
      _  ∎
    where open ≡-Reasoning
  δ-deterministic ×-tm ((q₁ , q₂) , inj₂ i₂) (run₂ x₁) (run₂ x₂) =
    let p = δ-deterministic tm₂ (q₂ , i₂) x₁ x₂
        p₁ = ,-injectiveˡ p
        p₂ = ,-injectiveˡ (,-injectiveʳ p)
        p₃ = ,-injectiveʳ (,-injectiveʳ p)
     in begin
      _  ≡⟨ cong (λ φ → (_ , φ) , _ , _) p₁ ⟩
      _  ≡⟨ cong (λ φ → _ , inj₂ φ , _) p₂ ⟩
      _  ≡⟨ cong (λ φ → _ , _ , φ) p₃ ⟩
      _  ∎
    where open ≡-Reasoning

  H ×-tm = ×H

  H-dec ×-tm ((q₁ , q₂) , inj₁ i) with H-dec tm₁ (q₁ , i)
  ... | no z = no λ { (halted₁ x) → z x }
  ... | yes z = yes (halted₁ z)
  H-dec ×-tm ((q₁ , q₂) , inj₂ i) with H-dec tm₂ (q₂ , i)
  ... | no z = no λ { (halted₂ x) → z x }
  ... | yes z = yes (halted₂ z)

  step-or-halt ×-tm ((q₁ , q₂) , inj₁ i₁ ) with step-or-halt tm₁ (q₁ , i₁)
  ... | inj₁ (( q₁'       ,      i₁' , d) ,      snd)
      = inj₁ (((q₁' , q₂) , inj₁ i₁' , d) , run₁ snd)
  ... | inj₂          h₁
      = inj₂ (halted₁ h₁)
  step-or-halt ×-tm ((q₁ , q₂) , inj₂ i₂ ) with step-or-halt tm₂ (q₂ , i₂)
  ... | inj₁ ((      q₂'  ,      i₂' , d) ,      snd)
      = inj₁ (((q₁ , q₂') , inj₂ i₂' , d) , run₂ snd)
  ... | inj₂          h₂
      = inj₂ (halted₂ h₂)

  b ×-tm = inj₁ (b tm₁)

  Q-ne-finite ×-tm =
    nonempty-fin
      (finite-prod (IsNonemptyFinite.finite (Q-ne-finite tm₁)) (IsNonemptyFinite.finite (Q-ne-finite tm₂)))
      ?
      ?
  Γ-ne-finite ×-tm =
    nonempty-fin
      (finite-sum (IsNonemptyFinite.finite (Γ-ne-finite tm₁)) (IsNonemptyFinite.finite (Γ-ne-finite tm₂)))
      ?
      ?

```
