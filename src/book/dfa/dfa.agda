module dfa.dfa where

open import Relation.Binary.PropositionalEquality
open import sets using (IsFinite)

record DFA (Γ : Set) : Set₁ where
  field
    Q : Set
    δ : Q → Γ → Q
    q₀ : Q
    F : Q → Set

    Q-fin : IsFinite Q
    Γ-fin : IsFinite Γ
    F-prop : ∀ {q} → (f f' : F q) → f ≡ f'

postulate
  trivial : {A : Set} → A


data Listʳ (A : Set) : Set where
  [] : Listʳ A
  _∷ʳ_ : Listʳ A → A → Listʳ A

infixl 5 _∷ʳ_

_++ʳ_ : {A : Set} → Listʳ A → Listʳ A → Listʳ A
xs ++ʳ [] = xs
xs ++ʳ (ys ∷ʳ y) = (xs ++ʳ ys) ∷ʳ y

mapʳ : {A B : Set} → (A → B) → Listʳ A → Listʳ B
mapʳ f [] = []
mapʳ f (xs ∷ʳ x) = mapʳ f xs ∷ʳ f x

module Matching {Γ : Set} (dfa : DFA Γ) where
  open DFA dfa

  data _After_ : Q → Listʳ Γ → Set where
    start : q₀ After []
    step
      : {r : Q} {g : Γ} {gs : Listʳ Γ}
      → r After gs
      → (δ r g) After (gs ∷ʳ g)

  record Recognizes (l : Listʳ Γ) : Set where
    constructor recog
    field
      end : Q
      F-end : F end
      matched : end After l

  open import propisos

  record Language : Set₁ where
    constructor language
    field
      Lang : Listʳ Γ → Set
      proof : (bs : Listʳ Γ) → Lang bs ↔ Recognizes bs

  postulate
    After-prop : ∀ {q ls} → (a₁ a₂ : q After ls) → a₁ ≡ a₂
    Recognizes-prop : ∀ {ls} → (a₁ a₂ : Recognizes ls) → a₁ ≡ a₂




module Example where
  open import Data.Bool using (Bool; true; false)

  data Q : Set where
    q₁ q₂ : Q

  data F : Q → Set where
    final : F q₂

  M₁ : DFA Bool
  DFA.Q M₁ = Q
  DFA.δ M₁ _ false = q₁
  DFA.δ M₁ _ true = q₂
  DFA.q₀ M₁ = q₁
  DFA.F M₁ = F
  DFA.Q-fin M₁ = trivial
  DFA.Γ-fin M₁ = trivial
  DFA.F-prop M₁ = trivial

  open Matching M₁
  open Recognizes

  _ : q₂ After ([] ∷ʳ false ∷ʳ false ∷ʳ true)
  _ = step (step (step start))

  open import Data.List renaming (_∷ʳ_ to _∷ᵣ_) hiding (reverse)

  data L : Listʳ Bool → Set where
    lang : (bs : Listʳ Bool) → L (bs ∷ʳ true)

  open import propisos
  open _↔_

  mutual
    lemma₁ : (bs : Listʳ Bool) → q₂ After (bs ∷ʳ true)
    lemma₁ [] = step start
    lemma₁ (bs ∷ʳ false) = step (lemma₀ bs)
    lemma₁ (bs ∷ʳ true) = step (lemma₁ bs)

    lemma₀ : (bs : Listʳ Bool) → q₁ After (bs ∷ʳ false)
    lemma₀ [] = step start
    lemma₀ (bs ∷ʳ false) = step (lemma₀ bs)
    lemma₀ (bs ∷ʳ true) = step (lemma₁ bs)


  lang-is-prop : ∀ bs → (x x' : L bs) → x ≡ x'
  lang-is-prop .(bs ∷ʳ true) (lang bs) (lang .bs) = refl

  mutual
    lem? : ∀ {bs r} → (matched₁ : r After bs) → lemma₀ bs ≡ step matched₁
    lem? {[]} Matching.start = refl
    lem? {bs ∷ʳ false} (Matching.step matched₁) = cong step (lem? matched₁)
    lem? {bs ∷ʳ true} (Matching.step matched₁) = cong step (lem matched₁)

    lem : ∀ {bs r} → (matched₁ : r After bs) → lemma₁ bs ≡ step matched₁
    lem {[]} Matching.start = refl
    lem {bs ∷ʳ false} (Matching.step matched₁) = cong step (lem? matched₁)
    lem {bs ∷ʳ true} (Matching.step matched₁) = cong step (lem matched₁)


  proof : (bs : Listʳ Bool) → L bs ↔ Recognizes bs
  to (proof .(bs ∷ʳ true)) (lang bs) = recog q₂ final (lemma₁ bs)
  from (proof []) record { end = .(DFA.q₀ M₁) ; F-end = () ; matched = start }
  from (proof (bs ∷ʳ false)) record { F-end = () ; matched = step _ }
  from (proof (bs ∷ʳ true)) x = lang bs
  left-inv-of (proof bs) x = lang-is-prop bs _ _
  right-inv-of (proof []) (recog .(DFA.q₀ M₁) () start)
  right-inv-of (proof (bs ∷ʳ false)) (recog _ () (step matched₁))
  right-inv-of (proof (bs ∷ʳ true)) (recog _ final (step matched₁)) = cong (recog q₂ final) (lem matched₁)

