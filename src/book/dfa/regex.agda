open import Relation.Binary.Definitions using (DecidableEquality)

module dfa.regex {Γ : Set} (_≟Γ_ : DecidableEquality Γ) where

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import dfa.dfa
open DFA




data LQ : Set where
  start one many : LQ

open import Data.Unit
open import Data.Empty
open import propisos
open _↔_



lit-dfa : (c : Γ) → DFA Γ
DFA.Q (lit-dfa c) = LQ
DFA.δ (lit-dfa c) start g with g ≟Γ c
... | yes refl = one
... | no _ = many
DFA.δ (lit-dfa c) one _ = many
DFA.δ (lit-dfa c) many _ = many
DFA.q₀ (lit-dfa c) = start
DFA.F (lit-dfa c) one = ⊤
DFA.F (lit-dfa c) start = ⊥
DFA.F (lit-dfa c) many = ⊥
DFA.Q-fin (lit-dfa c) = trivial
DFA.Γ-fin (lit-dfa c) = trivial
DFA.F-prop (lit-dfa c) = trivial


module _ (c : Γ) where
  LitLang : Listʳ Γ → Set
  LitLang x = x ≡ ([] ∷ʳ c)

  open Matching (lit-dfa c)

  one-proof : (bs : Listʳ Γ) → LitLang bs ↔ Recognizes bs
  to (one-proof ([] ∷ʳ g)) refl = Matching.recog one tt {! step start !}
  from (one-proof []) (Matching.recog _ () Matching.start)
  from (one-proof (bs ∷ʳ x₁)) x = ?
  left-inv-of (one-proof ([] ∷ʳ x₁)) x = {! !}
  right-inv-of (one-proof []) x = {! !}
  right-inv-of (one-proof (bs ∷ʳ x₁)) x = {! !}


data Regex : Set where
  ε : Regex
  lit : Γ → Regex
  _∣_ : Regex → Regex → Regex
  _∙_ : Regex → Regex → Regex
  _★ : Regex → Regex

open import Data.Bool

empty-dfa : DFA Γ
DFA.Q empty-dfa = Bool
DFA.δ empty-dfa _ _ = true
DFA.q₀ empty-dfa = false
DFA.F empty-dfa false = ⊤
DFA.F empty-dfa true = ⊥
DFA.Q-fin empty-dfa = trivial
DFA.Γ-fin empty-dfa = trivial
DFA.F-prop empty-dfa = trivial

module _ where
  open Matching empty-dfa

  empty-lang : Language
  Language.Lang empty-lang bs = bs ≡ []
  to (Language.proof empty-lang bs) refl = recog false tt start
  from (Language.proof empty-lang .[]) (Matching.recog false tt Matching.start) = refl
  left-inv-of (Language.proof empty-lang .[]) refl = refl
  right-inv-of (Language.proof empty-lang .[]) (recog false tt start) = refl


open import Data.Product
open import Data.Sum

module _ {d₁ d₂ : DFA Γ} (l₁ : Matching.Language d₁) (l₂ : Matching.Language d₂)  where
  open Matching
  open Language

  branch-dfa : DFA Γ
  Q branch-dfa = Q d₁ × Q d₂
  δ branch-dfa (q₁ , q₂) g = δ d₁ q₁ g , δ d₂ q₂ g
  q₀ branch-dfa = q₀ d₁ , q₀ d₂
  F branch-dfa (q₁ , q₂) = F d₁ q₁ ⊎ F d₂ q₂
  Q-fin branch-dfa = trivial
  Γ-fin branch-dfa = trivial
  F-prop branch-dfa = trivial

  branch-lang : Language branch-dfa
  Lang branch-lang x = Lang l₁ x ⊎ Lang l₂ x
  to (proof branch-lang bs) (inj₁ x) with to (proof l₁ bs) x
  ... | recog .(q₀ d₁) F-end start = recog (q₀ d₁ , q₀ d₂ ) (inj₁ F-end) start
  ... | recog .(δ d₁ _ _) F-end (step matched) = recog {! !} (inj₁ F-end) (step {! matched !})
  to (proof branch-lang bs) (inj₂ y) = {! !}
  from (proof branch-lang bs) (recog (r₁ , r₂) (inj₁ x) matched) = inj₁ (from (proof l₁ bs) (recog r₁ x {! !}))
  from (proof branch-lang bs) (recog (r₁ , r₂) (inj₂ x) matched) = inj₂ (from (proof l₂ bs) (recog r₂ x {! !}))
  left-inv-of (proof branch-lang bs) = {! !}
  right-inv-of (proof branch-lang bs) = {! !}

module _ {d₁ d₂ : DFA Γ} (l₁ : Matching.Language d₁) (l₂ : Matching.Language d₂)  where
  open Matching
  open Language

  data L : (Listʳ Γ) → Set where
    L-concat : {s₁ s₂ : Listʳ Γ} → Lang l₁ s₁ → Lang l₂ s₂ → L (s₁ ++ʳ s₂)

  concat-dfa : DFA Γ
  Q concat-dfa = {! !}
  δ concat-dfa = {! !}
  q₀ concat-dfa = {! !}
  F concat-dfa = {! !}
  Q-fin concat-dfa = {! !}
  Γ-fin concat-dfa = {! !}
  F-prop concat-dfa = {! !}

  concat-lang : Language concat-dfa
  Lang concat-lang = L
  to (proof concat-lang .(xs ++ʳ ys)) (L-concat {xs} {ys} x y)
    with to (proof l₁ xs) x | to (proof l₂ ys) y
  ... | recog end F-end matched | recog end₁ F-end₁ matched₁ = recog ? ? ?
  from (proof concat-lang bs) = {! !}
  left-inv-of (proof concat-lang bs) = {! !}
  right-inv-of (proof concat-lang bs) = {! !}

-- compile : Regex → DFA Γ
-- compile ε = empty-dfa
-- compile (lit x) = lit-dfa x
-- compile (x ∣ x₁) = {! !}
-- compile (x ∙ x₁) = {! !}
-- compile (x ★) = {! !}


