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


open import Data.Product hiding (zip)
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

  unzip : ∀ {r₁ r₂} ls → _After_ branch-dfa (r₁ , r₂) ls → _After_ d₁ r₁ ls × _After_ d₂ r₂ ls
  unzip [] start = start , start
  unzip (xs ∷ʳ x) (step s) with unzip xs s
  ... | l , r = step l , step r

  zip : ∀ {r₁ r₂} ls → _After_ d₁ r₁ ls → _After_ d₂ r₂ ls → _After_ branch-dfa (r₁ , r₂) ls
  zip [] start start = start
  zip (ls ∷ʳ x) (step m₁) (step m₂) = step (zip ls m₁ m₂)

  unzip-zip : ∀ ls {r₁ r₂} m₁ m₂ → unzip {r₁} {r₂} ls (zip {r₁} {r₂} ls m₁ m₂) ≡ (m₁ , m₂)
  unzip-zip [] start start = refl
  unzip-zip (ls ∷ʳ x) (step m₁) (step m₂) rewrite unzip-zip ls m₁ m₂ = refl

  run : {Γ : Set} {d : DFA Γ} → (ls : Listʳ Γ) → ∃[ q ] _After_ d q ls
  run {d = d} [] = q₀ d , start
  run {d = d} (ls ∷ʳ x) with run {d = d} ls
  ... | _ , m = _ , step m

  branch-lang : Language branch-dfa
  Lang branch-lang x = Lang l₁ x ⊎ Lang l₂ x
  to (proof branch-lang bs) (inj₁ x)
   with run {d = d₂} bs
      | to (proof l₁ bs) x
  ... | q₂ , m₂
      | recog end F-end m₁
      = recog (end , q₂) (inj₁ F-end) (zip bs m₁ m₂)
  to (proof branch-lang bs) (inj₂ x)
   with run {d = d₁} bs
      | to (proof l₂ bs) x
  ... | q₁ , m₁
      | recog end F-end m₂
      = recog (q₁ , end) (inj₂ F-end) (zip bs m₁ m₂)
  from (proof branch-lang bs) (recog (r₁ , r₂) (inj₁ x) m₁)
    = inj₁ (from (proof l₁ bs) (recog r₁ x (proj₁ (unzip bs m₁))))
  from (proof branch-lang bs) (recog (r₁ , r₂) (inj₂ x) m₂)
    = inj₂ (from (proof l₂ bs) (recog r₂ x (proj₂ (unzip bs m₂))))
  left-inv-of (proof branch-lang bs) (inj₁ x)
    rewrite unzip-zip bs (Recognizes.matched (to (proof l₁ bs) x)) (proj₂ (run bs))
    rewrite left-inv-of (proof l₁ bs) x = refl
  left-inv-of (proof branch-lang bs) (inj₂ y)
    rewrite unzip-zip bs (proj₂ (run bs)) (Recognizes.matched (to (proof l₂ bs) y))
    rewrite left-inv-of (proof l₂ bs) y = refl
  right-inv-of (proof branch-lang bs) (recog q x m
    ) = Recognizes-prop branch-dfa _ _

module _ {d₁ d₂ : DFA Γ} (l₁ : Matching.Language d₁) (l₂ : Matching.Language d₂)  where
  open Matching
  open Language

  data L : (Listʳ Γ) → Set where
    L-concat : {s₁ s₂ : Listʳ Γ} → Lang l₁ s₁ → Lang l₂ s₂ → L (s₁ ++ʳ s₂)

--   concat-dfa : DFA Γ
--   Q concat-dfa = {! !}
--   δ concat-dfa = {! !}
--   q₀ concat-dfa = {! !}
--   F concat-dfa = {! !}
--   Q-fin concat-dfa = {! !}
--   Γ-fin concat-dfa = {! !}
--   F-prop concat-dfa = {! !}

--   concat-lang : Language concat-dfa
--   Lang concat-lang = L
--   to (proof concat-lang .(xs ++ʳ ys)) (L-concat {xs} {ys} x y)
--     with to (proof l₁ xs) x | to (proof l₂ ys) y
--   ... | recog end F-end matched | recog end₁ F-end₁ matched₁ = recog ? ? ?
--   from (proof concat-lang bs) = {! !}
--   left-inv-of (proof concat-lang bs) = {! !}
--   right-inv-of (proof concat-lang bs) = {! !}

-- compile : Regex → DFA Γ
-- compile ε = empty-dfa
-- compile (lit x) = lit-dfa x
-- compile (x ∣ x₁) = {! !}
-- compile (x ∙ x₁) = {! !}
-- compile (x ★) = {! !}


