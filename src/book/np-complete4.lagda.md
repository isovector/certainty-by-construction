```agda
-- compile to SAT
{-# OPTIONS --allow-unsolved-metas #-}
module np-complete4 where

open import np-complete1 using (TuringMachine; MoveDirection; L; R)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_; yes; no; does)
open import Relation.Unary using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import sets
open import 8-iso using (Equivalent)
open import Agda.Primitive using (Level; lzero; lsuc)
open import Data.Nat
open import Data.Nat.Properties using (+-comm)
open import Data.Fin using (suc)
open import case-bash
open import Data.List using ([]; _∷_)

module TmToSat {Γ Q : Set} (tm : TuringMachine Γ Q) where
  open TuringMachine tm
  open import np-complete2 tm
  open import Data.Fin using (Fin; toℕ; splitAt; zero; suc)

  module _  (n : ℕ)  where
    TapeCell : Set
    TapeCell = Fin (suc (2 * n))

    tape-fin : IsFinite TapeCell
    tape-fin = fin-fin

    tape-ne-fin : IsNonemptyFinite TapeCell
    tape-ne-fin = nonempty-fin tape-fin (2 * n) refl

    TimeCell : Set
    TimeCell = Fin (suc n)

    time-fin : IsFinite TimeCell
    time-fin = fin-fin

    time-ne-fin : IsNonemptyFinite TimeCell
    time-ne-fin = nonempty-fin time-fin n refl

    get-time : TimeCell → ℕ
    get-time = toℕ

    open import Data.Integer using (ℤ; +_; -[1+_])
    open import Data.Sum using (_⊎_; inj₁; inj₂)

    get-pos : TapeCell → ℤ
    get-pos tc with splitAt (suc n) tc
    ... | inj₁ x = + (toℕ x)
    ... | inj₂ y = -[1+ toℕ y ]

    data SLit : Set where
      tape-contents : (tc : TapeCell) → (i : Γ) → (m : TimeCell) → SLit
      tape-position : (tc : TapeCell) → (m : TimeCell) → SLit
      state-at-time : (m : TimeCell) → (q : Q) → SLit

    open import Relation.Binary.Definitions using (DecidableEquality)
    open IsFinite

    open import propisos

    slit-iso : SLit ↔ ((TapeCell × Γ × TimeCell) ⊎ (TapeCell × TimeCell) ⊎ (TimeCell × Q))
    _↔_.to slit-iso (tape-contents tc i m) = inj₁ (tc , i , m)
    _↔_.to slit-iso (tape-position tc m) = inj₂ (inj₁ (tc , m))
    _↔_.to slit-iso (state-at-time m q) = inj₂ (inj₂ (m , q))
    _↔_.from slit-iso (inj₁ (fst , fst₁ , snd)) = tape-contents fst fst₁ snd
    _↔_.from slit-iso (inj₂ (inj₁ (fst , snd))) = tape-position fst snd
    _↔_.from slit-iso (inj₂ (inj₂ (fst , snd))) = state-at-time fst snd
    _↔_.left-inv-of slit-iso (tape-contents tc i m) = refl
    _↔_.left-inv-of slit-iso (tape-position tc m) = refl
    _↔_.left-inv-of slit-iso (state-at-time m q) = refl
    _↔_.right-inv-of slit-iso (inj₁ x) = refl
    _↔_.right-inv-of slit-iso (inj₂ (inj₁ x)) = refl
    _↔_.right-inv-of slit-iso (inj₂ (inj₂ y)) = refl

    slit-fin : IsFinite SLit
    IsFinite.card slit-fin
      = suc (2 * n) * (#∣ Γ-finite ∣ * suc n) + (suc (2 * n) * suc n + suc n * #∣ Q-finite ∣)
    IsFinite.is-fin slit-fin =
      ↔-trans slit-iso (is-fin
        (finite-sum (finite-prod tape-fin (finite-prod Γ-finite time-fin))
        (finite-sum
          (finite-prod tape-fin time-fin)
          (finite-prod time-fin Q-finite))))

    open import Data.Bool
    open Properties

    ↓ : Q × Tape → SLit → Bool
    ↓ qt (tape-contents tc i m) = cell-at-t-is qt (get-time m) (get-pos tc) i
    ↓ qt (tape-position tc m) = pos-at-t-is qt (get-time m) (get-pos tc)
    ↓ qt (state-at-time m q) = q-at-t-is qt (get-time m) q

    open import Relation.Binary using (Setoid)
    open import Relation.Binary.PropositionalEquality

    open import np-complete0 SLit slit-fin
    open import Data.Vec
    open IsNonemptyFinite using (card-pred; card-is-card; finite; ne-elements)

    nδ : ℕ
    nδ = card δ-finite

    nQ-1 nQ nΓ-1 nΓ : ℕ
    nQ-1 = card-pred Q-ne-finite

    nQ = #∣ finite Q-ne-finite ∣

    nΓ-1 = card-pred Γ-ne-finite

    nΓ = #∣ finite Γ-ne-finite ∣

    open import Function using (_$_; _∘_)


    t₀ : Tape → TapeCell → SLit
    t₀ t tc = tape-contents tc (read (get-pos tc) t) zero

    initial-tape-cnf : Tape → Vec Lit (suc (2 * n))
    initial-tape-cnf t = map (↪ ∘ t₀ t) $ elements tape-fin

    initial-state-cnf : Q → Vec Lit 1
    initial-state-cnf q₀ = ↪ (state-at-time zero q₀) ∷ []

    initial-pos-cnf : Vec Lit 1
    initial-pos-cnf = ↪ (tape-position zero zero) ∷ []

    no-duplicates : Vec Lit (card time-fin * (card (finite Γ-ne-finite) * card-pred Γ-ne-finite * 2 + (n + (n + 0)) * (card (finite Γ-ne-finite) * card-pred Γ-ne-finite * 2)))
    no-duplicates = do
      time <- elements time-fin
      pos <- elements tape-fin
      (sym , sym') <- ne-elements Γ-ne-finite
      ! (tape-contents pos sym time)
        ∷ ! (tape-contents pos sym' time)
        ∷ []
      where open CartesianBind

    one-holds : Vec Lit (suc n * (nΓ * 1 + (2 * n) * (nΓ * 1)))
    one-holds = subst (Vec Lit) refl $ do
      time <- elements time-fin
      pos <- elements tape-fin
      sym <- elements Γ-finite
      ↪ (tape-contents pos sym time) ∷ []
      where open CartesianBind

    head-writes-cnf : Vec Lit (card-pred time-ne-fin * (card (finite Γ-ne-finite) * card-pred Γ-ne-finite * 3 + (n + (n + 0)) * (card (finite Γ-ne-finite) * card-pred Γ-ne-finite * 3)))
    head-writes-cnf = do
      time <- tabulate (from-pred time-ne-fin)
      pos <- elements tape-fin
      (sym , sym') <- ne-elements Γ-ne-finite
      ↪ (tape-position pos time)
        ∷ ! (tape-contents pos sym time)
        ∷ ! (tape-contents pos sym' {! Fin.suc time !})
        ∷ []
      where open CartesianBind


    single-state : Vec Lit (suc n * (nQ * nQ-1 * 2))
    single-state = do
      time <- elements time-fin
      (q , q') <- ne-elements Q-ne-finite
      ! (state-at-time time q)
        ∷ ! (state-at-time time q')
        ∷ []
      where open CartesianBind

    single-head-pos : Vec Lit (card time-fin * ((n + (n + 0) + (n + (n + 0)) * (n + (n + 0))) * 2))
    single-head-pos = do
      time <- elements time-fin
      (pos , pos') <- ne-elements tape-ne-fin
      ! (tape-position pos time)
        ∷ ! (tape-position pos' time)
        ∷ []
      where open CartesianBind

    open import Function.Base using (case_of_)

    go : MoveDirection → TapeCell → TapeCell
    go = ?

    can-transition : Vec (Vec Lit 4) (card time-fin * (card δ-finite * 3 + (n + (n + 0)) * (card δ-finite * 3)))
    can-transition = do
      time <- elements time-fin
      pos <- elements tape-fin
      (q , i) , (q' , i' , dir) , tr <- elements δ-finite
      let pos' = go dir pos
          time' = {! time !}

      Data.Vec.map
        (λ x
        → ! (tape-position pos time)
        ∷ ! (state-at-time time q)
        ∷ ! (tape-contents pos i time)
        ∷ x
        ∷ []
        )
        ( ↪ (tape-position pos' time')
        ∷ ↪ (state-at-time time' q')
        ∷ ↪ (tape-contents pos' i' time')
        ∷ []
        )
      where open CartesianBind

    fromVec : {m n : ℕ} → Vec (Vec Lit m) n → CNF (n * suc m)
    fromVec [] = []
    fromVec {m} (x ∷ x₁) = subst CNF (cong suc (+-comm _ m)) (x ∷ fromVec x₁)


    the-size : ℕ → ℕ
    the-size n = (suc (suc (suc (suc (suc (suc (suc (suc (suc n * (nδ * 3 + (2 * n) * (nδ * 3)) * 5 + suc n * ((2 * n + (2 * n) * (2 * n)) * 2)) + suc n * (nQ * nQ-1 * 2)) + n * (nΓ * nΓ-1 * 3 + (2 * n) * (nΓ * nΓ-1 * 3))) + suc n * (nΓ * 1 + 2 * n * (nΓ * 1))) + suc n * (nΓ * nΓ-1 * 2 + (2 * n) * (nΓ * nΓ-1 * 2))) + 1) + 1) + suc (2 * n)))

    -- 8 * n ^ 3 + 2 * nQ-1 ^ 2 + 14 * n ^ 2 + 12 * n * nΓ-1 + 9 * n * nΓ-1 ^ 2 + 12 * n ^ 2 * nΓ-1 + 10 * n ^ 2 * nΓ-1 ^ 2 + 2 * nQ-1 + 15 * d + 9 * n + 3 * nΓ-1 + 2 * nΓ-1 ^ 2 + 45 * n * d + 30 * d * n ^ 2 + 2 * n * nQ-1 + 2 * n * nQ-1 ^ 2 + 12
    sat-problem : Q × Tape → CNF (the-size n)
    sat-problem qt
      = initial-tape-cnf (proj₂ qt)
      ∷ initial-state-cnf (proj₁ qt)
      ∷ initial-pos-cnf
      ∷ no-duplicates
      ∷ one-holds
      ∷ head-writes-cnf
      ∷ single-state
      ∷ single-head-pos
      ∷ fromVec can-transition

  open import np-complete3
  open import np-complete5

--   SAT-in-NPC : (qt : Q × Tape) → InNP-Complete (SAT-in-NP  (slit-fin qt))
--   SAT-in-NPC = ?
--   -- _≤ₚ_.size (InNP-Complete.is-complete SAT-in-NPC C'-in-np) n = the-size (InNP.runtime C'-in-np n)
--   -- _≤ₚ_.size-poly (InNP-Complete.is-complete SAT-in-NPC C'-in-np) n = {! poly-trans !}
--   -- _≤ₚ_.reduce (InNP-Complete.is-complete SAT-in-NPC C'-in-np) c' = {! InNP.compile C'-in-np c' !}
--   -- _≤ₚ_.equiv (InNP-Complete.is-complete SAT-in-NPC C'-in-np) = {! !}

--     test : ℕ
--     test = Data.List.length ⌊ sat-problem ⌋

--     test₂ : test ≡ test
--     test₂ = refl


-- open import Data.Bool

-- module _ {Name : Set} (name-fin : IsFinite Name) (bs : Name → Bool) where
--   open import np-complete3 name-fin bs
--   open InNP-Complete
--   open _≤ₚ_

--   SAT-in-NPC : InNP-Complete SAT-in-NP
--   size (is-complete SAT-in-NPC C'-in-np) = {! !}
--   size-poly (is-complete SAT-in-NPC C'-in-np) = {! !}
--   reduce (is-complete SAT-in-NPC C'-in-np) = {! !}
--   _≤ₚ_.equiv (is-complete SAT-in-NPC C'-in-np) = {! !}

-- ```
