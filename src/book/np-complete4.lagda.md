```agda
-- compile to SAT
module np-complete4 where

open import np-complete1 using (TuringMachine; L; R)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Unary using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import sets
open import 8-iso using (Equivalent)
open import Agda.Primitive using (Level; lzero; lsuc)
open import Data.Nat
open import Data.Fin using (suc)
open import case-bash

module TmToSat {Γ Q : Set} (tm : TuringMachine Γ Q) where
  open TuringMachine tm
  open import np-complete2 tm
  open import Data.Fin using (Fin; toℕ; splitAt; zero; suc)

  module _ {qt : Q × Tape} {q : Q} {n : ℕ} (hw : HaltsWith qt q n) where
    initial-tape : Tape
    initial-tape = proj₂ qt

    initial-state : Q
    initial-state = proj₁ qt

    arr : qt -⟨ n ⟩→ (q , HaltsWith.final-tape hw)
    arr = HaltsWith.arr hw

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

    ↓ : SLit → Bool
    ↓ (tape-contents tc i m) = cell-at-t-is qt (get-time m) (get-pos tc) i
    ↓ (tape-position tc m) = pos-at-t-is qt (get-time m) (get-pos tc)
    ↓ (state-at-time m q) = q-at-t-is qt (get-time m) q

    open import Relation.Binary using (Setoid)
    open import Relation.Binary.PropositionalEquality

    open import np-complete3 SLit slit-fin ↓ hiding (δ-dec)
    open import Data.Vec
    open IsNonemptyFinite using (card-pred; card-is-card; finite)

    ne-elements : {A : Set} → (ne : IsNonemptyFinite A) → Vec A (suc (card-pred ne))
    ne-elements {A} ne = subst (Vec A) (card-is-card ne) (elements (finite ne))

    open import Function using (_$_)

    initial-tape-cnf : Vec SLit (suc (2 * n))
    initial-tape-cnf
      = map (λ tc → tape-contents tc (read (get-pos tc) initial-tape) zero )
      $ elements tape-fin

    initial-state-cnf : Vec Lit 1
    initial-state-cnf = ↪ (state-at-time zero initial-state) ∷ []

    initial-pos-cnf : Vec Lit 1
    initial-pos-cnf = ↪ (tape-position zero zero) ∷ []

    postulate
      without : {A : Set} {n : ℕ} → A → Vec A (suc n) → Vec A n

    no-duplicates : Vec Lit (suc n * (#∣ Γ-finite ∣ * (card-pred Γ-ne-finite * 2) + (2 * n) * (#∣ Γ-finite ∣ * (card-pred Γ-ne-finite * 2))))
    no-duplicates = do
      time <- elements time-fin
      pos <- elements tape-fin
      sym <- elements Γ-finite
      sym' <- without sym (ne-elements Γ-ne-finite)
      ! (tape-contents pos sym time)
        ∷ ! (tape-contents pos sym' time)
        ∷ []
      where open CartesianBind

    one-holds : Vec Lit (suc n * (#∣ Γ-finite ∣ * 1 + (2 * n) * (#∣ Γ-finite ∣ * 1)))
    one-holds = subst (Vec Lit) refl $ do
      time <- elements time-fin
      pos <- elements tape-fin
      sym <- elements Γ-finite
      ↪ (tape-contents pos sym time) ∷ []
      where open CartesianBind

    head-writes-cnf : Vec Lit (n * (#∣ Γ-finite ∣ * (card-pred Γ-ne-finite * 3) + (2 * n) * (#∣ Γ-finite ∣ * (card-pred Γ-ne-finite * 3))))
    head-writes-cnf = do
      time <- tabulate (from-pred time-ne-fin)
      pos <- elements tape-fin
      sym <- elements Γ-finite
      sym' <- without sym (ne-elements Γ-ne-finite)

      ! (tape-position pos time)
        ∷ ! (tape-contents pos sym time)
        ∷ ! (tape-contents pos sym' {! Fin.suc time !})
        ∷ []

      -- (tape-contents pos sym time) and
      -- (tape-contents pos sym' (suc time))
      -- then
      -- tape-position pos time

      -- same as

      -- ! (tape-position pos time)
      -- or ! tape-contents pos sym time
      -- or ! tape-contents pos sym' (suc time)


      where open CartesianBind

    single-state : Vec Lit (suc n * (#∣ Q-finite ∣ * (card-pred Q-ne-finite * 2)))
    single-state = do
      time <- elements time-fin
      q <- elements Q-finite
      q' <- without q (ne-elements Q-ne-finite)
      ! (state-at-time time q)
        ∷ ! (state-at-time time q')
        ∷ []
      where open CartesianBind

    single-head-pos : Vec Lit (suc n * ((2 * n) * 2 + (2 * n) * ((2 * n) * 2)))
    single-head-pos = do
      time <- elements time-fin
      pos <- elements tape-fin
      pos' <- without pos (ne-elements tape-ne-fin)
      ! (tape-position pos time)
        ∷ ! (tape-position pos' time)
        ∷ []
      where open CartesianBind


    open import Function.Base using (case_of_)

    can-transition : Vec Lit ?
    can-transition = do
      time <- elements time-fin
      pos <- elements tape-fin
      q <- elements Q-finite
      q' <- elements Q-finite
      sym <- elements Γ-finite
      sym' <- elements Γ-finite
      dir <- L ∷ R ∷ []

      case δ-dec (q , sym) (q' , sym' , dir) of λ
        { (yes d) → ?
        ; (no _) → ?
        }

      where open CartesianBind




```
