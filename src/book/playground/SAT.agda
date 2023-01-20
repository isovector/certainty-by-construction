open import Data.Nat

module playground.SAT (A : Set) where

open import Data.Bool renaming (_∨_ to or; _∧_ to and) hiding (_≤_; _<_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using (Vec; _∷_; []; lookup)
open import Data.List hiding (last; head; lookup; or; and)
open import Data.Maybe
open import Data.Sum hiding (map₂)
import Data.Sum as ⊎
open import Data.Product
import Data.Product as ×
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Empty

data Lit : Set where
  ↪ : A → Lit
  ¬ : A → Lit

data Clause : Set where
  last : Lit → Clause
  _∨_ : Lit → Clause → Clause


data CNF : Set where
  last : Clause → CNF
  _∧_ : Clause → CNF → CNF
sizeClause : Clause → ℕ
sizeClause (last x) = 1
sizeClause (x ∨ xs) = 1 + sizeClause xs

size : CNF → ℕ
size (last x) = sizeClause x
size (x ∧ xs) = sizeClause x + size xs

infixr 3 _∧_
infixr 4 _∨_

data Instr : Set where
  pop : Instr
  val : Lit → Instr
  halt : Instr

State : Set
State = Bool × Bool

private variable
  lo hi : Bool
  q q₁ q₂ q₃ : State
  i : Instr
  is is₁ is₂ : List Instr
  cnf : CNF
  l l₁ : Lit
  c c₁ : Clause

module Stepping (bs : A → Bool) where

  evaluateLit : Lit → Bool
  evaluateLit (↪ x) = bs x
  evaluateLit (¬ x) = not (bs x)

  evaluateClause : Clause → Bool
  evaluateClause (last x) = evaluateLit x
  evaluateClause (x ∨ y) = or (evaluateLit x) (evaluateClause y)

  evaluate : CNF → Bool
  evaluate (last x) = evaluateClause x
  evaluate (x ∧ y) = and (evaluateClause x) (evaluate y)


  infix 1 _⟶_
  data _⟶_ : Instr × State → State → Set where
    ⟶pop : pop , lo , hi ⟶ and lo hi , false
    ⟶val : {x : Lit} → val x , lo , hi ⟶ lo , or hi (evaluateLit x)

  tr : (i , q₁) ⟶ q₂ → State
  tr {q₂ = q} _ = q

  data _-⟨_⟩→_ : State → List Instr → State → Set where
    nil : q -⟨ [] ⟩→ q
    step : (i , q₁)     ⟶ q₂
         → q₂ -⟨     is ⟩→ q₃
         → q₁ -⟨ i ∷ is ⟩→ q₃

  _-⟨++⟩→_ : q₁ -⟨ is₁        ⟩→ q₂
           → q₂ -⟨        is₂ ⟩→ q₃
           → q₁ -⟨ is₁ ++ is₂ ⟩→ q₃
  _-⟨++⟩→_ nil arr₂ = arr₂
  _-⟨++⟩→_ (step x arr₁) arr₂ = step x (arr₁ -⟨++⟩→ arr₂)

  data CompileClause : Clause → List Instr → Set where
    clast : {l : Lit} → CompileClause (last l) (val l ∷ pop ∷ [])
    c∨ : CompileClause c is → CompileClause (l ∨ c) (val l ∷ is)

  data Compile : CNF → List Instr → Set where
    cnflast : CompileClause c is → Compile (last c) is
    cnf∧    : CompileClause c is₁ → Compile cnf is₂ → Compile (c ∧ cnf) (is₁ ++ is₂)

  subst-arr : q₂ ≡ q₃
            → q₁ -⟨ is ⟩→ q₂
            → q₁ -⟨ is ⟩→ q₃
  subst-arr refl x = x

  open import Data.Bool.Properties

  step-comp₂ : CompileClause c is → (lo , hi) -⟨ is ⟩→ (and lo (or hi (evaluateClause c)) , false)
  step-comp₂ clast = step ⟶val (step ⟶pop nil)
  step-comp₂ {lo = lo} {hi} (c∨ {c = c} {l = l} x) =
    step ⟶val (subst-arr (cong (_, _) (cong (and lo) (∨-assoc hi (evaluateLit l) (evaluateClause c)))) (step-comp₂ {lo = lo} {hi = or hi (evaluateLit l)} x))

  lemma : ∀ (lo : Bool) c cnf → and (and lo (evaluateClause c)) (evaluate cnf) ≡ and lo (and (evaluateClause c) (evaluate cnf))
  lemma false c cnf = refl
  lemma true c cnf = refl

  step-comp : Compile cnf is → (lo , false) -⟨ is ⟩→ (and lo (evaluate cnf) , false)
  step-comp {lo = lo} (cnflast x) = step-comp₂ {lo = lo} {hi = false} x
  step-comp {lo = lo} (cnf∧ {c = c} {cnf = cnf} x x₁) = step-comp₂ {lo = lo} {hi = false} x -⟨++⟩→ subst-arr (cong (_, _) (lemma lo c cnf)) (step-comp {lo = and lo (evaluateClause c)} x₁)

  open import playground.turing renaming (step to steptm)
  open TuringMachine

  open import Relation.Nullary

  sat : TuringMachine Instr State Bool
  blank sat = halt
  initial-state sat = true , false
  transition sat q halt = inj₁ (proj₁ q)
  transition sat (lo , hi) pop = inj₂ (tr (⟶pop {lo = lo} {hi = hi}) , pop , R)
  transition sat (lo , hi) (val x) = inj₂ (tr (⟶val {lo = lo} {hi = hi} {x = x}) , (val x) , R)

  step-to-step : (i , q₁) ⟶ q₂ → transition sat q₁ i ≡ inj₂ (q₂ , i , R)
  step-to-step ⟶pop = refl
  step-to-step ⟶val = refl

  postulate
    l-irrel : (is₁ is₂ : List Instr) → tape is₁ i is₂ ≡ tape [] i is₂

  lemma₁ : ∀ i is q₃ q₂
         → runHelper sat (length is) q₃ (buildTape halt is)         ≡ inj₂ (q₂ , tape (reverse is) halt [])
         → runHelper sat (length is) q₃ (move sat R (tape [] i is)) ≡ inj₂ (q₂ , tape (reverse (i ∷ is)) halt [])
  lemma₁ i [] q₃ q₂ x =
    begin
      inj₂ (q₃ , tape (i ∷ []) halt [])
    ≡⟨ cong inj₂ (cong (q₃ ,_) (l-irrel (i ∷ []) [])) ⟩
      inj₂ (q₃ , tape [] halt [])
    ≡⟨ x ⟩
      inj₂ (q₂ , tape [] halt [])
    ≡⟨ cong inj₂ (cong (q₂ ,_) (sym (l-irrel (i ∷ []) []))) ⟩
      inj₂ (q₂ , tape (i ∷ []) halt [])
    ∎
    where open ≡-Reasoning
  lemma₁ i (h ∷ is) q₃ q₂ x =
    begin
      runHelper sat (length (h ∷ is)) q₃ (move sat R (tape [] i (h ∷ is)))
    ≡⟨⟩
      runHelper sat (length (h ∷ is)) q₃ (tape [ i ] h is)
    ≡⟨ cong (λ φ → runHelper sat (length (h ∷ is)) q₃ φ) (l-irrel {i = h} [ i ] is) ⟩
      runHelper sat (length (h ∷ is)) q₃ (tape [] h is)
    ≡⟨ x ⟩
      inj₂ (q₂ , tape (reverse (h ∷ is)) halt [])
    ≡⟨ cong inj₂ (cong (q₂ ,_) (l-irrel (reverse (h ∷ is)) [])) ⟩
      inj₂ (q₂ , tape [] halt [])
    ≡⟨ cong inj₂ (cong (q₂ ,_) (sym (l-irrel (reverse (i ∷ h ∷ is)) []))) ⟩
      inj₂ (q₂ , tape (reverse (i ∷ h ∷ is)) halt [])
    ∎
    where open ≡-Reasoning

  arr-to-run
      : q₁ -⟨ is ⟩→ q₂
      → runHelper sat (length is) q₁ (mkTape sat is) ≡ inj₂ (q₂ , tape (reverse is) halt [])
  arr-to-run {q₁} nil = refl
  arr-to-run {q₁} {i ∷ is} {q₂} (step x x₁) =
    begin
      runHelper sat (length (i ∷ is)) q₁ (mkTape sat (i ∷ is))
    ≡⟨⟩
      runHelper sat (suc (length is)) q₁ (tape [] i is)
    ≡⟨⟩
      [ inj₁ , uncurry (runHelper sat (length is)) ]′
        (steptm sat q₁ (tape [] i is))
    ≡⟨⟩
      let stuff x =
            [ inj₁ , uncurry (runHelper sat (length is)) ]′
              (⊎.map₂
                (×.map₂′ (λ { (sym , dir) → moveWrite sat dir sym (tape [] i is) }))
                x) in

      stuff (transition sat q₁ i)
    ≡⟨ cong stuff (step-to-step x) ⟩
      [ inj₁ , uncurry (runHelper sat (length is)) ]′
          (⊎.map₂
            (map₂′ (λ { (sym , dir) → moveWrite sat dir sym (tape [] i is) }))
            (inj₂ (_ , i , R)))
    ≡⟨⟩
      runHelper sat (length is) _ (moveWrite sat R i (tape [] i is))
    ≡⟨⟩
      runHelper sat (length is) _ (move sat R (write i (tape [] i is)))
    ≡⟨⟩
      runHelper sat (length is) _ (move sat R (tape [] i is))
    ≡⟨ lemma₁ i is _ q₂ (arr-to-run x₁) ⟩
      inj₂ (q₂ , tape (reverse (i ∷ is)) halt [])
    ∎
    where open ≡-Reasoning

