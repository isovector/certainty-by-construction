module playground.NP-complete where

open import Data.Bool renaming (_∨_ to or; _∧_ to and) hiding (_≤_; _<_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using (Vec; _∷_; []; lookup)
open import Data.Nat
open import Data.List hiding (last; head; lookup; or; and)
open import Data.Maybe
open import Data.Sum hiding (map₂)
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_])

data Lit (n : ℕ) : Set where
  ↪ : Fin n → Lit n
  ¬ : Fin n → Lit n

data Clause (n : ℕ) : Set where
  last : Lit n → Clause n
  _∨_ : Lit n → Clause n → Clause n


data CNF (n : ℕ) : Set where
  last : Clause n → CNF n
  _∧_ : Clause n → CNF n → CNF n

evaluateLit : {n : ℕ} → Vec Bool n → Lit n → Bool
evaluateLit bs (↪ x) = lookup bs x
evaluateLit bs (¬ x) = not (lookup bs x)

evaluateClause : {n : ℕ} → Vec Bool n → Clause n → Bool
evaluateClause bs (last x) = evaluateLit bs x
evaluateClause bs (x ∨ y) = or (evaluateLit bs x) (evaluateClause bs y)

evaluate : {n : ℕ} → Vec Bool n → CNF n → Bool
evaluate bs (last x) = evaluateClause bs x
evaluate bs (x ∧ y) = and (evaluateClause bs x) (evaluate bs y)

sizeClause : {n : ℕ} → Clause n → ℕ
sizeClause (last x) = 1
sizeClause (x ∨ xs) = 1 + sizeClause xs

size : {n : ℕ} → CNF n → ℕ
size (last x) = sizeClause x
size (x ∧ xs) = sizeClause x + size xs

infixr 3 _∧_
infixr 4 _∨_

x₁ x₂ x₃ : Fin 3
x₁ = zero
x₂ = suc zero
x₃ = suc (suc zero)

test : CNF 3
test = (↪ x₁ ∨ last (¬ x₂))
     ∧ (¬ x₁ ∨ ↪ x₂ ∨ last (↪ x₃))
     ∧ last (last (¬ x₁))

assignments : Vec Bool 3
assignments = false ∷ false ∷ true ∷ []

test2 : Bool
test2 = evaluate assignments test

record Problem (A : Set) : Set₁ where
  field
    Proof : Set
    Result : Set
    verify : Proof → A → Result

SAT : {n : ℕ} → Problem (CNF n)
Problem.Proof (SAT {n}) = Vec Bool n
Problem.Result (SAT {n}) = Bool
Problem.verify (SAT {n}) = evaluate

data MoveDirection : Set where
  L R : MoveDirection


record TuringMachine (Alphabet : Set) (State : Set) (HaltState : Set) : Set where
  field
    blank : Alphabet
    initial-state : State
    transition : State → Alphabet → HaltState ⊎ (State × Alphabet × MoveDirection)

record Tape (A : Set) : Set where
  constructor tape
  field
    left-of : List A
    head : A
    right-of : List A

buildTape : {A : Set} → A → List A → Tape A
buildTape blank [] = tape [] blank []
buildTape _ (x ∷ xs) = tape [] x xs

move : {A : Set} → A → MoveDirection → Tape A → Tape A
move blank L (tape [] h r) = tape [] blank (h ∷ r)
move blank L (tape (x ∷ l) h r) = tape l x (h ∷ r)
move blank R (tape l h []) = tape (h ∷ l) blank []
move blank R (tape l h (x ∷ r)) = tape (h ∷ l) x r

moveTM : {Γ Q F : Set} → TuringMachine Γ Q F → MoveDirection → Tape Γ → Tape Γ
moveTM tm = move (TuringMachine.blank tm)

write : {A : Set} → A → Tape A → Tape A
write a (tape l _ r) = tape l a r

step : {Γ Q F : Set} → TuringMachine Γ Q F → Q → Tape Γ → F ⊎ (Q × Tape Γ)
step tm q t with (TuringMachine.transition tm q (Tape.head t))
... | inj₁ x = inj₁ x
... | inj₂ (q' , sym , dir) = inj₂ (q' , moveTM tm dir (write sym t))


runHelper : {Γ Q F : Set} → ℕ → TuringMachine Γ Q F → Q → Tape Γ → F ⊎ (Q × Tape Γ)
runHelper zero _ q t = inj₂ (q , t)
runHelper (suc gas) tm q t with step tm q t
... | inj₁ f = inj₁ f
... | inj₂ (q' , t') = runHelper gas tm q' t'

runDebug : {Γ Q F : Set} → ℕ → TuringMachine Γ Q F → List Γ → F ⊎ (Q × Tape Γ)
runDebug gas tm t = runHelper gas tm (TuringMachine.initial-state tm) (buildTape (TuringMachine.blank tm) t)

run : {Γ Q F : Set} → ℕ → TuringMachine Γ Q F → List Γ → Maybe F
run gas tm t with runHelper gas tm (TuringMachine.initial-state tm) (buildTape (TuringMachine.blank tm) t)
... | inj₁ x = just x
... | inj₂ y = nothing

module BusyBeaver where
  data State : Set where
    A B C : State

  data HaltState : Set where
    HALT : HaltState

  bb : TuringMachine Bool State HaltState
  TuringMachine.blank bb = false
  TuringMachine.initial-state bb = A
  TuringMachine.transition bb A false = inj₂ (B , true , R)
  TuringMachine.transition bb B false = inj₂ (A , true , L)
  TuringMachine.transition bb C false = inj₂ (B , true , L)
  TuringMachine.transition bb A true  = inj₂ (C , true , L)
  TuringMachine.transition bb B true  = inj₂ (B , true , R)
  TuringMachine.transition bb C true  = inj₁ HALT

  yo : _
  yo = run 12 bb []

data Instr (n : ℕ) : Set where
  pop halt : Instr n
  val : Lit n → Instr n

-- compile : {n : ℕ} → Vec Bool n → CNF n → TuringMachine (StackInstr ⊎ Bool) (Bool × Bool) Bool × List (StackInstr ⊎ Bool)



compileClause : {n : ℕ} → Clause n → List (Instr n)
compileClause (last x) = [ val x ]
compileClause (x ∨ cnf) = val x ∷ compileClause cnf

compile : {n : ℕ} → CNF n → List (Instr n)
compile (last x) = (compileClause x ++ [ pop ])
compile (x ∧ cnf) = (compileClause x ++ (pop ∷ compile cnf))

instr : {n : ℕ} → Vec Bool n → Instr n → Bool × Bool → Bool × Bool
instr bs halt st = false , false
instr bs pop (lo , hi) = and lo hi , false
instr bs (val x) st = map₂ (or (evaluateLit bs x)) st

lift : {n : ℕ} → Bool × Bool → Bool ⊎ ((Bool × Bool) × Instr n × MoveDirection)
lift x = inj₂ (x , halt , R)

satTM : {n : ℕ} → Vec Bool n → TuringMachine (Instr n) (Bool × Bool) Bool
TuringMachine.blank (satTM _) = halt
TuringMachine.initial-state (satTM _) = true , false
TuringMachine.transition (satTM bs) st halt = inj₁ (proj₁ st)
TuringMachine.transition (satTM bs) st pop =  lift (instr bs pop st)
TuringMachine.transition (satTM bs) st (val x) = lift (instr bs (val x) st)

-- data TerminatesIn {Γ Q F : Set} (tm : TuringMachine Γ Q F ) : Q → Tape Γ → ℕ → Set where
--   proof
--     : {n : ℕ}
--     → {q : Q}
--     → {t : Tape Γ}
--     → ∃[ x ] runHelper n tm q t ≡ inj₁ x
--     → TerminatesIn tm q t n
--   done
--     : {q : Q}
--     → {t : Tape Γ}
--     → ∃[ x ] step tm q t ≡ inj₁ x
--     → TerminatesIn tm q t 1
--   right
--     : {n : ℕ}
--     → {q q' : Q}
--     → {t t' : Γ}
--     → {l r : List Γ}
--      →
--       let now = tape l t (t' ∷ r)
--           then = tape (t ∷ l) t' r
--        in
--       step tm q then ≡ inj₂ (q' , now)
--     → TerminatesIn tm q' then n
--     → TerminatesIn tm q now (suc n)


testTM : _
testTM = run 100 (satTM assignments) (compile test)

module _ {n : ℕ} (bs : Vec Bool n) where
  tm : TuringMachine (Instr n) (Bool × Bool) Bool
  tm = satTM bs

  private variable
    l r : List (Instr n)
    i : Instr n
    t : Tape (Instr n)
    q : Bool × Bool

  next-is-halt : moveTM tm R (tape l i []) ≡ tape (i ∷ l) halt []
  next-is-halt = refl

  open import Data.Empty
  open import Data.Sum.Properties
  open import Data.Product.Properties

  halt-is-halt : (x : Bool) → (step tm q (tape l i r) ≡ inj₁ x) → i ≡ halt
  halt-is-halt {i = halt} x p = refl

  each-is-right : i ≢ halt → ∃[ x ] step tm q (tape l i r) ≡ inj₂ (x , moveTM tm R (tape l i r))
  each-is-right {i} {q} {l} {r} i≠halt with step tm q (tape l i r) in eq
  ... | inj₁ x = ⊥-elim (i≠halt (halt-is-halt x eq))
  each-is-right {pop} {q} {l} {r} i≠halt | inj₂ (y , snd) = y , ,-injectiveʳ (inj₂-injective {! eq !})
  each-is-right {val x} {q} {l} {r} i≠halt | inj₂ (y , snd) = {! !}
    -- rewrite (,-injectiveʳ (inj₂-injective eq)) = y , refl
  -- each-is-right {val x} {q} {l} {r} i≠halt | inj₂ (y , snd)
    -- rewrite (,-injectiveʳ (inj₂-injective eq)) = y , refl

-- terminating
--     : {n : ℕ} {l : List (Instr n)}
--     → {q : Bool × Bool}
--     → (bs : Vec Bool n)
--     → (t : Instr n)
--     → (r : List (Instr n))
--     → TerminatesIn (satTM bs) q (tape l t r) (suc (suc (length r)))
-- terminating bs t (x ∷ r) with terminating bs x r
-- terminating {q = q} bs pop (pop ∷ r) | z = right {! !} z
-- terminating bs pop (halt ∷ r) | z = right {! !} z
-- terminating bs pop (val x ∷ r) | z = right {! !} z
-- terminating bs halt (x ∷ r) | z = right {! !} z
-- terminating bs (val x₄) (x ∷ r) | z = right {! !} z
-- terminating {q = q} bs pop [] = proof (and (proj₁ q) (proj₂ q) , refl)
-- terminating {q = q} bs halt [] = proof (proj₁ q , refl)
-- terminating {q = q} bs (val x) [] = proof (proj₁ q , refl)

