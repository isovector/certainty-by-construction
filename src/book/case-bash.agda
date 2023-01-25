
module case-bash where

open import Function.Base
open import Data.Unit.Base
open import Data.List.Base
open import Data.Nat.Base
open import Data.String.Base using (String)
open import Data.Product

open import Data.List.Effectful
import Data.List.Base as List

open import Reflection.AST
open import Reflection.AST.Term
open import Reflection.AST.Show
open import Reflection.TCM
open import Reflection.TCM.Syntax
open import Relation.Binary.PropositionalEquality

import Reflection.TCM.Effectful as TCM

open TraversableA

--------------------------------------------------------------------------------
-- Dumb printing utilities

print-tele-cell : String × Arg Type → List ErrorPart
print-tele-cell (nm , arg i x) =
  strErr "(" ∷ strErr nm ∷ strErr " : " ∷ strErr (showTerm x) ∷ strErr ") " ∷ []

print-tele : ∀ {ℓ} {A : Set ℓ} → Telescope → TC A
print-tele tele =
  typeError $ strErr "Telescope: " ∷ List.concatMap print-tele-cell tele

print-teles : ∀ {ℓ} {A : Set ℓ} → List Telescope → TC A
print-teles teles =
  typeError $ List.concatMap (λ tele → strErr "\n" ∷ List.concatMap print-tele-cell tele) teles

print-args : ∀ {ℓ} {A : Set ℓ} → List (Arg Term) → TC A
print-args args =
  typeError $ strErr "Args: " ∷ List.map (λ { (arg i x) → termErr x }) args


print-cons : ∀ {ℓ} {A : Set ℓ} → List (List (Name × Type)) → TC A
print-cons cons =
  typeError $ strErr "Cons: " ∷ List.concatMap (List.concatMap print-cell) cons
  where
    print-cell : Name × Type → List ErrorPart
    print-cell (nm , x) =
      strErr "(" ∷ strErr (showName nm) ∷ strErr " : " ∷ strErr (showTerm x) ∷ strErr ") " ∷ []

--------------------------------------------------------------------------------

-- Helper function used to construct the clause name lists
layer : ∀ {ℓ} {A : Set ℓ} → List A → List (List A) → List (List A)
layer xs [] = List.map (_∷ []) xs
layer xs yss = cartesianProductWith _∷_ xs yss

open import Data.Maybe using (just)

hide-arg : ∀ {ℓ} {A : Set ℓ} → Arg A → Arg A
hide-arg (arg (arg-info v m) x) = arg (arg-info hidden m) x

hide-args : ∀ {ℓ} {A : Set ℓ} → List (Arg A) → List (Arg A)
hide-args = List.map hide-arg


get-applied-constructor-type : List (Arg Term) → Name → TC (Name × Type)
get-applied-constructor-type args con-name = do
  con-tp ← inferType (con con-name args)
  pure (con-name , con-tp)

get-constructor-types-for-defn : Name → List (Arg Term) → TC (List (Name × Type))
get-constructor-types-for-defn nm args = do
  defn ← getDefinition nm
  case defn of λ where
    (data-type n cs) →
      -- We only want to apply parameters, so we truncate
      -- the list to the # of params, and mark them hidden.
      let hargs = hide-args $ List.take n args in
      mapA TCM.applicative (get-applied-constructor-type hargs) cs
    _ →
      pure []

get-visible-constructor-types : Term → TC (List (List (Name × Type)))
get-visible-constructor-types (pi a@(vArg (def nm args)) (abs x b)) = do
  tps ← get-constructor-types-for-defn nm args
  tpss ← extendContext x a $ get-visible-constructor-types b
  pure (layer tps tpss)
get-visible-constructor-types (pi a (abs x b)) =
  extendContext x a (get-visible-constructor-types b)
get-visible-constructor-types _ =
  pure []

-- Construct a pattern for a constructor type
-- by creating pattern variables for all visible constructor
-- arguments, and add the pattern variables to the current telescope.
--
-- We pass along the length of the telescope to avoid O(n^2)
-- asymptotics from 'length'.
mk-con-pattern : Term → Telescope → ℕ → Telescope × List (Arg Pattern) × ℕ
mk-con-pattern (pi (arg i@(arg-info visible m) a) (abs x b)) tele n =
  let (tele , pats , n') = mk-con-pattern b tele (suc n)
  -- Off by ??? where ??? is difference between # of pat vars and # of pis
  -- 2 Dimensions:
  -- One is that we get off-by-one errors in cases where there are 0 pattern variables.
  in (x , arg i a) ∷ tele , arg i (var n) ∷ pats , n'
mk-con-pattern (pi (arg (arg-info _ _) a) (abs x b)) tele n =
  -- The telescope contains the types of the pattern variables,
  -- and we don't bind pattern vars for invisible args, so
  -- we don't touch the telescope.
  mk-con-pattern b tele n
mk-con-pattern _ tele n = tele , [] , n

-- Construct patterns for a list of constructor names.
-- As before, we need to keep track of the number of pattern variables.
mk-cons-patterns : List (Name × Type) → Telescope → ℕ → TC (Telescope × List (Arg Pattern))
mk-cons-patterns ((nm , tp) ∷ nms) tele n = do
  let (tele , con-pats , n) = mk-con-pattern tp tele n
  (tele , pats) ← mk-cons-patterns nms tele n
  pure (tele , (vArg (Pattern.con nm con-pats) ∷ pats))
mk-cons-patterns [] tele n =
  pure (tele , [])


-- Construct a clause for a list of contructor names.
mk-case-bash-clause : List (Name × Type) → TC Clause
mk-case-bash-clause cs = do
  (tele , pats) ← mk-cons-patterns cs [] 0
  pure $ Clause.clause tele pats (con (quote refl) [])

debug-gather-teles : List (List (Name × Type)) → TC ⊤
debug-gather-teles cs = do
  xs ← mapA TCM.applicative (λ cs → mk-cons-patterns cs [] 0) cs
  let teles = List.map proj₁ xs
  print-teles teles


macro
  case-bash! : Term → TC ⊤
  case-bash! hole = do
    goal ← inferType hole
    con-tps ← get-visible-constructor-types goal
    -- debug-gather-teles con-tps
    clauses ← mapA TCM.applicative mk-case-bash-clause con-tps
    let tm = pat-lam clauses []
    -- -- typeError $ termErr tm ∷ []
    unify hole tm

