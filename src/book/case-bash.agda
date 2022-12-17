
module case-bash where

open import Function.Base
open import Data.Unit.Base
open import Data.List.Base
open import Data.List.Effectful
open import Reflection
open import Relation.Binary.PropositionalEquality hiding ([_])
import Reflection.TCM.Effectful as TCM

open TraversableA

private
  case-bash-clause : Term → Name → TC Clause
  case-bash-clause tm cs = do
    let ai = arg-info visible (modality relevant quantity-ω)
    return $ Clause.clause [] (arg ai (Pattern.con cs []) ∷ []) tm

  case-bash-data : Definition → Term → TC Term
  case-bash-data (data-type n cs) tm = do
    clauses ← mapA TCM.applicative (case-bash-clause tm) cs
    return $ pat-lam clauses []
  case-bash-data _ tm =
    return $ lam visible (abs "_" tm)

  case-bash-pis : Term → TC Term
  case-bash-pis (pi a@(arg i (def nm cls)) (abs x b)) = do
    tm ← extendContext x a $ case-bash-pis b
    defn ← getDefinition nm
    case-bash-data defn tm
  case-bash-pis _ =
    return $ con (quote refl) []

macro
  case-bash! : Term → TC ⊤
  case-bash! hole = do
    goal ← inferType hole
    soln ← case-bash-pis goal
    unify hole soln
