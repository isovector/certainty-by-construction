module np-complete-satagain where

open import np-complete1
open import Data.Bool

data Γ : Set where
  load : Bool → Γ
  suc : Γ
  val : Γ

  lit : Bool → Γ
  pop : Γ
  nop : Γ

-- record Q : Set where
--   field
--     lo hi : Bool
--     ;;


