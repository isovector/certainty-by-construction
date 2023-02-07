module playground.reed where

open import Data.Vec
open import Data.Nat
open import Data.Product
open import Data.Sum
open import Data.Empty
import np-complete2

record Encoding (P : ℕ → Set) : Set₁ where
  field
    Γ      : Set
    blowup : ℕ → ℕ  -- also blowup is polynomial
    ⌊_⌋    : {n : ℕ} → P n → Vec Γ (blowup n)

record Language {P : ℕ → Set} (enc : Encoding P) : Set₁ where
  open Encoding enc
  field
    Member : (n : ℕ) → Vec Γ n → Set

-- open import np-complete1

-- record Recognizer {P : ℕ → Set} {enc : Encoding P} (lang : Language enc) : Set₁ where
--   open Encoding enc using (Γ)
--   open Language lang

--   field
--     Q : Set
--     tm : TuringMachine Γ Q

--   open np-complete2 tm

--   open TuringMachine tm






