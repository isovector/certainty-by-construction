{-# OPTIONS --type-in-type #-}

module playground.levels where

open import Data.Empty
open import Relation.Nullary


record Self : Set where
  constructor _,_
  field
    self : Set
    proof : self

open Self

notme : Self
self notme = ⊥
proof notme = ?


