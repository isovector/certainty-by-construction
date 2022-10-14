```agda
module chapter-0 where

open import Data.Product


open import Relation.Unary

module _ {A : Set} {P : A → Set} (P? : Decidable P) where
  open import Data.List
  open import Data.List.Properties
  open import Data.List.Relation.Unary.All
  open import Relation.Nullary
  open import Relation.Unary.Properties
  open import Data.Empty
  open import Relation.Binary.PropositionalEquality

  filtered : (xs : List A) → All P (filter P? xs)
  filtered [] = []
  filtered (x ∷ xs) with P? x
  ... | yes p = p ∷ filtered xs
  ... | no p = filtered xs

  partitioned : (xs : List A) → Σ[ (xs , ys) ∈ List A × List A ] (All P xs × All (λ { x → P x → ⊥ }) ys)
  partitioned [] = ([] , []) , [] , []
  partitioned (x ∷ xs) with P? x | partitioned xs
  ... | yes p | (l , r) , pl , pr = (x ∷ l , r) , p ∷ pl , pr
  ... | no p  | (l , r) , pl , pr = (l , x ∷ r) , pl , p ∷ pr



open import Relation.Binary.PropositionalEquality


```
