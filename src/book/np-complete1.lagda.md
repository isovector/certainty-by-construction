## NP-Completeness

```agda
module np-complete1 where
  open import Data.List
    using (List; _∷_; [])

  data MoveDirection : Set where
    L R : MoveDirection

  record Tape (Γ : Set) : Set where
    constructor tape
    field
      left-of : List Γ
      head : Γ
      right-of : List Γ

  private variable
    Γ : Set

  move : Γ → MoveDirection → Tape Γ → Tape Γ
  move b L (tape [] h r)
    = tape [] b (h ∷ r)
  move _ L (tape (x ∷ l) h r)
    = tape l x (h ∷ r)
  move b R (tape l h [])
    = tape (h ∷ l) b []
  move _ R (tape l h (x ∷ r))
    = tape (h ∷ l) x r

  write : Γ → Tape Γ → Tape Γ
  write a (tape l _ r) = tape l a r
```
