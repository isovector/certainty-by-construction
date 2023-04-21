```agda
-- this is in a new module to help agda go fast
-- undo this before we publish
{-# OPTIONS --allow-unsolved-metas #-}
module 2-proofs2 where

open import Relation.Binary.PropositionalEquality
```

```agda
module Integer-Properties where
  import Data.Nat as ℕ
  import Data.Nat.Properties as ℕ
  import 2-numbers
  open 2-numbers.Sandbox-Integers
  open import 2-proofs
  open import case-bash

  -‿involutive : (x : ℤ) → - (- x) ≡ x
  -‿involutive +0 = refl
  -‿involutive +[1+ n ] = refl
  -‿involutive -[1+ n ] = refl

  +-identityˡ : (x : ℤ) → 0ℤ + x ≡ x
  +-identityˡ (+ x) = refl
  +-identityˡ -[1+ x ] = refl

  +-identityʳ : (x : ℤ) → x +⅋ 0ℤ ≡ x
  +-identityʳ (+ ℕ.zero) = refl
  +-identityʳ +[1+ x ] = refl
  +-identityʳ -[1+ x ] = refl

  *-zeroˡ : (m : ℤ) → +0 * m ≡ +0
  *-zeroˡ (+ ℕ.zero) = refl
  *-zeroˡ +[1+ ℕ.zero ] = refl
  *-zeroˡ +[1+ ℕ.suc x ] = refl
  *-zeroˡ -[1+ ℕ.zero ] = refl
  *-zeroˡ -[1+ ℕ.suc x ] = refl

  *-identityˡ : (m : ℤ) → 1ℤ * m ≡ m
  *-identityˡ (+ ℕ.zero) = refl
  *-identityˡ +[1+ ℕ.zero ] = refl
  *-identityˡ +[1+ ℕ.suc x ] rewrite ℕ.+-comm x 1 = refl
  *-identityˡ -[1+ ℕ.zero ] = refl
  *-identityˡ -[1+ ℕ.suc x ] rewrite ℕ.+-comm x 1 = refl

  ⊝-anticomm : (x y : ℕ.ℕ) → x ⊝ y ≡ - (y ⊝ x)
  ⊝-anticomm ℕ.zero ℕ.zero = refl
  ⊝-anticomm ℕ.zero (ℕ.suc y) = refl
  ⊝-anticomm (ℕ.suc x) ℕ.zero = refl
  ⊝-anticomm (ℕ.suc x) (ℕ.suc y) = ⊝-anticomm x y

  +-comm : (x y : ℤ) → x + y ≡ y + x
  +-comm (+ x) (+ y) = cong +_ (ℕ.+-comm x y)
  +-comm (+ x) -[1+ y ] = refl
  +-comm -[1+ x ] (+ y) = refl
  +-comm -[1+ x ] -[1+ y ] = cong -[1+_] (begin
    x ℕ.+ ℕ.suc y    ≡⟨ Nat-Properties.+-suc x y ⟩
    ℕ.suc (x ℕ.+ y)  ≡⟨ cong ℕ.suc (ℕ.+-comm x y) ⟩
    ℕ.suc (y ℕ.+ x)  ≡⟨ sym (Nat-Properties.+-suc y x) ⟩
    y ℕ.+ ℕ.suc x    ∎)
    where open ≡-Reasoning

  +-⊝-assocˡ : (x y z : ℕ.ℕ) → (x ℕ.+ y) ⊝ z ≡ + x + (y ⊝ z)
  +-⊝-assocˡ ℕ.zero ℕ.zero ℕ.zero = refl
  +-⊝-assocˡ ℕ.zero ℕ.zero (ℕ.suc z) = refl
  +-⊝-assocˡ ℕ.zero (ℕ.suc y) ℕ.zero = refl
  +-⊝-assocˡ ℕ.zero (ℕ.suc y) (ℕ.suc z) rewrite (+-identityˡ (y ⊝ z)) = refl
  +-⊝-assocˡ (ℕ.suc x) ℕ.zero ℕ.zero = refl
  +-⊝-assocˡ (ℕ.suc x) ℕ.zero (ℕ.suc z) rewrite (ℕ.+-identityʳ x) = refl
  +-⊝-assocˡ (ℕ.suc x) (ℕ.suc y) ℕ.zero = refl
  +-⊝-assocˡ (ℕ.suc x) (ℕ.suc y) (ℕ.suc z) = begin
    (x ℕ.+ ℕ.suc y) ⊝ z  ≡⟨ cong (_⊝ z) (Nat-Properties.+-suc x y) ⟩
    (ℕ.suc x ℕ.+ y) ⊝ z  ≡⟨ +-⊝-assocˡ (ℕ.suc x) y z ⟩
    +[1+ x ] + (y ⊝ z)   ∎
    where open ≡-Reasoning

  +-⊝-assocʳ : (x y z : ℕ.ℕ) → (x ⊝ y) + (+ z) ≡ + x + (z ⊝ y)
  +-⊝-assocʳ = ?

  0-⊝ : (x : ℕ.ℕ) → 0 ⊝ x ≡ - (+ x)
  0-⊝ ℕ.zero = refl
  0-⊝ (ℕ.suc x) = refl

  ⊝-identityʳ : (x : ℕ.ℕ) → x ⊝ 0 ≡ + x
  ⊝-identityʳ = ?

  ⊝-suc : (x y z : ℕ.ℕ) → (x ⊝ ℕ.suc y) + -[1+ z ] ≡ (x ⊝ y) + -[1+ ℕ.suc z ]
  ⊝-suc ℕ.zero ℕ.zero z = refl
  ⊝-suc ℕ.zero (ℕ.suc y) z rewrite 0-⊝ (ℕ.suc y)
    rewrite sym (Nat-Properties.+-suc y z)
    rewrite sym (Nat-Properties.+-suc y (ℕ.suc z)) = refl
  ⊝-suc (ℕ.suc x) ℕ.zero z rewrite ⊝-identityʳ x = refl
  ⊝-suc (ℕ.suc x) (ℕ.suc y) z = ⊝-suc x y z

  +-assoc : (x y z : ℤ) → (x + y) + z ≡ x + (y + z)
  +-assoc (+ x) (+ y) (+ z) = cong +_ (ℕ.+-assoc x y z)
  +-assoc (+ x) (+ y) -[1+ z ] = +-⊝-assocˡ x y (ℕ.suc z)
  +-assoc (+ x) -[1+ y ] (+ z) = +-⊝-assocʳ x (ℕ.suc y) z
  +-assoc (+ x) -[1+ y ] -[1+ z ] =
    begin
      (x ⊝ ℕ.suc y) + -[1+ z ]
    ≡⟨ ⊝-suc x y z ⟩
      (x ⊝ y) + -[1+ ℕ.suc z ]
    ≡⟨ ? ⟩
      x ⊝ ℕ.suc (y ℕ.+ ℕ.suc z)
    ∎
    where open ≡-Reasoning
  +-assoc -[1+ x ] (+ y) (+ z) = begin
    (y ⊝ ℕ.suc x) + (+ z)  ≡⟨ +-⊝-assocʳ y (ℕ.suc x) z ⟩
    (+ y) + (z ⊝ ℕ.suc x)  ≡⟨ sym (+-⊝-assocˡ y z (ℕ.suc x)) ⟩
    (y ℕ.+ z) ⊝ ℕ.suc x    ∎
    where open ≡-Reasoning
  +-assoc -[1+ x ] (+ y) -[1+ z ] = {! !}
  +-assoc -[1+ x ] -[1+ y ] (+ z) = {! !}
  +-assoc -[1+ x ] -[1+ y ] -[1+ z ] =
    cong -[1+_] (ℕ.+-assoc x (ℕ.suc y) (ℕ.suc z))

  *-negateˡ : (x : ℤ) → -1ℤ * x ≡ - x
  *-negateˡ (+ ℕ.zero) = refl
  *-negateˡ +[1+ ℕ.zero ] = refl
  *-negateˡ +[1+ ℕ.suc x ]
    rewrite (Nat-Properties.+-suc x ℕ.zero)
    rewrite ℕ.+-identityʳ x = refl
  *-negateˡ -[1+ ℕ.zero ] = refl
  *-negateˡ -[1+ ℕ.suc x ]
    rewrite (Nat-Properties.+-suc x ℕ.zero)
    rewrite (ℕ.+-identityʳ x) = refl

  *-comm : (x y : ℤ) → x * y ≡ y * x
  *-comm (+ x) (+ ℕ.zero) = sym (*-zeroˡ (+ x))
  *-comm (+ ℕ.zero) +[1+ y ] = *-zeroˡ (+ ℕ.suc y)
  *-comm +[1+ x ] +[1+ ℕ.zero ] = sym (*-identityˡ (+ ℕ.suc x))
  *-comm +[1+ ℕ.zero ] +[1+ ℕ.suc y ] rewrite ℕ.+-comm y 1 = refl
  *-comm +[1+ ℕ.suc x ] +[1+ ℕ.suc y ] =
    begin
      +[1+ x ] * +[1+ y ] + +[1+ y ] + +[1+ ℕ.suc x ]
    ≡⟨ ? ⟩
      +[1+ y ] * +[1+ x ] + +[1+ x ] + +[1+ ℕ.suc y ]
    ∎
    where open ≡-Reasoning
  *-comm (+ ℕ.zero) -[1+ y ] = *-zeroˡ -[1+ y ]
  *-comm +[1+ x ] -[1+ ℕ.zero ] = sym (*-negateˡ (+ ℕ.suc x))
  *-comm +[1+ ℕ.zero ] -[1+ ℕ.suc y ] rewrite ℕ.+-comm y 1 = refl
  *-comm +[1+ ℕ.suc x ] -[1+ ℕ.suc y ] =
    begin
      +[1+ x ] * -[1+ y ] + -[1+ y ] + -[1+ ℕ.suc x ]
    ≡⟨ ? ⟩
      -[1+ y ] * +[1+ x ] + -[1+ x ] + -[1+ ℕ.suc y ]
    ∎
    where open ≡-Reasoning
  *-comm -[1+ x ] (+ ℕ.zero) = sym (*-zeroˡ -[1+ x ])
  *-comm -[1+ x ] +[1+ ℕ.zero ] = sym (*-identityˡ -[1+ x ])
  *-comm -[1+ ℕ.zero ] +[1+ ℕ.suc y ] rewrite ℕ.+-comm y 1 = refl
  *-comm -[1+ ℕ.suc x ] +[1+ ℕ.suc y ] =
    begin
      -[1+ x ] * +[1+ y ] + -[1+ y ] + -[1+ ℕ.suc x ]
    ≡⟨ ? ⟩
      +[1+ y ] * -[1+ x ] + -[1+ x ] + -[1+ ℕ.suc y ]
    ∎
    where open ≡-Reasoning
  *-comm -[1+ x ] -[1+ ℕ.zero ] = sym (*-negateˡ -[1+ x ])
  *-comm -[1+ ℕ.zero ] -[1+ ℕ.suc y ] rewrite ℕ.+-comm y 1 = refl
  *-comm -[1+ ℕ.suc x ] -[1+ ℕ.suc y ] =
    begin
      -[1+ x ] * -[1+ y ] + +[1+ y ] + +[1+ ℕ.suc x ]
    ≡⟨ ? ⟩
      -[1+ y ] * -[1+ x ] + +[1+ x ] + +[1+ ℕ.suc y ]
    ∎
    where open ≡-Reasoning


--   *-comm : (x y : ℤ) → x * y ≡ y * x
--   *-comm x (+ ℕ.zero) = sym (*-zeroˡ x)
--   *-comm (+ ℕ.zero) +[1+ y ] = *-zeroˡ (+ ℕ.suc y)
--   *-comm (+ ℕ.zero) -[1+ y ] = *-zeroˡ -[1+ y ]
--   *-comm +[1+ x ] +[1+ ℕ.zero ] = sym (*-identityˡ (+ ℕ.suc x))
--   *-comm +[1+ ℕ.zero ] +[1+ ℕ.suc y ] rewrite (ℕ.+-identityʳ y) = refl
--   *-comm +[1+ ℕ.suc x ] +[1+ ℕ.suc y ] = begin
--     +[1+ x ] * +[1+ y ] + +[1+ y ] + +[1+ ℕ.suc x ]  ≡⟨ cong (λ φ → φ + +[1+ y ] + +[1+ ℕ.suc x ]) (*-comm +[1+ x ] +[1+ y ]) ⟩
--     +[1+ y ] * +[1+ x ] + +[1+ y ] + +[1+ ℕ.suc x ]  ≡⟨ lemma₁ (+[1+ y ] * +[1+ x ]) y x ⟩
--     +[1+ y ] * +[1+ x ] + +[1+ x ] + +[1+ ℕ.suc y ]  ∎
--     where open ≡-Reasoning
--   *-comm -[1+ x ] +[1+ ℕ.zero ] = sym (*-identityˡ -[1+ x ])
--   *-comm -[1+ ℕ.zero ] +[1+ ℕ.suc y ] rewrite (ℕ.+-identityʳ y) = refl
--   *-comm -[1+ ℕ.suc x ] +[1+ ℕ.suc y ] = begin
--     -[1+ x ] * +[1+ y ] + -[1+ y ] + -[1+ ℕ.suc x ] ≡⟨ cong (λ φ → φ + -[1+ y ] + -[1+ ℕ.suc x ]) (*-comm -[1+ x ] +[1+ y ]) ⟩
--     +[1+ y ] * -[1+ x ] + -[1+ y ] + -[1+ ℕ.suc x ] ≡⟨ lemma₂ (+[1+ y ] * -[1+ x ]) y x ⟩
--     +[1+ y ] * -[1+ x ] + -[1+ x ] + -[1+ ℕ.suc y ] ∎
--     where open ≡-Reasoning
--   *-comm +[1+ x ] -[1+ ℕ.zero ] rewrite *-negateˡ +[1+ x ] = refl
--   *-comm +[1+ ℕ.zero ] -[1+ ℕ.suc y ] rewrite (ℕ.+-identityʳ y) = refl
--   *-comm +[1+ ℕ.suc x ] -[1+ ℕ.suc y ] = begin
--     +[1+ x ] * -[1+ y ] + -[1+ y ] + -[1+ ℕ.suc x ]  ≡⟨ cong (λ φ → φ + -[1+ y ] + -[1+ ℕ.suc x ]) (*-comm +[1+ x ] -[1+ y ]) ⟩
--     -[1+ y ] * +[1+ x ] + -[1+ y ] + -[1+ ℕ.suc x ]  ≡⟨ lemma₂ (-[1+ y ] * +[1+ x ]) y x ⟩
--     -[1+ y ] * +[1+ x ] + -[1+ x ] + -[1+ ℕ.suc y ]  ∎
--     where open ≡-Reasoning
--   *-comm -[1+ x ] -[1+ ℕ.zero ] = begin
--     +[1+ x ]             ≡⟨ sym (-‿involutive +[1+ x ]) ⟩
--     - -[1+ x ]           ≡⟨ sym (*-negateˡ -[1+ x ]) ⟩
--     -[1+ 0 ] * -[1+ x ]  ∎
--     where open ≡-Reasoning
--   *-comm -[1+ ℕ.zero ] -[1+ ℕ.suc y ] rewrite (ℕ.+-identityʳ y) = refl
--   *-comm -[1+ ℕ.suc x ] -[1+ ℕ.suc y ] = begin
--     -[1+ x ] * -[1+ y ] + +[1+ y ] + +[1+ ℕ.suc x ] ≡⟨ cong (λ φ → φ + +[1+ y ] + +[1+ ℕ.suc x ]) (*-comm -[1+ x ] -[1+ y ]) ⟩
--     -[1+ y ] * -[1+ x ] + +[1+ y ] + +[1+ ℕ.suc x ] ≡⟨ lemma₁ (-[1+ y ] * -[1+ x ]) y x ⟩
--     -[1+ y ] * -[1+ x ] + +[1+ x ] + +[1+ ℕ.suc y ] ∎
--     where open ≡-Reasoning

  open import Data.Product

  +‿-‿zero : (m : ℤ) → m + - m ≡ +0
  +‿-‿zero +0             = refl
  +‿-‿zero +[1+ ℕ.zero  ] = refl
  +‿-‿zero +[1+ ℕ.suc x ] = +‿-‿zero +[1+ x ]
  +‿-‿zero -[1+ ℕ.zero  ] = refl
  +‿-‿zero -[1+ ℕ.suc x ] = +‿-‿zero -[1+ x ]

  *-pos-neg : (m n : ℤ) → m * - n ≡ - m * n
  *-pos-neg m (+ ℕ.zero) = refl
  *-pos-neg m +[1+ ℕ.zero ] = refl
  *-pos-neg m +[1+ ℕ.suc x ] = begin
    m * (- +[1+ ℕ.suc x ])  ≡⟨⟩
    -[1+ x ] * m + - m      ≡⟨ congₘ (*-comm -[1+ x ] m) ⟩
    m * -[1+ x ] + - m      ≡⟨ congₘ (*-pos-neg m +[1+ x ]) ⟩
    (- m) * +[1+ x ] + - m  ≡⟨ congₘ (*-comm (- m) +[1+ x ]) ⟩
    +[1+ x ] * (- m) + - m  ≡⟨⟩
    (- m) * +[1+ ℕ.suc x ]  ∎
    where
      congₘ = cong (_+ (- m))
      open ≡-Reasoning
  *-pos-neg m -[1+ ℕ.zero ] = sym (-‿involutive m)
  *-pos-neg m -[1+ ℕ.suc x ] = begin
    m * - -[1+ ℕ.suc x ]    ≡⟨⟩
    - -[1+ x ] * m + m      ≡⟨ congₘ (*-comm (- -[1+ x ]) m) ⟩
    m * - -[1+ x ] + m      ≡⟨ congₘ (*-pos-neg m -[1+ x ]) ⟩
    (- m) * -[1+ x ] + m    ≡⟨ congₘ (*-comm (- m) -[1+ x ]) ⟩
    -[1+ x ] * - m + m      ≡⟨ cong (λ φ → -[1+ x ] * - m + φ)
                                    (sym (-‿involutive m)) ⟩
    -[1+ x ] * - m + - - m  ≡⟨⟩
    - m * -[1+ ℕ.suc x ]    ∎
    where
      congₘ = cong (_+ m)
      open ≡-Reasoning

  +-cong₂ : {a₁ a₂ b₁ b₂ : ℤ} → a₁ ≡ a₂ → b₁ ≡ b₂ → a₁ + b₁ ≡ a₂ + b₂
  +-cong₂ refl refl = refl

  *-cong₂ : {a₁ a₂ b₁ b₂ : ℤ} → a₁ ≡ a₂ → b₁ ≡ b₂ → a₁ * b₁ ≡ a₂ * b₂
  *-cong₂ refl refl = refl

  *-neg-neg : (m n : ℤ) → - m * - n ≡ m * n
  *-neg-neg m n = begin
    - m * - n  ≡⟨ *-pos-neg (- m) n ⟩
    - - m * n  ≡⟨ *-cong₂ (-‿involutive m) (refl {x = n}) ⟩
    m * n      ∎
    where open ≡-Reasoning

  -- -‿hom : (m n : ℕ.ℕ) → -[1+ m ] + -[1+ n ] ≡ -[1+ m ℕ.+ ℕ.suc n ]
  -- -‿hom ℕ.zero n = refl
  -- -‿hom (ℕ.suc m) n = cong (λ φ → -[1+ ℕ.suc φ ]) (sym (ℕ.+-suc m n))
```

