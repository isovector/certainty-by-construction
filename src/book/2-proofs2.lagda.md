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

  -‿involutive : (x : ℤ) → - (- x) ≡ x
  -‿involutive +0 = refl
  -‿involutive +[1+ n ] = refl
  -‿involutive -[1+ n ] = refl

  +-identityˡ : (x : ℤ) → 0ℤ + x ≡ x
  +-identityˡ x = refl

  +-identityʳ : (x : ℤ) → x + 0ℤ ≡ x
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
  *-identityˡ +[1+ ℕ.suc x ] =
    cong (λ φ → +[1+ ℕ.suc φ ]) (ℕ.+-identityʳ x)
  *-identityˡ -[1+ ℕ.zero ] = refl
  *-identityˡ -[1+ ℕ.suc x ] =
    cong (λ φ → -[1+ ℕ.suc φ ]) (ℕ.+-identityʳ x)

  +-comm : (x y : ℤ) → x + y ≡ y + x
  +-comm +0 y = sym (+-identityʳ y)
  +-comm +[1+ x ] +0 = refl
  +-comm -[1+ x ] +0 = refl
  +-comm +[1+ ℕ.suc x ] -[1+ ℕ.suc y ] = +-comm +[1+ x ] -[1+ y ]
  +-comm -[1+ ℕ.suc x ] +[1+ ℕ.suc y ] = +-comm -[1+ x ] +[1+ y ]
  +-comm +[1+ x ] +[1+ y ] = cong (λ φ → +[1+ ℕ.suc φ ]) (ℕ.+-comm x y)
  +-comm -[1+ x ] -[1+ y ] = cong (λ φ → -[1+ ℕ.suc φ ]) (ℕ.+-comm x y)
  +-comm +[1+ ℕ.zero ] -[1+ ℕ.zero ] = refl
  +-comm +[1+ ℕ.zero ] -[1+ ℕ.suc y ] = refl
  +-comm +[1+ ℕ.suc x ] -[1+ ℕ.zero ] = refl
  +-comm -[1+ ℕ.zero ] +[1+ ℕ.zero ] = refl
  +-comm -[1+ ℕ.zero ] +[1+ ℕ.suc y ] = refl
  +-comm -[1+ ℕ.suc x ] +[1+ ℕ.zero ] = refl

  lemma₁ : (z : ℤ) → (x y : ℕ.ℕ) → z + +[1+ x ] + +[1+ ℕ.suc y ] ≡ z + +[1+ y ] + +[1+ ℕ.suc x ]
  lemma₁ (+ ℕ.zero) x y
    rewrite Nat-Properties.+-suc y x
    rewrite ℕ.+-comm x (ℕ.suc y) = refl
  lemma₁ +[1+ z ] x y = cong (λ φ → +[1+ ℕ.suc (ℕ.suc φ) ]) ( begin
    z ℕ.+ x ℕ.+ ℕ.suc y    ≡⟨ ℕ.+-assoc z x (ℕ.suc y) ⟩
    z ℕ.+ (x ℕ.+ ℕ.suc y)  ≡⟨ cong (z ℕ.+_) (ℕ.+-comm x (ℕ.suc y)) ⟩
    z ℕ.+ (ℕ.suc y ℕ.+ x)  ≡⟨ cong (z ℕ.+_) (sym (Nat-Properties.+-suc y x)) ⟩
    z ℕ.+ (y ℕ.+ ℕ.suc x)  ≡⟨ sym (ℕ.+-assoc z y (ℕ.suc x)) ⟩
    z ℕ.+ y ℕ.+ ℕ.suc x    ∎
    )
    where open ≡-Reasoning
  lemma₁ -[1+ z ] x y =
    begin
      -[1+ z ] + +[1+ x ] + +[1+ ℕ.suc y ]
    ≡⟨ ? ⟩
      -[1+ z ] + +[1+ y ] + +[1+ ℕ.suc x ]
    ∎
    where open ≡-Reasoning

  lemma₂ : (z : ℤ) → (x y : ℕ.ℕ) → z + -[1+ x ] + -[1+ ℕ.suc y ] ≡ z + -[1+ y ] + -[1+ ℕ.suc x ]
  lemma₂ = ?

  *-negateˡ : (x : ℤ) → -1ℤ * x ≡ - x
  *-negateˡ (+ ℕ.zero) = refl
  *-negateˡ +[1+ ℕ.zero ] = refl
  *-negateˡ +[1+ ℕ.suc x ] rewrite (ℕ.+-identityʳ x) = refl
  *-negateˡ -[1+ ℕ.zero ] = refl
  *-negateˡ -[1+ ℕ.suc x ] rewrite (ℕ.+-identityʳ x) = refl

  *-comm : (x y : ℤ) → x * y ≡ y * x
  *-comm x (+ ℕ.zero) = sym (*-zeroˡ x)
  *-comm (+ ℕ.zero) +[1+ y ] = *-zeroˡ (+ ℕ.suc y)
  *-comm (+ ℕ.zero) -[1+ y ] = *-zeroˡ -[1+ y ]
  *-comm +[1+ x ] +[1+ ℕ.zero ] = sym (*-identityˡ (+ ℕ.suc x))
  *-comm +[1+ ℕ.zero ] +[1+ ℕ.suc y ] rewrite (ℕ.+-identityʳ y) = refl
  *-comm +[1+ ℕ.suc x ] +[1+ ℕ.suc y ] = begin
    +[1+ x ] * +[1+ y ] + +[1+ y ] + +[1+ ℕ.suc x ]  ≡⟨ cong (λ φ → φ + +[1+ y ] + +[1+ ℕ.suc x ]) (*-comm +[1+ x ] +[1+ y ]) ⟩
    +[1+ y ] * +[1+ x ] + +[1+ y ] + +[1+ ℕ.suc x ]  ≡⟨ lemma₁ (+[1+ y ] * +[1+ x ]) y x ⟩
    +[1+ y ] * +[1+ x ] + +[1+ x ] + +[1+ ℕ.suc y ]  ∎
    where open ≡-Reasoning
  *-comm -[1+ x ] +[1+ ℕ.zero ] = sym (*-identityˡ -[1+ x ])
  *-comm -[1+ ℕ.zero ] +[1+ ℕ.suc y ] rewrite (ℕ.+-identityʳ y) = refl
  *-comm -[1+ ℕ.suc x ] +[1+ ℕ.suc y ] = begin
    -[1+ x ] * +[1+ y ] + -[1+ y ] + -[1+ ℕ.suc x ] ≡⟨ cong (λ φ → φ + -[1+ y ] + -[1+ ℕ.suc x ]) (*-comm -[1+ x ] +[1+ y ]) ⟩
    +[1+ y ] * -[1+ x ] + -[1+ y ] + -[1+ ℕ.suc x ] ≡⟨ lemma₂ (+[1+ y ] * -[1+ x ]) y x ⟩
    +[1+ y ] * -[1+ x ] + -[1+ x ] + -[1+ ℕ.suc y ] ∎
    where open ≡-Reasoning
  *-comm +[1+ x ] -[1+ ℕ.zero ] rewrite *-negateˡ +[1+ x ] = refl
  *-comm +[1+ ℕ.zero ] -[1+ ℕ.suc y ] rewrite (ℕ.+-identityʳ y) = refl
  *-comm +[1+ ℕ.suc x ] -[1+ ℕ.suc y ] = begin
    +[1+ x ] * -[1+ y ] + -[1+ y ] + -[1+ ℕ.suc x ]  ≡⟨ cong (λ φ → φ + -[1+ y ] + -[1+ ℕ.suc x ]) (*-comm +[1+ x ] -[1+ y ]) ⟩
    -[1+ y ] * +[1+ x ] + -[1+ y ] + -[1+ ℕ.suc x ]  ≡⟨ lemma₂ (-[1+ y ] * +[1+ x ]) y x ⟩
    -[1+ y ] * +[1+ x ] + -[1+ x ] + -[1+ ℕ.suc y ]  ∎
    where open ≡-Reasoning
  *-comm -[1+ x ] -[1+ ℕ.zero ] = begin
    +[1+ x ]             ≡⟨ sym (-‿involutive +[1+ x ]) ⟩
    - -[1+ x ]           ≡⟨ sym (*-negateˡ -[1+ x ]) ⟩
    -[1+ 0 ] * -[1+ x ]  ∎
    where open ≡-Reasoning
  *-comm -[1+ ℕ.zero ] -[1+ ℕ.suc y ] rewrite (ℕ.+-identityʳ y) = refl
  *-comm -[1+ ℕ.suc x ] -[1+ ℕ.suc y ] = begin
    -[1+ x ] * -[1+ y ] + +[1+ y ] + +[1+ ℕ.suc x ] ≡⟨ cong (λ φ → φ + +[1+ y ] + +[1+ ℕ.suc x ]) (*-comm -[1+ x ] -[1+ y ]) ⟩
    -[1+ y ] * -[1+ x ] + +[1+ y ] + +[1+ ℕ.suc x ] ≡⟨ lemma₁ (-[1+ y ] * -[1+ x ]) y x ⟩
    -[1+ y ] * -[1+ x ] + +[1+ x ] + +[1+ ℕ.suc y ] ∎
    where open ≡-Reasoning

  postulate
    -- *-comm : (m n : ℤ) → m * n ≡ n * m
    +-assoc : (x y z : ℤ) → (x + y) + z ≡  x + (y + z)

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

  -‿hom : (m n : ℕ.ℕ) → -[1+ m ] + -[1+ n ] ≡ -[1+ m ℕ.+ ℕ.suc n ]
  -‿hom ℕ.zero n = refl
  -‿hom (ℕ.suc m) n = cong (λ φ → -[1+ ℕ.suc φ ]) (sym (ℕ.+-suc m n))

