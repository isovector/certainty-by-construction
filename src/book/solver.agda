module solver where


open import Level using (Level)
open import Algebra.Bundles using (CommutativeSemiring)

module RingSolver {c ℓ : Level} (ring : CommutativeSemiring c ℓ) where
  open CommutativeSemiring ring renaming (Carrier to A; zero to A-zero)
  open import Data.Nat
    using (ℕ; zero; suc)
  open import Data.Fin
    using (Fin)
  open import Data.Product

  *-zeroˡ : (x : A) → 0# * x ≈ 0#
  *-zeroˡ = proj₁ A-zero

  *-zeroʳ : (x : A) → x * 0# ≈ 0#
  *-zeroʳ = proj₂ A-zero


  data Syn (n : ℕ) : Set c where
    var : Fin n → Syn n
    con : A → Syn n
    _:+_ : Syn n → Syn n → Syn n
    _:*_ : Syn n → Syn n → Syn n

  private variable
    n : ℕ

  ⟦_⟧ : Syn n → (Fin n → A) → A
  ⟦ var v ⟧  vs = vs v
  ⟦ con c ⟧  vs = c
  ⟦ x :+ y ⟧ vs = ⟦ x ⟧ vs + ⟦ y ⟧ vs
  ⟦ x :* y ⟧ vs = ⟦ x ⟧ vs * ⟦ y ⟧ vs

  mutual
    data HNF : ℕ → Set c where
      con : Poly n → HNF n
      x⟨_⟩+_ : HNF (suc n) → Poly (suc n) → HNF (suc n)
    infixl 4 x⟨_⟩+_

    data Poly : ℕ → Set c where
      con : A → Poly zero
      poly : HNF n → Poly (suc n)

  ↪ : A → HNF n
  ↪ {zero} x = con (con x)
  ↪ {suc n} x = con (poly (↪ x))

  ↪P : A → Poly n
  ↪P {zero} x = con x
  ↪P {suc n} x = poly (↪ x)

  0H : HNF n
  0H = ↪ 0#

  1H : HNF n
  1H = ↪ 1#



  x²+y²+xy : Poly 3
  x²+y²+xy = poly
    (x⟨ x⟨ 1H ⟩+ poly (x⟨ 1H ⟩+ poly 0H) ⟩+
        poly (x⟨ (x⟨ 1H ⟩+ poly 0H) ⟩+ poly 0H))

  mutual
    _+H_ : HNF n → HNF n → HNF n
    con x +H con x₁ = con (x +P x₁)
    con x +H (x⟨ x₁ ⟩+ x₂) = x⟨ x₁ ⟩+ (x +P x₂)
    (x⟨ x₁ ⟩+ x₂) +H con x = x⟨ x₁ ⟩+ (x +P x₂)
    (x⟨ x₁ ⟩+ x₂) +H (x⟨ x₃ ⟩+ x₄) = x⟨ x₁ +H x₃ ⟩+ (x₂ +P x₄)
    infixr 4 _+H_

    _+P_ : Poly n → Poly n → Poly n
    con x +P con x₁ = con (x + x₁)
    poly x +P poly x₁ = poly (x +H x₁)


  _*x+H_ : HNF (suc n) → HNF (suc n) → HNF (suc n)
  x *x+H (x⟨ x₁ ⟩+ x₂) = x⟨ x +H x₁ ⟩+ x₂
  con x *x+H con x₁ = x⟨ con x ⟩+ x₁
  (x⟨ x ⟩+ x₂) *x+H con x₁ = x⟨ x⟨ x ⟩+ x₂ ⟩+ x₁

  mutual
    _*PH_ : Poly n → HNF n → HNF n
    con x *PH con (con x₁) = con (con (x * x₁))
    poly x *PH con (poly x₁) = con (poly (x *H x₁))
    poly x *PH (x⟨ x₁ ⟩+ poly x₂) = x⟨ poly x *PH x₁ ⟩+ poly (x *H x₂)

    _*P_ : Poly n → Poly n → Poly n
    con x *P con x₁ = con (x * x₁)
    poly x *P poly x₁ = poly (x *H x₁)

    _*H_ : HNF n → HNF n → HNF n
    con x *H con x₁ = con (x *P x₁)
    con (poly x) *H (x⟨ x₁ ⟩+ poly x₂) = x⟨ poly x *PH x₁ ⟩+ poly (x *H x₂)
    (x⟨ x₁ ⟩+ poly x₂) *H con (poly x) = x⟨ poly x *PH x₁ ⟩+ poly (x *H x₂)
    (x⟨ x ⟩+ poly x₁) *H (x⟨ x₂ ⟩+ poly x₃)
      = ((x *H x₂) *x+H ((poly x₃ *PH x) +H (poly x₁ *PH x₂))) *x+H (con (poly (x₁ *H x₃)))

  to-var : Fin n → Poly (suc n)
  to-var Fin.zero = poly (x⟨ 1H ⟩+ poly 0H)
  to-var (Fin.suc x) = poly (x⟨ 0H ⟩+ to-var x)

  normalize : Syn n → Poly (suc n)
  normalize (var x) = to-var x
  normalize (con x) = ↪P x
  normalize (x :+ x₁) = normalize x +P normalize x₁
  normalize (x :* x₁) = normalize x *P normalize x₁

  open import Function using (_∘_)

  eval : (Fin n → A) → Poly (suc n) → A
  eval {n} f (poly (con x)) = {! !}
  eval {.(suc _)} f (poly (x⟨ x ⟩+ x₁)) = {! !}
  -- eval f (con (con x)) = x
  -- eval f (con (poly x)) = eval (f ∘ Fin.suc) x
  -- eval f (x⟨ x ⟩+ poly x₁) = f Fin.zero * eval f x + eval (f ∘ Fin.suc) x₁





  import Relation.Binary.PropositionalEquality as PropEq
  open PropEq using (_≡_)

  eval-is-norm : (f : Fin (n) → A) → (s : Syn n) → ⟦ s ⟧ f ≡ eval f (normalize s)
  eval-is-norm = ?


  -- DIDITWORK : blah PropEq.≡ x²+y²+xy
  -- DIDITWORK = {! PropEq.refl !}


--       -- con x *H con x₁ = con (x *P x₁)
--     -- con x *H (x⟨ x₁ ⟩+ x₂) = x⟨ x *PH x₁ ⟩+ ?
--     -- -- con (con x) *H (x⟨ x₁ ⟩+ x₂) = x⟨ x *SH x₁ ⟩+ (x *SP x₂)
--     -- -- con (poly x) *H (x⟨ x₁ ⟩+ x₂) = x⟨ ? ⟩+ ?
--     -- (x⟨ x ⟩+ x₁) *H con (con x₂) = x⟨ x₂ *SH x ⟩+ (x₂ *SP x₁)
--     -- (x⟨ x ⟩+ x₁) *H con (poly x₂) = {! x* (x₂ *H x) +H (x₁ *PH x₂) !}
--     -- (x⟨ x ⟩+ x₁) *H (x⟨ x₂ ⟩+ x₃)
--     --   =  x* (x* (x *H x₂))
--     --   +H x* {! (x₃ *PH x) !}
--     --   +H x* {! (x₁ *PH x₂) !}
--     --   +H ?

--     _*P_ : Poly n → Poly n → Poly n
--     con x *P con x₁ = con (x * x₁)
--     con x *P poly x₁ = poly (x *SH x₁)
--     poly x *P con x₁ = poly (x₁ *SH x)
--     poly x *P poly x₁ = poly ?
