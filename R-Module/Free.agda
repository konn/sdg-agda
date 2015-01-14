{-# OPTIONS --universe-polymorphism #-}
open import Level
open import Algebra

module R-Module.Free {c ℓ} (R : CommutativeRing c ℓ) where
open import R-Module R
import Algebra.FunctionProperties as FunctionProperties
import Relation.Binary.EqReasoning as EqR
open import Algebra.Structures
open import Relation.Binary
open import Relation.Binary.Core
open import Function hiding (const)
open import Data.Product
open import Data.Nat using  (ℕ)
open import Data.Fin using (Fin)
open import Function.Equality hiding (setoid)
import HomSetoid as I

open FunctionProperties using (Op₁ ; Op₂)

FreeModule : ∀{c′ ℓ′} → Setoid c′ ℓ′ → R-Module (ℓ′ ⊔ c′ ⊔ ℓ ⊔ c) (ℓ′ ⊔ c′ ⊔ ℓ)
FreeModule A = 
  record { Carrier = Carrier
         ; isR-Module = isR-Module
         }
  where
    infix  8 -_
    infixr 7 _*>_
    infixl 6 _+_

    setoid = A ⇨ setoidR
    open Setoid setoid
         renaming ( isEquivalence to ≈-equiv
                  ; sym   to ≈-sym
                  ; refl  to ≈-refl
                  ; trans to ≈-trans
                  )
    open EqR setoidR
         renaming ( _≈⟨_⟩_  to _≈R⟨_⟩_
                  ; begin_ to beginR_
                  ; _∎     to _∎R
                  ; _≡⟨⟩_   to _≡R⟨⟩_)

    open EqR setoid

    _+_ : Op₂ Carrier
    a + b = record { _⟨$⟩_ = λ x → (a ⟨$⟩ x) +R (b ⟨$⟩ x)
                   ; cong = λ {i} {j} i≈j →
                              beginR
                                (a ⟨$⟩ i) +R (b ⟨$⟩ i)
                              ≈R⟨ +R-cong (cong a i≈j) (cong b i≈j) ⟩
                                (a ⟨$⟩ j) +R (b ⟨$⟩ j)
                              ∎R
                   }

    0# : Carrier
    0# = const 0R

    _*>_ : Coeff → Carrier → Carrier
    a *> x = record { _⟨$⟩_ = λ i -> a *R (x ⟨$⟩ i)
                    ; cong = λ {i} {j} i≈j →
                               beginR
                                 a *R (x ⟨$⟩ i)
                               ≈R⟨ *R-cong ≈R-refl (cong x i≈j) ⟩
                                 a *R (x ⟨$⟩ j)
                               ∎R
                    }

    -_ : Op₁ Carrier
    - f = record { _⟨$⟩_ = λ x → -R (f ⟨$⟩ x)
                 ; cong = λ {i} {j} i≈j →
                            beginR
                              -R (f ⟨$⟩ i)
                            ≈R⟨ -R‿cong (cong f i≈j) ⟩
                              -R (f ⟨$⟩ j)
                            ∎R
                 }

    open FunctionProperties _≈_
    assoc : Associative _+_
    assoc a b c {x} {y} x≈y =
      beginR
        ((a + b + c) ⟨$⟩ x)
      ≡R⟨⟩
        ((a + b) ⟨$⟩ x) +R (c ⟨$⟩ x)
      ≡R⟨⟩
        ((a ⟨$⟩ x) +R (b ⟨$⟩ x)) +R (c ⟨$⟩ x)
      ≈R⟨ +R-assoc (a ⟨$⟩ x) (b ⟨$⟩ x) (c ⟨$⟩ x) ⟩
        (a ⟨$⟩ x) +R ((b ⟨$⟩ x) +R (c ⟨$⟩ x))
      ≡R⟨⟩
        (a ⟨$⟩ x) +R ((b + c) ⟨$⟩ x)
      ≡R⟨⟩
        (a + (b + c)) ⟨$⟩ x
      ≈R⟨ cong (a + (b + c)) x≈y ⟩
        (a + (b + c)) ⟨$⟩ y
      ∎R

    +-congs : _+_ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_
    +-congs {f} {f′} {g} {g′} f≈f′ g≈g′ {x} {y} x≈y =
      beginR
        (f + g) ⟨$⟩ x
      ≡R⟨⟩
        (f ⟨$⟩ x) +R (g ⟨$⟩ x)
      ≈R⟨ +R-cong (f≈f′ x≈y) (g≈g′ x≈y) ⟩
        (f′ + g′) ⟨$⟩ y
      ∎R

    comm : Commutative _+_
    comm f g {x} {y} x≈y =
      beginR
        (f + g) ⟨$⟩ x
      ≡R⟨⟩
        (f ⟨$⟩ x) +R  (g ⟨$⟩ x)
      ≈R⟨ +R-comm (f ⟨$⟩ x) (g ⟨$⟩ x) ⟩
        (g + f) ⟨$⟩ x
      ≈R⟨ cong (g + f) x≈y ⟩
        (g + f) ⟨$⟩ y
      ∎R

    isSemigroup : IsSemigroup _≈_ _+_
    isSemigroup = record { isEquivalence = ≈-equiv
                         ; assoc = assoc
                         ; ∙-cong = λ {f} {f′} {g} {g′} f≈f′ g≈g′ {x} {y} →
                                      +-congs {f} {f′} {g} {g′} f≈f′ g≈g′ {x} {y}
                         }

    identityʳ : RightIdentity 0# _+_
    identityʳ f {x} {y} x≈y =
      beginR
        (f + 0#) ⟨$⟩ x
      ≡R⟨⟩
        (f ⟨$⟩ x) +R (0# ⟨$⟩ x)
      ≡R⟨⟩
        (f ⟨$⟩ x) +R 0R
      ≈R⟨ proj₂ +R-identity (f ⟨$⟩ x) ⟩
        f ⟨$⟩ x
      ≈R⟨ cong f x≈y ⟩
        f ⟨$⟩ y
      ∎R

    identityˡ : LeftIdentity 0# _+_
    identityˡ f =
      begin
        0# + f
      ≈⟨ comm 0# f ⟩
        f + 0#
      ≈⟨ identityʳ f ⟩
        f
      ∎

    identity : Identity 0# _+_
    identity = (identityˡ , identityʳ)

    isMonoid : IsMonoid _≈_ _+_ 0#
    isMonoid = record { isSemigroup = isSemigroup
                      ; identity = identity
                      }

    inverseʳ : RightInverse 0# -_ _+_
    inverseʳ f {x} {y} x≈y =
      beginR
        (f + - f) ⟨$⟩ x
      ≡R⟨⟩
        (f ⟨$⟩ x) +R ((- f) ⟨$⟩ x)
      ≡R⟨⟩
        (f ⟨$⟩ x) +R -R (f ⟨$⟩ x)
      ≈R⟨ proj₂ -R‿inverse (f ⟨$⟩ x) ⟩
        0R
      ≡R⟨⟩
       0# ⟨$⟩ x
      ∎R

    inverseˡ : LeftInverse 0# -_ _+_
    inverseˡ f =
      begin
        - f + f
      ≈⟨ comm (- f) f ⟩
        f + - f
      ≈⟨ inverseʳ f ⟩
        0#
      ∎

    inverse : Inverse 0# -_ _+_
    inverse = ( inverseˡ , inverseʳ )

    ⁻¹-cong : -_ Preserves _≈_ ⟶ _≈_
    ⁻¹-cong {f} {g} f≈g {x} {y} x≈y =
      beginR
        (- f) ⟨$⟩ x
      ≡R⟨⟩
        -R (f ⟨$⟩ x)
      ≈R⟨ -R‿cong (f≈g x≈y) ⟩
        -R (g ⟨$⟩ y)
      ≡R⟨⟩
        (- g) ⟨$⟩ y
      ∎R

    isGroup : IsGroup _≈_ _+_ 0# -_
    isGroup = record { isMonoid = isMonoid
                     ; inverse  = inverse
                     ; ⁻¹-cong   = λ {f} {g} f≈g {x} {y} x≈y →
                                     ⁻¹-cong {f} {g} f≈g {x} {y} x≈y
                     }

    isAbelianGroup : IsAbelianGroup _≈_ _+_ 0# -_
    isAbelianGroup = record { comm = comm
                            ; isGroup = isGroup
                            }

    *>-assoc : ∀ a b x → (a *R b) *> x ≈ a *> b *> x
    *>-assoc a b v {x} {y} x≈y =
      beginR
        ((a *R b) *> v) ⟨$⟩ x
      ≡R⟨⟩
        (a *R b) *R (v ⟨$⟩ x)
      ≈R⟨ *R-assoc a b (v ⟨$⟩ x) ⟩
        a *R (b *R (v ⟨$⟩ x))
      ≡R⟨⟩
        (a *> b *> v) ⟨$⟩ x
      ≈R⟨ cong (a *> b *> v) x≈y ⟩
        (a *> b *> v) ⟨$⟩ y
      ∎R

    *>-+-distrib : ∀ a x y → (a *> (x + y)) ≈ ((a *> x) + (a *> y))
    *>-+-distrib a v u {x} {y} x≈y =
      beginR
        (a *> (v + u)) ⟨$⟩ x
      ≡R⟨⟩
        a *R ((v ⟨$⟩ x) +R (u ⟨$⟩ x))
      ≈R⟨ proj₁ R-distrib a (v ⟨$⟩ x) (u ⟨$⟩ x)  ⟩
        (a *R (v ⟨$⟩ x)) +R (a *R (u ⟨$⟩ x))
      ≡R⟨⟩
        ((a *> v) + (a *> u)) ⟨$⟩ x
      ≈R⟨ cong (a *> v + a *> u) x≈y ⟩
        ((a *> v) + (a *> u)) ⟨$⟩ y
      ∎R

    +-*>-distrib : ∀ a b v → ((a +R b) *> v) ≈ ((a *> v) + (b *> v))
    +-*>-distrib a b v {x} {y} x≈y =
      beginR
        ((a +R b) *> v) ⟨$⟩ x
      ≡R⟨⟩
        (a +R b) *R (v ⟨$⟩ x)
      ≈R⟨ proj₂ R-distrib (v ⟨$⟩ x) a b ⟩
        a *R (v ⟨$⟩ x) +R b *R (v ⟨$⟩ x)
      ≡R⟨⟩
        (a *> v + b *> v) ⟨$⟩ x
      ≈R⟨ cong (a *> v + b *> v) x≈y ⟩
        (a *> v + b *> v) ⟨$⟩ y
      ∎R

    *>-identity : ∀ x → (1R *> x) ≈ x
    *>-identity v {x} {y} x≈y =
      beginR
        (1R *> v) ⟨$⟩ x
      ≡R⟨⟩
        1R *R (v ⟨$⟩ x)
      ≈R⟨ proj₁ *R-identity (v ⟨$⟩ x)  ⟩
        v ⟨$⟩ x
      ≈R⟨ cong v x≈y  ⟩
        v ⟨$⟩ y
      ∎R

    *>-cong : _*>_ Preserves₂ _≈R_ ⟶ _≈_ ⟶ _≈_
    *>-cong {a} {b} {x} {y} a≈b x≈y {k} {k′} k≈k′ =
      beginR
        (a *> x) ⟨$⟩ k
      ≡R⟨⟩
        a *R (x ⟨$⟩ k)
      ≈R⟨ *R-cong ≈R-refl (x≈y k≈k′) ⟩
        a *R (y ⟨$⟩ k′)
      ≈R⟨ *R-cong a≈b ≈R-refl ⟩
        b *R (y ⟨$⟩ k′)
      ≡R⟨⟩
        (b *> y) ⟨$⟩ k′
      ∎R

    isR-Module : IsR-Module _≈_ _+_ _*>_ -_ 0#
    isR-Module = record { isAbelianGroup = isAbelianGroup
                        ; *>-assoc = *>-assoc
                        ; *>-cong  =
                          λ {a} {b} {x} {y} a≈b x≈y {k} {k′} k≈k′ →
                                *>-cong {a} {b} {x} {y} a≈b x≈y {k} {k′} k≈k′
                        ; *>-+-distrib = *>-+-distrib
                        ; +-*>-distrib = +-*>-distrib
                        ; *>-identity = *>-identity
                        }

_DimFreeModule : (n : ℕ) → R-Module _ _
n DimFreeModule = FreeModule (I.0-Setoid $ Fin n)
