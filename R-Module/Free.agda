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
open import Function
open import Data.Product
open import Data.Nat using  (ℕ)
open import Data.Fin using (Fin)
open import Function.Equality hiding (setoid)

open FunctionProperties using (Op₁ ; Op₂)

FreeModule : ∀{c′} → Set c′ → R-Module (c′ ⊔ c) (c′ ⊔ ℓ)
FreeModule A = 
  record { Carrier = Carrier
         ; isR-Module = isR-Module
         }
  where
    infix  8 -_
    infixr 7 _*>_
    infixl 6 _+_

    isetoidR = Setoid.indexedSetoid setoidR
    setoid   = ≡-setoid A isetoidR
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
    a + b = λ x → a x +R b x

    0# : Carrier
    0# = λ _ → 0R

    _*>_ : Coeff → Carrier → Carrier
    a *> x = λ i -> a *R x i

    -_ : Op₁ Carrier
    - f = λ x → -R (f x)

    open FunctionProperties _≈_
    assoc : Associative _+_
    assoc a b c x =
      beginR
        (a + b + c) x
      ≡R⟨⟩
        ((a + b) x) +R c x
      ≡R⟨⟩
        (a x +R b x) +R c x
      ≈R⟨ +R-assoc (a x) (b x) (c x) ⟩
        a x +R (b x +R c x)
      ≡R⟨⟩
        a x +R (b + c) x
      ≡R⟨⟩
        (a + (b + c)) x
      ∎R

    +-congs : _+_ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_
    +-congs {f} {f′} {g} {g′} f≈f′ g≈g′ x =
      beginR
        (f + g) x
      ≡R⟨⟩
        f x +R g x
      ≈R⟨ +R-cong (f≈f′ x) (g≈g′ x) ⟩
        (f′ + g′) x
      ∎R

    comm : Commutative _+_
    comm f g x =
      beginR
        (f + g) x
      ≡R⟨⟩
        f x +R g x
      ≈R⟨ +R-comm (f x) (g x) ⟩
        (g + f) x
      ∎R

    isSemigroup : IsSemigroup _≈_ _+_
    isSemigroup = record { isEquivalence = ≈-equiv
                         ; assoc = assoc
                         ; ∙-cong = +-congs
                         }

    identityʳ : RightIdentity 0# _+_
    identityʳ f x =
      beginR
        (f + 0#) x
      ≡R⟨⟩
        f x +R 0# x
      ≡R⟨⟩
        f x +R 0R
      ≈R⟨ proj₂ +R-identity (f x) ⟩
        f x
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
    inverseʳ f x =
      beginR
        (f + - f) x
      ≡R⟨⟩
        f x +R (- f) x
      ≡R⟨⟩
        f x +R -R (f x)
      ≈R⟨ proj₂ -R‿inverse (f x) ⟩
        0R
      ≡R⟨⟩
       0# x
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
    ⁻¹-cong {f} {g} f≈g x =
      beginR
        (- f) x
      ≡R⟨⟩
        -R (f x)
      ≈R⟨ -R‿cong (f≈g x) ⟩
        -R (g x)
      ≡R⟨⟩
        (- g) x
      ∎R

    isGroup : IsGroup _≈_ _+_ 0# -_
    isGroup = record { isMonoid = isMonoid
                     ; inverse  = inverse
                     ; ⁻¹-cong   = ⁻¹-cong
                     }

    isAbelianGroup : IsAbelianGroup _≈_ _+_ 0# -_
    isAbelianGroup = record { comm = comm
                            ; isGroup = isGroup
                            }

    *>-assoc : ∀ a b x → (a *R b) *> x ≈ a *> b *> x
    *>-assoc a b v x =
      beginR
        ((a *R b) *> v) x
      ≡R⟨⟩
        (a *R b) *R v x
      ≈R⟨ *R-assoc a b (v x) ⟩
        a *R (b *R v x)
      ≡R⟨⟩
        (a *> b *> v) x
      ∎R

    *>-+-distrib : ∀ a x y → (a *> (x + y)) ≈ ((a *> x) + (a *> y))
    *>-+-distrib a v u x =
      beginR
        (a *> (v + u)) x
      ≡R⟨⟩
        a *R (v x +R u x)
      ≈R⟨ proj₁ R-distrib a (v x) (u x)  ⟩
        (a *R v x) +R (a *R u x)
      ≡R⟨⟩
        ((a *> v) + (a *> u)) x
      ∎R

    +-*>-distrib : ∀ a b v → ((a +R b) *> v) ≈ ((a *> v) + (b *> v))
    +-*>-distrib a b v x =
      beginR
        ((a +R b) *> v) x
      ≡R⟨⟩
        (a +R b) *R v x
      ≈R⟨ proj₂ R-distrib (v x) a b ⟩
        a *R v x +R b *R v x
      ≡R⟨⟩
        (a *> v + b *> v) x
      ∎R

    *>-identity : ∀ x → (1R *> x) ≈ x
    *>-identity v x =
      beginR
        (1R *> v) x
      ≡R⟨⟩
        1R *R v x
      ≈R⟨ proj₁ *R-identity (v x)  ⟩
        v x
      ∎R

    *>-cong : _*>_ Preserves₂ _≈R_ ⟶ _≈_ ⟶ _≈_
    *>-cong {a} {b} {x} {y} a≈b x≈y k =
      beginR
        (a *> x) k
      ≡R⟨⟩
        a *R x k
      ≈R⟨ *R-cong ≈R-refl (x≈y k) ⟩
        a *R y k
      ≈R⟨ *R-cong a≈b ≈R-refl ⟩
        b *R y k
      ≡R⟨⟩
        (b *> y) k
      ∎R

    isR-Module : IsR-Module _≈_ _+_ _*>_ -_ 0#
    isR-Module = record { isAbelianGroup = isAbelianGroup
                        ; *>-assoc = *>-assoc
                        ; *>-cong  = *>-cong
                        ; *>-+-distrib = *>-+-distrib
                        ; +-*>-distrib = +-*>-distrib
                        ; *>-identity = *>-identity
                        }

_DimFreeModule : (n : ℕ) → R-Module (Level.zero ⊔ c) (Level.zero ⊔ ℓ)
n DimFreeModule = FreeModule (Fin n)
