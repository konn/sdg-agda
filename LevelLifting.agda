module LevelLifting where
open import Level
open import Algebra.FunctionProperties
open import Function
open import Data.Product
open import Relation.Binary
open import Algebra.Structures

LiftWith : ∀{c} → (ℓ : Level) → (A : Set c) → Set (c ⊔ ℓ)
LiftWith ℓ A = Lift {ℓ = ℓ} A

lift-Rel : ∀{c ℓ u r} {A : Set u} → Rel A r → Rel (LiftWith c A) (r ⊔ ℓ)
lift-Rel {c} {ℓ} {u} {r} {A} R = λ a b → Lift { ℓ = ℓ } $ R (lower a) (lower b)

lift-Op₁ : ∀{c ℓ} {A : Set c} → Op₁ A → Op₁ (LiftWith ℓ A)
lift-Op₁ f = lift ∘ f ∘ lower

lift-Op₂ : ∀{c ℓ} {A : Set c} → Op₂ A → Op₂ (LiftWith ℓ A)
lift-Op₂ _•_ = λ x y → lift (lower x • lower y)

lift-IsEquivalence : ∀{c ℓ c′ ℓ′} {A : Set c} {_≈_ : Rel A ℓ}
                   → IsEquivalence _≈_
                   → IsEquivalence (lift-Rel {c = c′} {ℓ = ℓ′} _≈_)
lift-IsEquivalence isEq = record { refl = lift refl
                                 ; sym  = λ x → lift $ sym $ lower x
                                 ; trans = λ x x₁ → lift $ trans (lower x) (lower x₁)
                                 }
  where
    open IsEquivalence isEq

lift-IsSemigroup : ∀{c ℓ c′ ℓ′} {A : Set c} {_≈_ : Rel A ℓ}
                       {_∙_ : Op₂ A}
                    → IsSemigroup _≈_ _∙_
                    → IsSemigroup
                        (lift-Rel {ℓ = ℓ′} _≈_)
                        (lift-Op₂ {ℓ = c′} _∙_)
lift-IsSemigroup isSem =
  record { isEquivalence = lift-IsEquivalence isEquivalence
         ; ∙-cong = λ x₁ x₂ → lift $ ∙-cong (lower x₁) (lower x₂)
         ; assoc  = λ x y z → lift $ assoc (lower x) (lower y) (lower z)
         }
  where
    open IsSemigroup isSem

lift-IsMonoid : ∀{c ℓ c′ ℓ′} {A : Set c} {_≈_ : Rel A ℓ}
                       {_∙_ : Op₂ A} {ε : A}
                    → IsMonoid _≈_ _∙_ ε
                    → IsMonoid
                        (lift-Rel {ℓ = ℓ′} _≈_)
                        (lift-Op₂ _∙_)
                        (lift {ℓ = c′} ε)
lift-IsMonoid isG =
  record { isSemigroup = lift-IsSemigroup isSemigroup
         ; identity = ( (λ x → lift $ proj₁ identity (lower x))
                      , (λ x → lift $ proj₂ identity (lower x))
                      )
         }
  where
    open IsMonoid isG

lift-IsGroup : ∀{c ℓ c′ ℓ′} {A : Set c} {_≈_ : Rel A ℓ}
                       {_∙_ : Op₂ A} {ε : A} {_⁻¹ : Op₁ A}
                    → IsGroup _≈_ _∙_ ε _⁻¹
                    → IsGroup
                        (lift-Rel {ℓ = ℓ′} _≈_)
                        (lift-Op₂ _∙_)
                        (lift {ℓ = c′} ε)
                        (lift-Op₁ _⁻¹)
lift-IsGroup isG =
  record { isMonoid = lift-IsMonoid isMonoid
         ; inverse = ((λ x → lift $ proj₁ inverse $ lower x)
                     ,(λ x → lift $ proj₂ inverse $ lower x))
         ; ⁻¹-cong = λ x → lift $ ⁻¹-cong $ lower x
         }
  where
    open IsGroup isG

lift-IsAbelianGroup : ∀{c ℓ c′ ℓ′} {A : Set c} {_≈_ : Rel A ℓ}
                       {_∙_ : Op₂ A} {ε : A} {_⁻¹ : Op₁ A}
                    → IsAbelianGroup _≈_ _∙_ ε _⁻¹
                    → IsAbelianGroup
                        (lift-Rel {ℓ = ℓ′} _≈_)
                        (lift-Op₂ _∙_)
                        (lift {ℓ = c′} ε)
                        (lift-Op₁ _⁻¹)
lift-IsAbelianGroup isAG =
  record { isGroup = lift-IsGroup isGroup
         ; comm = λ x y → lift $ comm (lower x) (lower y)
         }
  where
    open IsAbelianGroup isAG

lift-Morph : ∀{u v ℓ} {A : Set u} {B : Set v}
           → (A → B) → (LiftWith (v ⊔ ℓ) A → LiftWith (u ⊔ ℓ) B)
lift-Morph f = lift ∘ f ∘ lower

lift-Morph₂ : ∀{ℓ u v w} {A : Set u} {B : Set v} {C : Set w}
           → (A → B → C)
           → (LiftWith (v ⊔ w ⊔ ℓ) A → LiftWith (u ⊔ w ⊔ ℓ) B → LiftWith (u ⊔ v ⊔ ℓ) C)
lift-Morph₂ f (lift x) (lift y) = lift $ f x y
