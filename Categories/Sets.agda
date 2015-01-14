{-# OPTIONS --universe-polymorphism #-}
module Categories.Sets where
open import Categories
open import Relation.Binary.Core
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Level

_-Set⟶_ : ∀{ℓ} → (A B : Set ℓ) → Set _
A -Set⟶ B = A → B

private
   
  _o_ : ∀{ℓ} {A B C : Set ℓ} → (f : B → C) → (g : A → B) → A → C
  _o_ f g x = f (g x)
      
  SetId : ∀{ℓ} {A : Set ℓ} → A → A
  SetId x = x

Sets : ∀{ℓ} → Category _ _ _ _
Sets {ℓ} = record { isCategory = isCategory
                  }
  where
    _≈_ : {A B : Set ℓ} → Rel (A -Set⟶ B) ℓ
    _≈_ {A} {B} f g = ∀ x → f x ≡ g x
    isCategory : IsCategory (Set ℓ) _-Set⟶_ _≡_ (_≈_) _o_ SetId
    isCategory = record { isEquivalence₀ = isEquivalence
                        ; isEquivalence₁ =
                            record { refl = λ {f} x → refl
                                   ; trans = λ f∼g g∼h x → trans (f∼g x) (g∼h x)
                                   ; sym = λ i∼j x → sym (i∼j x)
                                   }
                        ; Hom-cong = cong₂ _-Set⟶_
                        ; identityˡ     = λ f x → refl
                        ; identityʳ     = λ f x → refl
                        ; o-cong      = λ {A} {B} {C} {f} {f′} {g} {g′} f∼f′ g∼g′ x →
                                          trans (f∼f′ (g x))
                                                (cong f′ (g∼g′ x))
                        ; assoc   = λ f g h x → refl
                        }
