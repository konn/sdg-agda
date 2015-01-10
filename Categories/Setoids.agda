{-# OPTIONS --universe-polymorphism #-}
module Categories.Setoids where
open import Categories
open import Relation.Binary
open import Function.Equality renaming (_∘_ to _⟨∘⟩_)
open import Level
open import Function using (_⟨_⟩_)
import Relation.Binary.PropositionalEquality as C

import HomSetoid as I
import Relation.Binary.EqReasoning as EqR

-- | Category of Setoids.
Setoids : ∀{c ℓ} → Category _ _ _ _
Setoids {c} {ℓ} = record { isCategory = isCategory }
  where
    infix  4 _≈_
    _≈_ : ∀{A B : Setoid c ℓ} → Rel (A ⟶ B) _
    _≈_ {A} {B}= _∼_
      where
        open Setoid (A ⇨ B) renaming (_≈_ to _∼_)

    ⟨∘⟩-cong : ∀{A B C} {f f′ : B ⟶ C} {g g′ : A ⟶ B}
           → f ≈ f′ → g ≈ g′
           → (f ⟨∘⟩ g) ≈ (f′ ⟨∘⟩ g′)
    ⟨∘⟩-cong {A} {B} {C} {f} {f′} {g} {g′} f≈f′ g≈g′ {x} {y} x≈y =
      begin
        (f ⟨∘⟩ g) ⟨$⟩ x
      ≡⟨⟩
        f ⟨$⟩ (g ⟨$⟩ x)
      ≈⟨ cong f (cong g x≈y) ⟩
        f ⟨$⟩ (g ⟨$⟩ y)
      ≈⟨ cong f (g≈g′ (Setoid.refl A)) ⟩
        f ⟨$⟩ (g′ ⟨$⟩ y)
      ≈⟨ f≈f′ (Setoid.refl B) ⟩
        f′ ⟨$⟩ (g′ ⟨$⟩ y)
      ≡⟨⟩
        (f′ ⟨∘⟩ g′) ⟨$⟩ y
      ∎
      where
        open EqR C
        open Setoid C

    isEquiv : I.IsEquivalence _ _≈_
    isEquiv = record { refl = λ {A} {B} {x} → refl {A} {B} {x}
                     ; trans = λ {A} {B} {i} {j} {k} → trans {i = i} {j} {k}
                     ; sym = λ {A} {B} {x} {y} → sym {i = x} {y}
                     }
      where
        module S {A} {B} = Setoid (_⇨_ {c} {ℓ} {c} {ℓ} A B)
        open S

    isCategory : IsCategory (Setoid c ℓ) _⟶_ C._≡_ _≈_ _⟨∘⟩_ id
    isCategory = record { isEquivalence₁ = isEquiv
                        ; isEquivalence₀ = C.isEquivalence
                        ; Hom-cong = C.cong₂ _⟶_
                        ; o-cong = λ {A} {B} {C} {f} {f′} {g} {g′} → ⟨∘⟩-cong {f = f} {f′} {g} {g′}
                        ; identityˡ = cong
                        ; identityʳ = cong
                        ; assoc = λ f g h → cong (f ⟨∘⟩ g ⟨∘⟩ h)
                        }
