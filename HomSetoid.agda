module HomSetoid where
open import Function hiding (flip)
open import Function.Equality
open import Level
import Relation.Binary.Core as B
import Relation.Binary      as B
import Relation.Binary.PropositionalEquality as PEq

0-Setoid : ∀{c} → Set c → B.Setoid c c
0-Setoid A = record { isEquivalence = PEq.isEquivalence
                    ; Carrier = A
                    }

Set′ : (c : Level) → B.Setoid (suc c) _
Set′ c = 0-Setoid (Set c)

_⇛_ : ∀ {f t₁ t₂} → Set f → B.Setoid t₁ t₂ → B.Setoid _ _
From ⇛ To = ≡-setoid From (B.Setoid.indexedSetoid  To)

_×_⇛_ : ∀{i j t₁ t₂} → Set i → Set j → B.Setoid t₁ t₂ → B.Setoid _ _
A × B ⇛ C = A ⇛ (B ⇛ C)

toDiscreteΠ : ∀{i j c ℓ} {A : Set i} {B : Set j} {C : B.Setoid c ℓ}
           → (H : A → B → B.Setoid.Carrier C)
           → 0-Setoid A ⟶ 0-Setoid B ⇨ C
toDiscreteΠ {A = A} {B} {C} H =
  record { _⟨$⟩_ = Tail
         ; cong = λ eq eq′ → reflexive $ PEq.cong₂ H eq eq′
         }
  where
    open B.Setoid C using (reflexive)
    Tail : A → 0-Setoid B ⟶ C
    Tail a = record { _⟨$⟩_ = H a
                    ; cong = λ eq → reflexive (PEq.cong (H a) eq)
                    }

Rel : ∀{i a r} {I : B.Setoid i r}
       (f : I ⟶ I ⇨ Set′ a) (ℓ : Level) → Set _
Rel f ℓ = ∀{i₁ i₂} → B.Rel (f ⟨$⟩ i₁ ⟨$⟩ i₂) ℓ

Reflexive : ∀ {i a r ℓ} {I : B.Setoid i r} (A : I ⟶ I ⇨ Set′ a) → Rel A ℓ → Set _
Reflexive _ _∼_ = ∀ {i j} → B.Reflexive (_∼_ {i} {j})

Symmetric : ∀ {i a r ℓ} {I : B.Setoid i r} (A : I ⟶ I ⇨ Set′ a) → Rel A ℓ → Set _
Symmetric _ _∼_ = ∀ {i j} → B.Symmetric (_∼_ {i} {j})

Transitive : ∀ {i a r ℓ} {I : B.Setoid i r} (A : I ⟶ I ⇨ Set′ a) → Rel A ℓ → Set _
Transitive _ _∼_ = ∀ {i j} → B.Transitive (_∼_ {i} {j})

record IsEquivalence {i a r ℓ} {I : B.Setoid i r} (A : I ⟶ I ⇨ Set′ a)
                     (_≈_ : Rel A ℓ) : Set (r ⊔ i ⊔ a ⊔ ℓ) where
  field
    refl  : Reflexive  A _≈_
    sym   : Symmetric  A _≈_
    trans : Transitive A _≈_

  reflexive : ∀{i j} → B._≡_ ⟨ B._⇒_ ⟩ _≈_ {i} {j}
  reflexive B.refl = refl

record Setoid {i r} (I : B.Setoid i r) c ℓ : Set (suc (r ⊔ i ⊔ c ⊔ ℓ)) where
  infix 4 _≈_
  field
    Carrier       : I ⟶ I ⇨ Set′ c
    _≈_           : Rel Carrier ℓ
    isEquivalence : IsEquivalence Carrier _≈_

  open IsEquivalence isEquivalence public

  flipped : Setoid I c ℓ
  flipped = record { Carrier = flip Carrier
                   ; _≈_ = _≈_
                   ; isEquivalence =
                       record { refl  = refl
                              ; sym   = λ {i} {j} eq → sym {j} {i} eq
                              ; trans = λ {i} {j} eq eq′ → trans {j} {i} eq eq′
                              }
                   }

_[_,_] : ∀ {i r s₁ s₂} {I : B.Setoid i r}
      → Setoid I s₁ s₂
      → B.Setoid.Carrier I
      → B.Setoid.Carrier I → B.Setoid _ _
S [ i , j ] = record { Carrier = S.Carrier ⟨$⟩ i ⟨$⟩ j
                   ; _≈_ = S._≈_
                   ; isEquivalence = record { refl  = S.refl
                                            ; sym   = S.sym
                                            ; trans = S.trans
                                            }
                   }
  where
    module S = Setoid S

