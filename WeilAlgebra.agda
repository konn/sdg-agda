{-# OPTIONS --universe-polymorphism #-}
open import Level hiding (zero ; Lift)
open import Algebra

module WeilAlgebra {c ℓ} (R : CommutativeRing c ℓ) where
open import Data.Nat using  (ℕ) renaming (suc to S)
open import R-Module R
open import R-Module.Free R
open import Algebra.Structures
open import Relation.Binary
open import Relation.Binary.Core
open import Function
open import Relation.Unary hiding (_⟨∘⟩_)
open import Data.Product
open import Algebra.Morphism
open import Data.Product.N-ary
open import Data.Fin using (Fin) renaming (zero to OZ ; suc to OS)
open import Function.Equality
            hiding   (setoid ; flip)
            renaming (_∘_ to _⟨∘⟩_)

open import Categories

import Algebra.FunctionProperties as FunctionProperties
import Relation.Binary.EqReasoning as EqR
import Relation.Binary.PropositionalEquality as PEq

open FunctionProperties using (Op₁ ; Op₂)

record IsDistributiveR-Algebra
         {c′ ℓ′} {A : Set c′}
         (_≈_ : Rel A ℓ′) (_+_ : Op₂ A)
         (_*>_ : Coeff → A → A)
         (-_ : Op₁ A)
         (_•_ : Op₂ A) (0# : A) : Set (c ⊔ ℓ ⊔ c′ ⊔ ℓ′) where
  open FunctionProperties _≈_ 
  field
    isR-Module : IsR-Module _≈_ _+_ _*>_ -_ 0#
  private
    R-module : R-Module _ _
    R-module = record { isR-Module = isR-Module }
  field
    •-cong     : _•_ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_
    •-bilinear : Bilinear R-module R-module R-module _•_
  open IsR-Module isR-Module
    renaming (isAbelianGroup to +-isAbelianGroup)
    public
  distribˡ : _•_ DistributesOverˡ _+_
  distribˡ x y z = Linear.+-homo (proj₂ •-bilinear x) y z

  distribʳ : _•_ DistributesOverʳ _+_
  distribʳ x y z = Linear.+-homo (proj₁ •-bilinear x) y z

  distrib : _•_ DistributesOver _+_
  distrib = ( distribˡ , distribʳ )

-- | R-module with bilinear multiplication.
record DistributiveR-Algebra c′ ℓ′ : Set (suc (c ⊔ ℓ ⊔ c′ ⊔ ℓ′)) where
  infix  8 -_
  infixr 7 _*>_
  infixr 7 _•_
  infixl 6 _+_
  infix  4 _≈_
  field
    Carrier : Set c′
    _≈_     : Rel Carrier ℓ′
    _+_     : Op₂ Carrier
    _*>_    : Coeff → Carrier → Carrier
    -_      : Op₁ Carrier
    _•_     : Op₂ Carrier
    0#      : Carrier
    isDistributiveR-Algebra : IsDistributiveR-Algebra _≈_ _+_ _*>_ -_ _•_ 0#
  open IsDistributiveR-Algebra isDistributiveR-Algebra public
  R-module : R-Module _ _
  R-module = record { isR-Module = isR-Module }
  open R-Module R-module
    using ( setoid )
    renaming ( abelianGroup      to +-abelianGroup
             ; monoid            to +-monoid
             ; rawMonoid         to +-rawMonoid
             ; group             to +-group
             ; commutativeMonoid to +-commutativeMonoid
             ; semigroup         to +-semigroup
             )
    public

-- | Coefficient ring trivially has R-algebra structure
coeffDistribAlg : DistributiveR-Algebra _ _
coeffDistribAlg = record { isDistributiveR-Algebra = isDistributiveR-Algebra
                         }
  where
    open R-Module coeffModule
    open EqR setoidR
    •-linearˡ : ∀ y → Linear coeffModule coeffModule (λ x → x *R y)
    •-linearˡ y = record { ⟦⟧-cong  = λ eq → *R-cong eq ≈R-refl
                        ; +-homo  = λ _ _ → proj₂ R-distrib _ _ _
                        ; *>-homo = λ _ _ → *R-assoc _ _ _
                        ; 0#-homo = proj₁ zero _
                        }

    •-linearʳ : ∀ x → Linear coeffModule coeffModule (λ y → x *R y)
    •-linearʳ x = record { ⟦⟧-cong  = *R-cong ≈R-refl
                        ; +-homo  = λ _ _ → proj₁ R-distrib _ _ _
                        ; *>-homo = *>-homo
                        ; 0#-homo = proj₂ zero _
                        }
      where
        ⟦_⟧ : Coeff → Coeff
        ⟦_⟧ y = x *R y
        *>-homo : ∀ a y → ⟦ a *> y ⟧ ≈R a *> ⟦ y ⟧
        *>-homo a y =
          begin
            ⟦ a *> y ⟧
          ≡⟨⟩
            x *R (a *R y)
          ≈⟨ ≈R-sym (*R-assoc _ _ _) ⟩
            (x *R a) *R y
          ≈⟨ *R-comm _ _ ⟨ *R-cong ⟩ ≈R-refl ⟩
            (a *R x) *R y
          ≈⟨ *R-assoc _ _ _ ⟩
            a *R (x *R y)
          ≡⟨⟩
            a *> ⟦ y ⟧
          ∎
        
    isDistributiveR-Algebra =
      record { isR-Module = isR-Module
             ; •-cong = *R-cong
             ; •-bilinear = (•-linearˡ , •-linearʳ)
             }

record IsAssociativeR-Algebra
         {c′ ℓ′} {A : Set c′}
         (_≈_ : Rel A ℓ′) (_+_ : Op₂ A)
         (_*>_ : Coeff → A → A)
         (-_ : Op₁ A)
         (_•_ : Op₂ A) (0# : A) : Set (c ⊔ ℓ ⊔ c′ ⊔ ℓ′) where
  open FunctionProperties _≈_
  field
    isDistributiveR-Algebra : IsDistributiveR-Algebra _≈_ _+_ _*>_ -_ _•_ 0#
    •-assoc : Associative _•_
  open IsDistributiveR-Algebra isDistributiveR-Algebra public

  private
    open EqR (record { isEquivalence = isEquivalence })
    open Setoid (record { isEquivalence = isEquivalence })
         using ()
         renaming (refl to ≈-refl ; sym to ≈-sym ; trans to ≈-trans)

    -‿•-distribˡ : ∀ x y → ((- x) • y) ≈ - (x • y)
    -‿•-distribˡ x y =
      begin
        - x • y
      ≈⟨ ≈-sym $ proj₂ +-identity _ ⟩
        (- x • y) + 0#
      ≈⟨ ≈-refl ⟨ +-cong ⟩ ≈-sym (proj₂ -‿inverse _) ⟩
        (- x • y) + ( (x • y) + - (x • y))
      ≈⟨ ≈-sym (+-assoc _ _ _) ⟩
        ((- x • y) + (x • y)) + - (x • y)
      ≈⟨ ≈-sym (distribʳ _ _ _) ⟨ +-cong ⟩ ≈-refl ⟩
        ((- x + x) • y) + - (x • y)
      ≈⟨ (proj₁ -‿inverse _ ⟨ •-cong ⟩ ≈-refl)
                ⟨ +-cong ⟩
         ≈-refl ⟩
        (0# • y) + - (x • y)
      ≈⟨ (≈-sym (*>-zero _) ⟨ •-cong ⟩ ≈-refl)
                ⟨ +-cong ⟩
         ≈-refl
       ⟩
        ((0R *> x) • y) + - (x • y)
      ≈⟨ Linear.*>-homo (proj₁ •-bilinear _) _ _
         ⟨ +-cong ⟩ ≈-refl ⟩
        (0R *> (x • y)) + - (x • y)
      ≈⟨ *>-zero _ ⟨ +-cong ⟩ ≈-refl  ⟩
        0# + - (x • y)
      ≈⟨ proj₁ +-identity _ ⟩
        - (x • y)
      ∎

    -‿•-distribʳ : ∀ x y → (x • - y) ≈ - (x • y)
    -‿•-distribʳ x y =
      begin
        x • - y
      ≈⟨ ≈-sym $ proj₁ +-identity _ ⟩
        0# + (x • - y)
      ≈⟨ ≈-sym (proj₁ -‿inverse _) ⟨ +-cong ⟩ ≈-refl ⟩
        (- (x • y) + (x • y)) + (x • - y)
      ≈⟨ +-assoc _ _ _ ⟩
        - (x • y) + ((x • y) + (x • - y))
      ≈⟨ ≈-refl ⟨ +-cong ⟩ ≈-sym (distribˡ _ _ _) ⟩
        - (x • y) + (x • (y + - y))
      ≈⟨ ≈-refl
                ⟨ +-cong ⟩
         (≈-refl ⟨ •-cong ⟩ proj₂ -‿inverse _) ⟩
        - (x • y) + (x • 0#)
      ≈⟨ ≈-refl
                ⟨ +-cong ⟩
         (≈-refl ⟨ •-cong ⟩ ≈-sym (*>-zero _))
       ⟩
        - (x • y) + (x • (0R *> y))
      ≈⟨ ≈-refl
           ⟨ +-cong ⟩
         Linear.*>-homo (proj₂ •-bilinear _) _ _ ⟩
        - (x • y) + (0R *> (x • y))
      ≈⟨ ≈-refl ⟨ +-cong ⟩ *>-zero _  ⟩
        - (x • y) + 0#
      ≈⟨ proj₂ +-identity _ ⟩
        - (x • y)
      ∎

    zeroˡ : LeftZero 0# _•_
    zeroˡ x = begin
               0# • x
             ≈⟨ ≈-sym (proj₂ -‿inverse x) ⟨ •-cong ⟩ ≈-refl ⟩
               (x + (- x)) • x
             ≈⟨ distribʳ x x (- x) ⟩
               (x • x) + ((- x) • x)
             ≈⟨ ≈-refl ⟨ +-cong ⟩ -‿•-distribˡ _ _ ⟩
                (x • x) - (x • x)
             ≈⟨ proj₂ -‿inverse (x • x) ⟩
               0#
             ∎

    zeroʳ : RightZero 0# _•_
    zeroʳ x = begin
               x • 0#
             ≈⟨ ≈-refl ⟨ •-cong ⟩ ≈-sym (proj₂ -‿inverse x) ⟩
               x • (x + (- x) )
             ≈⟨ distribˡ _ _ _ ⟩
               (x • x) + (x • - x)
             ≈⟨ ≈-refl ⟨ +-cong ⟩ -‿•-distribʳ _ _ ⟩
                (x • x) - (x • x)
             ≈⟨ proj₂ -‿inverse (x • x) ⟩
               0#
             ∎

  •-isSemigroup : IsSemigroup _≈_ _•_
  •-isSemigroup = record { assoc = •-assoc
                         ; isEquivalence = isEquivalence
                         ; ∙-cong = •-cong
                         }

  isSemiringWithoutOne : IsSemiringWithoutOne _≈_ _+_ _•_ 0#
  isSemiringWithoutOne = record { +-isCommutativeMonoid = isCommutativeMonoid
                                ; *-isSemigroup = •-isSemigroup
                                ; distrib = distrib
                                ; zero = (zeroˡ , zeroʳ)
                                }

-- | R-module with bilinear associative multiplication.
record AssociativeR-Algebra c′ ℓ′ : Set (suc (c ⊔ ℓ ⊔ c′ ⊔ ℓ′)) where
  infix  8 -_
  infixr 7 _*>_
  infixr 7 _•_
  infixl 6 _+_
  infix  4 _≈_
  field
    Carrier : Set c′
    _≈_     : Rel Carrier ℓ′
    _+_     : Op₂ Carrier
    _*>_    : Coeff → Carrier → Carrier
    -_      : Op₁ Carrier
    _•_     : Op₂ Carrier
    0#      : Carrier
    isAssociativeR-Algebra : IsAssociativeR-Algebra _≈_ _+_ _*>_ -_ _•_ 0#
  open IsAssociativeR-Algebra isAssociativeR-Algebra public

  distributiveR-algebra : DistributiveR-Algebra _ _
  distributiveR-algebra = record { isDistributiveR-Algebra = isDistributiveR-Algebra }

  open DistributiveR-Algebra distributiveR-algebra
    using ( setoid
          ; R-module
          ; +-abelianGroup     
          ; +-monoid           
          ; +-rawMonoid        
          ; +-group            
          ; +-commutativeMonoid
          ; +-semigroup        
          )
    public

  •-semigroup : Semigroup _ _
  •-semigroup = record { isSemigroup = •-isSemigroup }

  semiringWithoutOne : SemiringWithoutOne _ _
  semiringWithoutOne = record { isSemiringWithoutOne = isSemiringWithoutOne }

coeffAssocAlg : AssociativeR-Algebra _ _
coeffAssocAlg = record { isAssociativeR-Algebra = isAssociativeR-Algebra
                       }
  where
    open DistributiveR-Algebra coeffDistribAlg
    isAssociativeR-Algebra =
      record { isDistributiveR-Algebra = isDistributiveR-Algebra
             ; •-assoc = *R-assoc
             }

record IsR-Algebra
         {c′ ℓ′} {A : Set c′}
         (_≈_ : Rel A ℓ′) (_+_ : Op₂ A)
         (_*>_ : Coeff → A → A)
         (-_ : Op₁ A)
         (_•_ : Op₂ A) (0# : A) (1# : A) : Set (c ⊔ ℓ ⊔ c′ ⊔ ℓ′) where
  open FunctionProperties _≈_
  field
    isAssociativeR-Algebra : IsAssociativeR-Algebra _≈_ _+_ _*>_ -_ _•_ 0#
    •-identity : Identity 1# _•_
  open IsAssociativeR-Algebra isAssociativeR-Algebra public
  •-isMonoid : IsMonoid _≈_ _•_ 1#
  •-isMonoid = record { isSemigroup = •-isSemigroup
                      ; identity = •-identity
                      }

  isRing : IsRing _≈_ _+_ _•_ -_ 0# 1#
  isRing = record { +-isAbelianGroup = +-isAbelianGroup
                  ; *-isMonoid       = •-isMonoid
                  ; distrib          = distrib
                  }
-- | R-module with bilinear associative multiplication with identity.
record R-Algebra c′ ℓ′ : Set (suc (c ⊔ ℓ ⊔ c′ ⊔ ℓ′)) where
  infix  8 -_
  infixr 7 _*>_
  infixr 7 _•_
  infixl 6 _+_
  infix  4 _≈_
  field
    Carrier : Set c′
    _≈_     : Rel Carrier ℓ′
    _+_     : Op₂ Carrier
    _*>_    : Coeff → Carrier → Carrier
    -_      : Op₁ Carrier
    _•_     : Op₂ Carrier
    0#      : Carrier
    1#      : Carrier
    isR-Algebra : IsR-Algebra _≈_ _+_ _*>_ -_ _•_ 0# 1#

  open IsR-Algebra isR-Algebra public

  associativeR-algebra : AssociativeR-Algebra _ _
  associativeR-algebra = record { isAssociativeR-Algebra = isAssociativeR-Algebra}

  open AssociativeR-Algebra associativeR-algebra
    using ( distributiveR-algebra
          ; setoid             
          ; R-module           
          ; +-abelianGroup     
          ; +-monoid           
          ; +-rawMonoid        
          ; +-group            
          ; +-commutativeMonoid
          ; +-semigroup
          ; •-semigroup
          ; semiringWithoutOne
          )
    public

  •-monoid : Monoid _ _
  •-monoid = record { isMonoid = •-isMonoid }

  ring : Ring c′ ℓ′
  ring = record { isRing = isRing }

  open Ring ring
    using    ( semiring
             ; nearSemiring
             ; semiringWithoutAnnihilatingZero
             ) 
    renaming ( *-rawMonoid to •-rawMonoid )
    public

coeffAlg : R-Algebra _ _
coeffAlg = record { isR-Algebra = isR-Algebra
                  }
  where
    open AssociativeR-Algebra coeffAssocAlg
    isR-Algebra =
      record { isAssociativeR-Algebra = isAssociativeR-Algebra
             ; •-identity = *R-identity
             }

record _-R-Alg⟶_ {a₁ a₂ b₁ b₂}
       (A : R-Algebra a₁ a₂) (B : R-Algebra b₁ b₂)
       : Set (c ⊔ a₁ ⊔ a₂ ⊔ b₁ ⊔ b₂) where
  module F = R-Algebra A
  module T = R-Algebra B
  open Definitions F.Carrier T.Carrier T._≈_
  field
    ⟦_⟧ : Morphism
    ⟦⟧-linear : Linear F.R-module T.R-module ⟦_⟧
    •-homo    : Homomorphic₂ ⟦_⟧ F._•_ T._•_

  -R-module⟶ : F.R-module -R-Module⟶ T.R-module
  -R-module⟶ = record { ⟦⟧-linear = ⟦⟧-linear }
  open _-R-Module⟶_ -R-module⟶
    using (Πsetoid ; ⟦⟧-cong ; +-homo ; *>-homo ; 0#-homo)
    public

R-Alg : ∀{c′ ℓ′} → Category _ _ _ _
R-Alg {c′} {ℓ′} =
  subCategory
    {Base = R-Mod {c′} {ℓ′}}
    record { U₀ = U₀
           ; U₁ = U₁
           ; Morph-cong = PEq.cong₂ _-R-Alg⟶_
           ; ≈₀-cong = PEq.cong U₀
           ; Liftable = Liftable
           }
  where
    U₀ = R-Algebra.R-module
    U₁ = _-R-Alg⟶_.-R-module⟶
    Liftable : (a b : R-Algebra c′ ℓ′) → (f : U₀ a -R-Module⟶ U₀ b) → Set _
    Liftable a b f = Homomorphic₂ f.⟦_⟧ A._•_ B._•_
      where
        module A = R-Algebra a
        module B = R-Algebra b
        module f = _-R-Module⟶_ f
        open Definitions A.Carrier B.Carrier B._≈_
    Lift : ∀{A B} → (f : U₀ A -R-Module⟶ U₀ B) → {pf : Liftable A B f} → A -R-Alg⟶ B
    Lift f {pf} = record { •-homo = pf }

{-
R-Alg : ∀{c′ ℓ′} → Category _ _ _
R-Alg {c′} {ℓ′} = record { isCategory = isCategory }
  where
    module UCat = Category (R-Mod {c′} {ℓ′})
    open IsCategory UCat.isCategory
      renaming (cong to ≋-cong)

    toRMod = _-R-Alg⟶_.-R-module⟶

    _o_ : ∀{A B C : R-Algebra c′ ℓ′} → (B -R-Alg⟶ C) → (A -R-Alg⟶ B) → (A -R-Alg⟶ C)
    _o_ {A} {B} {C} g f =
      record { ⟦⟧-linear = _-R-Module⟶_.⟦⟧-linear (R-Mod [ G.-R-module⟶ o F.-R-module⟶ ])
             ; •-homo   = •-homo}
      where
        module G = _-R-Alg⟶_ g
        module F = _-R-Alg⟶_ f
        module W₁ = R-Algebra A
        module W₂ = R-Algebra B
        module W₃ = R-Algebra C

        open EqR W₃.setoid
        open Definitions W₁.Carrier W₃.Carrier W₃._≈_

        ⟦_⟧ : Morphism
        ⟦_⟧ = G.⟦_⟧ ∘ F.⟦_⟧

        •-homo : Homomorphic₂ ⟦_⟧ W₁._•_ W₃._•_
        •-homo x y =
          begin
            ⟦ x W₁.• y ⟧
          ≡⟨⟩
            G.⟦ F.⟦ x W₁.• y ⟧ ⟧
          ≈⟨ G.⟦⟧-cong (F.•-homo x y) ⟩
            G.⟦ F.⟦ x ⟧ W₂.• F.⟦ y ⟧ ⟧
          ≈⟨ G.•-homo F.⟦ x ⟧ F.⟦ y ⟧ ⟩
            ⟦ x ⟧ W₃.• ⟦ y ⟧
          ∎

    _≈_ : ∀{W₁ W₂} → Rel (W₁ -R-Alg⟶ W₂) _
    _≈_ {W₁} {W₂} f g = F.Πsetoid ≋ G.Πsetoid
      where
        module S = R-Algebra W₁
        module T = R-Algebra W₂
        module F = _-R-Alg⟶_ f
        module G = _-R-Alg⟶_ g
        open Setoid (S.setoid ⇨ T.setoid) renaming (_≈_ to _≋_)

    isEquiv : ∀ {A B} → IsEquivalence _≈_
    isEquiv {A} {B} = record { refl = λ {f} → ≋-refl {toΠ f}
                             ; sym = λ {f} {g} → ≋-sym {toΠ f} {toΠ g}
                             ; trans = λ {f} {g} {h} → ≋-trans {toΠ f} {toΠ g} {toΠ h}
                             }
      where
        module F = R-Algebra A
        module T = R-Algebra B
        toΠ : A -R-Alg⟶ B → F.setoid ⟶ T.setoid
        toΠ = _-R-Alg⟶_.Πsetoid
        open Setoid (F.setoid ⇨ T.setoid)
             renaming ( refl  to ≋-refl
                      ; sym   to ≋-sym
                      ; trans to ≋-trans
                      ; _≈_   to _≋_)
     
    IdV : ∀{A} → A -R-Alg⟶ A
    IdV {A} = record { ⟦_⟧ = ⟦_⟧
                     ; •-homo = λ x y → ≋-refl
                     ; ⟦⟧-linear = _-R-Module⟶_.⟦⟧-linear (Id′ R-Mod W.R-module)
                     }
      where
        module W = R-Algebra A
        open W renaming (_≈_ to _≋_ ; refl to ≋-refl)
        open Definitions Carrier Carrier _≋_ 
        ⟦_⟧ : Morphism
        ⟦ x ⟧ = x
        open EqR setoid
    
    isCategory : IsCategory (R-Algebra c′ ℓ′) _-R-Alg⟶_ _≈_ _o_ IdV
    isCategory = record { cong = λ {A} {B} {C} {f} {f′} {g} {g′} →
                                      ≋-cong
                                         {f = toRMod f}
                                         {toRMod f′}
                                         {toRMod g}
                                         {toRMod g′}
                        ; isEquivalence = λ {A} {B} → isEquiv {A} {B}
                        ; identityˡ = identityˡ ∘ toRMod
                        ; identityʳ = identityʳ ∘ toRMod
                        ; assoc = λ f g h → assoc (toRMod f) (toRMod g) (toRMod h)
                        }
-}
record IsCommutativeR-Algebra
         {c′ ℓ′} {A : Set c′}
         (_≈_ : Rel A ℓ′) (_+_ : Op₂ A)
         (_*>_ : Coeff → A → A)
         (-_ : Op₁ A)
         (_•_ : Op₂ A) (0# : A) (1# : A) : Set (c ⊔ ℓ ⊔ c′ ⊔ ℓ′) where
  open FunctionProperties _≈_
  field
    isR-Algebra : IsR-Algebra _≈_ _+_ _*>_ -_ _•_ 0# 1#
    •-comm : Commutative _•_
  open IsR-Algebra isR-Algebra public
  isCommutativeRing : IsCommutativeRing _≈_ _+_ _•_ -_ 0# 1#
  isCommutativeRing = record { isRing = isRing
                             ; *-comm = •-comm
                             }

  •-isCommutativeMonoid : IsCommutativeMonoid _≈_ _•_ 1# 
  •-isCommutativeMonoid = record { isSemigroup = •-isSemigroup
                                 ; identityˡ = proj₁ •-identity
                                 ; comm = •-comm
                                 }

-- | R-module with commutative, bilinear and associative multiplication with identity.
record CommutativeR-Algebra c′ ℓ′ : Set (suc (c ⊔ ℓ ⊔ c′ ⊔ ℓ′)) where
  infix  8 -_
  infixr 7 _*>_
  infixr 7 _•_
  infixl 6 _+_
  infix  4 _≈_
  field
    Carrier : Set c′
    _≈_     : Rel Carrier ℓ′
    _+_     : Op₂ Carrier
    _*>_    : Coeff → Carrier → Carrier
    -_      : Op₁ Carrier
    _•_     : Op₂ Carrier
    0#      : Carrier
    1#      : Carrier
    isCommutativeR-Algebra : IsCommutativeR-Algebra _≈_ _+_ _*>_ -_ _•_ 0# 1#
  open IsCommutativeR-Algebra isCommutativeR-Algebra public

  R-algebra : R-Algebra _ _
  R-algebra = record { isR-Algebra = isR-Algebra}

  open R-Algebra R-algebra
    using ( distributiveR-algebra
          ; associativeR-algebra
          ; setoid             
          ; R-module           
          ; +-abelianGroup     
          ; +-monoid           
          ; +-rawMonoid        
          ; +-group            
          ; +-commutativeMonoid
          ; +-semigroup
          ; •-semigroup
          ; •-monoid
          ; semiringWithoutOne
          ; semiringWithoutAnnihilatingZero
          ; semiring
          ; nearSemiring
          ; ring
          )
    public

  commutativeRing : CommutativeRing _ _
  commutativeRing = record { isCommutativeRing = isCommutativeRing }

  •-commutativeMonoid : CommutativeMonoid _ _
  •-commutativeMonoid = record { isCommutativeMonoid = •-isCommutativeMonoid }

product : ∀{c′} → {k : ℕ} → {A : Set c′} → A → Op₂ A → (Fin k → A) → A
product {k = 0}   i _ _ = i
product {k = S n} i _*_ p = p OZ * product {k = n} i _*_ (λ d → p (OS d))

private
  1#0 : ∀{n} → Fin (S n) → Coeff
  1#0 OZ     = 1R
  1#0 (OS k) = 0R

record IsAugmentedCommutativeR-Algebra
       {n : ℕ} (_•_ : Op₂ (R-Module.Carrier ((S n) DimFreeModule)))
       : Set (ℓ ⊔ c) where
  private
    Rⁿ⁺¹ = (S n) DimFreeModule
    open R-Module Rⁿ⁺¹
    open FunctionProperties _≈_ hiding (Op₁ ; Op₂)
    open Definitions Carrier Coeff _≈R_

    augmentation : Pred Carrier ℓ
    augmentation x = x OZ ≈R 0R
    π₀ : Carrier → Coeff
    π₀ f = f OZ
    1# : Carrier
    1# = 1#0

  field
    isCommutativeR-Algebra : IsCommutativeR-Algebra _≈_ _+_ _*>_ -_ _•_ 0# 1#
    π₀-linear : Linear Rⁿ⁺¹ coeffModule π₀
    π₀-•-homo : Homomorphic₂ π₀ _•_ _*R_
  open IsCommutativeR-Algebra isCommutativeR-Algebra public

record AugmentedCommutativeR-Algebra : Set (ℓ ⊔ c) where
  field
    n   : ℕ
    _•_ : Op₂ (R-Module.Carrier ((S n) DimFreeModule))
    isAugmentedCommutativeR-Algebra : IsAugmentedCommutativeR-Algebra _•_
  open IsAugmentedCommutativeR-Algebra isAugmentedCommutativeR-Algebra public

  dimension : ℕ
  dimension = S n

  commutativeR-algebra : CommutativeR-Algebra _ _
  commutativeR-algebra = record { isCommutativeR-Algebra = isCommutativeR-Algebra }

  open CommutativeR-Algebra commutativeR-algebra
    using ( distributiveR-algebra
          ; associativeR-algebra
          ; setoid             
          ; R-module
          ; R-algebra
          ; +-abelianGroup     
          ; +-monoid           
          ; +-rawMonoid        
          ; +-group            
          ; +-commutativeMonoid
          ; +-semigroup
          ; •-semigroup
          ; •-monoid
          ; semiringWithoutOne
          ; semiringWithoutAnnihilatingZero
          ; semiring
          ; nearSemiring
          ; ring
          ; commutativeRing
          ; •-commutativeMonoid
          ; _≈_
          ; _*>_
          ; _+_
          ; -_
          ; 0#
          ; 1#
          )
    public

  Carrier : Set _
  Carrier = R-Module.Carrier R-module

  augmentation : Pred Carrier ℓ
  augmentation x = x OZ ≈R 0R

  π₀ : R-algebra -R-Alg⟶ coeffAlg
  π₀ = record { ⟦⟧-linear = ⟦⟧-linear
              ; •-homo = π₀-•-homo
              }
    where
      open Linear π₀-linear using (⟦⟧-cong ; +-homo ; *>-homo; 0#-homo)
      ⟦_⟧ : Carrier → Coeff
      ⟦ f ⟧ = f OZ
      ⟦⟧-linear : Linear R-module coeffModule ⟦_⟧
      ⟦⟧-linear = record { ⟦⟧-cong = ⟦⟧-cong
                        ; +-homo  = +-homo
                        ; *>-homo = *>-homo
                        ; 0#-homo = 0#-homo
                        }


ACR-Algebra = AugmentedCommutativeR-Algebra
module ACR-Algebra = AugmentedCommutativeR-Algebra


              

record IsWeilAlgebra {n} (_•_ : Op₂ (R-Module.Carrier $ (S n) DimFreeModule)) : Set (c ⊔ ℓ) where
  field
    isAugmentedCommutativeR-Algebra : IsAugmentedCommutativeR-Algebra _•_
  open ACR-Algebra (record { isAugmentedCommutativeR-Algebra = isAugmentedCommutativeR-Algebra })
    using (1# ; 0# ; _•_ ; _≈_ ; Carrier)
  field
    nilpotent : Σ[ k ∈ ℕ ]
                   (∀ (F : Fin k → Carrier)
                   → (∀ i → F i OZ ≈R 0R)
                   → product 1#0 _•_ F ≈ 0# )
  open IsAugmentedCommutativeR-Algebra isAugmentedCommutativeR-Algebra public

record WeilAlgebra : Set (ℓ ⊔ c) where
  field
    n   : ℕ
    _•_ : Op₂ (R-Module.Carrier ((S n) DimFreeModule))
    isWeilAlgebra : IsWeilAlgebra _•_

  open IsWeilAlgebra isWeilAlgebra public
  augmentedCommutativeR-algebra : AugmentedCommutativeR-Algebra
  augmentedCommutativeR-algebra =
    record { isAugmentedCommutativeR-Algebra = isAugmentedCommutativeR-Algebra }

  acR-algebra : AugmentedCommutativeR-Algebra
  acR-algebra = augmentedCommutativeR-algebra

  open ACR-Algebra acR-algebra
    using ( commutativeR-algebra
          ; distributiveR-algebra
          ; associativeR-algebra
          ; setoid             
          ; R-module
          ; R-algebra
          ; +-abelianGroup     
          ; +-monoid           
          ; +-rawMonoid        
          ; +-group            
          ; +-commutativeMonoid
          ; +-semigroup
          ; •-semigroup
          ; •-monoid
          ; semiringWithoutOne
          ; semiringWithoutAnnihilatingZero
          ; semiring
          ; nearSemiring
          ; ring
          ; commutativeRing
          ; •-commutativeMonoid
          ; _≈_
          ; _*>_
          ; _+_
          ; -_
          ; 0#
          ; 1#
          ; dimension
          ; π₀
          ; augmentation
          ; Carrier
          )
    public
  
record _-Weil⟶_ (W₁ : WeilAlgebra) (W₂ : WeilAlgebra) : Set (c ⊔ ℓ) where
  private
    module F = WeilAlgebra W₁
    module T = WeilAlgebra W₂
  open Definitions F.Carrier T.Carrier T._≈_
  field
    ⟦_⟧       : Morphism
    ⟦⟧-linear : Linear F.R-module T.R-module ⟦_⟧
    •-homo    : Homomorphic₂ ⟦_⟧ F._•_ T._•_
    J-homo   : ∀ x → x ∈ F.augmentation → ⟦ x ⟧ ∈ T.augmentation

  -R-alg⟶ : F.R-algebra -R-Alg⟶ T.R-algebra
  -R-alg⟶ = record { ⟦⟧-linear = ⟦⟧-linear
                    ; •-homo = •-homo
                    }

  open _-R-Alg⟶_ -R-alg⟶ using (-R-module⟶) public

{-
Weil : Category _ _ _
Weil = record { isCategory = isCategory }
  where
    module UCat = Category (R-Alg {c} {ℓ})
    toUnderlying = _-Weil⟶_.-R-alg⟶
    toRAlg = WeilAlgebra.R-algebra

    open IsCategory UCat.isCategory
    open Category (record { isCategory = UCat.isCategory })
      using (_≈_)
      renaming (cong to ≈-cong)
     
    IdW : ∀{A} → A -Weil⟶ A
    IdW {A} = record { ⟦_⟧ = ⟦_⟧
                     ; J-homo = λ x x₁ → x₁
                     ; •-homo = _-R-Alg⟶_.•-homo (Id′ R-Alg W.R-algebra)
                     ; ⟦⟧-linear = _-R-Alg⟶_.⟦⟧-linear (Id′ R-Alg W.R-algebra)
                     }
      where
        module W = WeilAlgebra A
        open W using () renaming (_≈_ to _≋_ ; refl to ≋-refl)
        open Definitions W.Carrier W.Carrier _≋_ 
        ⟦_⟧ : Morphism
        ⟦ x ⟧ = x
        open EqR W.setoid


     
    _o_ : ∀{W₁ W₂ W₃ : WeilAlgebra} → W₂ -Weil⟶ W₃ → W₁ -Weil⟶ W₂ → W₁ -Weil⟶ W₃
    _o_ {W₁} {W₂} {W₃} g f = record { •-homo = •-homo
                                   ; J-homo = J-homo
                                   ; ⟦⟧-linear = linear
                                   }
      where
        module G = _-Weil⟶_ g
        module F = _-Weil⟶_ f
        module A = WeilAlgebra W₁
        module B = WeilAlgebra W₂
        module C = WeilAlgebra W₃
     
        open Definitions A.Carrier C.Carrier C._≈_
     
        ⟦_⟧ : Morphism
        ⟦_⟧ = G.⟦_⟧ ∘ F.⟦_⟧
     
        linear : Linear A.R-module C.R-module ⟦_⟧
        linear = _-R-Alg⟶_.⟦⟧-linear (R-Alg [ G.-R-alg⟶ o F.-R-alg⟶ ])
     
        •-homo : Homomorphic₂ ⟦_⟧ A._•_ C._•_
        •-homo = _-R-Alg⟶_.•-homo (R-Alg [ G.-R-alg⟶ o F.-R-alg⟶ ])
     
        J-homo : ∀ x → x ∈ A.augmentation → ⟦ x ⟧ ∈ C.augmentation
        J-homo x x∈Jₐ = G.J-homo  F.⟦ x ⟧ (F.J-homo x x∈Jₐ)

    _∼_ : ∀{A B} → Rel (A -Weil⟶ B) _
    f ∼ g = R-Alg [ toUnderlying f ≈ toUnderlying g ]

    isEquiv : ∀{A B} → IsEquivalence (_∼_ {A} {B})
    isEquiv {A} {B} =
      record { refl  = λ {f} → ≈-refl {toUnderlying f}
             ; sym   = λ {f} {g} → ≈-sym {toUnderlying f} {toUnderlying g}
             ; trans = λ {f} {g} {h} → ≈-trans {toUnderlying f} {toUnderlying g} {toUnderlying h}
             }
      where
        open IsEquivalence (isEquivalence {toRAlg A} {toRAlg B})
          using ()
          renaming ( refl  to ≈-refl
                   ; sym   to ≈-sym
                   ; trans to ≈-trans
                   )

    isCategory : IsCategory WeilAlgebra _-Weil⟶_ _∼_ _o_ IdW
    isCategory = record { cong = λ {A} {B} {C} {f} {f′} {g} {g′} →
                                      ≈-cong
                                         {f = toUnderlying f}
                                         {toUnderlying f′}
                                         {toUnderlying g}
                                         {toUnderlying g′}                                       
                        ; isEquivalence = λ {A} {B} → isEquiv {A} {B}
                        ; identityˡ = identityˡ ∘ toUnderlying
                        ; identityʳ = identityʳ ∘ toUnderlying
                        ; assoc = λ f g h → assoc (toUnderlying f) (toUnderlying g) (toUnderlying h)
                        }

-}
