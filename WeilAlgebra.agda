{-# OPTIONS --universe-polymorphism #-}
open import Level hiding (zero ; Lift)
import Level as L
open import Algebra

module WeilAlgebra {c ℓ} (R : CommutativeRing c ℓ) where
open import Data.Nat using  (ℕ) renaming (suc to S)
open import R-Module R
open import R-Module.Free R
open import Algebra.Structures
open import Relation.Binary
open import Relation.Binary.Core
open import Function hiding (id)
open import Relation.Unary hiding (_⟨∘⟩_ ; U)
open import Data.Product
open import Algebra.Morphism
open import Data.Product.N-ary
import Relation.Binary.SetoidReasoning as SetR
open import Data.Fin using (Fin) renaming (zero to OZ ; suc to OS)
open import Function.Equality
            hiding   (setoid ; flip ; const)
            renaming (_∘_ to _⟨∘⟩_)
import Function.Equality as FEq

open import Categories
open import Categories.Setoids
open import Categories.Sets
open import LevelLifting

import Categories.Properties as CatProps
import HomSetoid as I
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
    record { Gadget = I.0-Setoid (R-Algebra c′ ℓ′)
           ; Morph = _-R-Alg⟶_
           ; U₀ = U₀
           ; U₁ = U₁
           ; Morph-cong = PEq.cong₂ _-R-Alg⟶_
           ; ≈₀-cong = PEq.cong U₀
           ; Liftable = Liftable
           ; Lift = Lift
           ; U₁-Lift-inverse = λ {A} {B} {f} → _-R-Module⟶_.⟦⟧-cong f
           ; U₁-liftable = λ {A} {B} {f} → _-R-Alg⟶_.•-homo f
           ; id-liftable = λ {A} _ _ → Setoid.refl (R-Algebra.setoid A)
           ; o-liftable = λ {A} {B} {C} {f} {g} → o-liftable {A} {B} {C} {f} {g}
           }
  where
    open Category (R-Mod {c′} {ℓ′})
      using (isEquivalence₁)
    open I.IsEquivalence isEquivalence₁
      renaming (refl to ≈₁-refl)
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
    Lift f {pf} = record { ⟦⟧-linear = f.⟦⟧-linear
                         ; •-homo = pf
                         }
      where module f = _-R-Module⟶_ f
    o-liftable : ∀{a b c} {g : U₀ b -R-Module⟶ U₀ c} {f : U₀ a -R-Module⟶ U₀ b}
               → Liftable b c g
               → Liftable a b f
               → Liftable a c (R-Mod [ g o f ])
    o-liftable {a} {b} {c} {g} {f} g-•-homo f-•-homo x y =
      begin
        ⟦ x A.• y ⟧
      ≡⟨⟩
        g.⟦ f.⟦ x A.• y ⟧ ⟧
      ≈⟨ g.⟦⟧-cong (f-•-homo x y) ⟩
        g.⟦ f.⟦ x ⟧ B.• f.⟦ y ⟧ ⟧
      ≈⟨ g-•-homo f.⟦ x ⟧ f.⟦ y ⟧ ⟩
        ⟦ x ⟧ C.• ⟦ y ⟧
      ∎
      where
        module g = _-R-Module⟶_ g
        module f = _-R-Module⟶_ f
        module A = R-Algebra a
        module B = R-Algebra b
        module C = R-Algebra c
        ⟦_⟧ = g.⟦_⟧ ∘ f.⟦_⟧
        open EqR C.setoid

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
  1#0 : ∀{n} → I.0-Setoid (Fin (S n)) ⟶ setoidR
  1#0 = record { _⟨$⟩_ = fun
               ; cong = λ {i} {j} i≈j →
                          IsEquivalence.reflexive
                            R-isEquivalence
                            (PEq.cong fun i≈j)
               }
    where
      fun = λ { OZ → 1R ; (OS _) → 0R }

record IsAugmentedCommutativeR-Algebra
       {n : ℕ} (_•_ : Op₂ (R-Module.Carrier ((S n) DimFreeModule)))
       : Set (ℓ ⊔ c) where
  private
    Rⁿ⁺¹ = (S n) DimFreeModule
    open R-Module Rⁿ⁺¹
    open FunctionProperties _≈_ hiding (Op₁ ; Op₂)
    open Definitions Carrier Coeff _≈R_

    augmentation : Pred Carrier ℓ
    augmentation x = (x ⟨$⟩ OZ) ≈R 0R
    π₀ : Carrier → Coeff
    π₀ f = f ⟨$⟩ OZ
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
  augmentation x = (x ⟨$⟩ OZ) ≈R 0R

  π₀ : R-algebra -R-Alg⟶ coeffAlg
  π₀ = record { ⟦⟧-linear = ⟦⟧-linear
              ; •-homo = π₀-•-homo
              }
    where
      open Linear π₀-linear using (⟦⟧-cong ; +-homo ; *>-homo; 0#-homo)
      ⟦_⟧ : Carrier → Coeff
      ⟦ f ⟧ = f ⟨$⟩ OZ
      ⟦⟧-linear : Linear R-module coeffModule ⟦_⟧
      ⟦⟧-linear = record { ⟦⟧-cong = λ {a} {b} → ⟦⟧-cong {a} {b}
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
                   → (∀ i → F i ⟨$⟩ OZ ≈R 0R)
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

  open _-R-Alg⟶_ -R-alg⟶ using (-R-module⟶ ; ⟦⟧-cong) public

private
  U₀ = WeilAlgebra.R-algebra
  U₁ = _-Weil⟶_.-R-alg⟶
  Liftable : ∀ W W′ → (f : U₀ W -R-Alg⟶ U₀ W′) → Set _
  Liftable W W′ f = ∀ x → x ∈ W.augmentation → f.⟦ x ⟧ ∈ W′.augmentation
    where
      module f = _-R-Alg⟶_ f
      module W = WeilAlgebra W
      module W′ = WeilAlgebra W′
  Lift : ∀ {A B} → (f : U₀ A -R-Alg⟶ U₀ B) → { pf : Liftable A B f} → A -Weil⟶ B
  Lift {A} {B} f {pf} = record { J-homo = pf
                               ; ⟦⟧-linear = f.⟦⟧-linear
                               ; •-homo = f.•-homo
                               }
    where
      module f = _-R-Alg⟶_ f

  J-homo : ∀{A B C : WeilAlgebra}
         → {f : U₀ B -R-Alg⟶ U₀ C} → {g : U₀ A -R-Alg⟶ U₀ B}
         → Liftable B C f → Liftable A B g → Liftable A C (R-Alg [ f o g ])
  J-homo {g = g} f-J-homo g-J-homo x x∈Jₐ =
    f-J-homo g.⟦ x ⟧ (g-J-homo x x∈Jₐ)
      where module g = _-R-Alg⟶_ g

  W-Pair : Σ[ Weil ∈ Category _ _ _ _ ] (Functor Weil R-Alg)
  W-Pair =
      extend R-Alg
      by record { Gadget   = I.0-Setoid WeilAlgebra
                ; Morph    = _-Weil⟶_
                ; U₀ = U₀ ; U₁ = U₁ ; Lift = Lift
                ; ≈₀-cong = PEq.cong U₀
                ; Liftable = Liftable
                ; Morph-cong = PEq.cong₂ _-Weil⟶_
                ; U₁-Lift-inverse = λ {A} {B} {f} → _-R-Alg⟶_.⟦⟧-cong f
                ; U₁-liftable = λ {A} {B} {f} → _-Weil⟶_.J-homo f
                ; id-liftable = λ _ pf → pf
                ; o-liftable = λ {A} {B} {C} {f} {g} → J-homo {A} {B} {C} {f} {g}
                }

_=R-Alg⇒_ : ∀{a₁ a₂ b₁ b₂} → (A : R-Algebra a₁ a₂) (B : R-Algebra b₁ b₂) → Setoid _ _
A =R-Alg⇒ B = record { Carrier = A -R-Alg⟶ B
                      ; _≈_ = λ f g → ∀ {x y} → x ≈₁ y → _-R-Alg⟶_.⟦_⟧ f x ≈₂ _-R-Alg⟶_.⟦_⟧ g y
                      ; isEquivalence = record
                        { refl = λ {f} → ⟦⟧-cong f
                        ; sym = λ f∼g x≈y → ≈₂-sym (f∼g (≈₁-sym x≈y))
                        ; trans = λ f∼g g∼h x≈y → (f∼g x≈y) ⟨ ≈₂-trans ⟩ g∼h ≈₁-refl
                        }
                      }
  where
    ⟦⟧-cong = _-R-Alg⟶_.⟦⟧-cong
    open module From = Setoid (R-Algebra.setoid A)
         renaming (_≈_ to _≈₁_ ; refl to ≈₁-refl ; sym to ≈₁-sym)
    open module To   = Setoid (R-Algebra.setoid B)
         renaming (_≈_ to _≈₂_ ; sym to ≈₂-sym ; trans to ≈₂-trans)

Weil : Category _ _ _ _
Weil = proj₁ W-Pair

U : Functor Weil R-Alg
U = proj₂ W-Pair

lift-IsDistributiveR-Algebra : ∀{c ℓ c′ ℓ′} {A : Set c′}
                    {_≈_ : Rel A ℓ′} {_+_ _•_ : Op₂ A}
                    {_*>_ : Coeff → A → A} { -_ : Op₁ A } {0# : A}
                 → IsDistributiveR-Algebra _≈_ _+_ _*>_ -_ _•_ 0#
                 → IsDistributiveR-Algebra
                       (lift-Rel {c = c} {ℓ = ℓ} _≈_)
                       (lift-Op₂ {ℓ = c} _+_)
                       (λ x → lift-Op₁ (_*>_ x))
                       (lift-Op₁ -_) (lift-Op₂ _•_)
                       (lift {ℓ = c} 0#)
lift-IsDistributiveR-Algebra {d} {k} {c′} {ℓ′} isR =
  record { isR-Module = lift-IsR-Module isR-Module
         ; •-cong = λ x≈y u≈v → lift (•-cong (lower x≈y) (lower u≈v))
         ; •-bilinear = ((λ x → proj₁ {!•-bilinear!} {!!})
                        ,(λ x → {!!}))
         }
  where
    open IsDistributiveR-Algebra isR


lift-IsAssociativeR-Algebra : ∀{c′ ℓ′ d k} {A : Set c′}
                    {_≈_ : Rel A ℓ′} {_+_ _•_ : Op₂ A}
                    {_*>_ : Coeff → A → A} { -_ : Op₁ A } {0# : A}
                 → IsAssociativeR-Algebra _≈_ _+_ _*>_ -_ _•_ 0#
                 → IsAssociativeR-Algebra
                       (lift-Rel {c = d} {ℓ = k} _≈_)
                       (lift-Op₂ {ℓ = d} _+_)
                       (λ x → lift-Op₁ (_*>_ x))
                       (lift-Op₁ -_) (lift-Op₂ _•_)
                       (lift 0#)
lift-IsAssociativeR-Algebra {d} {k} isR =
  record { isDistributiveR-Algebra = lift-IsDistributiveR-Algebra isDistributiveR-Algebra
         ; •-assoc = λ x y z → lift (•-assoc (lower x) (lower y) (lower z))
         }
  where
    open IsAssociativeR-Algebra isR

lift-IsR-Algebra : ∀{c′ ℓ′ d k} {A : Set c′}
                    {_≈_ : Rel A ℓ′} {_+_ _•_ : Op₂ A}
                    {_*>_ : Coeff → A → A} { -_ : Op₁ A } {0# 1# : A}
                 → IsR-Algebra _≈_ _+_ _*>_ -_ _•_ 0# 1#
                 → IsR-Algebra
                       (lift-Rel {c = d} {ℓ = k} _≈_)
                       (lift-Op₂ {ℓ = d} _+_)
                       (λ x → lift-Op₁ (_*>_ x))
                       (lift-Op₁ -_) (lift-Op₂ _•_)
                       (lift 0#) (lift 1#)
lift-IsR-Algebra {d} {k} isR =
  record { •-identity = ((λ x → lift $ proj₁ •-identity (lower x))
                        ,(λ x → lift $ proj₂ •-identity (lower x)))
         ; isAssociativeR-Algebra = lift-IsAssociativeR-Algebra isAssociativeR-Algebra
         }
  where
    open IsR-Algebra isR

lift-R-Algebra : ∀{c′ ℓ′ c ℓ} → R-Algebra c′ ℓ′ → R-Algebra (c′ ⊔ c) (ℓ′ ⊔ ℓ)
lift-R-Algebra {c′} {ℓ′} {d} {k} W =
  record { Carrier = L.Lift { ℓ = d } Carrier
         ; _≈_  = lift-Rel { ℓ = k } _≈_
         ; _+_  = lift-Op₂ _+_
         ; _•_  = lift-Op₂ _•_
         ; _*>_ = λ a b → L.lift (a *> lower b)
         ; -_   = lift-Op₁ -_
         ; 0#   = lift 0#
         ; 1#   = lift 1#
         ; isR-Algebra = lift-IsR-Algebra isR-Algebra
         }
  where
    open R-Algebra W

Spec₀ : ∀{c′ ℓ′ c″ ℓ″} (A : R-Algebra c′ ℓ′) (W : R-Algebra c″ ℓ″)
    → Setoid (ℓ″ ⊔ c″ ⊔ ℓ′ ⊔ c′ ⊔ c) (ℓ″ ⊔ c″ ⊔ ℓ′)
Spec₀ A W = W =R-Alg⇒ A

Spec₁ : ∀{c′ ℓ′} {A : R-Algebra c′ ℓ′} { B : R-Algebra c′ ℓ′ }
      → (C : R-Algebra c′ ℓ′)
      → (A -R-Alg⟶ B)
      → Hom Setoids (Spec₀ C B) (Spec₀ C A)
Spec₁ {B = B} C f = 
            record { _⟨$⟩_ = λ g → (R-Alg [ g o f ])
                   ; cong = λ {g₀} {g′₀} g∼g′ {x} {y} x≈y →
                            let open EqR (R-Algebra.setoid C)
                                open Category Setoids
                                open Setoid (R-Algebra.setoid B)
                                  renaming (refl to B-refl)
                                f′ = _-R-Alg⟶_.Πsetoid f
                                g = _-R-Alg⟶_.Πsetoid g₀
                                g′ = _-R-Alg⟶_.Πsetoid g′₀
                                Πcong = Π.cong
                            in begin
                                 g o f′ ⟨$⟩ x
                               ≈⟨ Πcong (g o f′) x≈y ⟩
                                 g o f′ ⟨$⟩ y
                               ≡⟨⟩
                                 g ⟨$⟩ (f′ ⟨$⟩ y)
                               ≈⟨ g∼g′ B-refl ⟩
                                 g′ ⟨$⟩ (f′ ⟨$⟩ y)
                               ≡⟨⟩
                                 g′ o f′ ⟨$⟩ y
                               ∎
                   }

{-
Spec : ∀(A : R-Algebra ) → ContravariantFunctor Weil (Setoids {c ⊔ ℓ} {c ⊔ ℓ})
Spec A = record { ⟦_⟧₀ = ⟦_⟧₀
                ; ⟦_⟧₁ = Spec₁ A ∘ _-Weil⟶_.-R-alg⟶
                ; isFunctor = isFunctor
                }
  where
    module Setoids = Category (Setoids {c ⊔ ℓ} {c ⊔ ℓ})
    module R-Alg = Category (R-Alg {c ⊔ ℓ} {ℓ ⊔ c})
    module Weil = Category Weil
    ⟦_⟧₀ : WeilAlgebra → Setoid _ _
    ⟦_⟧₀ = Spec₀ A ∘ WeilAlgebra.R-algebra
    ⟦_⟧₁ : ∀{A B} → A -Weil⟶ B → ⟦ B ⟧₀ ⟶ ⟦ A ⟧₀
    ⟦_⟧₁ = Spec₁ A ∘ _-Weil⟶_.-R-alg⟶
    Id-homo : {A : WeilAlgebra} → Setoids [ ⟦ Id′ Weil A ⟧₁ ≈₁ Id′ Setoids ⟦ A ⟧₀ ]
    Id-homo {A} {x} {y} x≈y =
      begin
        ⟦ Id′ Weil A ⟧₁ ⟨$⟩ x
      ≡⟨⟩
        (λ g → R-Alg [ g o Id′ R-Alg (WeilAlgebra.R-algebra A) ] ) x
      ≡⟨⟩
        R-Alg [ x o Id′ R-Alg (WeilAlgebra.R-algebra A) ]
      ≈⟨ R-Alg.identityʳ x ⟩
        x
      ≈⟨ x≈y ⟩
        y
      ≡⟨⟩
        Id′ Setoids ⟦ A ⟧₀ ⟨$⟩ y
      ∎
      where
        open EqR ⟦ A ⟧₀
        open Setoids using (_o_)

    o-homo : ∀{a b c} → (f : b -Weil⟶ c) → (g : a -Weil⟶ b)
           → Setoids [ ⟦ f Weil.o g ⟧₁ ≈₁ ⟦ g ⟧₁ Setoids.o ⟦ f ⟧₁ ]
    o-homo {A} {B} {C} f g {x} {y} x≈y =
      begin
        ⟦ f Weil.o g ⟧₁ ⟨$⟩ x
      ≡⟨⟩
        x R-Alg.o (toA f R-Alg.o toA g)
      ≈⟨ R-Alg.o-cong {f = x} {f′ = y}
                      {g = toA f R-Alg.o toA g}
                      {g′ = toA f R-Alg.o toA g}
                      x≈y (≈₁-refl {x = toA f R-Alg.o toA g}) ⟩
        y R-Alg.o (toA f R-Alg.o toA g)
      ≈⟨ R-Alg.assoc y (toA f) (toA g) ⟩
        (y R-Alg.o toA f) R-Alg.o toA g
      ≡⟨⟩
       (⟦ g ⟧₁ Setoids.o ⟦ f ⟧₁) ⟨$⟩ y
      ∎
      where
        toA = _-Weil⟶_.-R-alg⟶
        open EqR ⟦ A ⟧₀
        open Setoids using (_o_)
        open I.IsEquivalence R-Alg.isEquivalence₁
          renaming (refl to ≈₁-refl)
    isFunctor : IsContravariantFunctor Weil Setoids ⟦_⟧₀ ⟦_⟧₁
    isFunctor = record { Id-homo  = λ {A} {x} {y} → Id-homo {A} {x} {y}
                       ; o-homo   = λ {A} {B} {C} → o-homo {A} {B} {C}
                       ; ⟦_⟧₁-cong = λ {W₁} {W₂} {f₀} {g₀} f≈g {x} {y} x≈y →
                                       let open EqR ⟦ W₁ ⟧₀
                                           f = _-Weil⟶_.-R-alg⟶ f₀
                                           g = _-Weil⟶_.-R-alg⟶ g₀
                                           open I.IsEquivalence R-Alg.isEquivalence₁
                                             renaming (refl to ≈₁-refl)
                                       in begin
                                            ⟦ f₀ ⟧₁ ⟨$⟩ x
                                          ≡⟨⟩
                                            x R-Alg.o f
                                          ≈⟨ R-Alg.o-cong {f = x} {f′ = y} {g = f} {g′ = g}
                                                          x≈y f≈g ⟩
                                            y R-Alg.o g
                                          ≡⟨⟩
                                            ⟦ g₀ ⟧₁ ⟨$⟩ y
                                          ∎
                       
                       }
-}
{-
R^_ : ∀{c′ ℓ′} → Setoid c′ ℓ′ → R-Algebra _ _
R^ I = record { Carrier = Carrier
              ; isR-Algebra = isR-Algebra
              }
  where
    open R-Module (FreeModule I)
    _•_ : Op₂ Carrier
    f • g = λ n → f n *R g n
    isR-Algebra = record {}
-}
