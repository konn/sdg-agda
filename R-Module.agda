open import Level hiding (Lift)
open import Algebra 
module R-Module {c ℓ} (R : CommutativeRing c ℓ) where
import Algebra.FunctionProperties as FunctionProperties
open import Algebra.Structures
open import Relation.Binary
open import Function hiding (id)
open FunctionProperties using (Op₁ ; Op₂)
open import Data.Product
open import Algebra.Morphism
open import Categories
open import Function.Equality
            hiding   (setoid ; flip)
            renaming (_∘_ to _⟨∘⟩_)
import Relation.Binary.EqReasoning as EqR
import Algebra.Properties.Group as GroupP
import Relation.Binary.PropositionalEquality as PEq
import Algebra.Properties.Ring as RingP
import Algebra.Properties.Ring as RingP
open import Relation.Binary.Core
import HomSetoid as I
open import HomSetoid using (Set′ ; 0-Setoid )
open import Categories.Setoids

open CommutativeRing R hiding   (ring)
                       renaming ( Carrier to Coeff
                                ; 1#      to 1R
                                ; 0#      to 0R
                                ; -_      to -R_
                                ; _-_     to _-R_
                                ; _+_     to _+R_
                                ; _*_     to _*R_
                                ; _≈_     to _≈R_
                                ; *-cong  to *R-cong
                                ; +-cong  to +R-cong
                                ; +-identity to +R-identity
                                ; +-assoc    to +R-assoc
                                ; *-assoc    to *R-assoc
                                ; *-semigroup to *R-semigroup
                                ; +-isAbelianGroup to +R-isAbelianGroup
                                ; -‿inverse  to -R‿inverse
                                ; *-isSemigroup to *R-isSemigroup
                                ; setoid  to setoidR
                                ; isCommutativeRing to R-isCommutativeRing
                                ; isRing  to R-isRing
                                ; distrib to R-distrib
                                ; isEquivalence to R-isEquivalence
                                ; isSemiringWithoutOne to R-isSemiringWithoutOne
                                ; semiringWithoutOne   to R-semiringWithoutOne
                                ; +-comm     to +R-comm
                                ; +-isMonoid to +R-isMonoid
                                ; +-isGroup  to +R-isGroup
                                ; -‿cong     to -R‿cong
                                ; *-comm     to *R-comm     
                                ; *-identity to *R-identity 
                                ; *-isMonoid to *R-isMonoid
                                ; refl  to ≈R-refl
                                ; sym   to ≈R-sym
                                ; trans to ≈R-trans
                                ) public

record IsR-Module {c′ ℓ′} {C : Set c′} (_≈_ : Rel C ℓ′) (_+_ : Op₂ C) (_*>_ : Coeff → C → C) (-_ : Op₁ C) (0# : C) : Set (c ⊔ ℓ ⊔ c′ ⊔ ℓ′) where
  open FunctionProperties _≈_
  field
    isAbelianGroup : IsAbelianGroup _≈_ _+_ 0# -_
    *>-cong      : _*>_ Preserves₂ _≈R_ ⟶ _≈_ ⟶ _≈_
    *>-assoc     : ∀ a b x -> ((a *R b) *> x) ≈ (a *> (b *> x))
    *>-+-distrib : ∀ a x y → (a *> (x + y)) ≈ ((a *> x) + (a *> y))
    +-*>-distrib : ∀ a b x → ((a +R b) *> x) ≈ ((a *> x) + (b *> x))
    *>-identity  : ∀ x → (1R *> x) ≈ x

  open IsAbelianGroup isAbelianGroup
    renaming ( ∙-cong to +-cong
             ; identity to +-identity
             ; inverse  to -‿inverse
             ; assoc    to +-assoc
             )
    public

  private
    G : Group _ _
    G = record { isGroup = isGroup }
    open GroupP G
    open EqR (Group.setoid G)
    open IsEquivalence isEquivalence
      renaming ( refl  to ≈-refl
               ; sym   to ≈-sym
               ; trans to ≈-trans
               )

  *>-zero : ∀ x → (0R *> x) ≈ 0#
  *>-zero x = left-identity-unique (0R *> x) x $ begin
                (0R *> x) + x
              ≈⟨ +-cong ≈-refl (≈-sym (*>-identity x)) ⟩
                (0R *> x) + (1R *> x)
              ≈⟨ ≈-sym (+-*>-distrib 0R 1R x) ⟩
                (0R +R 1R) *> x
              ≈⟨ *>-cong (proj₁ +R-identity 1R) ≈-refl ⟩
                1R *> x
              ≈⟨ *>-identity x ⟩
                x
              ∎

  *>-inverse : ∀ x → ((-R 1R) *> x) ≈ - x
  *>-inverse x = left-inverse-unique ((-R 1R) *> x) x $ begin
                   (-R_ 1R *> x) + x
                 ≈⟨ +-cong ≈-refl (≈-sym (*>-identity x)) ⟩
                   (-R_ 1R *> x) + (1R *> x)
                 ≈⟨ ≈-sym (+-*>-distrib (-R 1R) 1R x) ⟩
                   (-R 1R +R 1R) *> x
                 ≈⟨ *>-cong (proj₁ -R‿inverse 1R) ≈-refl ⟩
                   0R *> x
                 ≈⟨ *>-zero x ⟩
                   0#
                 ∎
      
record R-Module c′ ℓ′ : Set (suc (c ⊔ ℓ ⊔ c′ ⊔ ℓ′)) where
  infix  8 -_
  infixr 7 _*>_
  infixl 6 _+_
  infix  4 _≈_
  field
    Carrier : Set c′
    _≈_     : Rel Carrier ℓ′
    _+_     : Op₂ Carrier
    _*>_    : Coeff → Carrier → Carrier
    -_      : Op₁ Carrier
    0#      : Carrier
    isR-Module : IsR-Module _≈_ _+_ _*>_ -_ 0#
  open IsR-Module isR-Module public

  abelianGroup : AbelianGroup c′ ℓ′
  abelianGroup = record { isAbelianGroup = isAbelianGroup }

  open AbelianGroup abelianGroup
    using ( setoid; semigroup
          ; monoid; rawMonoid
          ; group ; commutativeMonoid
          )
    public

record Linear {m₁ m₂ m₃ m₄} (From : R-Module m₁ m₂) (To : R-Module m₃ m₄)
              (⟦_⟧ : R-Module.Carrier From → R-Module.Carrier To) : Set (c ⊔ m₁ ⊔ m₂ ⊔ m₃ ⊔ m₄) where
  private
    module F = R-Module From
    module T = R-Module To
  open Definitions F.Carrier T.Carrier T._≈_
  field
    ⟦⟧-cong  : ⟦_⟧ Preserves F._≈_ ⟶ T._≈_
    +-homo  : Homomorphic₂ ⟦_⟧ F._+_  T._+_
    *>-homo : ∀ a x → ⟦ a F.*> x ⟧ T.≈ a T.*> ⟦ x ⟧
    0#-homo : Homomorphic₀ ⟦_⟧ F.0#   T.0#

coeffModule : R-Module c ℓ
coeffModule = record { isR-Module = isR-Module }
  where
    isR-Module : IsR-Module _≈R_ _+R_ _*R_ -R_ 0R
    isR-Module = record { isAbelianGroup = +R-isAbelianGroup
                        ; *>-cong  = *R-cong
                        ; *>-assoc = *R-assoc
                        ; *>-+-distrib = proj₁ R-distrib
                        ; +-*>-distrib = λ a b x → proj₂ R-distrib x a b
                        ; *>-identity  = proj₁ *R-identity
                        }



record _-R-Module⟶_ {m₁ m₂ m₃ m₄} (From : R-Module m₁ m₂) (To : R-Module m₃ m₄)
       : Set (c ⊔ m₁ ⊔ m₂ ⊔ m₃ ⊔ m₄)  where
  private
    module F = R-Module From
    module T = R-Module To
  open Definitions F.Carrier T.Carrier T._≈_
  field
    ⟦_⟧       : Morphism
    ⟦⟧-linear : Linear From To ⟦_⟧

  open Linear ⟦⟧-linear public
  Πsetoid : F.setoid ⟶ T.setoid
  Πsetoid = record { _⟨$⟩_ = ⟦_⟧  ; cong = ⟦⟧-cong }

R-Mod : ∀{c′ ℓ′} → Category _ _ _ _
R-Mod {c′} {ℓ′} =
  subCategory {Base = Setoids {c′} {ℓ′}}
              record { Gadget = 0-Setoid (R-Module c′ ℓ′)
                     ; Morph  = _-R-Module⟶_
                     ; Morph-cong = PEq.cong₂ _-R-Module⟶_
                     ; U₀ = U₀
                     ; U₁ = U₁
                     ; ≈₀-cong = PEq.cong U₀
                     ; Liftable = Liftable
                     ; Lift = Lift
                     ; U₁-Lift-inverse = λ {A} {B} {f} → cong f
                     ; U₁-liftable = λ {A} {B} {f} → _-R-Module⟶_.⟦⟧-linear f
                     ; id-liftable = id-liftable
                     ; o-liftable  = λ {A} {B} {C} {g} {f} → o-liftable {g = g} {f}
                     }
  where
    open Category (Setoids {c′} {ℓ′})
      using (HomSetoid)
      renaming (_≈₁_ to _∼₁_)
    open I.Setoid HomSetoid
      using ()
      renaming ( refl  to refl₁
               ; trans to trans₁
               ; sym   to sym₁
               )
    U₀ = R-Module.setoid
    U₁ = _-R-Module⟶_.Πsetoid
    toFun = Π._⟨$⟩_
    Liftable : ∀ A B → ((U₀ A) ⟶ (U₀ B)) → Set _
    Liftable A B f = Linear A B (_⟨$⟩_ f)
    Lift  : ∀{A B} → (f : U₀ A ⟶ U₀ B) → {pf : Liftable A B f} → A -R-Module⟶ B
    Lift {A} {B} f {lin} = record { ⟦_⟧ = toFun f ; ⟦⟧-linear = lin}
    id-liftable : ∀{A} → Liftable A A id
    id-liftable {A} = record { ⟦⟧-cong = λ x → x       
                             ; +-homo = λ x y → A.refl
                             ; *>-homo = λ x y → A.refl
                             ; 0#-homo = A.refl
                             }
      where
        module A = R-Module A

    o-liftable : ∀{a b c} {g : U₀ b ⟶ U₀ c} {f : U₀ a ⟶ U₀ b}
                 → Liftable b c g
                 → Liftable a b f
                 → Liftable a c (Setoids [ g o f ])
    o-liftable {A} {B} {C} {g} {f} g-lin f-lin =
        record { ⟦⟧-cong = G.⟦⟧-cong ∘ F.⟦⟧-cong
               ; +-homo = λ x y →
                          begin
                            ⟦ x V₁.+ y ⟧
                          ≈⟨ G.⟦⟧-cong (F.+-homo x y) ⟩
                            g ⟨$⟩ ((f ⟨$⟩ x) V₂.+ (f ⟨$⟩ y) )
                          ≈⟨ G.+-homo (f ⟨$⟩ x) (f ⟨$⟩ y) ⟩
                            ⟦ x ⟧ V₃.+ ⟦ y ⟧
                          ∎
               ; *>-homo = λ x y →
                          begin
                            ⟦ x V₁.*> y ⟧
                          ≈⟨ G.⟦⟧-cong (F.*>-homo x y) ⟩
                            g ⟨$⟩ ( x V₂.*> (f ⟨$⟩ y) )
                          ≈⟨ G.*>-homo x (f ⟨$⟩ y) ⟩
                            x V₃.*> ⟦ y ⟧
                          ∎
               ; 0#-homo = begin
                             ⟦ V₁.0# ⟧
                           ≈⟨ G.⟦⟧-cong F.0#-homo ⟩
                             g ⟨$⟩ V₂.0#
                           ≈⟨ G.0#-homo ⟩
                             V₃.0#
                           ∎
               }
      where
        module G = Linear g-lin
        module F = Linear f-lin
        module V₁ = R-Module A
        module V₂ = R-Module B
        module V₃ = R-Module C
        open EqR V₃.setoid
        ⟦_⟧ : V₁.Carrier → V₃.Carrier
        ⟦_⟧ x = g ⟨$⟩ (f ⟨$⟩ x)
      

_-Linear⟶_ : ∀ {m₁ m₂ m₃ m₄} → (From : R-Module m₁ m₂) → (To : R-Module m₃ m₄) → Set _
_-Linear⟶_ = _-R-Module⟶_

Bilinear : ∀ {m₁ m₂ n₁ n₂ k₁ k₂}
         → (From₁ : R-Module m₁ m₂)
         → (From₂ : R-Module n₁ n₂)
         → (To : R-Module k₁ k₂)
         → (R-Module.Carrier From₁ → R-Module.Carrier From₂ → R-Module.Carrier To)
         → Set _
Bilinear F₁ F₂ T ⟦_,_⟧ = (∀ x → Linear F₁ T (flip ⟦_,_⟧ x)) ×  (∀ x → Linear F₂ T (⟦_,_⟧ x))

record -_×_-Bilinear⟶_ {m₁ m₂ n₁ n₂ k₁ k₂}
       (From₁ : R-Module m₁ m₂)
       (From₂ : R-Module n₁ n₂)
       (To : R-Module k₁ k₂) : Set (c ⊔ m₁ ⊔ m₂ ⊔ n₁ ⊔ n₂ ⊔ k₁ ⊔ k₂) where
  private
    module F₁ = R-Module From₁
    module F₂ = R-Module From₂
    module T  = R-Module To
  field
    ⟦_,_⟧ : F₁.Carrier → F₂.Carrier → T.Carrier
    ⟦⟧-bilinear : Bilinear From₁ From₂ To ⟦_,_⟧
