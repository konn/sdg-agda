{-# OPTIONS --universe-polymorphism #-}
module Categories where
open import Level hiding (Lift)
open import Function
open import Relation.Binary
open import Data.Product
open import Function.Equality hiding (flip ; _∘_)
open import Relation.Binary.PropositionalEquality
            using (_≡_)
import Relation.Binary.EqReasoning as EqR

import HomSetoid as I
open I using (Set′)

record IsCategory {c₀ c₁ ℓ₀ ℓ₁ : Level}
                  (Obj : Set c₀)
                  (Hom : Obj → Obj → Set c₁)
                  (_≈₀_ : Rel Obj ℓ₀)
                  (_≈₁_ : ∀{i₀ i₁ : Obj} → Rel (Hom i₀ i₁) ℓ₁)
                  (_o_ : ∀{A B C} → Hom B C → Hom A B → Hom A C)
                  (Id  : ∀{A} → Hom A A)
                   : Set (suc (c₀ ⊔ ℓ₀ ⊔ c₁ ⊔ ℓ₁)) where
  field
    isEquivalence₀ : IsEquivalence _≈₀_
    Hom-cong : ∀{i i′ j j′ : Obj}
             → i ≈₀ i′ → j ≈₀ j′ → Hom i j ≡ Hom i′ j′

  private
    ObjSetoid : Setoid c₀ ℓ₀
    ObjSetoid = record { isEquivalence = isEquivalence₀ }

  open Setoid ObjSetoid
    using ()
    renaming ( refl    to refl₀
             ; sym     to sym₀
             ; trans   to trans₀
             ) public

  private
    Hom″ : Obj → (ObjSetoid ⟶ Set′ c₁)
    Hom″ A = record { _⟨$⟩_ = λ B → Hom A B
                   ; cong = Hom-cong {A} {A} refl₀
                   }

    Hom′ : ObjSetoid ⟶ ObjSetoid ⇨ Set′ c₁
    Hom′ = record { _⟨$⟩_ = λ A → Hom″ A
                 ; cong = λ i≈i′ j≈j′ → Hom-cong i≈i′ j≈j′
                 }

  field
    isEquivalence₁ : I.IsEquivalence Hom′ _≈₁_

  field
    o-cong : ∀{A B C} {f f′ : Hom B C} {g g′ : Hom A B}
           → f ≈₁ f′ → g ≈₁ g′ → (f o g) ≈₁ (f′ o g′)
    identityˡ : ∀{A B} (f : Hom A B) → (Id o f) ≈₁ f
    identityʳ : ∀{A B} (f : Hom A B) → (f o Id) ≈₁ f
    assoc : ∀{A B C D}
            → (f : Hom C D)
            → (g : Hom B C)
            → (h : Hom A B)
            → ((f o g) o h) ≈₁ (f o (g o h))

record Category c₀ c₁ ℓ₀ ℓ₁ : Set (suc (c₀ ⊔ c₁ ⊔ ℓ₀ ⊔ ℓ₁)) where
  infixl 9 _o_
  infix  4 _≈₀_ _≈₁_
  field
    Obj : Set c₀
    Hom : Obj → Obj → Set c₁
    _o_ : {A B C : Obj} → Hom B C → Hom A B → Hom A C
    _≈₀_ : Rel Obj ℓ₀
    _≈₁_ : ∀{i₀ i₁ : Obj} → Rel (Hom i₀ i₁) ℓ₁
    Id  : {A : Obj} → Hom A A
    isCategory : IsCategory Obj Hom _≈₀_ _≈₁_ _o_ Id

  open IsCategory isCategory public

  ObjSetoid : Setoid c₀ ℓ₀
  ObjSetoid = record { isEquivalence = isEquivalence₀ }

  HomSetoid : I.Setoid ObjSetoid _ _
  HomSetoid = record { isEquivalence = isEquivalence₁ }

  dom : {A B : Obj} → Hom A B → Obj
  dom {A} _ = A
  cod : {A B : Obj} → Hom A B → Obj
  cod {B = B} _ = B

  Id′ : (A : Obj) →  Hom A A
  Id′ A = Category.Id

  _ᵒᵖ : Category c₀ c₁ ℓ₀ ℓ₁
  _ᵒᵖ = record { isCategory = opIsCategory }
    where
      open Setoid using    (sym ; refl ; trans)
      module Orig = I.Setoid HomSetoid
      module F = I.Setoid Orig.flipped
      opIsCategory : IsCategory Obj (flip Hom) _≈₀_ _≈₁_ (flip _o_) Id 
      opIsCategory = record { isEquivalence₀ = isEquivalence₀
                            ; isEquivalence₁ = F.isEquivalence
                            ; identityˡ = identityʳ
                            ; identityʳ = identityˡ
                            ; assoc    = λ f g h → sym (HomSetoid I.[ _ , _ ]) (assoc h g f)
                            ; o-cong = flip o-cong
                            }


open Category using (_ᵒᵖ ; Id ; Id′ ; Obj ; Hom) public

_[_≈₀_] : ∀{c₀ c₁ ℓ₀ ℓ₁} → (C : Category c₀ c₁ ℓ₀ ℓ₁) → Rel (Obj C) ℓ₀
C [ i ≈₀ j ] = Category._≈₀_ C i j

_[_≈₁_] : ∀{c₀ c₁ ℓ₀ ℓ₁} → (C : Category c₀ c₁ ℓ₀ ℓ₁) → {A B : Obj C} → Rel (Hom C A B) ℓ₁
C [ f ≈₁ g ] = Category._≈₁_ C f g

_[_o_] : ∀{c₀ c₁ ℓ₀ ℓ₁} → (C : Category c₀ c₁ ℓ₀ ℓ₁)
       → {a b c : Obj C} → Hom C b c → Hom C a b → Hom C a c
C [ f o g ] = Category._o_ C f g

infixr 9 _[_o_]
infix  4 _[_≈₁_] _[_≈₀_]

record IsFunctor {c₀ c₁ ℓ₀ ℓ₁ c₀′ c₁′ ℓ₀′ ℓ₁′ : Level}
                 (C : Category c₀ c₁ ℓ₀ ℓ₁) (D : Category c₀′ c₁′ ℓ₁′ ℓ₀′)
                 (⟦_⟧₀ : Obj C → Obj D)
                 (⟦_⟧₁ : ∀{A B} → Hom C A B → Hom D ⟦ A ⟧₀ ⟦ B ⟧₀)
                 : Set (suc (c₀ ⊔ c₁ ⊔ ℓ₀ ⊔ ℓ₁ ⊔ c₀′ ⊔ c₁′ ⊔ ℓ₀′ ⊔ ℓ₁′)) where
  module F = Category C
  module T = Category D
  field
    ⟦_⟧₁-cong : ∀{A B} {f g : F.Hom A B} → C [ f ≈₁ g ] → D [ ⟦ f ⟧₁ ≈₁ ⟦ g ⟧₁ ]
    Id-cong : {A : Obj C} → D [ ⟦ F.Id′ A ⟧₁ ≈₁ T.Id′ ⟦ A ⟧₀ ]
    o-homo  : ∀{a b c} → (f : Hom C b c) → (g : Hom C a b)
            → D [ ⟦ f F.o g ⟧₁ ≈₁ ⟦ f ⟧₁ T.o ⟦ g ⟧₁ ]

record Functor {c₀ c₁ ℓ₀ ℓ₁ c₀′ c₁′ ℓ₀′ ℓ₁′ : Level}
       (C : Category c₀ c₁ ℓ₀ ℓ₁) (D : Category c₀′ c₁′ ℓ₀′ ℓ₁′)
  : Set (suc (c₀ ⊔ c₁ ⊔ ℓ₀ ⊔ ℓ₁ ⊔ c₀′ ⊔ c₁′ ⊔ ℓ₀′ ⊔ ℓ₁′)) where
  field
    ⟦_⟧₀ : Obj C → Obj D
    ⟦_⟧₁ : {A B : Obj C} → Hom C A B → Hom D ⟦ A ⟧₀ ⟦ B ⟧₀
    isFunctor : IsFunctor C D ⟦_⟧₀ ⟦_⟧₁
  open IsFunctor isFunctor public

record SubCategory {c₀ c₁ ℓ₀ ℓ₁} (Base : Category c₀ c₁ ℓ₀ ℓ₁)  c₀′ c₁′ ℓ r
       : Set (suc (c₀ ⊔ c₁ ⊔ ℓ₀ ⊔ ℓ₁ ⊔ c₀′ ⊔ c₁′ ⊔ ℓ ⊔ r)) where
  field
    Gadget : Setoid c₀′ ℓ
  open Setoid Gadget
      using ()
      renaming (_≈_ to _≈₀_ ; Carrier to Gad)
  open Category Base
     using ()
     renaming (_≈₀_ to _∼₀_ ; _≈₁_ to _∼₁_)
  field
    Morph : Gad → Gad → Set c₁′
    Morph-cong : ∀{i i′ j j′} → i ≈₀ i′ → j ≈₀ j′ → Morph i j ≡ Morph i′ j′
    U₀ : Gad → Obj Base
    U₁ : ∀{g g′} → Morph g g′ → Hom Base (U₀ g) (U₀ g′)
    ≈₀-cong : _≈₀_ =[ U₀ ]⇒ _∼₀_
    Liftable : ∀ A B → Hom Base (U₀ A) (U₀ B) → Set r
    Lift  : ∀{A B} → (f : Hom Base (U₀ A) (U₀ B)) → {pf : Liftable A B f} → Morph A B
    U₁-Lift-inverse : ∀{A B} {f : Hom Base (U₀ A) (U₀ B)} {pf : Liftable A B f}
                    → Base [ (U₁ (Lift f {pf})) ≈₁ f ]
    U₁-liftable : ∀{A B} {f : Morph A B} → Liftable A B (U₁ f)
    o-liftable   : ∀{a b c} {g : Hom Base (U₀ b) (U₀ c)} {f : Hom Base (U₀ a) (U₀ b)}
                 → Liftable b c g
                 → Liftable a b f
                 → Liftable a c (Base [ g o f ])

  _o′_ : ∀{a b c} → Morph b c → Morph a b → Morph a c
  _o′_ g f = Lift (Base [ U₁ g o U₁ f ]) {o-liftable U₁-liftable U₁-liftable}

  field
    id-liftable : ∀{a : Gad} → Liftable a a (Id′ Base (U₀ a))

  ID : ∀{a} → Morph a a
  ID {a} = Lift (Id′ Base (U₀ a)) {id-liftable}

  U₁-o-distrib : ∀{A B C} → (f : Morph B C) → (g : Morph A B)
               → U₁ (f o′ g) ∼₁ Base [ U₁ f o U₁ g ]
  U₁-o-distrib {A} {B} {C} f g =
    begin
      U₁ (f o′ g)
    ≡⟨⟩
      U₁ (Lift (U₁ f o U₁ g))
    ≈⟨ U₁-Lift-inverse ⟩
      U₁ f o U₁ g
    ∎
    where
      open Category Base
      open EqR (record {isEquivalence = isEquivalence₁}  I.[ U₀ A , U₀ C ] )
      open I.IsEquivalence isEquivalence₁

subCategory : ∀{c₀ c₁ ℓ₀ ℓ₁ c₀′ c₁′ ℓ r}
            → {Base : Category c₀ c₁ ℓ₀ ℓ₁}
            → SubCategory Base c₀′ c₁′ ℓ r
            → Category c₀′ c₁′ ℓ ℓ₁
subCategory {Base = Base} defs = record { isCategory = isCategory }
  where
    open SubCategory defs
    open Setoid Gadget
      using ()
      renaming ( isEquivalence to isEquivalence₀
               ; _≈_ to _≈₀_
               ; Carrier to Gad
               ; refl to refl₀
               )

    open Category Base
      hiding (_≈₀_ ; isCategory ; isEquivalence₀ ; refl₀ ; Hom ; Id)
      -- using (isEquivalence₁ ; HomSetoid ; o-cong ; assoc)
      renaming ( _≈₁_ to _∼₁_
               )

  
    Morph″ : Gad → (Gadget ⟶ Set′ _)
    Morph″ A = record { _⟨$⟩_ = λ B → Morph A B
                      ; cong = Morph-cong {A} {A} refl₀
                      }
  
    Morph′ : Gadget ⟶ Gadget ⇨ Set′ _
    Morph′ = record { _⟨$⟩_ = λ A → Morph″ A
                   ; cong = λ i≈i′ j≈j′ → Morph-cong i≈i′ j≈j′
                   }

    _≈₁_ : I.Rel Morph′ _
    f ≈₁ g = U₁ f ∼₁ U₁ g

    Lift-cong : ∀{a b} {f f′ : Hom Base (U₀ a) (U₀ b)}
              → { pf : Liftable a b f  }
              → { pf′ : Liftable a b f′ }
              → f ∼₁ f′
              → Lift f {pf} ≈₁ Lift f′ {pf′}
    Lift-cong {a} {b} {f} {f′} f∼f′ =
      begin
        U₁ (Lift f)
      ≈⟨ U₁-Lift-inverse ⟩
        f
      ≈⟨ f∼f′ ⟩
        f′
      ≈⟨ sym U₁-Lift-inverse ⟩
        U₁ (Lift f′)
      ∎
      where
        open EqR (HomSetoid I.[ U₀ a , U₀ b ])
        open I.IsEquivalence isEquivalence₁

    isEquiv₁ : I.IsEquivalence Morph′ _≈₁_
    isEquiv₁ = record { refl = refl ; sym = sym ; trans = trans }
      where
        open I.IsEquivalence isEquivalence₁


    assoc′ : ∀{A B C D}
            → (f : Morph C D)
            → (g : Morph B C)
            → (h : Morph A B)
            → ((f o′ g) o′ h) ≈₁ (f o′ (g o′ h))
    assoc′ {A} {B} {C} {D} f g h =
      begin
        (f o′ g) o′ h
      ≡⟨⟩
        Lift (U₁ f o U₁ g) o′ h
      ≡⟨⟩
        Lift (U₁ (Lift (U₁ f o U₁ g)) o U₁ h )
      ≈⟨ Lift-cong
           {pf′ = o-liftable (o-liftable U₁-liftable U₁-liftable) U₁-liftable}
           (U₁-Lift-inverse ⟨ o-cong ⟩ refl) ⟩
        Lift ((U₁ f o U₁ g) o U₁ h)
      ≈⟨ Lift-cong {pf′ = o-liftable U₁-liftable (o-liftable U₁-liftable U₁-liftable) } (assoc _ _ _) ⟩
        Lift (U₁ f o (U₁ g o U₁ h))
      ≈⟨ Lift-cong (o-cong refl (sym U₁-Lift-inverse)) ⟩
        Lift (U₁ f o U₁ (Lift (U₁ g o U₁ h)))
      ≡⟨⟩
        f o′ (g o′ h)
      ∎
      where
        open EqR (record {isEquivalence = isEquiv₁}  I.[ A , D ] )
        open I.IsEquivalence isEquivalence₁

    idˡ : ∀{A B} → (f : Morph A B) → (ID o′ f) ≈₁ f
    idˡ {A} {B} f =
      begin
        U₁ (ID o′ f)
      ≡⟨⟩
        U₁ (Lift (U₁ (Lift (Id Base)) o U₁ f))
      ≈⟨ U₁-Lift-inverse ⟩
        U₁ (Lift (Id Base)) o U₁ f
      ≈⟨ o-cong U₁-Lift-inverse refl ⟩
        Id Base o U₁ f
      ≈⟨ identityˡ _ ⟩
        U₁ f
      ∎
      where
        open EqR (record {isEquivalence = isEquivalence₁}  I.[ U₀ A , U₀ B ] )
        open I.IsEquivalence isEquivalence₁

    idʳ : ∀{A B} → (f : Morph A B) → (f o′ ID) ≈₁ f
    idʳ {A} {B} f =
      begin
        U₁ (f o′ ID)
      ≡⟨⟩
        U₁ (Lift (U₁ f o U₁ (Lift (Id Base))))
      ≈⟨ U₁-Lift-inverse ⟩
        U₁ f o U₁ (Lift (Id Base))
      ≈⟨ o-cong refl U₁-Lift-inverse ⟩
        U₁ f o Id Base
      ≈⟨ identityʳ _ ⟩
        U₁ f
      ∎
      where
        open EqR (record {isEquivalence = isEquivalence₁}  I.[ U₀ A , U₀ B ] )
        open I.IsEquivalence isEquivalence₁

    o-cong′ : ∀{A B C} {f f′ : Morph B C} {g g′ : Morph A B}
           → f ≈₁ f′ → g ≈₁ g′ → (f o′ g) ≈₁ (f′ o′ g′)
    o-cong′ {A} {B} {C} {f} {f′} {g} {g′} f≈f′ g≈g′ =
      begin
        U₁ (f o′ g)
      ≈⟨ U₁-o-distrib _ _ ⟩
        U₁ f o U₁ g
      ≈⟨ o-cong f≈f′ g≈g′ ⟩
        U₁ f′ o U₁ g′
      ≈⟨ sym (U₁-o-distrib _ _) ⟩
        U₁ (f′ o′ g′)
      ∎
      where
        open EqR (record {isEquivalence = isEquivalence₁}  I.[ U₀ A , U₀ C ] )
        open I.IsEquivalence isEquivalence₁

    isCategory : IsCategory (Setoid.Carrier Gadget) Morph _≈₀_ _ _o′_ ID
    isCategory = record { Hom-cong = Morph-cong
                        ; isEquivalence₀ = isEquivalence₀
                        ; isEquivalence₁ = isEquiv₁
                        ; o-cong = o-cong′
                        ; identityˡ = idˡ
                        ; identityʳ = idʳ
                        ; assoc = assoc′
                        }

Forgetful : ∀{c₀ c₁ ℓ₀ ℓ₁ c₀′ c₁′ ℓ r} { C : Category c₀ c₁ ℓ₀ ℓ₁ }
          → (D : SubCategory C c₀′ c₁′ ℓ r)
          → Functor (subCategory D) C
Forgetful {C = C} sub = record { isFunctor = isFunctor }
  where
    open SubCategory sub
    D = subCategory sub
    isFunctor : IsFunctor D C U₀ U₁
    isFunctor = record { o-homo   = U₁-o-distrib
                       ; ⟦_⟧₁-cong = λ x → x
                       ; Id-cong  = U₁-Lift-inverse
                       }

extend_by_ : ∀{c₀ c₁ ℓ₀ ℓ₁ c₀′ c₁′ ℓ r}
            → (Base : Category c₀ c₁ ℓ₀ ℓ₁)
            → SubCategory Base c₀′ c₁′ ℓ r
            → Σ[ C ∈ Category c₀′ c₁′ ℓ ℓ₁ ] Functor C Base
extend Base by def = (subCategory def , Forgetful def)
