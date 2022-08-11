module Products where

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Constructions.BinProduct renaming (_×_ to _×C_)

private
  variable
    ℓA ℓA' ℓB ℓB' ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level

open Category
open Functor

-- | These are copied from Andreas Nuyt's pull request
-- | (https://github.com/agda/cubical/pull/872), so should be pulled
-- | into cubical soon

Fst : (C : Category ℓC ℓC') → (D : Category ℓD ℓD') → Functor (C ×C D) C
F-ob (Fst C D) = fst
F-hom (Fst C D) = fst
F-id (Fst C D) = refl
F-seq (Fst C D) _ _ = refl

Snd : (C : Category ℓC ℓC') → (D : Category ℓD ℓD') → Functor (C ×C D) D
F-ob (Snd C D) = snd
F-hom (Snd C D) = snd
F-id (Snd C D) = refl
F-seq (Snd C D) _ _ = refl

module _ where
  private
    variable
      A : Category ℓA ℓA'
      B : Category ℓB ℓB'
      C : Category ℓC ℓC'
      D : Category ℓD ℓD'
      E : Category ℓE ℓE'

  open Functor

  _,F_ : Functor C D → Functor C E → Functor C (D ×C E)
  (G ,F H) .F-ob a = (G ⟅ a ⟆ , H ⟅ a ⟆)
  (G ,F H) .F-hom g = (G ⟪ g ⟫ , H ⟪ g ⟫)
  (G ,F H) .F-id = ≡-× (G .F-id) (H .F-id)
  (G ,F H) .F-seq _ _ = ≡-× (G .F-seq _ _) (H .F-seq _ _)

Constant : (C : Category ℓC ℓC') (D : Category ℓD ℓD') (d : ob D) → Functor C D
F-ob (Constant C D d) c = d
F-hom (Constant C D d) φ = id D
F-id (Constant C D d) = refl
F-seq (Constant C D d) φ χ = sym (⋆IdR D _)

open import Cubical.Data.Unit
𝟙C : Category ℓ-zero ℓ-zero
𝟙C .ob = Unit*
𝟙C .Hom[_,_] x y = Unit*
𝟙C .id = lift tt
𝟙C ._⋆_ (lift tt) (lift tt) = lift tt
𝟙C .⋆IdL (lift tt) = refl
𝟙C .⋆IdR (lift tt) = refl
𝟙C .⋆Assoc (lift tt) (lift tt) (lift tt) = refl
𝟙C .isSetHom (lift tt) (lift tt) _ _ = refl

𝟙F : ∀ (C : Category ℓC ℓC') → Functor C 𝟙C
𝟙F C = Constant C 𝟙C (lift tt)

open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Instances.Sets
open import Cubical.HITs.PropositionalTruncation.Base

SET-BinProducts : ∀ ℓ → BinProducts (SET ℓ)
SET-BinProducts ℓ = P
  where
    open BinProduct
    P : BinProducts (SET ℓ)
    (P X Y) .binProdOb = (fst X × fst Y) , isSet× (snd X) (snd Y)
    (P X Y) .binProdPr₁ = fst
    (P X Y) .binProdPr₂ = snd
    (P X Y) .univProp f₁ f₂ = uniqueExists (λ z → (f₁ z) , (f₂ z)) (refl , refl)
                              (λ a' → isProp× (isSet→ (snd X) _ _)
                                              (isSet→ (snd Y) _ _))
                              λ f f-properties → λ i z → (fst f-properties (~ i) z) , snd f-properties (~ i) z

BinProductIntro : ∀ {C : Category ℓC ℓC'} {a b c} → (ps : BinProducts C) → C [ a , b ] → C [ a , c ] → C [ a , BinProduct.binProdOb (ps b c) ]
BinProductIntro ps f₁ f₂ = fst (fst (BinProduct.univProp (ps _ _) f₁ f₂))


BPπ₁ : ∀ {C : Category ℓC ℓC'} {a b} → (ps : BinProducts C) → C [ BinProduct.binProdOb (ps a b) , a ]
BPπ₁ ps = BinProduct.binProdPr₁ (ps _ _)

BPπ₂ : ∀ {C : Category ℓC ℓC'} {a b} → (ps : BinProducts C) → C [ BinProduct.binProdOb (ps a b) , b ]
BPπ₂ ps = BinProduct.binProdPr₂ (ps _ _)

BinProductβ₁ : ∀ {C : Category ℓC ℓC'} {a b c} → (ps : BinProducts C) → (f : C [ a , b ]) (g : C [ a , c ])
                   → (Category._⋆_ C (BinProductIntro ps f g) (BPπ₁ ps) ≡ f)
BinProductβ₁ {C = C}{b = b}{c = c} ps f g = fst (snd (fst (BP.univProp f g)))
  where module BP = BinProduct (ps b c)
        

BinProductβ₂ : ∀ {C : Category ℓC ℓC'} {a b c} → (ps : BinProducts C) → (f : C [ a , b ]) (g : C [ a , c ])
                   → (Category._⋆_ C (BinProductIntro ps f g) (BPπ₂ ps) ≡ g)
BinProductβ₂ {C = C}{b = b}{c = c} ps f g = snd (snd (fst (BP.univProp f g)))
  where module BP = BinProduct (ps b c)

BinProductIntroEqv : ∀ {C : Category ℓC ℓC'} {a b c} → (ps : BinProducts C) → (f : C [ a , b ]) (g : C [ a , c ]) (h : C [ a , BinProduct.binProdOb (ps b c) ])
                   → (f ≡ (Category._⋆_ C h (BPπ₁ ps)))
                   → (g ≡ (Category._⋆_ C h (BPπ₂ ps)))
                   → (BinProductIntro ps f g ≡ h)
BinProductIntroEqv {C = C}{b = b}{c = c} ps f g h fP gP = λ i → fst (snd (BP.univProp f g) (h , ((sym fP) , (sym gP))) i)                   
  where module BP = BinProduct (ps b c)

-- | TODO: if C is univalent this can be done from hasBinProducts
BinProductF : ∀ {C : Category ℓC ℓC'} → BinProducts C → Functor (C ×C C) C
(BinProductF {C = C} BinProducts-C) .F-ob = λ x → BinProduct.binProdOb (BinProducts-C (fst x) (snd x))
(BinProductF {C = C} BinProducts-C) .F-hom f*g =
    BinProductIntro BinProducts-C (BinProduct.binProdPr₁ (BinProducts-C _ _) ⋆C fst f*g)
                                  (BinProduct.binProdPr₂ (BinProducts-C _ _) ⋆C snd f*g)
  where module C = Category C
        _⋆C_ = C._⋆_

-- id x id = < id o pi1 , id o pi2 >
-- by UMP to prove id = < id o pi1 , id o pi2 >
-- STS pii o id = id o pii (ez)
-- 
(BinProductF {C = C} BinProducts-C) .F-id {x = x} =
    BinProductIntroEqv BinProducts-C (π₁ ⋆C C.id) (π₂ ⋆C C.id) C.id
             (π₁ ⋆C C.id ≡⟨ C.⋆IdR _ ⟩
              π₁         ≡⟨ sym (C.⋆IdL _) ⟩
              C.id ⋆C π₁
              ∎)
             (π₂ ⋆C C.id ≡⟨ C.⋆IdR _ ⟩
              π₂         ≡⟨ sym (C.⋆IdL _) ⟩
              C.id ⋆C π₂
              ∎)
  where module C = Category C
        _⋆C_ = C._⋆_
        module BP = BinProduct (BinProducts-C (fst x) (snd x))
        π₁ = BP.binProdPr₁ 
        π₂ = BP.binProdPr₂

-- (f x g) o (f' x g') = < f o pi1 , g o pi1 > o < f' o pi1 , g' o pi2 >
-- vs (f o f') x (g o g') = < f o f' o pi1 , g o g' o pi2 >
-- by UMP STS
--   pi1 o < f o pi1 , g o pi1 > o < f' o pi1 , g' o pi2 >
--   = f o f' o pi1
-- 
--   pi1 o < f o pi1 , g o pi1 > o < f' o pi1 , g' o pi2 >
--   =(β)= f o pi1 o < f' o pi1 , g' o pi2 >
--   =(β)= f o f' o pi1
(BinProductF {C = C} BinProducts-C) .F-seq {x}{y}{z} f⋆g f'⋆g' =
    BinProductIntroEqv BinProducts-C (π₁ ⋆C (fst f⋆g ⋆C fst f'⋆g')) ((π₂ ⋆C (snd f⋆g ⋆C snd f'⋆g')) )
                       (⟨ π₁ ⋆C fst f⋆g , π₂ ⋆C snd f⋆g ⟩' ⋆C ⟨ π₁' ⋆C fst f'⋆g' , π₂' ⋆C snd f'⋆g' ⟩'')
                       (sym
                       (((⟨ π₁ ⋆C fst f⋆g , π₂ ⋆C snd f⋆g ⟩' ⋆C ⟨ π₁' ⋆C fst f'⋆g' , π₂' ⋆C snd f'⋆g' ⟩'') ⋆C π₁'') ≡⟨ C.⋆Assoc _ _ _ ⟩
                        (⟨ π₁ ⋆C fst f⋆g , π₂ ⋆C snd f⋆g ⟩' ⋆C (⟨ π₁' ⋆C fst f'⋆g' , π₂' ⋆C snd f'⋆g' ⟩'' ⋆C π₁'')) ≡⟨ (λ i → ⟨ π₁ ⋆C fst f⋆g , π₂ ⋆C snd f⋆g ⟩' ⋆C BinProductβ₁ BinProducts-C (π₁' ⋆C fst f'⋆g') (π₂' ⋆C snd f'⋆g') i) ⟩
                        (⟨ π₁ ⋆C fst f⋆g , π₂ ⋆C snd f⋆g ⟩' ⋆C (π₁' ⋆C fst f'⋆g')) ≡⟨ sym (C.⋆Assoc _ _ _)  ⟩
                        ((⟨ π₁ ⋆C fst f⋆g , π₂ ⋆C snd f⋆g ⟩' ⋆C π₁') ⋆C fst f'⋆g') ≡⟨ (λ i → BinProductβ₁ BinProducts-C (π₁ ⋆C fst f⋆g) (π₂ ⋆C snd f⋆g) i ⋆C fst f'⋆g') ⟩
                        ((π₁ ⋆C fst f⋆g) ⋆C fst f'⋆g') ≡⟨ C.⋆Assoc _ _ _ ⟩
                        (π₁ ⋆C (fst f⋆g ⋆C fst f'⋆g'))
                        ∎))
                       (sym
                       (((⟨ π₁ ⋆C fst f⋆g , π₂ ⋆C snd f⋆g ⟩' ⋆C ⟨ π₁' ⋆C fst f'⋆g' , π₂' ⋆C snd f'⋆g' ⟩'') ⋆C π₂'') ≡⟨ C.⋆Assoc _ _ _ ⟩
                        (⟨ π₁ ⋆C fst f⋆g , π₂ ⋆C snd f⋆g ⟩' ⋆C (⟨ π₁' ⋆C fst f'⋆g' , π₂' ⋆C snd f'⋆g' ⟩'' ⋆C π₂'')) ≡⟨ (λ i → ⟨ π₁ ⋆C fst f⋆g , π₂ ⋆C snd f⋆g ⟩' ⋆C BinProductβ₂ BinProducts-C (π₁' ⋆C fst f'⋆g') (π₂' ⋆C snd f'⋆g') i) ⟩
                        (⟨ π₁ ⋆C fst f⋆g , π₂ ⋆C snd f⋆g ⟩' ⋆C (π₂' ⋆C snd f'⋆g')) ≡⟨ sym (C.⋆Assoc _ _ _)  ⟩
                        ((⟨ π₁ ⋆C fst f⋆g , π₂ ⋆C snd f⋆g ⟩' ⋆C π₂') ⋆C snd f'⋆g') ≡⟨ (λ i → BinProductβ₂ BinProducts-C (π₁ ⋆C fst f⋆g) (π₂ ⋆C snd f⋆g) i ⋆C snd f'⋆g') ⟩
                        ((π₂ ⋆C snd f⋆g) ⋆C snd f'⋆g') ≡⟨ C.⋆Assoc _ _ _ ⟩
                        (π₂ ⋆C (snd f⋆g ⋆C snd f'⋆g'))
                        ∎))
  where module C = Category C
        _⋆C_ = C._⋆_
        module BP = BinProduct (BinProducts-C (fst x) (snd x))
        π₁ = BP.binProdPr₁ 
        π₂ = BP.binProdPr₂

        module BP' = BinProduct (BinProducts-C (fst y) (snd y))
        π₁' = BP'.binProdPr₁ 
        π₂' = BP'.binProdPr₂
        ⟨_,_⟩' : ∀ {Γ} → C [ Γ , fst y ] → C [ Γ , snd y ] → C [ Γ , BP'.binProdOb ]
        ⟨_,_⟩' f₁ f₂ = fst (fst (BP'.univProp f₁ f₂))

        module BP'' = BinProduct (BinProducts-C (fst z) (snd z))
        π₁'' = BP''.binProdPr₁ 
        π₂'' = BP''.binProdPr₂
        ⟨_,_⟩'' : ∀ {Γ} → C [ Γ , fst z ] → C [ Γ , snd z ] → C [ Γ , BP''.binProdOb ]
        ⟨_,_⟩'' f₁ f₂ = fst (fst (BP''.univProp f₁ f₂))
