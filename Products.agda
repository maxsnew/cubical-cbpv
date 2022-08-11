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

-- | TODO: if C is univalent this can be done from hasBinProducts
BinProductF : ∀ {C : Category ℓC ℓC'} → BinProducts C → Functor (C ×C C) C
(BinProductF {C = C} BinProducts-C) .F-ob = λ x → BinProduct.binProdOb (BinProducts-C (fst x) (snd x))
(BinProductF {C = C} BinProducts-C) .F-hom f*g =
    BinProductIntro BinProducts-C (BinProduct.binProdPr₁ (BinProducts-C _ _) ⋆C fst f*g)
                                  (BinProduct.binProdPr₂ (BinProducts-C _ _) ⋆C snd f*g)
  where module C = Category C
        _⋆C_ = C._⋆_
(BinProductF BinProducts-C) .F-id = {!!}
(BinProductF BinProducts-C) .F-seq = {!!}

