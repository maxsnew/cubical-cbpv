module Products where

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Constructions.BinProduct

private
  variable
    ℓA ℓA' ℓB ℓB' ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level

open Category
open Functor

-- | These are copied from Andreas Nuyt's pull request
-- | (https://github.com/agda/cubical/pull/872), so should be pulled
-- | into cubical soon

Fst : (C : Category ℓC ℓC') → (D : Category ℓD ℓD') → Functor (C × D) C
F-ob (Fst C D) = fst
F-hom (Fst C D) = fst
F-id (Fst C D) = refl
F-seq (Fst C D) _ _ = refl

Snd : (C : Category ℓC ℓC') → (D : Category ℓD ℓD') → Functor (C × D) D
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

  _,F_ : Functor C D → Functor C E → Functor C (D × E)
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
