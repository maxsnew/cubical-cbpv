{-# OPTIONS --safe #-}

module RelativeAdjoint where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Functors.HomFunctor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Foundations.Isomorphism

open Functor
open Iso
open Category

open import Profunctor

private
  variable
    ℓB ℓB' ℓC ℓC' ℓD ℓD' : Level

hasRelLeftAdjoint : {B : Category ℓB ℓB'} {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} (J : Functor B D) (R : Functor C D)
                  → Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓB ℓB') ℓC) (ℓ-suc ℓC')) (ℓ-suc ℓD'))
hasRelLeftAdjoint {B = B}{C = C}{D = D} J R = LeftRepresentable {C = B}{D = C} (HomFunctor D prof[ J , R ])                  

record RelLeftAdjoint {B : Category ℓB ℓB'} {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
                      (J : Functor B D) (L : Functor B C) (R : Functor C D)
                         : Type (ℓ-max (ℓ-max ℓB ℓB') (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD'))) where
  field
    relAdjIso : ∀ {b c} → Iso (C [ L ⟅ b ⟆ , c ]) (D [ J ⟅ b ⟆ , R ⟅ c ⟆ ]) 
  -- this probably needs more to be homotopy coherent?

record RelRightAdjoint {B : Category ℓB ℓB'} {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
                       (J : Functor B D) (L : Functor C D) (R : Functor B C)
                         : Type (ℓ-max (ℓ-max ℓB ℓB') (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD'))) where

  field
    relAdjIso : ∀ {b c} → Iso (D [ L ⟅ c ⟆ , J ⟅ b ⟆ ]) (C [ c , R ⟅ b ⟆ ])
  -- todo: more Cubical
