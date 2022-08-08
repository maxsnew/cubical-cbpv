{-# OPTIONS --safe --cubical #-}

module RelativeAdjoint where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Foundations.Isomorphism

open Functor
open Iso
open Category

private
  variable
    ℓB ℓB' ℓC ℓC' ℓD ℓD' : Level


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
