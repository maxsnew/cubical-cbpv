{-# OPTIONS --safe #-}
module Presheaf.Representable where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Presheaf.Base
open import Cubical.Data.Sigma.Base

private
  variable
    ℓ ℓ' ℓS : Level

Presheaf : Category ℓ ℓ' → (ℓS : Level) → Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓS))
Presheaf C ℓS = Category.ob (PreShv C ℓS)

open import Cubical.Categories.Functor

record RepresentingObject {C : Category ℓ ℓ'}  (P : Presheaf C ℓS) (A : Category.ob C) : Type (ℓ-max ℓS (ℓ-max ℓ ℓ')) where
  module C = Category C
  _∘C_ = C._∘_
  field
    universal : fst (P ⟅ A ⟆)
    Intro : ∀ {Γ} → fst (P ⟅ Γ ⟆) → C.Hom[ Γ , A ] -- P → Yo₀ A

  _∘P_ : ∀ {Γ A} → fst (P ⟅ A ⟆) → C.Hom[ Γ , A ] → fst (P ⟅ Γ ⟆)
  ϕ ∘P f = Functor.F-hom P f ϕ

  field
    β : ∀ {Γ} → (ϕ : fst (P ⟅ Γ ⟆)) → universal ∘P (Intro ϕ) ≡ ϕ
    weak-η : Intro universal ≡ C.id
    Intro-nat : ∀ {Γ} ϕ → (f : C.Hom[ Γ , A ]) → Intro (ϕ ∘P f) ≡ Intro ϕ ∘C f

  strong-η : ∀ {Γ}(f : C.Hom[ Γ , A ]) → Intro (universal ∘P f) ≡ f
  strong-η f = Intro (universal ∘P f) ≡⟨ Intro-nat universal f ⟩
                 (Intro universal ∘C f) ≡⟨ (λ i → weak-η i ∘C f) ⟩
                 (C.id ∘C f) ≡⟨ C.⋆IdR f ⟩
                 f ∎

Representable : {C : Category ℓ ℓ'} → (P : Presheaf C ℓS) → Type (ℓ-max (ℓ-max ℓ ℓ') ℓS)
Representable {C = C} P = ∃ (Category.ob C) (RepresentingObject {C = C} P)

open Functor
Yo₀ : ∀ {C : Category ℓ ℓ'} → (Category.ob C) → Presheaf C ℓ'
(Yo₀ {C = C} A) .F-ob Γ = C [ Γ , A ] , Category.isSetHom C
(Yo₀ {C = C} A) .F-hom f ϕ = (C Category.⋆ f) ϕ
(Yo₀ {C = C} A) .F-id  = λ i f → Category.⋆IdL C f i
(Yo₀ {C = C} A) .F-seq = λ f g i h → Category.⋆Assoc C g f h i

