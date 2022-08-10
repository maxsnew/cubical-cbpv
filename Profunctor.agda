{-# OPTIONS --safe #-}
module Profunctor where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Functor
open import Cubical.Categories.Functors.HomFunctor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Foundations.Isomorphism
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Functors
open import Cubical.Data.Unit

private
  variable
    ℓP ℓB ℓB' ℓC ℓC' ℓD ℓD' ℓD₁ ℓD₁' ℓD₂ ℓD₂' ℓE ℓE' ℓF ℓG : Level

-- A "slick" profunctor
Prof : (C : Category ℓC ℓC') (D : Category ℓD ℓD') → (ℓP : Level) → Category (ℓ-max (ℓ-suc ℓP) (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD'))) (ℓ-max ℓP (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')))
Prof C D ℓP = FUNCTOR ((C ^op) × D) (SET ℓP)

Profunctor : (C : Category ℓC ℓC') (D : Category ℓD ℓD') → (ℓP : Level) → Type (ℓ-max (ℓ-suc ℓP) (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')))
Profunctor C D ℓP = Category.ob (Prof C D ℓP)

open Functor

open import Cubical.Data.Sigma hiding (_×_)
_×Func_ : {B : Category ℓB ℓB'}{C : Category ℓC ℓC'}{D : Category ℓD ℓD'}{E : Category ℓE ℓE'}
          (F : Functor B C) (G : Functor D E) → Functor (B × D) (C × E)
(F ×Func G) .F-ob (b , d) = (F-ob F b) , (F-ob G d)
(F ×Func G) .F-hom (f , g) = (F-hom F f) , (F-hom G g)
(F ×Func G) .F-id = ≡-× (F-id F) (F-id G)
(F ×Func G) .F-seq (f , g) (f' , g') = ≡-× (F-seq F f f') (F-seq G g g')

_^opFunc : {C : Category ℓC ℓC'}{D : Category ℓD ℓD'} (F : Functor C D) → Functor (C ^op) (D ^op)
(F ^opFunc) .F-ob c = F-ob F c
(F ^opFunc) .F-hom f = F-hom F f
(F ^opFunc) .F-id = F-id F
(F ^opFunc) .F-seq f g = F-seq F g f

_prof[_,_] : ∀ {B : Category ℓB ℓB'}{C : Category ℓC ℓC'}{D : Category ℓD ℓD'}{E : Category ℓE ℓE'}
           → (P : Profunctor D E ℓP) → (F : Functor B D) (G : Functor C E) → Profunctor B C ℓP
P prof[ F , G ] = P ∘F ((F ^opFunc) ×Func G)


LiftSet : ∀ ℓ ℓ' (A : Type ℓ) → isSet A → isSet (Lift {ℓ}{ℓ'} A)
LiftSet ℓ ℓ' A A-isSet x y p-x≡y q-x≡y i j = lift (A-isSet (x .lower) (y .lower) (λ i₁ → (p-x≡y i₁) .lower) (λ i₁ → q-x≡y i₁ .lower) i j)
  where open Lift

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
LiftF : ∀ ℓ ℓ' → Functor (SET ℓ) (SET (ℓ-max ℓ ℓ'))
LiftF ℓ ℓ' .F-ob X = (Lift (fst X)) , LiftSet ℓ ℓ' (fst X) (snd X)
LiftF ℓ ℓ' .F-hom f x =  lift (f (Lift.lower x))
LiftF ℓ ℓ' .F-id = refl
LiftF ℓ ℓ' .F-seq f g = refl

LeftRepresents : {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} (F : Functor C D) (P : Profunctor C D ℓP)
               → Type ((ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓD) (ℓ-suc ℓD')) (ℓ-suc ℓP)))
LeftRepresents {ℓD' = ℓD'}{ℓP = ℓP}{D = D} F P =
  NatIso (LiftF ℓD' ℓP ∘F (HomFunctor D prof[ F , Id {C = D} ]))
         (LiftF ℓP ℓD' ∘F P)

record LeftRepresentable {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} (P : Profunctor C D ℓP) : Type (((ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓD) (ℓ-suc ℓD')) (ℓ-suc ℓP)))) where
  field
    F : Functor C D
    repr : LeftRepresents F P

record LeftRepresentablePreservingFunctor {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} {E : Category ℓE ℓE'}
                                    (Pd : Profunctor C D ℓP) (Pe : Profunctor C E ℓP)
                                    (ReprD : LeftRepresentable {C = C}{D = D} Pd) (ReprE : LeftRepresentable Pe)
                                    : Type (ℓ-max (ℓ-max ℓE ℓE') (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD'))) where
  field
    F : Functor D E
    preserves : NatIso (LeftRepresentable.F ReprE) (F ∘F LeftRepresentable.F ReprD)

RightRepresents : {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} (G : Functor D C) (P : Profunctor C D ℓP)
                → Type ((ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC (ℓ-suc ℓC')) ℓD) ℓD') (ℓ-suc ℓP)))
RightRepresents {ℓC' = ℓC'}{ℓP = ℓP}{C = C} G P =
  NatIso (LiftF ℓC' ℓP ∘F (HomFunctor C prof[ Id {C = C} , G ]))
         (LiftF ℓP ℓC' ∘F P)


record RightRepresentable {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} (P : Profunctor C D ℓP) : Type ((ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC (ℓ-suc ℓC')) ℓD) ℓD') (ℓ-suc ℓP))) where
  field
    G : Functor D C
    repr : RightRepresents G P

record RightRepresentablePreservingFunctor {D : Category ℓD ℓD'} {B : Category ℓB ℓB'}{C : Category ℓC ℓC'}
                                    (Pb : Profunctor B D ℓP) (Pc : Profunctor C D ℓP)
                                    (ReprB : RightRepresentable {C = B}{D = D} Pb) (ReprC : RightRepresentable Pc)
                                    : Type (ℓ-max (ℓ-max ℓB ℓB') (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD'))) where
  field
    G : Functor B C
    preserves : NatIso (RightRepresentable.G ReprC) (G ∘F RightRepresentable.G ReprB)


-- -- A "mundane" profunctor
-- record MundaneProfunctor (C : Category ℓC ℓC') (D : Category ℓD ℓD') : Type (ℓ-max (ℓ-suc ℓP) (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD'))) where
--   module C = Category C
--   module D = Category D
  
--   field
--     Het[_,_] : C.ob → D.ob → Type ℓP
--     _L⋆_ : ∀ {c c' d} → (f : C.Hom[ c' , c ]) (h : Het[ c , d ]) → Het[ c' , d ]
--     _⋆R_ : ∀ {c d d'} → (h : Het[ c , d ]) (g : D.Hom[ d , d' ]) → Het[ c , d' ]
--     L⋆id : ∀ {c d} (h : Het[ c , d ]) → C.id L⋆ h ≡ h
--     ⋆Rid : ∀ {c d} (h : Het[ c , d ]) → h ⋆R D.id ≡ h
--     ⋆Assoc : ∀ {c' c d d'} → (f : C.Hom[ c' , c ]) (h : Het[ c , d ]) (g : D.Hom[ d , d' ])
--            → (f L⋆ h) ⋆R g ≡ f L⋆ (h ⋆R g)
--     isSetHet : ∀ {c d} → isSet Het[ c , d ]
