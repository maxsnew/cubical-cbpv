{-# OPTIONS --cubical #-}
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

private
  variable
    ℓP ℓB ℓB' ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level


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
(F ×Func G) .F-seq (f , g) (f' , g') = ≡-× (F-seq F f f') (F-seq G g g') -- todo: munge some equalities

_^opFunc : {C : Category ℓC ℓC'}{D : Category ℓD ℓD'} (F : Functor C D) → Functor (C ^op) (D ^op)
(F ^opFunc) .F-ob c = F-ob F c
(F ^opFunc) .F-hom f = F-hom F f
(F ^opFunc) .F-id = F-id F
(F ^opFunc) .F-seq f g = F-seq F g f

-- BigHomFunctor : (C : Category ℓC ℓC') → (ℓP : Level) → Functor ((C ^op) × C) (SET (ℓ-max ℓP (ℓ-suc ℓC')))
-- BigHomFunctor C ℓP = record { F-ob = λ (c , c') → C.Hom[ c , c' ] , {!C.isSetHom!} ; F-hom = {!!} ; F-id = {!!} ; F-seq = {!!} }
--   where module C = Category C


_prof[_,_] : ∀ {B : Category ℓB ℓB'}{C : Category ℓC ℓC'}{D : Category ℓB ℓB'}{E : Category ℓC ℓC'}
           → (P : Profunctor D E ℓP) → (F : Functor B D) (G : Functor C E) → Profunctor B C ℓP
P prof[ F , G ] = funcComp P ((F ^opFunc) ×Func G)

LeftRepresents : {C : Category ℓC ℓC'} {D : Category ℓC ℓC'} (F : Functor C D) (P : Profunctor C D ℓC') → Type ((ℓ-max ℓC (ℓ-suc ℓC')))
LeftRepresents {C = C}{D = D} F P = NatIso (HomFunctor D prof[ F , Id ]) P

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
