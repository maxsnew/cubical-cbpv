{-# OPTIONS --cubical --experimental-lossy-unification #-}

module CBPV  where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Adjoint
open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Instances.EilenbergMoore
open import Cubical.Categories.Functor
open import Cubical.Categories.Functors.HomFunctor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Monad.Base
open import Cubical.Categories.NaturalTransformation
open import Cubical.Data.Unit

private
  variable
    ℓ ℓ' : Level

open import Profunctor
open import Products

-- The following is a definition of a model of CBPV internal to a
-- ∞?-topos.

-- By a sheaf construction every model of CBPV embeds into one of this form.
-- We can use the notion of model itself as a kind of HOAS for CBPV.

-- The construction is parameterized by a monad T on SET that
-- specifies the "built-in" notion of effects. For certain proofs (LR)
-- we probably want to require that this is the monad for some
-- algebraic theory. (Classically, a finitary monad).
record CBPV ℓ ℓ' (T : Monad (SET ℓ')) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  -- First, for the judgmental structure of values we just need a
  -- universe of sets that we call value types
  field
    VTy : Type ℓ
    el : VTy -> hSet ℓ'

  -- This presents a full subcategory of the category of SET (I copied the definition)
  𝕍 : Category ℓ ℓ'
  𝕍 = record
        { ob = VTy
        ; Hom[_,_] = λ A A' → fst (el A) → fst (el A')
        ; id = λ z → z
        ; _⋆_ = λ f g z → g (f z)
        ; ⋆IdL = λ f → refl
        ; ⋆IdR = λ f → refl
        ; ⋆Assoc = λ f g h → refl
        ; isSetHom = λ {A} {A'} → isSetΠ ((λ _ → snd (el A')))
        }

  i : Functor 𝕍 (SET ℓ')
  i = record { F-ob = el ; F-hom = λ z → z ; F-id = refl ; F-seq = λ f g → refl  }

  Val : VTy -> Type ℓ'
  Val A = fst (el A)

  -- We can then extremely tersely define the structure needed for
  -- computation types by specifying that we have a category of
  -- computations equipped with a functor to the category of algebras of the monad
  ALG : Category (ℓ-suc ℓ') ℓ'
  ALG = EMCategory T
  field
    ℂ : Category ℓ ℓ'
    𝕋 : Functor ℂ ALG

  module ℂ = Category(ℂ)

  -- We model the type structure by the presence of certain UMPs.

  field
    -- Note that unlike *all* other types, we do *not* require that this UMP is preserved
    -- by a functor.
    --
    -- The requirement would be to have 𝕋 (F A) = FreeEMAlgebra T (i A)
    -- but this would force ℂ to be a subcategory of ALG just like 𝕍 is
    -- a subcategory of SET. Then a model would amount to essentially
    -- choosing universes 𝕍 and ℂ of sets and algebras.
    --
    -- By not requiring this, we allow for more models (such as kont
    -- models)

    -- ℂ (F A) B ≡ SET (i A) (Forget (𝕋 B))
    F-UMP : LeftRepresentable (HomFunctor (SET ℓ') prof[ i , ForgetEMAlgebra T ∘F 𝕋 ])

    -- for uniformity's sake we define the U in the following slightly overcomplicated definition.
    -- In fact the entire thing is equivalent to having a type U with Val (U B) ≡ Comp B

    -- 𝕍(A, U B) ≡ SET(i A, Forget (𝕋 B))
    -- SET(X, U' B) ≡ SET(X, Forget (𝕋 B))
    -- and 𝕋 (U B) = U' B
    i-preserves-U : RightRepresentablePreservingFunctor
                    {D = ℂ} {B = 𝕍} {C = (SET ℓ')}
                    (HomFunctor (SET ℓ') prof[ i , ForgetEMAlgebra T ∘F 𝕋 ])
                    ((HomFunctor (SET ℓ') prof[ Id {C = SET ℓ'} , ForgetEMAlgebra T ∘F 𝕋 ]))
                    i

    --   ℂ B' (A ⟶ℂ B) ≡ SET (i A) (ℂ B' B)
    --   SET X (A ⟶SET B) ≡ SET (i A) (SET X (Comp B))
    --   𝕋 (A ⟶ℂ B) ≡ (A ⟶SET B)
    𝕋-preserves-𝕍-ℂ-powers : RightRepresentablePreservingFunctor
                             (((HomFunctor (SET ℓ') prof[ i , HomFunctor ℂ ]) ∘F (Fst (𝕍 ^op) _ ∘F Snd _ _ ,F (Fst (ℂ ^op) _  ,F Snd _ ℂ ∘F Snd _ _))))
                             ((((HomFunctor (SET ℓ') prof[ i , HomFunctor (SET ℓ') prof[ Id {C = SET ℓ'} , ForgetEMAlgebra T ∘F 𝕋 ] ])) ∘F (Fst (𝕍 ^op) _ ∘F Snd _ _ ,F (Fst ((SET ℓ') ^op) _  ,F Snd _ ℂ ∘F Snd _ _))))
                             (ForgetEMAlgebra T ∘F 𝕋)

    -- 𝕍 (A₁ ⊗ A₂) A ≡ SET (i A₁) (𝕍 A₂ A)
    -- SET (A₁ ⊗' A₂) X ≡ SET (i A₁) (SET (i A₂) X)
    -- i (A₁ ⊗ A₂) ≡ (A₁ ⊗' A₂)
    i-preserves-𝕍-tensors : LeftRepresentablePreservingFunctor
                            {C = 𝕍 × 𝕍} {D = 𝕍} {E = (SET ℓ')}
                            ((HomFunctor (SET ℓ') prof[ i , HomFunctor 𝕍 ]) ∘F ((Fst _ (𝕍 ^op) ∘F Fst _ _ ,F (Snd _ _ ∘F Fst _ _ ,F Snd _ _))))
                            ((HomFunctor (SET ℓ') prof[ i , HomFunctor (SET ℓ') prof[ i , Id {C = SET ℓ'} ] ]) ∘F (Fst _ (𝕍 ^op) ∘F Fst _ _ ,F (Snd _ _ ∘F Fst _ _ ,F Snd _ _)))
                            i
    -- 𝕍 𝟙 A ≡ i A
    -- SET 𝟙' X ≡ X
    -- i 𝟙 ≡ 𝟙'
    i-preserves-𝟙 : LeftRepresentablePreservingFunctor
                      {C = 𝟙C} {D = 𝕍} {E = (SET ℓ')}
                      (i ∘F Snd 𝟙C 𝕍)
                      (Snd 𝟙C (SET ℓ'))
                      i

  -- Finally, for the additives, we need the cartesian product structure in SET
  SET-× : Functor ((SET ℓ') × (SET ℓ')) (SET ℓ')
  SET-× = BinProductF (SET-BinProducts ℓ')

  SET-Unit : hSet ℓ'
  SET-Unit = Unit* , (λ x y x₁ y₁ → refl)

    -- 𝕍 (A₁ + A₂) A ≡ (𝕍 A₁ A) × (𝕍 A₂ A)
    -- SET (A₁ +' A₂) X ≡ (SET (i A₁) X) × (SET (i A₂) X)
    -- i (A₁ + A₂) ≡ (A₁ +' A₂)
  field
    i-preserves-𝕍-coproducts : LeftRepresentablePreservingFunctor
                               {C = 𝕍 × 𝕍} {D = 𝕍} {E = SET ℓ'}
                               (SET-× ∘F ((HomFunctor 𝕍 prof[ Fst 𝕍 𝕍 , Id {C = 𝕍} ]) ,F (HomFunctor 𝕍 prof[ Snd 𝕍 𝕍 , Id {C = 𝕍} ])))
                               (SET-× ∘F ((HomFunctor (SET ℓ') prof[ i ∘F Fst 𝕍 𝕍 , Id {C = SET ℓ'} ]) ,F ((HomFunctor (SET ℓ') prof[ i ∘F Snd 𝕍 𝕍 , Id {C = SET ℓ'} ]))))
                               i

    -- 𝕍 0 A ≡ 1
    -- SET 0' X ≡ 1
    -- i 0 ≡ 0'
    i-preserves-0 : LeftRepresentablePreservingFunctor
                    {C = 𝟙C} {D = 𝕍} {E = SET ℓ'}
                    (Constant _ _ SET-Unit)
                    (Constant _ _ SET-Unit)
                    i

  -- TODO: This should probably be that the functor to ALG has
  -- products to ensure that the effect operations are correct?

    -- ℂ   B (B₁ & B₂) ≡ (ℂ B B₁) × (ℂ B B₂)
    -- ALG Φ (B₁ &' B₂) ≡ ALG Φ (𝕋 B₁) × ALG Φ (𝕋 B₂)
    -- 𝕋 (B₁ & B₂) ≡ (B₁ &' B₂)
    𝕋-preserves-& : RightRepresentablePreservingFunctor
                    {D = ℂ × ℂ} {B = ℂ} {C = ALG}
                    (SET-× ∘F ((HomFunctor ℂ prof[ Id {C = ℂ} , Fst ℂ ℂ ]) ,F ((HomFunctor ℂ prof[ Id {C = ℂ} , Snd ℂ ℂ ]))))
                    (SET-× ∘F ((HomFunctor ALG prof[ Id {C = ALG} , 𝕋 ∘F Fst ℂ ℂ ]) ,F ((HomFunctor ALG prof[ Id {C = ALG} , 𝕋 ∘F Snd ℂ ℂ ]))))
                    𝕋
    -- ℂ   B ⊤  ≡ 1
    -- ALG Φ ⊤' ≡ 1
    -- 𝕋 ⊤ ≡ ⊤'
    𝕋-preserves-⊤ : RightRepresentablePreservingFunctor
                    {D = 𝟙C} {B = ℂ} {C = ALG}
                    (Constant _ _ SET-Unit)
                    (Constant _ _ SET-Unit)
                    𝕋

  -- TODO: possibly add EEC structures (⊸, ⊘, W)
  -- TODO: dependent types! Π Σ, 𝕍al ℂomp


module Syntax {ℓ ℓ'} (T : Monad (SET ℓ')) (M : CBPV ℓ ℓ' T) where
  module M = CBPV M
  open M
  open RightRepresentablePreservingFunctor
  open LeftRepresentablePreservingFunctor

  -- The objects of the computation category are the computation types.
  CTy = ℂ.ob

  -- The morphisms are the *stacks* aka *linear* morphisms
  Stk : CTy → CTy → Type ℓ'
  Stk B B' = ℂ.Hom[ B , B' ]

  -- Composing the  action of the functor on objects gives us the set of terms.
  ℂomp : CTy → hSet ℓ'
  ℂomp B = ((ForgetEMAlgebra T) ∘F 𝕋) ⟅ B ⟆
  Comp : CTy → Type ℓ'
  Comp B = fst (Functor.F-ob ((ForgetEMAlgebra T) ∘F 𝕋) B)

  -- The action of the functor on morphisms gives us the "pile" of a
  -- stack onto a term (with its assoc/unit)
  _[_] : ∀ {B B'} → Stk B B' → Comp B → Comp B'
  S [ M ] = Functor.F-hom (funcComp (ForgetEMAlgebra T) 𝕋) S M
  private
    module i-preserves-U = RightRepresentablePreservingFunctor i-preserves-U
    U-Functor : Functor ℂ 𝕍
    U-Functor = RightRepresentable.G i-preserves-U.ReprB

    U'-Functor : Functor ℂ (SET ℓ')
    U'-Functor = RightRepresentable.G i-preserves-U.ReprC

  U : CTy → VTy
  U = Functor.F-ob U-Functor

  -- and the thunk/force are the components of the natural isomorphism
  force : ∀ {B} → Val (U B) → Comp B
  force {B} = Repr𝕍.ϵ B
    where module Repr𝕍 = RightRepresentable (i-preserves-U.ReprB)

  thunk : ∀ {B} → Comp B → Val (U B)
  thunk {B} M = doop (foo' M)
    where
      U' : CTy → hSet ℓ'
      U' = Functor.F-ob (RightRepresentable.G i-preserves-U.ReprC)
      thunk' : ∀ {X : hSet ℓ'}{B} → (fst X → Comp B) → (fst X → fst (U' B))
      thunk' {X}{B} = RightRepresentable.Intro i-preserves-U.ReprC {c = X}

      foo' : (Comp B → fst (U' B))
      foo' = thunk' {X = ℂomp B} λ x → x

      doop : fst (U' B) → Val (U B)
      doop = NatTrans.N-ob (NatIso.trans (preserves i-preserves-U)) B

  F : VTy → CTy
  F = Functor.F-ob (LeftRepresentable.F F-UMP)

  ret : ∀ {A} → Val A → Comp (F A)
  ret {A} = LeftRepresentable.η F-UMP A

  bind : ∀ {A B} → (Val A → Comp B) → Stk (F A) B
  bind = LeftRepresentable.Elim F-UMP

  infixr 20 _⟶_
  _⟶_ : VTy → CTy → CTy
  A ⟶ B = Functor.F-ob (RightRepresentable.G (ReprB 𝕋-preserves-𝕍-ℂ-powers)) (A , B)

  _⟶SET_ : VTy → CTy → Type ℓ'
  A ⟶SET B = fst (Functor.F-ob (RightRepresentable.G (ReprC 𝕋-preserves-𝕍-ℂ-powers)) (A , B))

  app' : ∀ {A B} → Val A → (A ⟶SET B) → Comp B
  app' {A}{B} = RightRepresentable.ϵ (ReprC 𝕋-preserves-𝕍-ℂ-powers) (A , B)

  foo : ∀ {A B} → (A ⟶SET B) → Comp (A ⟶ B)
  foo {A}{B} = NatTrans.N-ob (NatIso.trans (preserves 𝕋-preserves-𝕍-ℂ-powers)) (A , B)

  app : ∀ {A B} → Comp (A ⟶ B) → Val A → Comp B
  app f x = app' x (isIso.inv (NatIso.nIso (preserves 𝕋-preserves-𝕍-ℂ-powers) _) f)

  lam : ∀ {A B} → (Val A → Comp B) → Comp (A ⟶ B)
  lam {A}{B} M[x] = foo (RightRepresentable.Intro (ReprC 𝕋-preserves-𝕍-ℂ-powers) {c = ((Val A → Comp B) , isSet→ (snd ((Functor.F-ob ((ForgetEMAlgebra T) ∘F 𝕋) B))))}{d = A , B}  (λ x f → f x) M[x])

  internalApp : ∀ {A B} → Comp (U (A ⟶ B) ⟶ A ⟶ B)
  internalApp = lam (λ f → lam (λ x → app (force f) x))

  -- We should be able to then derive the adjunction between F and U
  -- F -| U
  -- ℂ (F A) B ≡ SET(i A, Forget (𝕋 B))
  --           ≡ 𝕍(A, U B)
  -- adjoint : NaturalBijection._⊣_ F-Functor U-Functor
  -- adjoint = {!!}

  -- TODO: ⟶ "syntax"
  -- _⟶_ : VTy → CTy → CTy
  -- A ⟶ B = Functor.F-ob ⟶-Functor (A , B)
  --   -- ℂ has 𝕍-powers
  -- field
  --   -- this needs to be a natural isomorphism though...
  --   ⟶-Powers : ∀ {A B B'} → Iso (Stk B' (A ⟶ B)) (Val A → Stk B' B)
  -- app : ∀ {A B} → Val A → Stk (A ⟶ B) B
  -- app = Iso.fun ⟶-Powers (Category.id ℂ)

  -- lam : ∀ {A B} → (Val A → Comp B) → Comp (A ⟶ B)
  -- lam = Iso.inv ⟶-𝕋-Powers
