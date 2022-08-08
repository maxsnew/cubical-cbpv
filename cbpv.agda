{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude

open import Cubical.Foundations.HLevels
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets

private
  variable
    ℓ ℓ' : Level

-- The following is a definition of a model of CBPV internal to a
-- ∞?-topos.

-- By a sheaf construction every model of CBPV embeds into one of this form.
-- We can use the notion of model itself as a kind of HOAS for CBPV.
record CBPV ℓ ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  -- First, for the judgmental structure of values we just need a
  -- universe of sets that we call value types
  field
    VTy : Type ℓ
    el : VTy -> hSet ℓ

  -- This presents a subcategory of the category of hSets (I copied the definition)
  𝕍 : Category ℓ ℓ
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

  i : Functor 𝕍 (SET ℓ)
  i = record { F-ob = el ; F-hom = λ z → z ; F-id = refl ; F-seq = λ f g → refl  }

  Val : VTy -> Type ℓ
  Val A = fst (el A)
  -- We can then extremely tersely define the structure needed for
  -- computation types by specifying that we have a *concrete*
  -- category of computations.
  field
    ℂ : Category ℓ ℓ'
    𝕋 : Functor ℂ (SET ℓ)
    
  module ℂ = Category(ℂ)
  -- The objects of the computation category are the computation types.
  CTy = ℂ.ob
  -- The morphisms are the *stacks* aka *linear* morphisms
  Stk : CTy → CTy → Type ℓ'
  Stk B B' = ℂ.Hom[ B , B' ]

  -- The action of the functor on objects gives us the set of terms.
  Comp : CTy → Type ℓ
  Comp B = fst (Functor.F-ob 𝕋 B)

  -- The action of the functor on morphisms gives us the "pile" of a
  -- stack onto a term (with its assoc/unit)
  _[_] : ∀ {B B'} → Stk B B' → Comp B → Comp B'
  S [ M ] = Functor.F-hom 𝕋 S M

  -- Now we can model the type structure by certain UMPs
  -- First, a thunk type U should be a factorization of 𝕋 through 𝕍
  field
    U-Functor : Functor ℂ 𝕍
    U-UMP : funcComp i U-Functor ≡ 𝕋 -- I'm assuming this will mean natural iso?

  -- The action of the functor on objects is the type
  U : CTy → VTy
  U = Functor.F-ob U-Functor

  -- and the thunk/force are the components of the natural isomorphism
  thunk : ∀ {B} → Comp B → Val (U B)
  thunk = {!!}

  force : ∀ {B} → Val (U B) → Comp B
  force = {!!}

  -- The F type is a left adjoint to 𝕋, relative to the inclusion i
  field
    F-Functor : Functor 𝕍 ℂ
    -- Stk (F A) B =~ Val A -> Comp B

  -- TODO: more F stuff

  -- The CBPV function type says that ℂ has *𝕍-powers*
  -- and that 𝕋 *preserves* 𝕍-powers
  field
    _⟶_ : VTy → CTy → CTy
    -- ℂ has *𝕍-powers*:        Stk B' (A ⟶ B) ≡ Val A → Stk B' B
    -- 𝕋 *preserves* 𝕍-powers?: Comp (A ⟶ B) ≡ Val A → Comp B

  -- Value products: 𝕍 has products and i preserves them
  -- Value coproducts: 𝕍 has coproducts and i preserves them
  -- Computation products: ℂ has products and 𝕋 preserves them

  -- We can also add the EEC structures
  -- Linear function space says ℂ is 𝕍-enriched
  field
    _⊸_ : CTy → CTy → VTy
    -- Val (B ⊸ B') ≡ Stk B B'

  -- Tensor product says that ℂ has 𝕍-tensors
  field
    _⊘_ : VTy → CTy → CTy
    -- Stk (A ⊘ B) B' ≡ A → Stk B B'

  -- A *world* type is one that represents 𝕋
  field
    W : CTy
    -- Stk W B ≡ Comp B

  -- If these are all available we have
  -- U B ≡ W ⊸ B
  -- F A ≡ A ⊘ W


  -- Maybe some dependently typed stuff too...
  -- ValTy : VTy -- impredicative, can also make predicative
  -- Val ValTy ≡ VTy

  -- Pi types
  -- Π : ∀ A → (Val A → CTy) → CTy
  -- ((x : Val A) → (Comp (B x))) ≡ Comp (Π A B)
  -- (x : Val A) → Stk B' (Comp (B x)) ≡ Stk B' (Π A B)

  -- We can also extend this with algebraic structures
  -- The cleanest way to do this would basically be to
  -- change 𝕋 : ℂ → SET
  -- to     𝕋 : ℂ → 𝕄
  -- where 𝕄 is the category of models of the algebraic theory

  -- this would say that our computation types support the algebraic
  -- structure and all stacks preserve it.

-- We should be able to show that for any theory T, we get a CBPV
-- model that has all T structures, or more generally, for any
-- extension of a theory T -> T' we get a T-CBPV structure from the
-- algebras of T'

-- This would give us a nice abstract syntax for any effect theory,
-- cool!

-- Things get very cool if we can define exotic algebraic structures
-- using modalities such as later. For instance, in SGDT we could have
-- later algebras which would allow us to use "meta-level" guarded
-- recursion to implement fixed points.

-- wait_ : ▹ (cmp B) → cmp B
