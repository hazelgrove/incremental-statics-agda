open import Data.Empty
open import Relation.Nullary 
open import Relation.Binary.PropositionalEquality

open import Prelude
open import Core.Core
open import Core.Marking
open import Core.TypVariableUpdate
open import Core.WellFormed

module Core.TypVariableUpdatePreservation where

  data CtxTInv : Var -> Ctx -> Ctx -> Set where 
    CInit : ∀ {x Γ} ->
      CtxTInv x Γ (x T∷ Γ)
    CCons : ∀ {x x' Γ Γ'} ->
      CtxTInv x Γ Γ' ->
      ¬(x ≡ x') ->
      CtxTInv x (x' T∷ Γ) (x' T∷ Γ')

  CCons? : ∀ {x' x Γ Γ'} ->
    CtxTInv x Γ Γ' ->
    ¬(BVar x ≡ x') ->
    CtxTInv x (x' T∷? Γ) (x' T∷? Γ')
  CCons? {BHole} inv neq = inv
  CCons? {BVar x} inv neq = CCons inv (λ eq → neq (cong BVar eq))

  ctx-tinv-inctx-eq : ∀ {x Γ Γ'} ->
    CtxTInv x Γ Γ' ->
    x T∈ Γ' , ✔
  ctx-tinv-inctx-eq CInit = InCtxFound
  ctx-tinv-inctx-eq (CCons inv neq) = InCtxTSkip neq (ctx-tinv-inctx-eq inv)

  ctx-tinv-inctx-neq : ∀ {x x' Γ Γ' m} ->
    CtxTInv x' Γ Γ' ->
    x T∈ Γ , m ->
    ¬(x ≡ x') ->
    x T∈ Γ' , m
  ctx-tinv-inctx-neq CInit inctx neq = InCtxTSkip neq inctx
  ctx-tinv-inctx-neq (CCons inv _) InCtxFound neq = InCtxFound
  ctx-tinv-inctx-neq (CCons inv _) (InCtxTSkip x inctx) neq = InCtxTSkip x (ctx-tinv-inctx-neq inv inctx neq)

  ctx-tinv-inctxR-neq : ∀ {x x' Γ Γ' m} ->
    CtxTInv x' Γ' Γ ->
    x T∈ Γ , m ->
    ¬(x ≡ x') ->
    x T∈ Γ' , m
  ctx-tinv-inctxR-neq CInit InCtxFound neq = ⊥-elim (neq refl)
  ctx-tinv-inctxR-neq CInit (InCtxTSkip x inctx) neq = inctx
  ctx-tinv-inctxR-neq (CCons inv x) InCtxFound neq = InCtxFound
  ctx-tinv-inctxR-neq (CCons inv x) (InCtxTSkip x₁ inctx) neq = InCtxTSkip x₁ (ctx-tinv-inctxR-neq inv inctx neq)

  data CtxTEquiv : Ctx -> Ctx -> Set where 
    CEInit : ∀ {x Γ Γ'} ->
      CtxTInv x Γ Γ' ->
      CtxTEquiv (x T∷ Γ) (x T∷ Γ')
    CEInitR : ∀ {x Γ Γ'} ->
      CtxTInv x Γ' Γ ->
      CtxTEquiv (x T∷ Γ) (x T∷ Γ')
    CECons : ∀ {x Γ Γ'} ->
      CtxTEquiv Γ Γ' ->
      CtxTEquiv (x T∷ Γ) (x T∷ Γ')

  CECons? : ∀ {x Γ Γ'} ->
    CtxTEquiv Γ Γ' ->
    CtxTEquiv (x T∷? Γ) (x T∷? Γ')
  CECons? {BHole} inv = inv
  CECons? {BVar x} inv = CECons inv

  ctx-tequiv-inctx : 
    ∀ {Γ Γ' x m} ->
    x T∈ Γ , m ->
    CtxTEquiv Γ Γ' ->
    x T∈ Γ' , m
  ctx-tequiv-inctx InCtxFound (CEInit x) = InCtxFound
  ctx-tequiv-inctx (InCtxTSkip x₁ inctx) (CEInit x) = InCtxTSkip x₁ (ctx-tinv-inctx-neq x inctx x₁)
  ctx-tequiv-inctx InCtxFound (CEInitR x) = InCtxFound
  ctx-tequiv-inctx (InCtxTSkip x₁ inctx) (CEInitR x) = InCtxTSkip x₁ (ctx-tinv-inctxR-neq x inctx x₁)
  ctx-tequiv-inctx InCtxFound (CECons equiv) = InCtxFound
  ctx-tequiv-inctx (InCtxTSkip x inctx) (CECons equiv) = InCtxTSkip x (ctx-tequiv-inctx inctx equiv)

  ctx-tequiv-t :
    ∀ {Γ Γ' t} ->
    Γ T⊢ t ->
    CtxTEquiv Γ Γ' ->
    Γ' T⊢ t
  ctx-tequiv-t WFBase equiv = WFBase
  ctx-tequiv-t WFHole equiv = WFHole
  ctx-tequiv-t (WFArrow wf wf₁) equiv = WFArrow (ctx-tequiv-t wf equiv) (ctx-tequiv-t wf₁ equiv)
  ctx-tequiv-t (WFProd wf wf₁) equiv = WFProd (ctx-tequiv-t wf equiv) (ctx-tequiv-t wf₁ equiv)
  ctx-tequiv-t (WFTVar x) equiv = WFTVar (ctx-tequiv-inctx x equiv)
  ctx-tequiv-t (WFForall wf) equiv = WFForall (ctx-tequiv-t wf (CECons? equiv))

  preservation-vars-t :
    ∀ {x Γ Γ' t t'} ->
    Γ T⊢ t ->
    TypVariableUpdate x ✔ t t' ->
    CtxTInv x Γ Γ' ->
    Γ' T⊢ t'
  preservation-vars-t WFBase TVUBase inv = WFBase
  preservation-vars-t WFHole TVUHole inv = WFHole
  preservation-vars-t (WFArrow wf wf₁) (TVUArrow update update₁) inv 
    = WFArrow (preservation-vars-t wf update inv) (preservation-vars-t wf₁ update₁ inv)
  preservation-vars-t (WFProd wf wf₁) (TVUProd update update₁) inv
    = WFProd (preservation-vars-t wf update inv) (preservation-vars-t wf₁ update₁ inv)
  preservation-vars-t (WFTVar x) TVUVarEq inv = WFTVar (ctx-tinv-inctx-eq inv)
  preservation-vars-t (WFTVar x) (TVUVarNeq x₁) inv = WFTVar (ctx-tinv-inctx-neq inv x x₁)
  preservation-vars-t (WFForall wf) TVUForallEq inv = WFForall (ctx-tequiv-t wf (CEInit inv))
  preservation-vars-t (WFForall wf) (TVUForallNeq x update) inv = WFForall (preservation-vars-t wf update (CCons? inv x))

  preservation-vars-t? :
    ∀ {x Γ t t'} ->
    Γ T⊢ t ->
    TypVariableUpdate? x ✔ t t' ->
    (x T∷? Γ) T⊢ t'
  preservation-vars-t? {BHole} wf refl = wf
  preservation-vars-t? {BVar x} wf update = preservation-vars-t wf update CInit

  InCtxTSkip? : ∀ {x' A free x m} -> {Γ : Context A free} -> 
    ¬(BVar x ≡ x') ->
    (x T∈ Γ , m) -> 
    (x T∈ (x' T∷? Γ) , m)
  InCtxTSkip? {BHole} neq inctx = inctx
  InCtxTSkip? {BVar x} neq inctx = InCtxTSkip (λ eq → neq (cong BVar eq)) inctx

  preservation-vars-unwrap-t :
    ∀ {x Γ Γ' t t' m} ->
    Γ' T⊢ t ->
    x T∈ Γ , m ->
    TypVariableUpdate x m t t' ->
    CtxTInv x Γ Γ' ->
    Γ T⊢ t'
  preservation-vars-unwrap-t WFBase inctx TVUBase inv = WFBase
  preservation-vars-unwrap-t WFHole inctx TVUHole inv = WFHole
  preservation-vars-unwrap-t (WFArrow wf wf₁) inctx (TVUArrow update update₁) inv 
    = WFArrow (preservation-vars-unwrap-t wf inctx update inv) (preservation-vars-unwrap-t wf₁ inctx update₁ inv)
  preservation-vars-unwrap-t (WFProd wf wf₁) inctx (TVUProd update update₁) inv 
    = WFProd (preservation-vars-unwrap-t wf inctx update inv) (preservation-vars-unwrap-t wf₁ inctx update₁ inv)
  preservation-vars-unwrap-t (WFTVar x) inctx TVUVarEq inv = WFTVar inctx
  preservation-vars-unwrap-t (WFTVar x) inctx (TVUVarNeq x₁) inv = WFTVar (ctx-tinv-inctxR-neq inv x x₁)
  preservation-vars-unwrap-t (WFForall wf) inctx TVUForallEq inv = WFForall (ctx-tequiv-t wf (CEInitR inv))
  preservation-vars-unwrap-t (WFForall wf) inctx (TVUForallNeq x update) inv = WFForall (preservation-vars-unwrap-t wf (InCtxTSkip? x inctx) update (CCons? inv x))

  preservation-vars-unwrap-t? :
    ∀ {x Γ t t' m} ->
    (x T∷? Γ) T⊢ t ->
    x T∈? Γ , m ->
    TypVariableUpdate? x m t t' ->
    Γ T⊢ t'
  preservation-vars-unwrap-t? {BHole} wf _ refl = wf
  preservation-vars-unwrap-t? {BVar x} wf inctx update = preservation-vars-unwrap-t wf inctx update CInit