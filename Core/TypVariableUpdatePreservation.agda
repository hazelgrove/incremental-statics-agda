open import Data.Empty
open import Data.Product
open import Relation.Nullary 
open import Relation.Binary.PropositionalEquality

open import Prelude
open import Core.Core
open import Core.Marking
open import Core.Lemmas
open import Core.TypVariableUpdate
open import Core.WellFormed

module Core.TypVariableUpdatePreservation where

  -- data CtxTInv : Var -> Ctx -> Ctx -> Set where 
  --   CInit : ∀ {x Γ} ->
  --     CtxTInv x Γ (x T∷ Γ)
  --   CCons : ∀ {x x' Γ Γ'} ->
  --     CtxTInv x Γ Γ' ->
  --     ¬(x ≡ x') ->
  --     CtxTInv x (x' T∷ Γ) (x' T∷ Γ')
  --   CVCons : ∀ {x x' t t' Γ Γ'} ->
  --     CtxTInv x Γ Γ' ->
  --     (=▷ t' t) ->
  --     CtxTInv x (x' ∶ t ∷ Γ) (x' ∶ t' ∷ Γ')

  -- CCons? : ∀ {x' x Γ Γ'} ->
  --   CtxTInv x Γ Γ' ->
  --   ¬(BVar x ≡ x') ->
  --   CtxTInv x (x' T∷? Γ) (x' T∷? Γ')
  -- CCons? {BHole} inv neq = inv
  -- CCons? {BVar x} inv neq = CCons inv (λ eq → neq (cong BVar eq))
  
  -- CVCons? : ∀ {x' x t t' Γ Γ'} ->
  --   CtxTInv x Γ Γ' ->
  --   (=▷ t' t) ->
  --   CtxTInv x (x' ∶ t ∷? Γ) (x' ∶ t' ∷? Γ')
  -- CVCons? {BHole} inv beyond = inv
  -- CVCons? {BVar x} inv beyond = CVCons inv beyond

  -- ctx-tinv-inctx-eq : ∀ {x Γ Γ'} ->
  --   CtxTInv x Γ Γ' ->
  --   x T∈ Γ' , ✔
  -- ctx-tinv-inctx-eq CInit = InCtxFound
  -- ctx-tinv-inctx-eq (CCons inv neq) = InCtxTSkip neq (ctx-tinv-inctx-eq inv)
  -- ctx-tinv-inctx-eq (CVCons inv _) = InCtxSkip (ctx-tinv-inctx-eq inv)

  -- ctx-tinv-inctx-neq : ∀ {x x' Γ Γ' m} ->
  --   CtxTInv x' Γ Γ' ->
  --   x T∈ Γ , m ->
  --   ¬(x ≡ x') ->
  --   x T∈ Γ' , m
  -- ctx-tinv-inctx-neq CInit inctx neq = InCtxTSkip neq inctx
  -- ctx-tinv-inctx-neq (CCons inv _) InCtxFound neq = InCtxFound
  -- ctx-tinv-inctx-neq (CCons inv _) (InCtxTSkip x inctx) neq = InCtxTSkip x (ctx-tinv-inctx-neq inv inctx neq)
  -- ctx-tinv-inctx-neq (CVCons inv _) (InCtxSkip inctx) neq = InCtxSkip (ctx-tinv-inctx-neq inv inctx neq)

  -- ctx-tinv-inctxR-neq : ∀ {x x' Γ Γ' m} ->
  --   CtxTInv x' Γ' Γ ->
  --   x T∈ Γ , m ->
  --   ¬(x ≡ x') ->
  --   x T∈ Γ' , m
  -- ctx-tinv-inctxR-neq CInit InCtxFound neq = ⊥-elim (neq refl)
  -- ctx-tinv-inctxR-neq CInit (InCtxTSkip x inctx) neq = inctx
  -- ctx-tinv-inctxR-neq (CCons inv x) InCtxFound neq = InCtxFound
  -- ctx-tinv-inctxR-neq (CCons inv x) (InCtxTSkip x₁ inctx) neq = InCtxTSkip x₁ (ctx-tinv-inctxR-neq inv inctx neq)
  -- ctx-tinv-inctxR-neq (CVCons inv _) (InCtxSkip inctx) neq = InCtxSkip (ctx-tinv-inctxR-neq inv inctx neq)

  -- ctx-tinv-inctx-var : ∀ {x x' t Γ Γ' m} ->
  --   CtxTInv x' Γ' Γ ->
  --   x , t ∈ Γ , m ->
  --   ∃[ t' ] (x , t' ∈ Γ' , m) × (=▷ t t')
  -- ctx-tinv-inctx-var CInit (InCtxTSkip inctx) = _ , inctx , =▷Refl
  -- ctx-tinv-inctx-var (CCons inv x) (InCtxTSkip inctx) with ctx-tinv-inctx-var inv inctx 
  -- ... | t , inctx' , beyond = t , InCtxTSkip inctx' , beyond 
  -- ctx-tinv-inctx-var (CVCons inv x) InCtxFound = _ , InCtxFound , x
  -- ctx-tinv-inctx-var (CVCons inv x) (InCtxSkip x₁ inctx) with ctx-tinv-inctx-var inv inctx
  -- ... | t , inctx' , beyond = t , InCtxSkip x₁ inctx' , beyond

  -- data CtxTEquiv : Ctx -> Ctx -> Set where 
  --   CEInit : ∀ {x Γ Γ'} ->
  --     CtxTInv x Γ Γ' ->
  --     CtxTEquiv (x T∷ Γ) (x T∷ Γ')
  --   CEInitR : ∀ {x Γ Γ'} ->
  --     CtxTInv x Γ' Γ ->
  --     CtxTEquiv (x T∷ Γ) (x T∷ Γ')
  --   CECons : ∀ {x Γ Γ'} ->
  --     CtxTEquiv Γ Γ' ->
  --     CtxTEquiv (x T∷ Γ) (x T∷ Γ')
  --   CEVCons : ∀ {x t Γ Γ'} ->
  --     CtxTEquiv Γ Γ' ->
  --     CtxTEquiv (x ∶ t ∷ Γ) (x ∶ t ∷ Γ')

  -- CECons? : ∀ {x Γ Γ'} ->
  --   CtxTEquiv Γ Γ' ->
  --   CtxTEquiv (x T∷? Γ) (x T∷? Γ')
  -- CECons? {BHole} inv = inv
  -- CECons? {BVar x} inv = CECons inv

  -- CEVCons? : ∀ {x t Γ Γ'} ->
  --   CtxTEquiv Γ Γ' ->
  --   CtxTEquiv (x ∶ t ∷? Γ) (x ∶ t ∷? Γ')
  -- CEVCons? {BHole} inv = inv
  -- CEVCons? {BVar x} inv = CEVCons inv

  -- ctx-tequiv-inctx : 
  --   ∀ {Γ Γ' x m} ->
  --   x T∈ Γ , m ->
  --   CtxTEquiv Γ Γ' ->
  --   x T∈ Γ' , m
  -- ctx-tequiv-inctx InCtxFound (CEInit x) = InCtxFound
  -- ctx-tequiv-inctx (InCtxTSkip x₁ inctx) (CEInit x) = InCtxTSkip x₁ (ctx-tinv-inctx-neq x inctx x₁)
  -- ctx-tequiv-inctx InCtxFound (CEInitR x) = InCtxFound
  -- ctx-tequiv-inctx (InCtxTSkip x₁ inctx) (CEInitR x) = InCtxTSkip x₁ (ctx-tinv-inctxR-neq x inctx x₁)
  -- ctx-tequiv-inctx InCtxFound (CECons equiv) = InCtxFound
  -- ctx-tequiv-inctx (InCtxTSkip x inctx) (CECons equiv) = InCtxTSkip x (ctx-tequiv-inctx inctx equiv)
  -- ctx-tequiv-inctx InCtxEmpty ()
  -- ctx-tequiv-inctx (InCtxSkip inctx) (CEVCons equiv) = InCtxSkip (ctx-tequiv-inctx inctx equiv)
  
  -- ctx-tequiv-t :
  --   ∀ {Γ Γ' t} ->
  --   Γ T⊢ t ->
  --   CtxTEquiv Γ Γ' ->
  --   Γ' T⊢ t
  -- ctx-tequiv-t WFBase equiv = WFBase
  -- ctx-tequiv-t WFHole equiv = WFHole
  -- ctx-tequiv-t (WFArrow wf wf₁) equiv = WFArrow (ctx-tequiv-t wf equiv) (ctx-tequiv-t wf₁ equiv)
  -- ctx-tequiv-t (WFProd wf wf₁) equiv = WFProd (ctx-tequiv-t wf equiv) (ctx-tequiv-t wf₁ equiv)
  -- ctx-tequiv-t (WFTVar x) equiv = WFTVar (ctx-tequiv-inctx x equiv)
  -- ctx-tequiv-t (WFForall wf) equiv = WFForall (ctx-tequiv-t wf (CECons? equiv))

  -- -- ctx-tequiv-inctx-var : ∀ {x t Γ Γ' m} ->
  -- --   CtxTEquiv Γ' Γ ->
  -- --   x , t ∈ Γ , m ->
  -- --   ∃[ t' ] (x , t' ∈ Γ' , m) × (=▷ t t')
  -- -- ctx-tequiv-inctx-var (CEInit x) (InCtxTSkip inctx) = {!   !}
  -- -- ctx-tequiv-inctx-var (CEInitR x) (InCtxTSkip inctx) = {!   !}
  -- -- ctx-tequiv-inctx-var (CECons equiv) (InCtxTSkip inctx) = {!   !}
  -- -- ctx-tequiv-inctx-var (CEVCons equiv) InCtxFound = {!   !}
  -- -- ctx-tequiv-inctx-var (CEVCons equiv) (InCtxSkip x inctx) = {!   !}

  -- mutual 
  --   ctx-tequiv-ana : ∀ {Γ Γ' e} ->
  --     CtxTEquiv Γ Γ' ->
  --     Γ L⊢ e ->
  --     Γ' L⊢ e
  --   ctx-tequiv-ana equiv (WFSubsume x x₁ x₂ x₃) = WFSubsume x x₁ x₂ (ctx-tequiv-syn equiv x₃)
  --   ctx-tequiv-ana equiv (WFFun x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ wf) = WFFun (ctx-tequiv-t x equiv) x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ (ctx-tequiv-ana (CEVCons? equiv) wf)
  --   ctx-tequiv-ana equiv (WFPair x x₁ x₂ x₃ x₄ x₅ x₆ wf wf₁) = WFPair x x₁ x₂ x₃ x₄ x₅ x₆ (ctx-tequiv-ana equiv wf) (ctx-tequiv-ana equiv wf₁)
  --   ctx-tequiv-ana equiv (WFTypFun x x₁ x₂ x₃ x₄ x₅ wf) = WFTypFun x x₁ x₂ x₃ x₄ x₅ (ctx-tequiv-ana (CECons? equiv) wf)

  --   ctx-tequiv-syn : ∀ {Γ Γ' e} ->
  --     CtxTEquiv Γ Γ' ->
  --     Γ S⊢ e ->
  --     Γ' S⊢ e
  --   ctx-tequiv-syn equiv (WFConst x) = WFConst x
  --   ctx-tequiv-syn equiv (WFHole x) = WFHole x
  --   ctx-tequiv-syn equiv (WFAp x x₁ x₂ x₃ x₄ x₅) = WFAp x x₁ x₂ x₃ (ctx-tequiv-ana equiv x₄) (ctx-tequiv-ana equiv x₅)
  --   ctx-tequiv-syn equiv (WFVar x x₁) = WFVar {!   !} {!   !}
  --   ctx-tequiv-syn equiv (WFAsc x x₁ x₂ x₃) = {!   !}
  --   ctx-tequiv-syn equiv (WFProj x x₁ x₂ x₃) = {!   !}
  --   ctx-tequiv-syn equiv (WFTypAp x x₁ x₂ x₃ x₄ x₅) = {!   !}

  --   -- ctx-tequiv-ana equiv (WFSubsume x x₁ x₂ syn) with etvu-syn etvu 
  --   -- ... | refl = WFSubsume (etvu-subsumable etvu x) x₁ x₂ (preservation-etvu-unwrap-syn syn inctx etvu inv)
  --   -- ctx-tequiv-ana equiv (WFFun typ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ ana)  
  --   --   = WFFun (preservation-tvu-unwrap typ inctx tvu inv) x₁ (■~N-pair (~N-pair (proj₂ (~D-dec _ _)))) x₃ x₄ ▶★ (consist-unless-new x₆) x₇ x₈ (ctx-tequiv-ana ana (TInCtxSkip? inctx) etvu (CVCons? inv =▷★))
  --   -- ctx-tequiv-ana equiv (WFPair x x₁ x₂ x₃ x₄ x₅ x₆ ana1 ana2) inctx (ETVUPair {e1' = e1' ⇒ syn1'} {e2' = e2' ⇒ syn2'} etvu1 etvu2) inv 
  --   --   with etvu-syn etvu1 | etvu-syn etvu2 
  --   -- ... | refl | refl = WFPair x x₁ x₂ x₃ x₄ x₅ x₆ (ctx-tequiv-ana ana1 inctx etvu1 inv) (ctx-tequiv-ana ana2 inctx etvu2 inv)
  --   -- ctx-tequiv-ana equiv (WFTypFun x x₁ x₂ x₃ x₄ x₅ ana) inctx ETVUTypFunEq inv = WFTypFun x x₁ x₂ x₃ x₄ x₅ (ctx-tequiv-ana (CEInitR inv) ana)
  --   -- ctx-tequiv-ana equiv (WFTypFun x x₁ x₂ x₃ x₄ x₅ ana) inctx (ETVUTypFunNeq {e' = e' ⇒ syn'} neq etvu) inv 
  --   --   with etvu-syn etvu
  --   -- ... | refl = WFTypFun x x₁ x₂ x₃ x₄ x₅ (ctx-tequiv-ana ana (InCtxTSkip? neq inctx) etvu (CCons? inv neq))

  -- preservation-vars-t :
  --   ∀ {x Γ Γ' t t'} ->
  --   Γ T⊢ t ->
  --   TypVariableUpdate x ✔ t t' ->
  --   CtxTInv x Γ Γ' ->
  --   Γ' T⊢ t'
  -- preservation-vars-t WFBase TVUBase inv = WFBase
  -- preservation-vars-t WFHole TVUHole inv = WFHole
  -- preservation-vars-t (WFArrow wf wf₁) (TVUArrow update update₁) inv 
  --   = WFArrow (preservation-vars-t wf update inv) (preservation-vars-t wf₁ update₁ inv)
  -- preservation-vars-t (WFProd wf wf₁) (TVUProd update update₁) inv
  --   = WFProd (preservation-vars-t wf update inv) (preservation-vars-t wf₁ update₁ inv)
  -- preservation-vars-t (WFTVar x) TVUVarEq inv = WFTVar (ctx-tinv-inctx-eq inv)
  -- preservation-vars-t (WFTVar x) (TVUVarNeq x₁) inv = WFTVar (ctx-tinv-inctx-neq inv x x₁)
  -- preservation-vars-t (WFForall wf) TVUForallEq inv = WFForall (ctx-tequiv-t wf (CEInit inv))
  -- preservation-vars-t (WFForall wf) (TVUForallNeq x update) inv = WFForall (preservation-vars-t wf update (CCons? inv x))

  -- preservation-vars-t? :
  --   ∀ {x Γ t t'} ->
  --   Γ T⊢ t ->
  --   TypVariableUpdate? x ✔ t t' ->
  --   (x T∷? Γ) T⊢ t'
  -- preservation-vars-t? {BHole} wf refl = wf
  -- preservation-vars-t? {BVar x} wf update = preservation-vars-t wf update CInit

  InCtxTSkip? : ∀ {x' A free x m} -> {Γ : Context A free} -> 
    ¬(BVar x ≡ x') ->
    (x T∈ Γ , m) -> 
    (x T∈ (x' T∷? Γ) , m)
  InCtxTSkip? {BHole} neq inctx = inctx
  InCtxTSkip? {BVar x} neq inctx = InCtxTSkip (λ eq → neq (cong BVar eq)) inctx

  TInCtxSkip? : ∀ {x' A free x t m} -> {Γ : Context A free} -> 
    (x T∈ Γ , m) -> 
    (x T∈ (x' ∶ t ∷? Γ) , m)
  TInCtxSkip? {BHole} inctx = inctx
  TInCtxSkip? {BVar x} inctx = InCtxSkip inctx

  data tvu-rel : Var -> Ctx -> Ctx -> Set where 
    TVURInit : ∀ {x Γ} ->
      tvu-rel x (x T∷ Γ) Γ
    TVURCons : ∀ {x x' Γ Γ'} ->
      tvu-rel x Γ Γ' ->
      ¬(x ≡ x') ->
      tvu-rel x (x' T∷ Γ) (x' T∷ Γ')

  TVURCons? : ∀ {x' x Γ Γ'} ->
    tvu-rel x Γ Γ' ->
    ¬(BVar x ≡ x') ->
    tvu-rel x (x' T∷? Γ) (x' T∷? Γ')
  TVURCons? {BHole} inv neq = inv
  TVURCons? {BVar x} inv neq = TVURCons inv (λ eq → neq (cong BVar eq))
  
  -- TVURVCons? : ∀ {x' x t t' Γ Γ'} ->
  --   tvu-rel x Γ Γ' ->
  --   (=▷ t' t) ->
  --   tvu-rel x (x' ∶ t ∷? Γ) (x' ∶ t' ∷? Γ')
  -- TVURVCons? {BHole} inv beyond = inv
  -- TVURVCons? {BVar x} inv beyond = TVURVCons inv beyond


  tvu-unwrap-var : ∀ {x x' Γ Γ' m} ->
    tvu-rel x' Γ Γ' ->
    x T∈ Γ , m ->
    ¬(x ≡ x') ->
    x T∈ Γ' , m
  tvu-unwrap-var TVURInit InCtxFound neq = ⊥-elim (neq refl)
  tvu-unwrap-var TVURInit (InCtxTSkip x inctx) neq = inctx
  tvu-unwrap-var (TVURCons inv x) InCtxFound neq = InCtxFound
  tvu-unwrap-var (TVURCons inv x) (InCtxTSkip neq1 inctx) neq2 = InCtxTSkip neq1 (tvu-unwrap-var inv inctx neq2)

  data tvu-unwrap-equiv : Ctx -> Ctx -> Set where 
    TVUUInit : ∀ {x Γ Γ'} ->
      tvu-rel x Γ Γ' ->
      tvu-unwrap-equiv (x T∷ Γ) (x T∷ Γ')
    TVUUCons : ∀ {x Γ Γ'} ->
      tvu-unwrap-equiv Γ Γ' ->
      tvu-unwrap-equiv (x T∷ Γ) (x T∷ Γ')

  TVUUCons? : ∀ {x Γ Γ'} ->
    tvu-unwrap-equiv Γ Γ' ->
    tvu-unwrap-equiv (x T∷? Γ) (x T∷? Γ')
  TVUUCons? {BHole} equiv = equiv
  TVUUCons? {BVar x} equiv = TVUUCons equiv

  tvu-unwrap-equiv-tvar : ∀ {x Γ Γ' m} ->
    tvu-unwrap-equiv Γ Γ' ->
    x T∈ Γ , m ->
    x T∈ Γ' , m
  tvu-unwrap-equiv-tvar (TVUUInit x) InCtxFound = InCtxFound
  tvu-unwrap-equiv-tvar (TVUUInit x) (InCtxTSkip neq inctx) = InCtxTSkip neq (tvu-unwrap-var x inctx neq)
  tvu-unwrap-equiv-tvar (TVUUCons equiv) InCtxFound = InCtxFound
  tvu-unwrap-equiv-tvar (TVUUCons equiv) (InCtxTSkip neq inctx) = InCtxTSkip neq (tvu-unwrap-equiv-tvar equiv inctx)

  preservation-tvu-unwrap-equiv : ∀ {Γ Γ' t} ->
    Γ T⊢ t ->
    tvu-unwrap-equiv Γ Γ' ->
    Γ' T⊢ t
  preservation-tvu-unwrap-equiv WFBase equiv = WFBase
  preservation-tvu-unwrap-equiv WFHole equiv = WFHole
  preservation-tvu-unwrap-equiv (WFArrow wf wf₁) equiv = 
    WFArrow (preservation-tvu-unwrap-equiv wf equiv) (preservation-tvu-unwrap-equiv wf₁ equiv)
  preservation-tvu-unwrap-equiv (WFProd wf wf₁) equiv = 
    WFProd (preservation-tvu-unwrap-equiv wf equiv) (preservation-tvu-unwrap-equiv wf₁ equiv)
  preservation-tvu-unwrap-equiv (WFTVar x) equiv = WFTVar (tvu-unwrap-equiv-tvar equiv x)
  preservation-tvu-unwrap-equiv (WFForall wf) equiv = WFForall (preservation-tvu-unwrap-equiv wf (TVUUCons? equiv))

  preservation-tvu-unwrap :
    ∀ {x Γ Γ' t t' m} ->
    Γ T⊢ t ->
    x T∈ Γ' , m ->
    TypVariableUpdate x m t t' ->
    tvu-rel x Γ Γ' ->
    Γ' T⊢ t'
  preservation-tvu-unwrap WFBase inctx TVUBase inv = WFBase
  preservation-tvu-unwrap WFHole inctx TVUHole inv = WFHole
  preservation-tvu-unwrap (WFArrow wf wf₁) inctx (TVUArrow update update₁) inv 
    = WFArrow (preservation-tvu-unwrap wf inctx update inv) (preservation-tvu-unwrap wf₁ inctx update₁ inv)
  preservation-tvu-unwrap (WFProd wf wf₁) inctx (TVUProd update update₁) inv 
    = WFProd (preservation-tvu-unwrap wf inctx update inv) (preservation-tvu-unwrap wf₁ inctx update₁ inv)
  preservation-tvu-unwrap (WFTVar x) inctx TVUVarEq inv = WFTVar inctx
  preservation-tvu-unwrap (WFTVar x) inctx (TVUVarNeq neq) inv = WFTVar (tvu-unwrap-var inv x neq)
  preservation-tvu-unwrap (WFForall wf) inctx TVUForallEq inv = WFForall (preservation-tvu-unwrap-equiv wf (TVUUInit inv))
  preservation-tvu-unwrap (WFForall wf) inctx (TVUForallNeq neq update) inv 
    = WFForall (preservation-tvu-unwrap wf (InCtxTSkip? neq inctx) update (TVURCons? inv neq)) 

  preservation-tvu-unwrap? :
    ∀ {x Γ t t' m} ->
    (x T∷? Γ) T⊢ t ->
    x T∈? Γ , m ->
    TypVariableUpdate? x m t t' ->
    Γ T⊢ t'
  preservation-tvu-unwrap? {BHole} wf inctx refl = wf
  preservation-tvu-unwrap? {BVar x} wf inctx update = preservation-tvu-unwrap wf inctx update TVURInit

  ------------------------------------------------------------------------------

  preservation-tvu-wrap-var-eq : ∀ {x Γ Γ' m} ->
    tvu-rel x Γ' Γ ->
    x T∈ Γ , m ->
    x T∈ Γ' , ✔
  preservation-tvu-wrap-var-eq TVURInit _ = InCtxFound
  preservation-tvu-wrap-var-eq (TVURCons inv neq) InCtxFound = ⊥-elim (neq refl)
  preservation-tvu-wrap-var-eq (TVURCons inv x) (InCtxTSkip neq inctx) = InCtxTSkip neq (preservation-tvu-wrap-var-eq inv inctx)

  preservation-tvu-wrap-var-neq : ∀ {x x' Γ Γ' m} ->
    tvu-rel x' Γ' Γ ->
    x T∈ Γ , m ->
    ¬ x ≡ x' ->
    x T∈ Γ' , m
  preservation-tvu-wrap-var-neq TVURInit inctx neq = InCtxTSkip neq inctx
  preservation-tvu-wrap-var-neq (TVURCons inv x) InCtxFound neq = InCtxFound
  preservation-tvu-wrap-var-neq (TVURCons inv x) (InCtxTSkip neq1 inctx) neq2 = InCtxTSkip neq1 (preservation-tvu-wrap-var-neq inv inctx neq2)

  data tvu-wrap-equiv : Ctx -> Ctx -> Set where 
    TVUWInit : ∀ {x Γ Γ'} ->
      tvu-rel x Γ' Γ ->
      tvu-wrap-equiv (x T∷ Γ) (x T∷ Γ')
    TVUWCons : ∀ {x Γ Γ'} ->
      tvu-wrap-equiv Γ Γ' ->
      tvu-wrap-equiv (x T∷ Γ) (x T∷ Γ')

  TVUWCons? : ∀ {x Γ Γ'} ->
    tvu-wrap-equiv Γ Γ' ->
    tvu-wrap-equiv (x T∷? Γ) (x T∷? Γ')
  TVUWCons? {BHole} equiv = equiv
  TVUWCons? {BVar x} equiv = TVUWCons equiv

  tvu-wrap-equiv-tvar : ∀ {x Γ Γ' m} ->
    tvu-wrap-equiv Γ Γ' ->
    x T∈ Γ , m ->
    x T∈ Γ' , m
  tvu-wrap-equiv-tvar (TVUWInit x) InCtxFound = InCtxFound
  tvu-wrap-equiv-tvar (TVUWInit x) (InCtxTSkip x₁ inctx) = InCtxTSkip x₁ (preservation-tvu-wrap-var-neq x inctx x₁)
  tvu-wrap-equiv-tvar (TVUWCons equiv) InCtxFound = InCtxFound
  tvu-wrap-equiv-tvar (TVUWCons equiv) (InCtxTSkip x inctx) = InCtxTSkip x (tvu-wrap-equiv-tvar equiv inctx)

  preservation-tvu-wrap-equiv : ∀ {Γ Γ' t} ->
    Γ T⊢ t ->
    tvu-wrap-equiv Γ Γ' ->
    Γ' T⊢ t
  preservation-tvu-wrap-equiv WFBase equiv = WFBase
  preservation-tvu-wrap-equiv WFHole equiv = WFHole
  preservation-tvu-wrap-equiv (WFArrow wf wf₁) equiv = 
    WFArrow (preservation-tvu-wrap-equiv wf equiv) (preservation-tvu-wrap-equiv wf₁ equiv)
  preservation-tvu-wrap-equiv (WFProd wf wf₁) equiv = 
    WFProd (preservation-tvu-wrap-equiv wf equiv) (preservation-tvu-wrap-equiv wf₁ equiv)
  preservation-tvu-wrap-equiv (WFTVar x) equiv = WFTVar (tvu-wrap-equiv-tvar equiv x)
  preservation-tvu-wrap-equiv (WFForall wf) equiv = WFForall (preservation-tvu-wrap-equiv wf (TVUWCons? equiv))

  preservation-tvu-wrap :
    ∀ {x Γ Γ' t t'} ->
    Γ T⊢ t ->
    TypVariableUpdate x ✔ t t' ->
    tvu-rel x Γ' Γ ->
    Γ' T⊢ t'
  preservation-tvu-wrap WFBase TVUBase inv = WFBase
  preservation-tvu-wrap WFHole TVUHole inv = WFHole
  preservation-tvu-wrap (WFArrow wf wf₁) (TVUArrow update update₁) inv = 
    WFArrow (preservation-tvu-wrap wf update inv) (preservation-tvu-wrap wf₁ update₁ inv)
  preservation-tvu-wrap (WFProd wf wf₁) (TVUProd update update₁) inv = 
    WFProd (preservation-tvu-wrap wf update inv) (preservation-tvu-wrap wf₁ update₁ inv)
  preservation-tvu-wrap (WFTVar x) TVUVarEq inv = WFTVar (preservation-tvu-wrap-var-eq inv x)
  preservation-tvu-wrap (WFTVar x) (TVUVarNeq neq) inv = WFTVar (preservation-tvu-wrap-var-neq inv x neq)
  preservation-tvu-wrap (WFForall wf) TVUForallEq inv = WFForall (preservation-tvu-wrap-equiv wf (TVUWInit inv))
  preservation-tvu-wrap (WFForall wf) (TVUForallNeq x update) inv = WFForall (preservation-tvu-wrap wf update (TVURCons? inv x))

  preservation-tvu-wrap? :
    ∀ {x Γ t t'} ->
    Γ T⊢ t ->
    TypVariableUpdate? x ✔ t t' ->
    (x T∷? Γ) T⊢ t'
  preservation-tvu-wrap? {BHole} wf refl = wf
  preservation-tvu-wrap? {BVar x} wf update = preservation-tvu-wrap wf update TVURInit

  ------------------------------------------------------------------------------

  etvu-subsumable : ∀ {x m e e' syn syn'} ->
    ExpTypVariableUpdate x m (e ⇒ syn) (e' ⇒ syn') -> 
    SubsumableMid e ->
    SubsumableMid e'
  etvu-subsumable ETVUConst SubsumableConst = SubsumableConst
  etvu-subsumable ETVUHole SubsumableHole = SubsumableHole
  etvu-subsumable (ETVUFun x etvu) ()
  etvu-subsumable (ETVUAp etvu etvu₁) SubsumableAp = SubsumableAp
  etvu-subsumable ETVUVar SubsumableVar = SubsumableVar
  etvu-subsumable (ETVUAsc x etvu) SubsumableAsc = SubsumableAsc
  etvu-subsumable (ETVUPair etvu etvu₁) ()
  etvu-subsumable (ETVUProj etvu) SubsumableProj = SubsumableProj
  etvu-subsumable ETVUTypFunEq ()
  etvu-subsumable (ETVUTypFunNeq x etvu) ()
  etvu-subsumable (ETVUTypAp etvu x) SubsumableTypAp = SubsumableTypAp

  etvu-syn : ∀ {x t e syn e' syn'} ->
    ExpTypVariableUpdate x t (e ⇒ syn) (e' ⇒ syn') -> 
    syn ≡ syn' 
  etvu-syn ETVUConst = refl
  etvu-syn ETVUHole = refl
  etvu-syn (ETVUFun x update) = refl
  etvu-syn (ETVUAp update update₁) = refl
  etvu-syn ETVUVar = refl
  etvu-syn (ETVUAsc x update) = refl
  etvu-syn (ETVUPair update update₁) = refl
  etvu-syn (ETVUProj update) = refl
  etvu-syn ETVUTypFunEq = refl
  etvu-syn (ETVUTypFunNeq x update) = refl
  etvu-syn (ETVUTypAp update x) = refl

  
  data etvu-unwrap-inv : Var -> Ctx -> Ctx -> Set where 
    ETVUUInit : ∀ {x Γ Γ'} ->
      etvu-unwrap-inv x (x T∷ Γ) Γ'
    ETVUUCons : ∀ {x x' Γ Γ'} ->
      etvu-unwrap-inv x Γ Γ' ->
      ¬(x ≡ x') ->
      etvu-unwrap-inv x (x' T∷ Γ) (x' T∷ Γ')
    ETVUUVCons : ∀ {x x' t t' n m Γ Γ'} ->
      etvu-unwrap-inv x Γ Γ' ->
      TypVariableUpdate x m t t' ->
      etvu-unwrap-inv x (x' ∶ t , n ∷ Γ) (x' ∶ t' , ★ ∷ Γ')

  ETVUUCons? : ∀ {x' x Γ Γ'} ->
    etvu-unwrap-inv x Γ Γ' ->
    ¬(BVar x ≡ x') ->
    etvu-unwrap-inv x (x' T∷? Γ) (x' T∷? Γ')
  ETVUUCons? {BHole} inv neq = inv
  ETVUUCons? {BVar x} inv neq = ETVUUCons inv (λ eq → neq (cong BVar eq))

  ETVUUVCons? : ∀ {x' x t t' n m Γ Γ'} ->
    etvu-unwrap-inv x Γ Γ' ->
    TypVariableUpdate x m t t' ->
    etvu-unwrap-inv x (x' ∶ t , n ∷? Γ) (x' ∶ t' , ★ ∷? Γ')
  ETVUUVCons? {BHole} inv tvu = inv
  ETVUUVCons? {BVar x} inv tvu = ETVUUVCons inv tvu

  mutual 

    preservation-etvu-unwrap-ana :
      ∀ {x Γ Γ' e e' m m' ana} ->
      Γ L⊢ (e [ m' ]⇐ ana) ->
      x T∈ Γ' , m ->
      ExpTypVariableUpdate x m e e' ->
      etvu-unwrap-inv x Γ Γ' ->
      Γ' L⊢ (e' [ m' ]⇐ ana)
    preservation-etvu-unwrap-ana {e' = e' ⇒ syn'} (WFSubsume x x₁ x₂ syn) inctx etvu inv  with etvu-syn etvu 
    ... | refl = WFSubsume (etvu-subsumable etvu x) x₁ x₂ (preservation-etvu-unwrap-syn syn inctx etvu inv)
    preservation-etvu-unwrap-ana (WFFun typ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ ana) inctx (ETVUFun {e-body' = e' ⇒ syn'} tvu etvu) inv 
      = WFFun {!   !} x₁ (■~N-pair (~N-pair (proj₂ (~D-dec _ _)))) x₃ x₄ ▶★ (consist-unless-new x₆) x₇ x₈ (preservation-etvu-unwrap-ana ana (TInCtxSkip? inctx) etvu (ETVUUVCons? inv tvu))
    preservation-etvu-unwrap-ana (WFPair x x₁ x₂ x₃ x₄ x₅ x₆ ana1 ana2) inctx (ETVUPair {e1' = e1' ⇒ syn1'} {e2' = e2' ⇒ syn2'} etvu1 etvu2) inv with etvu-syn etvu1 | etvu-syn etvu2 
    ... | refl | refl = WFPair x x₁ x₂ x₃ x₄ x₅ x₆ (preservation-etvu-unwrap-ana ana1 inctx etvu1 inv) (preservation-etvu-unwrap-ana ana2 inctx etvu2 inv)
    preservation-etvu-unwrap-ana (WFTypFun x x₁ x₂ x₃ x₄ x₅ ana) inctx ETVUTypFunEq inv = WFTypFun x x₁ x₂ x₃ x₄ x₅ {!   !} --(ctx-tequiv-ana (CEInitR inv) ana)
    preservation-etvu-unwrap-ana (WFTypFun x x₁ x₂ x₃ x₄ x₅ ana) inctx (ETVUTypFunNeq {e' = e' ⇒ syn'} neq etvu) inv with etvu-syn etvu
    ... | refl = WFTypFun x x₁ x₂ x₃ x₄ x₅ (preservation-etvu-unwrap-ana ana (InCtxTSkip? neq inctx) etvu (ETVUUCons? inv neq))

    preservation-etvu-unwrap-syn :
      ∀ {x Γ Γ' e e' m} ->
      Γ S⊢ e ->
      x T∈ Γ' , m ->
      ExpTypVariableUpdate x m e e' ->
      etvu-unwrap-inv x Γ Γ' ->
      Γ' S⊢ e'
    preservation-etvu-unwrap-syn (WFConst x) inctx ETVUConst inv = WFConst x
    preservation-etvu-unwrap-syn (WFHole x) inctx ETVUHole inv = WFHole x
    preservation-etvu-unwrap-syn (WFAp x x₁ x₂ x₃ syn ana) inctx (ETVUAp {e1 = e1 ⇒ syn1} {e2 = e2 ⇒ syn2} {e1' = e1' ⇒ syn1'} {e2' = e2' ⇒ syn2'} etvu1 etvu2) inv with etvu-syn etvu1 | etvu-syn etvu2
    ... | refl | refl = WFAp x x₁ x₂ x₃ (preservation-etvu-unwrap-ana syn inctx etvu1 inv) (preservation-etvu-unwrap-ana ana inctx etvu2 inv)
    preservation-etvu-unwrap-syn (WFVar x x₁) inctx ETVUVar inv = {!   !}
    --  with ctx-tinv-inctx-var inv x 
    -- ... | t , inctx' , beyond = WFVar inctx' (beyond-▷ beyond x₁) 
    preservation-etvu-unwrap-syn (WFAsc typ x₁ x₂ ana) inctx (ETVUAsc x₄ etvu) inv 
      = WFAsc {!   !} (▷Pair ▶★) (▷Pair ▶★) (preservation-etvu-unwrap-ana ana inctx etvu inv)
      -- = WFAsc (preservation-tvu-unwrap typ inctx x₄ inv) (▷Pair ▶★) (▷Pair ▶★) (preservation-etvu-unwrap-ana ana inctx etvu inv)
    preservation-etvu-unwrap-syn (WFProj {s = s} mprod x₁ x₂ syn) inctx (ETVUProj {e' = e' ⇒ syn'} etvu) inv with ▸NTProj-dec s syn'
    ... | t , m , mprod' with etvu-syn etvu 
    ... | refl with ▸NTProj-unicity mprod mprod' 
    ... | refl , refl = WFProj mprod x₁ x₂ (preservation-etvu-unwrap-ana syn inctx etvu inv)
    preservation-etvu-unwrap-syn (WFTypAp typ x₁ x₂ x₃ x₄ syn) inctx (ETVUTypAp {e' = e' ⇒ syn'} etvu tvu) inv with etvu-syn etvu 
    ... | refl = WFTypAp {!   !} x₁ x₂ (NSub-pair (proj₂ (DSub-dec _ _ _))) (▷Pair ▶★) (preservation-etvu-unwrap-ana syn inctx etvu inv)  
    -- ... | refl = WFTypAp (preservation-tvu-unwrap typ inctx tvu inv) x₁ x₂ (NSub-pair (proj₂ (DSub-dec _ _ _))) (▷Pair ▶★) (preservation-etvu-unwrap-ana syn inctx etvu inv)  
 
  preservation-etvu-unwrap-ana? :
    ∀ {x Γ e e' m m' ana} ->
    (x T∷? Γ) L⊢ (e [ m' ]⇐ ana) ->
    x T∈? Γ , m ->
    ExpTypVariableUpdate? x m e e' ->
    Γ L⊢ (e' [ m' ]⇐ ana)
  preservation-etvu-unwrap-ana? {BHole} wf inctx refl = wf
  preservation-etvu-unwrap-ana? {BVar x} wf inctx etvu = preservation-etvu-unwrap-ana wf inctx etvu ETVUUInit
