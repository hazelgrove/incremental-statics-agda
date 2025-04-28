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
    ETVUUInit : ∀ {x Γ} ->
      etvu-unwrap-inv x (x T∷ Γ) Γ
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

  etvu-unwrap-inctx : ∀ {x x' Γ Γ' m} ->
    etvu-unwrap-inv x' Γ Γ' ->
    x T∈ Γ , m ->
    ¬(x ≡ x') ->
    x T∈ Γ' , m
  etvu-unwrap-inctx ETVUUInit InCtxFound neq = ⊥-elim (neq refl)
  etvu-unwrap-inctx ETVUUInit (InCtxTSkip x inctx) neq = inctx
  etvu-unwrap-inctx (ETVUUCons inv x) InCtxFound neq = InCtxFound
  etvu-unwrap-inctx (ETVUUCons inv x) (InCtxTSkip neq1 inctx) neq2 = InCtxTSkip neq1 (etvu-unwrap-inctx inv inctx neq2)
  etvu-unwrap-inctx (ETVUUVCons inv x) (InCtxSkip inctx) neq = InCtxSkip (etvu-unwrap-inctx inv inctx neq)

  etvu-unwrap-inctx-var : ∀ {x x' t Γ Γ' m} ->
    etvu-unwrap-inv x' Γ Γ' ->
    x , t ∈ Γ , m ->
    ∃[ t' ] (x , t' ∈ Γ' , m) × (=▷ t t')
  etvu-unwrap-inctx-var ETVUUInit (InCtxTSkip inctx) = _ , inctx , =▷Refl
  etvu-unwrap-inctx-var (ETVUUCons inv x) (InCtxTSkip inctx) with etvu-unwrap-inctx-var inv inctx
  ... | _ , inctx , beyond = _ , InCtxTSkip inctx , beyond
  etvu-unwrap-inctx-var (ETVUUVCons inv x) InCtxFound = _ , InCtxFound , =▷★
  etvu-unwrap-inctx-var (ETVUUVCons inv x) (InCtxSkip neq inctx) with etvu-unwrap-inctx-var inv inctx
  ... | _ , inctx , beyond = _ , InCtxSkip neq inctx , beyond

  data etvu-unwrap-equiv : Ctx -> Ctx -> Set where 
    ETVUUEInit : ∀ {x Γ Γ'} ->
      etvu-unwrap-inv x Γ Γ' ->
      etvu-unwrap-equiv (x T∷ Γ) (x T∷ Γ')
    ETVUUECons : ∀ {x Γ Γ'} ->
      etvu-unwrap-equiv Γ Γ' ->
      etvu-unwrap-equiv (x T∷ Γ) (x T∷ Γ')
    ETVUUEVCons : ∀ {x t Γ Γ'} ->
      etvu-unwrap-equiv Γ Γ' ->
      etvu-unwrap-equiv (x ∶ t ∷ Γ) (x ∶ t ∷ Γ')
  
  ETVUUECons? : ∀ {x Γ Γ'} ->
    etvu-unwrap-equiv Γ Γ' ->
    etvu-unwrap-equiv (x T∷? Γ) (x T∷? Γ')
  ETVUUECons? {BHole} equiv = equiv
  ETVUUECons? {BVar x} equiv = ETVUUECons equiv

  ETVUUEVCons? : ∀ {x t Γ Γ'} ->
    etvu-unwrap-equiv Γ Γ' ->
    etvu-unwrap-equiv (x ∶ t ∷? Γ) (x ∶ t ∷? Γ')
  ETVUUEVCons? {BHole} equiv = equiv
  ETVUUEVCons? {BVar x} equiv = ETVUUEVCons equiv

  etvu-unwrap-equiv-inctx : ∀ {x Γ Γ' m} ->
    x T∈ Γ , m ->
    etvu-unwrap-equiv Γ Γ' ->
    x T∈ Γ' , m
  etvu-unwrap-equiv-inctx InCtxFound (ETVUUEInit x) = InCtxFound
  etvu-unwrap-equiv-inctx InCtxFound (ETVUUECons equiv) = InCtxFound
  etvu-unwrap-equiv-inctx (InCtxSkip inctx) (ETVUUEVCons equiv) = InCtxSkip (etvu-unwrap-equiv-inctx inctx equiv)
  etvu-unwrap-equiv-inctx (InCtxTSkip neq inctx) (ETVUUEInit inv) = InCtxTSkip neq (etvu-unwrap-inctx inv inctx neq)
  etvu-unwrap-equiv-inctx (InCtxTSkip neq inctx) (ETVUUECons equiv) = InCtxTSkip neq (etvu-unwrap-equiv-inctx inctx equiv)

  etvu-unwrap-equiv-inctx-var : ∀ {x t Γ Γ' m} ->
    etvu-unwrap-equiv Γ Γ' ->
    x , t ∈ Γ , m ->
    ∃[ t' ] (x , t' ∈ Γ' , m) × (=▷ t t')
  etvu-unwrap-equiv-inctx-var (ETVUUEInit inv) (InCtxTSkip inctx) with etvu-unwrap-inctx-var inv inctx 
  ... | _ , inctx' , beyond = _ , InCtxTSkip inctx' , beyond
  etvu-unwrap-equiv-inctx-var (ETVUUECons equiv) (InCtxTSkip inctx) with etvu-unwrap-equiv-inctx-var equiv inctx 
  ... | _ , inctx' , beyond = _ , InCtxTSkip inctx' , beyond
  etvu-unwrap-equiv-inctx-var (ETVUUEVCons equiv) InCtxFound = _ , InCtxFound , =▷Refl
  etvu-unwrap-equiv-inctx-var (ETVUUEVCons equiv) (InCtxSkip neq inctx) with etvu-unwrap-equiv-inctx-var equiv inctx 
  ... | _ , inctx' , beyond = _ , InCtxSkip neq inctx' , beyond

  preservation-etvu-unwrap-equiv : ∀ {Γ Γ' t} ->
    Γ T⊢ t ->
    etvu-unwrap-equiv Γ Γ' ->
    Γ' T⊢ t
  preservation-etvu-unwrap-equiv WFBase equiv = WFBase
  preservation-etvu-unwrap-equiv WFHole equiv = WFHole
  preservation-etvu-unwrap-equiv (WFArrow wf wf₁) equiv 
    = WFArrow (preservation-etvu-unwrap-equiv wf equiv) (preservation-etvu-unwrap-equiv wf₁ equiv)
  preservation-etvu-unwrap-equiv (WFProd wf wf₁) equiv 
    = WFProd (preservation-etvu-unwrap-equiv wf equiv) (preservation-etvu-unwrap-equiv wf₁ equiv)
  preservation-etvu-unwrap-equiv (WFTVar x) equiv = WFTVar (etvu-unwrap-equiv-inctx x equiv)
  preservation-etvu-unwrap-equiv (WFForall wf) equiv = WFForall (preservation-etvu-unwrap-equiv wf (ETVUUECons? equiv))

  mutual 

    preservation-etvu-unwrap-equiv-ana : ∀ {Γ Γ' e} ->
      Γ L⊢ e ->
      etvu-unwrap-equiv Γ Γ' ->
      Γ' L⊢ e
    preservation-etvu-unwrap-equiv-ana (WFSubsume x x₁ x₂ x₃) equiv = WFSubsume x x₁ x₂ (preservation-etvu-unwrap-equiv-syn x₃ equiv)
    preservation-etvu-unwrap-equiv-ana (WFFun x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ wf) equiv = WFFun (preservation-etvu-unwrap-equiv x equiv) x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ (preservation-etvu-unwrap-equiv-ana wf (ETVUUEVCons? equiv))
    preservation-etvu-unwrap-equiv-ana (WFPair x x₁ x₂ x₃ x₄ x₅ x₆ wf wf₁) equiv = WFPair x x₁ x₂ x₃ x₄ x₅ x₆ (preservation-etvu-unwrap-equiv-ana wf equiv) (preservation-etvu-unwrap-equiv-ana wf₁ equiv)
    preservation-etvu-unwrap-equiv-ana (WFTypFun x x₁ x₂ x₃ x₄ x₅ wf) equiv = WFTypFun x x₁ x₂ x₃ x₄ x₅ (preservation-etvu-unwrap-equiv-ana wf (ETVUUECons? equiv))

    preservation-etvu-unwrap-equiv-syn : ∀ {Γ Γ' e} ->
      Γ S⊢ e ->
      etvu-unwrap-equiv Γ Γ' ->
      Γ' S⊢ e
    preservation-etvu-unwrap-equiv-syn (WFConst x) equiv = WFConst x
    preservation-etvu-unwrap-equiv-syn (WFHole x) equiv = WFHole x
    preservation-etvu-unwrap-equiv-syn (WFAp x x₁ x₂ x₃ x₄ x₅) equiv = WFAp x x₁ x₂ x₃ (preservation-etvu-unwrap-equiv-ana x₄ equiv) (preservation-etvu-unwrap-equiv-ana x₅ equiv)
    preservation-etvu-unwrap-equiv-syn (WFVar x x₁) equiv with etvu-unwrap-equiv-inctx-var equiv x 
    ... | t , inctx' , beyond = WFVar inctx' (beyond-▷ beyond x₁)
    preservation-etvu-unwrap-equiv-syn (WFAsc x x₁ x₂ x₃) equiv = WFAsc (preservation-etvu-unwrap-equiv x equiv) x₁ x₂ (preservation-etvu-unwrap-equiv-ana x₃ equiv)
    preservation-etvu-unwrap-equiv-syn (WFProj x x₁ x₂ x₃) equiv = WFProj x x₁ x₂ (preservation-etvu-unwrap-equiv-ana x₃ equiv)
    preservation-etvu-unwrap-equiv-syn (WFTypAp x x₁ x₂ x₃ x₄ x₅) equiv = WFTypAp (preservation-etvu-unwrap-equiv x equiv) x₁ x₂ x₃ x₄ (preservation-etvu-unwrap-equiv-ana x₅ equiv)

  preservation-etvu-unwrap :
    ∀ {x Γ Γ' t t' m} ->
    Γ T⊢ t ->
    x T∈ Γ' , m ->
    TypVariableUpdate x m t t' ->
    etvu-unwrap-inv x Γ Γ' ->
    Γ' T⊢ t'
  preservation-etvu-unwrap WFBase inctx TVUBase inv = WFBase
  preservation-etvu-unwrap WFHole inctx TVUHole inv = WFHole
  preservation-etvu-unwrap (WFArrow typ1 typ2) inctx (TVUArrow tvu1 tvu2) inv 
    = WFArrow (preservation-etvu-unwrap typ1 inctx tvu1 inv) (preservation-etvu-unwrap typ2 inctx tvu2 inv)
  preservation-etvu-unwrap (WFProd typ1 typ2) inctx (TVUProd tvu1 tvu2) inv 
    = WFProd (preservation-etvu-unwrap typ1 inctx tvu1 inv) (preservation-etvu-unwrap typ2 inctx tvu2 inv)
  preservation-etvu-unwrap (WFTVar inctx) inctx' TVUVarEq inv = WFTVar inctx'
  preservation-etvu-unwrap (WFTVar inctx) inctx' (TVUVarNeq neq) inv = WFTVar (etvu-unwrap-inctx inv inctx neq)
  preservation-etvu-unwrap (WFForall typ) inctx TVUForallEq inv = WFForall (preservation-etvu-unwrap-equiv typ (ETVUUEInit inv))
  preservation-etvu-unwrap (WFForall typ) inctx (TVUForallNeq neq tvu) inv = WFForall (preservation-etvu-unwrap typ (InCtxTSkip? neq inctx) tvu (ETVUUCons? inv neq))

  mutual 

    preservation-etvu-unwrap-ana :
      ∀ {x Γ Γ' e e' m m' ana} ->
      Γ L⊢ (e [ m' ]⇐ ana) ->
      x T∈ Γ' , m ->
      ExpTypVariableUpdate x m e e' ->
      etvu-unwrap-inv x Γ Γ' ->
      Γ' L⊢ (e' [ m' ]⇐ ana)
    preservation-etvu-unwrap-ana {e' = e' ⇒ syn'} (WFSubsume x x₁ x₂ syn) inctx etvu inv with etvu-syn etvu 
    ... | refl = WFSubsume (etvu-subsumable etvu x) x₁ x₂ (preservation-etvu-unwrap-syn syn inctx etvu inv)
    preservation-etvu-unwrap-ana (WFFun typ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ ana) inctx (ETVUFun {e-body' = e' ⇒ syn'} tvu etvu) inv 
      = WFFun (preservation-etvu-unwrap typ inctx tvu inv) x₁ (■~N-pair (~N-pair (proj₂ (~D-dec _ _)))) x₃ x₄ ▶★ (consist-unless-new x₆) x₇ x₈ (preservation-etvu-unwrap-ana ana (TInCtxSkip? inctx) etvu (ETVUUVCons? inv tvu))
    preservation-etvu-unwrap-ana (WFPair x x₁ x₂ x₃ x₄ x₅ x₆ ana1 ana2) inctx (ETVUPair {e1' = e1' ⇒ syn1'} {e2' = e2' ⇒ syn2'} etvu1 etvu2) inv with etvu-syn etvu1 | etvu-syn etvu2 
    ... | refl | refl = WFPair x x₁ x₂ x₃ x₄ x₅ x₆ (preservation-etvu-unwrap-ana ana1 inctx etvu1 inv) (preservation-etvu-unwrap-ana ana2 inctx etvu2 inv)
    preservation-etvu-unwrap-ana (WFTypFun x x₁ x₂ x₃ x₄ x₅ ana) inctx ETVUTypFunEq inv = WFTypFun x x₁ x₂ x₃ x₄ x₅ (preservation-etvu-unwrap-equiv-ana ana (ETVUUEInit inv)) 
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
    preservation-etvu-unwrap-syn (WFVar x x₁) inctx ETVUVar inv with etvu-unwrap-inctx-var inv x 
    ... | t , inctx' , beyond = WFVar inctx' (beyond-▷ beyond x₁)
    preservation-etvu-unwrap-syn (WFAsc typ x₁ x₂ ana) inctx (ETVUAsc tvu etvu) inv 
      = WFAsc (preservation-etvu-unwrap typ inctx tvu inv) (▷Pair ▶★) (▷Pair ▶★) (preservation-etvu-unwrap-ana ana inctx etvu inv)
    preservation-etvu-unwrap-syn (WFProj {s = s} mprod x₁ x₂ syn) inctx (ETVUProj {e' = e' ⇒ syn'} etvu) inv with ▸NTProj-dec s syn'
    ... | t , m , mprod' with etvu-syn etvu 
    ... | refl with ▸NTProj-unicity mprod mprod' 
    ... | refl , refl = WFProj mprod x₁ x₂ (preservation-etvu-unwrap-ana syn inctx etvu inv)
    preservation-etvu-unwrap-syn (WFTypAp typ x₁ x₂ x₃ x₄ syn) inctx (ETVUTypAp {e' = e' ⇒ syn'} etvu tvu) inv with etvu-syn etvu 
    ... | refl = WFTypAp (preservation-etvu-unwrap typ inctx tvu inv) x₁ x₂ (NSub-pair (proj₂ (DSub-dec _ _ _))) (▷Pair ▶★) (preservation-etvu-unwrap-ana syn inctx etvu inv)  
 
  preservation-etvu-unwrap-ana? :
    ∀ {x Γ e e' m m' ana} ->
    (x T∷? Γ) L⊢ (e [ m' ]⇐ ana) ->
    x T∈? Γ , m ->
    ExpTypVariableUpdate? x m e e' ->
    Γ L⊢ (e' [ m' ]⇐ ana)
  preservation-etvu-unwrap-ana? {BHole} wf inctx refl = wf
  preservation-etvu-unwrap-ana? {BVar x} wf inctx etvu = preservation-etvu-unwrap-ana wf inctx etvu ETVUUInit

  ------------------------------------------------------------------------------

  data etvu-wrap-inv : Var -> Ctx -> Ctx -> Set where 
    ETVUWInit : ∀ {x Γ} ->
      etvu-wrap-inv x Γ (x T∷ Γ)
    ETVUWCons : ∀ {x x' Γ Γ'} ->
      etvu-wrap-inv x Γ Γ' ->
      ¬(x ≡ x') ->
      etvu-wrap-inv x (x' T∷ Γ) (x' T∷ Γ')
    ETVUWVCons : ∀ {x x' t t' n m Γ Γ'} ->
      etvu-wrap-inv x Γ Γ' ->
      TypVariableUpdate x m t t' ->
      etvu-wrap-inv x (x' ∶ t , n ∷ Γ) (x' ∶ t' , ★ ∷ Γ')

  ETVUWCons? : ∀ {x' x Γ Γ'} ->
    etvu-wrap-inv x Γ Γ' ->
    ¬(BVar x ≡ x') ->
    etvu-wrap-inv x (x' T∷? Γ) (x' T∷? Γ')
  ETVUWCons? {BHole} inv neq = inv
  ETVUWCons? {BVar x} inv neq = ETVUWCons inv (λ eq → neq (cong BVar eq))

  ETVUWVCons? : ∀ {x' x t t' n m Γ Γ'} ->
    etvu-wrap-inv x Γ Γ' ->
    TypVariableUpdate x m t t' ->
    etvu-wrap-inv x (x' ∶ t , n ∷? Γ) (x' ∶ t' , ★ ∷? Γ')
  ETVUWVCons? {BHole} inv tvu = inv
  ETVUWVCons? {BVar x} inv tvu = ETVUWVCons inv tvu

  etvu-wrap-inctx-eq : ∀ {x Γ Γ' m} ->
    etvu-wrap-inv x Γ Γ' ->
    x T∈ Γ , m ->
    x T∈ Γ' , ✔
  etvu-wrap-inctx-eq ETVUWInit inctx = InCtxFound
  etvu-wrap-inctx-eq (ETVUWCons inv x) InCtxFound = InCtxFound
  etvu-wrap-inctx-eq (ETVUWCons inv x) (InCtxTSkip neq inctx) = InCtxTSkip neq (etvu-wrap-inctx-eq inv inctx)
  etvu-wrap-inctx-eq (ETVUWVCons inv x) (InCtxSkip inctx) = InCtxSkip (etvu-wrap-inctx-eq inv inctx)

  etvu-wrap-inctx-neq : ∀ {x x' Γ Γ' m} ->
    etvu-wrap-inv x' Γ Γ' ->
    x T∈ Γ , m ->
    ¬ x ≡ x' ->
    x T∈ Γ' , m
  etvu-wrap-inctx-neq ETVUWInit inctx neq = InCtxTSkip neq inctx
  etvu-wrap-inctx-neq (ETVUWCons inv x) InCtxFound neq = InCtxFound
  etvu-wrap-inctx-neq (ETVUWCons inv x) (InCtxTSkip neq1 inctx) neq2 = InCtxTSkip neq1 (etvu-wrap-inctx-neq inv inctx neq2)
  etvu-wrap-inctx-neq (ETVUWVCons inv x) (InCtxSkip inctx) neq = InCtxSkip (etvu-wrap-inctx-neq inv inctx neq)

  etvu-wrap-inctx-var : ∀ {x x' t Γ Γ' m} ->
    etvu-wrap-inv x' Γ Γ' ->
    x , t ∈ Γ , m ->
    ∃[ t' ] (x , t' ∈ Γ' , m) × (=▷ t t')
  etvu-wrap-inctx-var ETVUWInit inctx = _ , InCtxTSkip inctx , =▷Refl
  etvu-wrap-inctx-var (ETVUWCons inv x) (InCtxTSkip inctx) with etvu-wrap-inctx-var inv inctx
  ... | _ , inctx , beyond = _ , InCtxTSkip inctx , beyond
  etvu-wrap-inctx-var (ETVUWVCons inv x) InCtxFound = _ , InCtxFound , =▷★
  etvu-wrap-inctx-var (ETVUWVCons inv x) (InCtxSkip neq inctx) with etvu-wrap-inctx-var inv inctx
  ... | _ , inctx , beyond = _ , InCtxSkip neq inctx , beyond

  data etvu-wrap-equiv : Ctx -> Ctx -> Set where 
    ETVUWEInit : ∀ {x Γ Γ'} ->
      etvu-wrap-inv x Γ Γ' ->
      etvu-wrap-equiv (x T∷ Γ) (x T∷ Γ')
    ETVUWECons : ∀ {x Γ Γ'} ->
      etvu-wrap-equiv Γ Γ' ->
      etvu-wrap-equiv (x T∷ Γ) (x T∷ Γ')
    ETVUWEVCons : ∀ {x t Γ Γ'} ->
      etvu-wrap-equiv Γ Γ' ->
      etvu-wrap-equiv (x ∶ t ∷ Γ) (x ∶ t ∷ Γ')

  ETVUWECons? : ∀ {x Γ Γ'} ->
    etvu-wrap-equiv Γ Γ' ->
    etvu-wrap-equiv (x T∷? Γ) (x T∷? Γ')
  ETVUWECons? {BHole} equiv = equiv
  ETVUWECons? {BVar x} equiv = ETVUWECons equiv

  ETVUWEVCons? : ∀ {x t Γ Γ'} ->
    etvu-wrap-equiv Γ Γ' ->
    etvu-wrap-equiv (x ∶ t ∷? Γ) (x ∶ t ∷? Γ')
  ETVUWEVCons? {BHole} equiv = equiv
  ETVUWEVCons? {BVar x} equiv = ETVUWEVCons equiv

  etvu-wrap-equiv-inctx : ∀ {x Γ Γ' m} ->
    x T∈ Γ , m ->
    etvu-wrap-equiv Γ Γ' ->
    x T∈ Γ' , m
  etvu-wrap-equiv-inctx InCtxFound (ETVUWEInit x) = InCtxFound
  etvu-wrap-equiv-inctx InCtxFound (ETVUWECons equiv) = InCtxFound
  etvu-wrap-equiv-inctx (InCtxSkip inctx) (ETVUWEVCons equiv) = InCtxSkip (etvu-wrap-equiv-inctx inctx equiv)
  etvu-wrap-equiv-inctx (InCtxTSkip neq inctx) (ETVUWEInit inv) = InCtxTSkip neq (etvu-wrap-inctx-neq inv inctx neq)
  etvu-wrap-equiv-inctx (InCtxTSkip neq inctx) (ETVUWECons equiv) = InCtxTSkip neq (etvu-wrap-equiv-inctx inctx equiv) 

  etvu-wrap-equiv-inctx-var : ∀ {x t Γ Γ' m} ->
    etvu-wrap-equiv Γ Γ' ->
    x , t ∈ Γ , m ->
    ∃[ t' ] (x , t' ∈ Γ' , m) × (=▷ t t')
  etvu-wrap-equiv-inctx-var (ETVUWEInit inv) (InCtxTSkip inctx) with etvu-wrap-inctx-var inv inctx 
  ... | _ , inctx' , beyond = _ , InCtxTSkip inctx' , beyond
  etvu-wrap-equiv-inctx-var (ETVUWECons equiv) (InCtxTSkip inctx) with etvu-wrap-equiv-inctx-var equiv inctx 
  ... | _ , inctx' , beyond = _ , InCtxTSkip inctx' , beyond
  etvu-wrap-equiv-inctx-var (ETVUWEVCons equiv) InCtxFound = _ , InCtxFound , =▷Refl
  etvu-wrap-equiv-inctx-var (ETVUWEVCons equiv) (InCtxSkip neq inctx) with etvu-wrap-equiv-inctx-var equiv inctx 
  ... | _ , inctx' , beyond = _ , InCtxSkip neq inctx' , beyond

  preservation-etvu-wrap-equiv : ∀ {Γ Γ' t} ->
    Γ T⊢ t ->
    etvu-wrap-equiv Γ Γ' ->
    Γ' T⊢ t
  preservation-etvu-wrap-equiv WFBase equiv = WFBase
  preservation-etvu-wrap-equiv WFHole equiv = WFHole
  preservation-etvu-wrap-equiv (WFArrow wf wf₁) equiv 
    = WFArrow (preservation-etvu-wrap-equiv wf equiv) (preservation-etvu-wrap-equiv wf₁ equiv)
  preservation-etvu-wrap-equiv (WFProd wf wf₁) equiv 
    = WFProd (preservation-etvu-wrap-equiv wf equiv) (preservation-etvu-wrap-equiv wf₁ equiv)
  preservation-etvu-wrap-equiv (WFTVar x) equiv = WFTVar (etvu-wrap-equiv-inctx x equiv)
  preservation-etvu-wrap-equiv (WFForall wf) equiv = WFForall (preservation-etvu-wrap-equiv wf (ETVUWECons? equiv))

  mutual 

    preservation-etvu-wrap-equiv-ana : ∀ {Γ Γ' e} ->
      Γ L⊢ e ->
      etvu-wrap-equiv Γ Γ' ->
      Γ' L⊢ e
    preservation-etvu-wrap-equiv-ana (WFSubsume x x₁ x₂ x₃) equiv = WFSubsume x x₁ x₂ (preservation-etvu-wrap-equiv-syn x₃ equiv)
    preservation-etvu-wrap-equiv-ana (WFFun x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ wf) equiv = WFFun (preservation-etvu-wrap-equiv x equiv) x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ (preservation-etvu-wrap-equiv-ana wf (ETVUWEVCons? equiv))
    preservation-etvu-wrap-equiv-ana (WFPair x x₁ x₂ x₃ x₄ x₅ x₆ wf wf₁) equiv = WFPair x x₁ x₂ x₃ x₄ x₅ x₆ (preservation-etvu-wrap-equiv-ana wf equiv) (preservation-etvu-wrap-equiv-ana wf₁ equiv)
    preservation-etvu-wrap-equiv-ana (WFTypFun x x₁ x₂ x₃ x₄ x₅ wf) equiv = WFTypFun x x₁ x₂ x₃ x₄ x₅ (preservation-etvu-wrap-equiv-ana wf (ETVUWECons? equiv))

    preservation-etvu-wrap-equiv-syn : ∀ {Γ Γ' e} ->
      Γ S⊢ e ->
      etvu-wrap-equiv Γ Γ' ->
      Γ' S⊢ e
    preservation-etvu-wrap-equiv-syn (WFConst x) equiv = WFConst x
    preservation-etvu-wrap-equiv-syn (WFHole x) equiv = WFHole x
    preservation-etvu-wrap-equiv-syn (WFAp x x₁ x₂ x₃ x₄ x₅) equiv = WFAp x x₁ x₂ x₃ (preservation-etvu-wrap-equiv-ana x₄ equiv) (preservation-etvu-wrap-equiv-ana x₅ equiv)
    preservation-etvu-wrap-equiv-syn (WFVar x x₁) equiv with etvu-wrap-equiv-inctx-var equiv x 
    ... | t , inctx' , beyond = WFVar inctx' (beyond-▷ beyond x₁)
    preservation-etvu-wrap-equiv-syn (WFAsc x x₁ x₂ x₃) equiv = WFAsc (preservation-etvu-wrap-equiv x equiv) x₁ x₂ (preservation-etvu-wrap-equiv-ana x₃ equiv)
    preservation-etvu-wrap-equiv-syn (WFProj x x₁ x₂ x₃) equiv = WFProj x x₁ x₂ (preservation-etvu-wrap-equiv-ana x₃ equiv)
    preservation-etvu-wrap-equiv-syn (WFTypAp x x₁ x₂ x₃ x₄ x₅) equiv = WFTypAp (preservation-etvu-wrap-equiv x equiv) x₁ x₂ x₃ x₄ (preservation-etvu-wrap-equiv-ana x₅ equiv)

  preservation-etvu-wrap :
    ∀ {x Γ Γ' t t'} ->
    Γ T⊢ t ->
    TypVariableUpdate x ✔ t t' ->
    etvu-wrap-inv x Γ Γ' ->
    Γ' T⊢ t'
  -- preservation-etvu-wrap = {!   !}
  preservation-etvu-wrap WFBase TVUBase inv = WFBase
  preservation-etvu-wrap WFHole TVUHole inv = WFHole
  preservation-etvu-wrap (WFArrow typ1 typ2) (TVUArrow tvu1 tvu2) inv 
    = WFArrow (preservation-etvu-wrap typ1 tvu1 inv) (preservation-etvu-wrap typ2 tvu2 inv)
  preservation-etvu-wrap (WFProd typ1 typ2) (TVUProd tvu1 tvu2) inv 
    = WFProd (preservation-etvu-wrap typ1 tvu1 inv) (preservation-etvu-wrap typ2 tvu2 inv)
  preservation-etvu-wrap (WFTVar inctx) TVUVarEq inv = WFTVar (etvu-wrap-inctx-eq inv inctx)
  preservation-etvu-wrap (WFTVar inctx) (TVUVarNeq neq) inv = WFTVar (etvu-wrap-inctx-neq inv inctx neq) 
  preservation-etvu-wrap (WFForall typ) TVUForallEq inv = WFForall (preservation-etvu-wrap-equiv typ (ETVUWEInit inv))
  preservation-etvu-wrap (WFForall typ) (TVUForallNeq neq tvu) inv = WFForall (preservation-etvu-wrap typ tvu (ETVUWCons? inv neq))

  mutual 

    preservation-etvu-wrap-ana :
      ∀ {x Γ Γ' e e' m' ana} ->
      Γ L⊢ (e [ m' ]⇐ ana) ->
      ExpTypVariableUpdate x ✔ e e' ->
      etvu-wrap-inv x Γ Γ' ->
      Γ' L⊢ (e' [ m' ]⇐ ana)
    preservation-etvu-wrap-ana {e' = e' ⇒ syn'} (WFSubsume x x₁ x₂ syn) etvu inv with etvu-syn etvu 
    ... | refl = WFSubsume (etvu-subsumable etvu x) x₁ x₂ (preservation-etvu-wrap-syn syn etvu inv)
    preservation-etvu-wrap-ana (WFFun typ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ ana) (ETVUFun {e-body' = e' ⇒ syn'} tvu etvu) inv 
      = WFFun (preservation-etvu-wrap typ tvu inv) x₁ (■~N-pair (~N-pair (proj₂ (~D-dec _ _)))) x₃ x₄ ▶★ (consist-unless-new x₆) x₇ x₈ (preservation-etvu-wrap-ana ana etvu (ETVUWVCons? inv tvu)) 
    preservation-etvu-wrap-ana (WFPair x x₁ x₂ x₃ x₄ x₅ x₆ ana1 ana2) (ETVUPair {e1' = e1' ⇒ syn1'} {e2' = e2' ⇒ syn2'} etvu1 etvu2) inv with etvu-syn etvu1 | etvu-syn etvu2 
    ... | refl | refl = WFPair x x₁ x₂ x₃ x₄ x₅ x₆ (preservation-etvu-wrap-ana ana1 etvu1 inv) (preservation-etvu-wrap-ana ana2 etvu2 inv)
    preservation-etvu-wrap-ana (WFTypFun x x₁ x₂ x₃ x₄ x₅ ana) ETVUTypFunEq inv = WFTypFun x x₁ x₂ x₃ x₄ x₅ (preservation-etvu-wrap-equiv-ana ana (ETVUWEInit inv)) 
    preservation-etvu-wrap-ana (WFTypFun x x₁ x₂ x₃ x₄ x₅ ana) (ETVUTypFunNeq {e' = e' ⇒ syn'} neq etvu) inv with etvu-syn etvu
    ... | refl = WFTypFun x x₁ x₂ x₃ x₄ x₅ (preservation-etvu-wrap-ana ana etvu (ETVUWCons? inv neq))

    preservation-etvu-wrap-syn :
      ∀ {x Γ Γ' e e'} ->
      Γ S⊢ e ->
      ExpTypVariableUpdate x ✔ e e' ->
      etvu-wrap-inv x Γ Γ' ->
      Γ' S⊢ e'
    preservation-etvu-wrap-syn (WFConst x) ETVUConst inv = WFConst x
    preservation-etvu-wrap-syn (WFHole x) ETVUHole inv = WFHole x
    preservation-etvu-wrap-syn (WFAp x x₁ x₂ x₃ syn ana) (ETVUAp {e1 = e1 ⇒ syn1} {e2 = e2 ⇒ syn2} {e1' = e1' ⇒ syn1'} {e2' = e2' ⇒ syn2'} etvu1 etvu2) inv with etvu-syn etvu1 | etvu-syn etvu2
    ... | refl | refl = WFAp x x₁ x₂ x₃ (preservation-etvu-wrap-ana syn etvu1 inv) (preservation-etvu-wrap-ana ana etvu2 inv)
    preservation-etvu-wrap-syn (WFVar x x₁) ETVUVar inv with etvu-wrap-inctx-var inv x 
    ... | t , inctx' , beyond = WFVar inctx' (beyond-▷ beyond x₁)
    preservation-etvu-wrap-syn (WFAsc typ x₁ x₂ ana) (ETVUAsc tvu etvu) inv 
      = WFAsc (preservation-etvu-wrap typ tvu inv) (▷Pair ▶★) (▷Pair ▶★) (preservation-etvu-wrap-ana ana etvu inv)
    preservation-etvu-wrap-syn (WFProj {s = s} mprod x₁ x₂ syn) (ETVUProj {e' = e' ⇒ syn'} etvu) inv with ▸NTProj-dec s syn'
    ... | t , m , mprod' with etvu-syn etvu 
    ... | refl with ▸NTProj-unicity mprod mprod' 
    ... | refl , refl = WFProj mprod x₁ x₂ (preservation-etvu-wrap-ana syn etvu inv)
    preservation-etvu-wrap-syn (WFTypAp typ x₁ x₂ x₃ x₄ syn) (ETVUTypAp {e' = e' ⇒ syn'} etvu tvu) inv with etvu-syn etvu 
    ... | refl = WFTypAp (preservation-etvu-wrap typ tvu inv) x₁ x₂ (NSub-pair (proj₂ (DSub-dec _ _ _))) (▷Pair ▶★) (preservation-etvu-wrap-ana syn etvu inv)  
 
  preservation-etvu-wrap-ana-outer :
    ∀ {x Γ e e' m ana} ->
    Γ L⊢ (e [ m ]⇐ ana) ->
    ExpTypVariableUpdate x ✔ e e' ->
    (x T∷ Γ) L⊢ (e' [ m ]⇐ ana)
  preservation-etvu-wrap-ana-outer wf etvu = preservation-etvu-wrap-ana wf etvu ETVUWInit
 