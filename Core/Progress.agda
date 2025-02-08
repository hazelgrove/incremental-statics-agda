open import Data.Nat hiding (_+_)
open import Data.Unit 
open import Data.Empty 
open import Data.Bool hiding (_<_; _≟_)
open import Data.Sum renaming (_⊎_ to _+_; inj₁ to Inl ; inj₂ to Inr) hiding (map)
open import Data.Product hiding (map)
open import Relation.Nullary 
open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Prelude

open import Core.Core
open import Core.WellTyped
open import Core.Environment
open import Core.Update
open import Core.Settled

module Core.Progress where


  -- -- ProgressLow : (e : ExpLow) ->
  -- --   ∃[ e' ] (e L↦ e') + (Settled e)
  -- -- ProgressLow

  -- settled-syn-old : ∀ {Γ e t n} ->
  --   Γ ⊢ e ⇒ (t , n) ->
  --   SettledSyn Γ e ->
  --   n ≡ Old
  -- settled-syn-old (SynConst MergeInfoOld) SettledSynConst = refl
  -- settled-syn-old (SynHole MergeInfoOld) SettledSynHole = refl
  -- settled-syn-old (SynFun syn refl m) (SettledSynFun s) rewrite settled-syn-old syn s with m 
  -- ... | MergeInfoOld = refl
  -- settled-syn-old (SynFunVoid syn) ()
  -- settled-syn-old (SynAp syn _ mn _ m) (SettledSynAp s _) rewrite settled-syn-old syn s with mn | m 
  -- ... | MNArrowOld | MergeInfoOld = refl
  -- settled-syn-old (SynApFail syn _ mn _ m) (SettledSynAp s x₄) rewrite settled-syn-old syn s with mn | m 
  -- ... | MNArrowOld | MergeInfoOld = refl
  -- settled-syn-old (SynVar {info = t , Old} ctx1 m) (SettledSynVar (Inl ctx2)) rewrite (ctx-unique ctx1 ctx2) with m 
  -- ... | MergeInfoOld = refl 
  -- settled-syn-old (SynVar {info = t , Old} ctx _) (SettledSynVar (Inr notin)) = ⊥-elim (notin ctx)
  -- settled-syn-old (SynVarFail x MergeInfoOld) (SettledSynVar inctx) = refl
  -- settled-syn-old (SynAsc x MergeInfoOld) (SettledSynAsc x₂) = refl

  -- syn-child : ∀ {Γ e t n} ->
  --   Γ ⊢ e ⇒ (t , n) -> 
  --   SettledSynExcept Γ e ->
  --   ∃[ n' ] ∃[ e' ] e ≡ EUp (⇑ (t , n')) e'
  -- syn-child (SynConst MergeInfoOld) s = _ , _ , refl
  -- syn-child (SynHole MergeInfoOld) s = _ , _ , refl
  -- syn-child (SynFun syn eq m) (SettledSynExceptFun s) rewrite (settled-syn-old syn s) rewrite (sym eq) with m 
  -- ... | MergeInfoOld = _ , _ , refl
  -- syn-child (SynAp syn x mn x₂ m) (SettledSynExceptAp s _) rewrite (settled-syn-old syn s) with mn | m
  -- ... | MNArrowOld | MergeInfoOld = _ , _ , refl
  -- syn-child (SynApFail syn x mn x₂ m) (SettledSynExceptAp s _) rewrite (settled-syn-old syn s) with mn | m
  -- ... | MNArrowOld | MergeInfoOld = _ , _ , refl
  -- syn-child (SynVar ctx1 m) (SettledSynExceptVar (Inl ctx2)) rewrite (ctx-unique ctx1 ctx2) with m 
  -- ... | MergeInfoOld = _ , _ , refl
  -- syn-child (SynVar ctx _) (SettledSynExceptVar (Inr notin)) = ⊥-elim (notin ctx)
  -- syn-child (SynVarFail x m) s with m 
  -- ... | MergeInfoOld = _ , _ , refl
  -- syn-child (SynAsc x m) (SettledSynExceptAsc x₂) with m 
  -- ... | MergeInfoOld = _ , _ , refl

  -- settle-no-except : ∀ {Γ t e} ->
  --   SettledSynExcept Γ (EUp (⇑ (t , Old)) e) ->
  --   SettledSyn Γ (EUp (⇑ (t , Old)) e) 
  -- settle-no-except SettledSynExceptConst = SettledSynConst
  -- settle-no-except SettledSynExceptHole = SettledSynHole
  -- settle-no-except (SettledSynExceptFun x) = SettledSynFun x
  -- settle-no-except (SettledSynExceptAp x x₁) = SettledSynAp x x₁
  -- settle-no-except (SettledSynExceptVar inctx) = SettledSynVar inctx
  -- settle-no-except (SettledSynExceptAsc x) = SettledSynAsc x

  new-ana-steps-inner : ∀ {e m t} ->
    ∃[ e' ] (e [ m ]⇐ (t , New)) L↦ e' 
  new-ana-steps-inner {EConst ⇒ _} = _ , {! StepNewAnaConsist  !}
  new-ana-steps-inner {EHole ⇒ _} = {!   !}
  new-ana-steps-inner {EAp _ _ _ ⇒ _} = {!   !}
  new-ana-steps-inner {EVar _ _ ⇒ _} = {!   !}
  new-ana-steps-inner {EAsc _ _ ⇒ _} = {!   !}
  new-ana-steps-inner {EFun _ _ _ _ _ ⇒ _} = {!   !}

  new-ana-steps : ∀ {e m t} ->
    ∃[ e' ] (e [ m ]⇐ (t , New)) Low↦ e' 
  new-ana-steps = {!   !}


  mutual 
    
  --   ProgressSyn : 
  --     ∀ {Γ e} ->
  --     -- AllOld Γ ->
  --     ∃[ t ] (Γ ⊢ e ⇒ t) ->
  --     ∃[ e' ] (e Up↦ e') + (SettledSynExcept Γ e)
  --   ProgressSyn (t , SynConst _) = Inr SettledSynExceptConst
  --   ProgressSyn (t , SynHole _) = Inr SettledSynExceptHole
  --   ProgressSyn (t , SynFun syn refl m) with ProgressSyn (_ , syn) 
  --   ProgressSyn (t , SynFun syn refl m) | Inl (_ , StepUp fill1 step fill2) = Inl (_ , StepUp (FillUEnvUpRec (FillUEnvFun (FillUEnvLowRec fill1))) step (FillUEnvUpRec (FillUEnvFun (FillUEnvLowRec fill2))))
  --   ProgressSyn (t , SynFun syn refl m) | Inl (_ , StepLow fill1 step fill2) = Inl (_ , StepLow (FillLEnvUpRec (FillLEnvFun (FillLEnvLowRec fill1))) step (FillLEnvUpRec (FillLEnvFun (FillLEnvLowRec fill2))))
  --   ProgressSyn (t , SynFun syn refl m) | Inr s with syn-child syn s 
  --   ProgressSyn (t , SynFun syn refl m) | Inr s | New , _ , refl = {! Inl (_ , StepUp FillU⊙ (StepAp IsNewNew mt MNArrowNew) FillU⊙)  !}
  --   ProgressSyn (t , SynFun syn refl m) | Inr s | NArrow _ _ , _ , refl = {!   !}
  --   ProgressSyn (t , SynFun syn refl m) | Inr s | Old , _ , refl = {!   !}
  --   ProgressSyn (.(TArrow _ _ , New) , SynFunVoid syn) = {!   !}
  --   ProgressSyn (t , SynAp syn mt mn ana m) with ProgressSyn (_ , syn) | ProgressLow ana 
  --   ProgressSyn (t , SynAp syn mt mn ana m) | Inl (_ , StepUp fill1 step fill2) | ssana = Inl (_ , StepUp (FillUEnvUpRec (FillUEnvAp1 (FillUEnvLowRec fill1))) step (FillUEnvUpRec (FillUEnvAp1 (FillUEnvLowRec fill2))))
  --   ProgressSyn (t , SynAp syn mt mn ana m) | Inl (_ , StepLow fill1 step fill2) | ssana = Inl (_ , StepLow (FillLEnvUpRec (FillLEnvAp1 (FillLEnvLowRec fill1))) step (FillLEnvUpRec (FillLEnvAp1 (FillLEnvLowRec fill2))))
  --   ProgressSyn (t , SynAp syn mt mn ana m) | Inr s1 | Inl (_ , StepUp fill1 step fill2) = Inl (_ , StepUp (FillUEnvUpRec (FillUEnvAp2 fill1)) step (FillUEnvUpRec (FillUEnvAp2 fill2)))
  --   ProgressSyn (t , SynAp syn mt mn ana m) | Inr s1 | Inl (_ , StepLow fill1 step fill2) = Inl (_ , StepLow (FillLEnvUpRec (FillLEnvAp2 fill1)) step (FillLEnvUpRec (FillLEnvAp2 fill2)))
  --   ProgressSyn (t , SynAp syn mt mn ana m) | Inr s1 | Inr s2 with syn-child syn s1 
  --   ProgressSyn (t , SynAp {e2 = (ELow _ _ _)} syn mt mn ana m) | Inr s1 | Inr s2 | New , _ , refl = Inl (_ , StepUp FillU⊙ (StepAp IsNewNew mt MNArrowNew) FillU⊙)
  --   ProgressSyn (t , SynAp {e2 = (ELow _ _ _)} syn mt mn ana m) | Inr s1 | Inr s2 | NArrow _ _ , _ , refl = Inl (_ , StepUp FillU⊙ (StepAp IsNewArrow mt MNArrowArrow) FillU⊙)
  --   ProgressSyn (t , SynAp syn mt mn ana m) | Inr s1 | Inr s2 | Old , _ , refl = Inr (SettledSynExceptAp (settle-no-except s1) s2)
  --   ProgressSyn (t , SynApFail syn mt mn ana m) with ProgressSyn (_ , syn) | ProgressLow ana 
  --   ProgressSyn (t , SynApFail syn mt mn ana m) | Inl (_ , StepUp fill1 step fill2) | ssana = Inl (_ , StepUp (FillUEnvUpRec (FillUEnvAp1 (FillUEnvLowRec fill1))) step (FillUEnvUpRec (FillUEnvAp1 (FillUEnvLowRec fill2))))
  --   ProgressSyn (t , SynApFail syn mt mn ana m) | Inl (_ , StepLow fill1 step fill2) | ssana = Inl (_ , StepLow (FillLEnvUpRec (FillLEnvAp1 (FillLEnvLowRec fill1))) step (FillLEnvUpRec (FillLEnvAp1 (FillLEnvLowRec fill2))))
  --   ProgressSyn (t , SynApFail syn mt mn ana m) | Inr s1 | Inl (_ , StepUp fill1 step fill2) = Inl (_ , StepUp (FillUEnvUpRec (FillUEnvAp2 fill1)) step (FillUEnvUpRec (FillUEnvAp2 fill2)))
  --   ProgressSyn (t , SynApFail syn mt mn ana m) | Inr s1 | Inl (_ , StepLow fill1 step fill2) = Inl (_ , StepLow (FillLEnvUpRec (FillLEnvAp2 fill1)) step (FillLEnvUpRec (FillLEnvAp2 fill2)))
  --   ProgressSyn (t , SynApFail syn mt mn ana m) | Inr s1 | Inr s2 with syn-child syn s1 
  --   ProgressSyn (t , SynApFail {e2 = (ELow _ _ _)} syn mt mn ana m) | Inr s1 | Inr s2 | New , _ , refl = Inl (_ , StepUp FillU⊙ (StepApFail IsNewNew mt MNArrowNew) FillU⊙)
  --   ProgressSyn (t , SynApFail {e2 = (ELow _ _ _)} syn mt mn ana m) | Inr s1 | Inr s2 | NArrow n n₁ , _ , refl = Inl (_ , StepUp FillU⊙ (StepApFail IsNewArrow mt MNArrowArrow) FillU⊙)
  --   ProgressSyn (t , SynApFail syn mt mn ana m) | Inr s1 | Inr s2 | Old , _ , refl = Inr (SettledSynExceptAp (settle-no-except s1) s2)
  --   ProgressSyn (t , SynVar {t = _ , New} ctx _) = {!   !}
  --   ProgressSyn (t , SynVar {t = _ , NArrow n n₁} ctx _) = {!   !}
  --   ProgressSyn (t , SynVar {t = _ , Old} ctx _) = Inr (SettledSynExceptVar (Inl ctx))
  --   ProgressSyn (t , SynVarFail notin _) = Inr (SettledSynExceptVar {t1 = THole} (Inr notin)) 
  --   ProgressSyn (t , SynAsc ana _) with ProgressLow ana
  --   ProgressSyn (t , SynAsc ana _) | Inl (_ , StepUp fill1 step fill2) = Inl (_ , StepUp (FillUEnvUpRec (FillUEnvAsc fill1)) step (FillUEnvUpRec (FillUEnvAsc fill2)))
  --   ProgressSyn (t , SynAsc ana _) | Inl (_ , StepLow fill1 step fill2) = Inl (_ , StepLow (FillLEnvUpRec (FillLEnvAsc fill1)) step (FillLEnvUpRec (FillLEnvAsc fill2)))
  --   ProgressSyn (t , SynAsc {t = (_ , New)} {e = (ELow _ _ _)} ana _) | Inr sana = Inl (_ , StepUp FillU⊙ (StepAsc IsNewNew) FillU⊙)
  --   ProgressSyn (t , SynAsc {t = (_ , NArrow _ _)} {e = (ELow _ _ _)} ana _) | Inr sana = Inl (_ , StepUp FillU⊙ (StepAsc IsNewArrow) FillU⊙)
  --   ProgressSyn (t , SynAsc {t = (_ , Old)} ana _) | Inr sana = Inr (SettledSynExceptAsc sana)
    
    ProgressUp :  
      ∀ {Γ e} ->
      (Γ ⊢ e ⇒) ->      
      (∃[ e' ] (e Up↦ e')) + (SettledUp e)
    ProgressUp = {!   !}

    ProgressLow :  
      ∀ {Γ e} ->
      (Γ ⊢ e ⇐) ->      
      (∃[ e' ] (e Low↦ e')) + (SettledLow e)
    ProgressLow (AnaSubsume {ana-all = t , n} subsumable consist m-consist syn) with ProgressUp syn 
    ProgressLow (AnaSubsume {ana-all = t , n} subsumable consist m-consist syn) | Inl (e' , step) = Inl (_ , StepUpLow (FillUEnvLowRec FillU⊙) step (FillUEnvLowRec FillU⊙))
    ProgressLow (AnaSubsume {ana-all = t , Old} subsumable consist m-consist syn) | Inr settled = Inr (SettledLowC settled)
    ProgressLow (AnaSubsume {ana-all = t , New} subsumable consist m-consist syn) | Inr settled = Inl (_ , {!   !})
    ProgressLow (AnaFun x x₁ x₂ x₃ x₄ x₅ x₆ x₇ ana) = {!   !}     

  step-preserves-program : ∀ {p e} -> 
    ExpLowOfProgram p Low↦ e -> 
    ∃[ p' ] (e ≡ ExpLowOfProgram p')
  step-preserves-program {p = Root e n} (StepUp (FillUEnvLowRec x) step (FillUEnvLowRec x₁)) = Root _ _ , refl
  step-preserves-program {p = Root e n} (StepLow (FillLEnvLowRec x) step (FillLEnvLowRec x₁)) = Root _ _ , refl
  step-preserves-program {p = Root e n} (StepLow FillL⊙ (StepAnaFun x x₁) FillL⊙) = Root _ _ , refl
  step-preserves-program {p = Root e n} (StepLow FillL⊙ (StepNewAnnFun x) FillL⊙) = Root _ _ , refl
  step-preserves-program {p = Root e n} (StepLow FillL⊙ StepSynFun FillL⊙) = Root _ _ , refl

  ProgressProgram : ∀ {p} ->
    WellTypedProgram p ->  
    (∃[ p' ] (p P↦ p')) + (SettledProgram p)
  ProgressProgram (WTProg ana) with ProgressLow ana 
  ProgressProgram (WTProg ana) | Inl (e' , step) with step-preserves-program step 
  ProgressProgram (WTProg ana) | Inl (e' , step) | p' , refl = Inl (p' , (TopStep step)) 
  ProgressProgram {p = Root e n} (WTProg ana) | Inr settled = Inr (SettledRoot settled)