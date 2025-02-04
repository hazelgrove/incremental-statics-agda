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
open import Core.Update
open import Core.Merge
open import Core.Settled
-- open import Core.Lemmas-Context

module Core.UpdatePreservation where

  -- mutual 

  --   UEnvUpCtx : Ctx -> UEnvUp -> Ctx 
  --   UEnvUpCtx Γ U⊙ = Γ
  --   UEnvUpCtx Γ (UEnvUpRec x ε) = UEnvMidCtx Γ ε

  --   UEnvMidCtx : Ctx -> UEnvMid -> Ctx
  --   UEnvMidCtx Γ (UEnvFun t x₁ ε) = UEnvLowCtx (t , Γ) ε
  --   UEnvMidCtx Γ (UEnvAp1 ε x₁ x₂) = UEnvLowCtx Γ ε
  --   UEnvMidCtx Γ (UEnvAp2 x x₁ ε) = UEnvLowCtx Γ ε
  --   UEnvMidCtx Γ (UEnvAsc x ε) = UEnvLowCtx Γ ε

  --   UEnvLowCtx : Ctx -> UEnvLow -> Ctx
  --   UEnvLowCtx Γ (UEnvLowRec x x₁ ε) = UEnvUpCtx Γ ε 

  -- LEnvUpCtx : Ctx -> LEnvUp -> Ctx
  -- LEnvUpCtx = {!   !}

  -- LEnvUpFillTyping : 
  --   ∀ {Γ ε e e' t e-in e-in' t-in } ->
  --   ((LEnvUpCtx Γ ε) ⊢ e-in ⇐ t-in) ->
  --   (ε L⟦ e-in ⟧Up== e) -> 
  --   (Γ ⊢ e ⇒ t) ->
  --   ((LEnvUpCtx Γ ε) ⊢ e-in' ⇐ t-in) ->
  --   (ε L⟦ e-in' ⟧Up== e') -> 
  --   (Γ ⊢ e' ⇒ t)
  -- LEnvUpFillTyping = {!   !}

  -- UEnvLowFillTyping : 
  --   ∀ {Γ ε e e' t e-in e-in' t-in } ->
  --   ((UEnvLowCtx Γ ε) ⊢ e-in ⇒ t-in) ->
  --   (ε U⟦ e-in ⟧Low== e) -> 
  --   (Γ ⊢ e ⇐ t) ->
  --   ((UEnvLowCtx Γ ε) ⊢ e-in' ⇒ t-in) ->
  --   (ε U⟦ e-in' ⟧Low== e') -> 
  --   (Γ ⊢ e' ⇐ t)
  -- UEnvLowFillTyping = {!   !}

  -- UEnvUpFillTyping : 
  --   ∀ {Γ ε e e' t e-in e-in' t-in } ->
  --   ((UEnvUpCtx Γ ε) ⊢ e-in ⇒ t-in) ->
  --   (ε U⟦ e-in ⟧Up== e) -> 
  --   (Γ ⊢ e ⇒ t) ->
  --   ((UEnvUpCtx Γ ε) ⊢ e-in' ⇒ t-in) ->
  --   (ε U⟦ e-in' ⟧Up== e') -> 
  --   (Γ ⊢ e' ⇒ t)
  -- UEnvUpFillTyping syn-in1 FillU⊙ syn syn-in2 FillU⊙ rewrite (syn-unicity syn syn-in1) = syn-in2
  -- UEnvUpFillTyping syn-in1 (FillUEnvUpRec (FillUEnvFun (FillUEnvLowRec fill1))) (SynFun syn mn m) syn-in2 (FillUEnvUpRec (FillUEnvFun (FillUEnvLowRec fill2))) = SynFun (UEnvUpFillTyping syn-in1 fill1 syn syn-in2 fill2) mn m
  -- UEnvUpFillTyping syn-in1 (FillUEnvUpRec (FillUEnvFun (FillUEnvLowRec fill1))) (SynFunVoid syn) syn-in2 (FillUEnvUpRec (FillUEnvFun (FillUEnvLowRec fill2))) = SynFunVoid (UEnvUpFillTyping syn-in1 fill1 syn syn-in2 fill2)
  -- UEnvUpFillTyping syn-in1 (FillUEnvUpRec (FillUEnvAp1 (FillUEnvLowRec fill1))) (SynAp syn mt mn ana m) syn-in2 (FillUEnvUpRec (FillUEnvAp1 (FillUEnvLowRec fill2))) = SynAp (UEnvUpFillTyping syn-in1 fill1 syn syn-in2 fill2) mt mn ana m
  -- UEnvUpFillTyping syn-in1 (FillUEnvUpRec (FillUEnvAp1 (FillUEnvLowRec fill1))) (SynApFail syn mt mn ana m) syn-in2 (FillUEnvUpRec (FillUEnvAp1 (FillUEnvLowRec fill2))) = SynApFail (UEnvUpFillTyping syn-in1 fill1 syn syn-in2 fill2) mt mn ana m
  -- UEnvUpFillTyping syn-in1 (FillUEnvUpRec (FillUEnvAp2 fill1)) (SynAp syn mt mn ana m) syn-in2 (FillUEnvUpRec (FillUEnvAp2 fill2)) = SynAp syn mt mn (UEnvLowFillTyping syn-in1 fill1 ana syn-in2 fill2) m
  -- UEnvUpFillTyping syn-in1 (FillUEnvUpRec (FillUEnvAp2 fill1)) (SynApFail syn mt mn ana m) syn-in2 (FillUEnvUpRec (FillUEnvAp2 fill2)) = SynApFail syn mt mn (UEnvLowFillTyping syn-in1 fill1 ana syn-in2 fill2) m
  -- UEnvUpFillTyping syn-in1 (FillUEnvUpRec (FillUEnvAsc fill1)) (SynAsc ana m) syn-in2 (FillUEnvUpRec (FillUEnvAsc fill2)) = SynAsc (UEnvLowFillTyping syn-in1 fill1 ana syn-in2 fill2) m

  -- merge-syn-consist : ∀ {t n syn syn'} ->
  --   MergeSyn (t , n) syn syn' ->
  --   (t , Old) ▷ syn'
  -- merge-syn-consist MergeSynVoid = MergeInfoOld
  -- merge-syn-consist (MergeSynMerge (MergeInfoType _)) = MergeInfoOld

  -- merge-ana-consist : ∀ {t n ana ana'} ->
  --   MergeAna (t , n) ana ana' ->
  --   (t , Old) ▷ ana'
  -- merge-ana-consist MergeAnaVoid = MergeInfoOld
  -- merge-ana-consist (MergeAnaMerge (MergeInfoType _)) = MergeInfoOld

  -- oldify-syn : ∀ {Γ t n e} ->
  --   Γ ⊢ EUp (⇑ (t , n)) e ⇒ ->
  --   Γ ⊢ EUp (⇑ (t , Old)) e ⇒
  -- oldify-syn (SynConst (SynConsistMerge MergeInfoOld)) = SynConst (SynConsistMerge MergeInfoOld)
  -- oldify-syn (SynHole (SynConsistMerge MergeInfoOld)) = SynHole (SynConsistMerge MergeInfoOld)

  -- freshen-ana : ∀ {Γ ana m e t n ana'} ->
  --   Γ ⊢ ELow ana m e ⇐ ->
  --   MergeAna (t , n) ana ana' ->
  --   Γ ⊢ ELow (⇓ ana') m e ⇐
  -- freshen-ana () merge

  -- oldify-ntmatch : ∀ {t n t1 t2 m n1 n2 n3} ->
  --   (t , n) ▸NTArrow (t1 , n1) , (t2 , n2) , (m , n3) ->
  --   (t , Old) ▸NTArrow (t1 , Old) , (t2 , Old) , (m , MarkOld)
  -- oldify-ntmatch (MNTArrowOldMatch m) = MNTArrowOldMatch m
  -- oldify-ntmatch (MNTArrowOldNoMatch m) = MNTArrowOldNoMatch m
  -- oldify-ntmatch (MNTArrowNewMatch m) = MNTArrowOldMatch m
  -- oldify-ntmatch (MNTArrowNewNoMatch m) = MNTArrowOldNoMatch m
  -- oldify-ntmatch MNTArrowArrow = MNTArrowOldMatch MArrowArrow

  PreservationStepSyn :  
    ∀ {Γ e e'} ->
    (Γ ⊢ e ⇒) ->
    (e U↦ e') ->   
    (Γ ⊢ e' ⇒)
  PreservationStepSyn = {!   !}
  -- PreservationStepSyn (SynConst x) ()
  -- PreservationStepSyn (SynHole x) ()
  -- PreservationStepSyn 
  --   (SynAp (SynArrowSome match1) syncon anacon markcon wtsyn wtana) 
  --   (StepAp {t1 = (t3 , n3)} {t2 = (t4 , n4)} isnew match2 mergesyn mergeana) 
  --   = SynAp (SynArrowSome (oldify-ntmatch match2)) (SynConsistMerge (merge-syn-consist mergesyn)) (AnaConsistMerge (merge-ana-consist mergeana)) MarkConsistOld (oldify-syn wtsyn) (freshen-ana wtana mergeana)
  -- PreservationStepSyn 
  --   (SynAsc syncon anacon wtana) 
  --   (StepAsc isnew mergesyn mergeana) 
  --   = SynAsc (SynConsistMerge (merge-syn-consist mergesyn)) (AnaConsistMerge (merge-ana-consist mergeana)) (freshen-ana wtana mergeana)

  -- PreservationStepAna :  
  --   ∀ {Γ e e' t} ->
  --   (Γ ⊢ e ⇐ t) ->
  --   (e L↦ e') ->   
  --   (Γ ⊢ e' ⇐ t)
  -- PreservationStepAna ana step = {!   !}

  -- it's not quite this, because syn cannot be some while syn' is none.
  step-syn-consist : ∀ {e e' syn syn'} -> 
    (e ⇒ syn) U↦ (e' ⇒ syn') -> 
    ▷D syn' syn 
  step-syn-consist = {!   !}

  PreservationAna :  
    ∀ {Γ e e'} ->
    (Γ ⊢ e ⇐) ->
    (e Low↦ e') ->   
    (Γ ⊢ e' ⇐)
  PreservationAna = {!   !}

  -- these holes are not set up right. rethink arguments to Syn constructors. Use decidable function version of matched arrow, e.g.
  PreservationSyn :  
    ∀ {Γ e e'} ->
    (Γ ⊢ e ⇒) ->
    (e Up↦ e') ->   
    (Γ ⊢ e' ⇒)
  PreservationSyn syn (StepUp FillU⊙ step FillU⊙) = PreservationStepSyn syn step
  PreservationSyn (SynConst _) (StepUp (FillUEnvUpRec ()) step (FillUEnvUpRec fill2))
  PreservationSyn (SynHole _) (StepUp (FillUEnvUpRec ()) step (FillUEnvUpRec fill2))
  PreservationSyn (SynFun consist syn) (StepUp (FillUEnvUpRec (FillUEnvFun (FillUEnvLowRec FillU⊙))) step (FillUEnvUpRec (FillUEnvFun (FillUEnvLowRec {e' = e' ⇒ syn'} FillU⊙)))) 
    = SynFun {!   !} (PreservationSyn syn (StepUp FillU⊙ step FillU⊙))

  PreservationSyn (SynFun consist syn) (StepUp (FillUEnvUpRec (FillUEnvFun (FillUEnvLowRec (FillUEnvUpRec fill1)))) step (FillUEnvUpRec (FillUEnvFun (FillUEnvLowRec {e' = e' ⇒ syn'} (FillUEnvUpRec fill2))))) = SynFun consist (PreservationSyn syn (StepUp (FillUEnvUpRec fill1) step (FillUEnvUpRec fill2)))
  PreservationSyn (SynAp marrow consist-syn consist-ana consist-mark syn ana) (StepUp {e-in' = e-fun' ⇒ syn-fun'} (FillUEnvUpRec (FillUEnvAp1 (FillUEnvLowRec FillU⊙))) step (FillUEnvUpRec (FillUEnvAp1 (FillUEnvLowRec FillU⊙)))) 
    = SynAp {!   !} consist-syn consist-ana consist-mark (PreservationSyn syn (StepUp FillU⊙ step FillU⊙)) ana

  PreservationSyn (SynAp marrow consist-syn consist-ana consist-mark syn ana) (StepUp {e-in' = e-fun' ⇒ syn-fun'} (FillUEnvUpRec (FillUEnvAp1 (FillUEnvLowRec (FillUEnvUpRec fill1)))) step (FillUEnvUpRec (FillUEnvAp1 (FillUEnvLowRec (FillUEnvUpRec fill2))))) = SynAp marrow consist-syn consist-ana consist-mark (PreservationSyn syn (StepUp (FillUEnvUpRec fill1) step (FillUEnvUpRec fill2))) ana
  PreservationSyn (SynAp marrow consist-syn consist-ana consist-mark syn ana) (StepUp (FillUEnvUpRec (FillUEnvAp2 (FillUEnvLowRec fill1))) step (FillUEnvUpRec (FillUEnvAp2 (FillUEnvLowRec fill2)))) 
    = {!   !}

  PreservationSyn (SynVar _ _ _) (StepUp (FillUEnvUpRec ()) step (FillUEnvUpRec fill2))
  PreservationSyn (SynAsc consist-syn consist-ana ana) (StepUp (FillUEnvUpRec (FillUEnvAsc (FillUEnvLowRec FillU⊙))) step (FillUEnvUpRec (FillUEnvAsc (FillUEnvLowRec FillU⊙)))) = SynAsc consist-syn consist-ana (PreservationAna ana (StepUp (FillUEnvLowRec FillU⊙) step (FillUEnvLowRec FillU⊙)))
  PreservationSyn (SynAsc consist-syn consist-ana ana) (StepUp (FillUEnvUpRec (FillUEnvAsc (FillUEnvLowRec (FillUEnvUpRec fill1)))) step (FillUEnvUpRec (FillUEnvAsc (FillUEnvLowRec (FillUEnvUpRec fill2))))) = SynAsc consist-syn consist-ana (PreservationAna ana (StepUp (FillUEnvLowRec (FillUEnvUpRec fill1)) step (FillUEnvLowRec (FillUEnvUpRec fill2))))
  PreservationSyn syn (StepLow x x₁ x₂) = {!   !}

  -- PreservationSyn syn (StepUp FillU⊙ step FillU⊙) = PreservationStepSyn syn step
  -- PreservationSyn (SynFun syn x x₁) (StepUp (FillUEnvUpRec (FillUEnvFun (FillUEnvLowRec fill1))) step (FillUEnvUpRec (FillUEnvFun (FillUEnvLowRec fill2)))) = SynFun (PreservationSyn syn (StepUp fill1 step fill2)) x x₁
  -- PreservationSyn (SynFunVoid syn) (StepUp (FillUEnvUpRec (FillUEnvFun (FillUEnvLowRec fill1))) step (FillUEnvUpRec (FillUEnvFun (FillUEnvLowRec fill2)))) = SynFunVoid (PreservationSyn syn (StepUp fill1 step fill2))
  -- PreservationSyn (SynAp syn x x₁ x₂ x₃) (StepUp (FillUEnvUpRec (FillUEnvAp1 (FillUEnvLowRec fill1))) step (FillUEnvUpRec (FillUEnvAp1 (FillUEnvLowRec fill2)))) = SynAp (PreservationSyn syn (StepUp fill1 step fill2)) x x₁ x₂ x₃
  -- PreservationSyn (SynApFail syn x x₁ x₂ x₃) (StepUp (FillUEnvUpRec (FillUEnvAp1 (FillUEnvLowRec fill1))) step (FillUEnvUpRec (FillUEnvAp1 (FillUEnvLowRec fill2)))) = SynApFail (PreservationSyn syn (StepUp fill1 step fill2)) x x₁ x₂ x₃
  -- PreservationSyn (SynAp syn x x₁ ana x₃) (StepUp (FillUEnvUpRec (FillUEnvAp2 fill1)) step (FillUEnvUpRec (FillUEnvAp2 fill2))) = SynAp syn x x₁ (PreservationAna ana (StepUp fill1 step fill2)) x₃
  -- PreservationSyn (SynApFail syn x x₁ ana x₃) (StepUp (FillUEnvUpRec (FillUEnvAp2 fill1)) step (FillUEnvUpRec (FillUEnvAp2 fill2))) = SynApFail syn x x₁ (PreservationAna ana (StepUp fill1 step fill2)) x₃
  -- PreservationSyn (SynAsc ana m) (StepUp (FillUEnvUpRec (FillUEnvAsc fill1)) step (FillUEnvUpRec (FillUEnvAsc fill2))) = SynAsc (PreservationAna ana (StepUp fill1 step fill2)) m
  -- PreservationSyn (SynFun (SynFunVoid syn) x x₁) (StepLow (FillLEnvUpRec (FillLEnvFun FillL⊙)) () (FillLEnvUpRec (FillLEnvFun FillL⊙)))
  -- PreservationSyn (SynFun syn x x₁) (StepLow (FillLEnvUpRec (FillLEnvFun (FillLEnvLowRec fill1))) step (FillLEnvUpRec (FillLEnvFun (FillLEnvLowRec fill2)))) = SynFun (PreservationSyn syn (StepLow fill1 step fill2)) x x₁
  -- PreservationSyn (SynFunVoid ()) (StepLow {e-in' = ELow _ _ _} (FillLEnvUpRec (FillLEnvFun FillL⊙)) StepNoAnaFun (FillLEnvUpRec (FillLEnvFun FillL⊙)))
  -- PreservationSyn (SynFunVoid syn) (StepLow (FillLEnvUpRec (FillLEnvFun (FillLEnvLowRec fill1))) step (FillLEnvUpRec (FillLEnvFun (FillLEnvLowRec fill2)))) = SynFunVoid (PreservationSyn syn (StepLow fill1 step fill2))
  -- PreservationSyn (SynAp () x x₁ ana x₃) (StepLow (FillLEnvUpRec (FillLEnvAp1 FillL⊙)) StepNoAnaFun (FillLEnvUpRec (FillLEnvAp1 FillL⊙))) 
  -- PreservationSyn (SynAp syn x x₁ ana x₃) (StepLow (FillLEnvUpRec (FillLEnvAp1 (FillLEnvLowRec fill1))) step (FillLEnvUpRec (FillLEnvAp1 (FillLEnvLowRec fill2)))) = SynAp (PreservationSyn syn (StepLow fill1 step fill2)) x x₁ ana x₃
  -- PreservationSyn (SynApFail () x x₁ ana x₃) (StepLow (FillLEnvUpRec (FillLEnvAp1 FillL⊙)) StepNoAnaFun (FillLEnvUpRec (FillLEnvAp1 FillL⊙)))  
  -- PreservationSyn (SynApFail syn x x₁ ana x₃) (StepLow (FillLEnvUpRec (FillLEnvAp1 (FillLEnvLowRec fill1))) step (FillLEnvUpRec (FillLEnvAp1 (FillLEnvLowRec fill2)))) = SynApFail (PreservationSyn syn (StepLow fill1 step fill2)) x x₁ ana x₃
  -- PreservationSyn (SynAp syn x x₁ ana x₃) (StepLow (FillLEnvUpRec (FillLEnvAp2 fill1)) step (FillLEnvUpRec (FillLEnvAp2 fill2))) = SynAp syn x x₁ (PreservationAna ana (StepLow fill1 step fill2)) x₃
  -- PreservationSyn (SynApFail syn x x₁ ana m) (StepLow (FillLEnvUpRec (FillLEnvAp2 fill1)) step (FillLEnvUpRec (FillLEnvAp2 fill2))) = SynApFail syn x x₁ (PreservationAna ana (StepLow fill1 step fill2)) m
  -- PreservationSyn (SynAsc ana m) (StepLow (FillLEnvUpRec (FillLEnvAsc fill1)) step (FillLEnvUpRec (FillLEnvAsc fill2))) = SynAsc (PreservationAna ana (StepLow fill1 step fill2)) m        