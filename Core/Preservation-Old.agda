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
open import Core.Settled
open import Core.Lemmas-Context
open import Core.Lemmas-WellTyped

module Core.Preservation where

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

  -- Thing : 
  --   ∀ {Γ ana1 m1 e1 ana2 m2 e2 t n} ->
  --   (Γ ⊢ e1 ⇒ (t , n)) -> 
  --   (ELow ana1 m1 e1 L↦ ELow ana2 m2 e2) -> 
  --   ∃[ n' ] (Γ ⊢ e2 ⇒ (t , n'))
  -- Thing (SynConst MergeInfoOld) (StepNewSynConsist x x₁) = Old , SynConst MergeInfoOld
  -- Thing (SynHole MergeInfoOld) (StepNewSynConsist x x₁) = Old , SynHole MergeInfoOld
  -- Thing (SynFun syn x₂ m) (StepNewSynConsist x x₁) with oldify-merge m 
  -- ... | n , m' = _ , SynFun syn x₂ m'
  -- Thing (SynAp syn x₂ x₃ x₄ m) (StepNewSynConsist x x₁) with oldify-merge m 
  -- ... | n , m' = _ , SynAp syn x₂ x₃ x₄ m'
  -- Thing (SynApFail syn x₂ x₃ x₄ m) (StepNewSynConsist x x₁) with oldify-merge m 
  -- ... | n , m' = _ , SynApFail syn x₂ x₃ x₄ m'
  -- Thing (SynVar x₂ m) (StepNewSynConsist x x₁) with oldify-merge m 
  -- ... | n , m' = _ , SynVar x₂ m'
  -- Thing (SynVarFail x₂ m) (StepNewSynConsist x x₁) with oldify-merge m 
  -- ... | n , m' = _ , SynVarFail x₂ m'
  -- Thing (SynAsc x₂ m) (StepNewSynConsist x x₁) with oldify-merge m 
  -- ... | n , m' = _ , SynAsc x₂ m'
  -- Thing (SynConst MergeInfoOld) (StepNewSynInconsist x x₁) = Old , SynConst MergeInfoOld
  -- Thing (SynHole MergeInfoOld) (StepNewSynInconsist x x₁) = Old , SynHole MergeInfoOld
  -- Thing (SynFun syn x₂ m) (StepNewSynInconsist x x₁) with oldify-merge m 
  -- ... | n , m' = _ , SynFun syn x₂ m'
  -- Thing (SynAp syn x₂ x₃ x₄ m) (StepNewSynInconsist x x₁) with oldify-merge m 
  -- ... | n , m' = _ , SynAp syn x₂ x₃ x₄ m'
  -- Thing (SynApFail syn x₂ x₃ x₄ m) (StepNewSynInconsist x x₁) with oldify-merge m 
  -- ... | n , m' = _ , SynApFail syn x₂ x₃ x₄ m'
  -- Thing (SynVar x₂ m) (StepNewSynInconsist x x₁) with oldify-merge m 
  -- ... | n , m' = _ , SynVar x₂ m'
  -- Thing (SynVarFail x₂ m) (StepNewSynInconsist x x₁) with oldify-merge m 
  -- ... | n , m' = _ , SynVarFail x₂ m'
  -- Thing (SynAsc x₂ m) (StepNewSynInconsist x x₁) with oldify-merge m 
  -- ... | n , m' = _ , SynAsc x₂ m'
  -- Thing (SynConst MergeInfoOld) (StepNewAnaConsist _ x x₁) = Old , SynConst MergeInfoOld
  -- Thing (SynHole MergeInfoOld) (StepNewAnaConsist _ x x₁) = Old , SynHole MergeInfoOld
  -- Thing (SynFun syn x₂ m) (StepNewAnaConsist _ x x₁) with oldify-merge m 
  -- ... | n , m' = _ , SynFun syn x₂ m'
  -- Thing (SynAp syn x₂ x₃ x₄ m) (StepNewAnaConsist _ x x₁) with oldify-merge m 
  -- ... | n , m' = _ , SynAp syn x₂ x₃ x₄ m'
  -- Thing (SynApFail syn x₂ x₃ x₄ m) (StepNewAnaConsist _ x x₁) with oldify-merge m 
  -- ... | n , m' = _ , SynApFail syn x₂ x₃ x₄ m'
  -- Thing (SynVar x₂ m) (StepNewAnaConsist _ x x₁) with oldify-merge m 
  -- ... | n , m' = _ , SynVar x₂ m'
  -- Thing (SynVarFail x₂ m) (StepNewAnaConsist _ x x₁) with oldify-merge m 
  -- ... | n , m' = _ , SynVarFail x₂ m'
  -- Thing (SynAsc x₂ m) (StepNewAnaConsist _ x x₁) with oldify-merge m 
  -- ... | n , m' = _ , SynAsc x₂ m'
  -- Thing (SynConst MergeInfoOld) (StepNewAnaInconsist _ x x₁) = Old , SynConst MergeInfoOld
  -- Thing (SynHole MergeInfoOld) (StepNewAnaInconsist _ x x₁) = Old , SynHole MergeInfoOld
  -- Thing (SynFun syn x₂ m) (StepNewAnaInconsist _ x x₁) with oldify-merge m 
  -- ... | n , m' = _ , SynFun syn x₂ m'
  -- Thing (SynAp syn x₂ x₃ x₄ m) (StepNewAnaInconsist _ x x₁) with oldify-merge m 
  -- ... | n , m' = _ , SynAp syn x₂ x₃ x₄ m'
  -- Thing (SynApFail syn x₂ x₃ x₄ m) (StepNewAnaInconsist _ x x₁) with oldify-merge m 
  -- ... | n , m' = _ , SynApFail syn x₂ x₃ x₄ m'
  -- Thing (SynVar x₂ m) (StepNewAnaInconsist _ x x₁) with oldify-merge m 
  -- ... | n , m' = _ , SynVar x₂ m'
  -- Thing (SynVarFail x₂ m) (StepNewAnaInconsist _ x x₁) with oldify-merge m 
  -- ... | n , m' = _ , SynVarFail x₂ m'
  -- Thing (SynAsc x₂ m) (StepNewAnaInconsist _ x x₁) with oldify-merge m 
  -- ... | n , m' = _ , SynAsc x₂ m'
  -- Thing (SynFun syn x₄ x₅) (StepAnaFun x x₁ x₂ x₃) = {!   !}
  -- Thing (SynFunVoid syn) (StepAnaFun x x₁ x₂ x₃) = {!   !}
  -- Thing syn (StepAnaFunFail1 x x₁ x₂ x₃) = {!   !}

  -- Silly : 
  --   ∀ {Γ syn e1 t n e2} ->
  --   (Γ ⊢ EUp syn e1 ⇒ (t , n)) -> 
  --   (e1 L↦ e2) -> 
  --   ∃[ n' ] (Γ ⊢ EUp syn e2 ⇒ (t , n'))
  -- Silly syn step = ?



  -- the classification is not true - it only works on a part-by-part basis

  -- data SynClass (Γ : Ctx) (t1 : Type) (n1 : Newness) (t2 : Type) (n2 : Newness) (e : ExpMid) : Set where 
  --   UpToDate : t1 ≡ t2 -> n1 ≡ n2 -> SynClass Γ t1 n1 t2 n2 e
  --   OutOfDate : (∀ {t1' n1' t2' n2'} -> (Γ ⊢ EUp (⇑ (t1' , n1')) e ⇒ (t2' , n2')) -> (t1 ≡ t2) × (n1 ≡ n2)) -> SynClass Γ t1 n1 t2 n2 e

  -- classify-syn : 
  --   ∀ {Γ e t1 t2 n1 n2} ->
  --   (Γ ⊢ EUp (⇑ (t1 , n1)) e ⇒ (t2 , n2)) ->
  --   SynClass Γ t1 n1 t2 n2 e
  -- classify-syn (SynConst (MergeSynMerge MergeInfoOld)) = UpToDate refl refl
  -- classify-syn (SynHole (MergeSynMerge MergeInfoOld)) = UpToDate refl refl
  -- classify-syn (SynFun {n1 = Old} {n2 = Old} syn refl (MergeSynMerge MergeInfoOld)) = UpToDate refl refl
  -- classify-syn (SynFun {n1 = New} {n2 = Old} syn refl (MergeSynMerge (MergeInfoArrow nm MergeInfoNew MergeInfoOld refl))) = {!   !}
  -- classify-syn (SynFun {n1 = NArrow n1 n2} {n2 = Old} syn refl (MergeSynMerge (MergeInfoArrow nm m1 m2 refl))) = {!   !}
  -- classify-syn (SynFun {n2 = New} syn refl (MergeSynMerge m)) = {!   !}
  -- classify-syn (SynFun {n2 = NArrow n2 n3} syn refl (MergeSynMerge m)) = {!   !}
  -- classify-syn (SynAp syn x x₁ x₂ x₃) = {!   !}
  -- classify-syn (SynApFail syn x x₁ x₂ x₃) = {!   !}
  -- classify-syn (SynVar x x₁) = {!   !}
  -- classify-syn (SynVarFail x x₁) = {!   !}
  -- classify-syn (SynAsc x x₁) = {!   !}

  -- oldify-syn : 
  --   ∀ {Γ e t1 t2 n1 n2} ->
  --   (Γ ⊢ EUp (⇑ (t1 , n1)) e ⇒ (t2 , n2)) ->
  --   ∃[ n3 ] (Γ ⊢ EUp (⇑ (t1 , Old)) e ⇒ (t2 , n3)) 
  -- oldify-syn (SynConst (MergeSynMerge m)) with oldify-merge m 
  -- ... | n , m' = n , SynConst (MergeSynMerge m')
  -- oldify-syn (SynHole (MergeSynMerge m)) with oldify-merge m 
  -- ... | n , m' = n , SynHole (MergeSynMerge m')
  -- oldify-syn (SynFun syn x (MergeSynMerge m)) with oldify-merge m 
  -- ... | n , m' = n , SynFun syn x (MergeSynMerge m')
  -- oldify-syn (SynAp syn x x₁ ana (MergeSynMerge m)) with oldify-merge m 
  -- ... | n , m' = n , SynAp syn x x₁ ana (MergeSynMerge m')
  -- oldify-syn (SynApFail syn x x₁ ana (MergeSynMerge m)) with oldify-merge m 
  -- ... | n , m' = n , SynApFail syn x x₁ ana (MergeSynMerge m')
  -- oldify-syn (SynVar x (MergeSynMerge m)) with oldify-merge m 
  -- ... | n , m' = n , SynVar x (MergeSynMerge m')
  -- oldify-syn (SynVarFail x (MergeSynMerge m)) with oldify-merge m 
  -- ... | n , m' = n , SynVarFail x (MergeSynMerge m')
  -- oldify-syn (SynAsc x (MergeSynMerge m)) with oldify-merge m 
  -- ... | n , m' = n , SynAsc x (MergeSynMerge m')

  merge-syn-lemma :
      ∀ {syn syn1 syn2 t n} ->
    MergeSyn syn (t , n) syn1 ->
    MergeSyn syn (t , n) syn2 ->
    MergeInfo syn2 (t , Old) syn1
  merge-syn-lemma MergeSynVoid MergeSynVoid = MergeInfoOld
  merge-syn-lemma (MergeSynMerge MergeInfoNew) (MergeSynMerge MergeInfoNew) = MergeInfoOld
  merge-syn-lemma (MergeSynMerge MergeInfoOld) (MergeSynMerge MergeInfoOld) = MergeInfoOld
  merge-syn-lemma (MergeSynMerge (MergeInfoArrow nm1 m1 m2 na1)) (MergeSynMerge (MergeInfoArrow nm2 m3 m4 na2)) 
    with ▸NArrow-unicity nm1 nm2 | na1 | na2 | merge-same m1 | merge-same m2 | merge-same m3 | merge-same m4
  ... | refl , refl | refl | refl | refl | refl | refl | refl with merge-unicity m1 m3 | merge-unicity m2 m4 
  ... | refl | refl = MergeInfoOld

  merge-ana-lemma :
      ∀ {ana ana1 ana2 t n} ->
    MergeAna ana (t , n) ana1 ->
    MergeAna ana (t , n) ana2 ->
    MergeInfo ana2 (t , Old) ana1
  merge-ana-lemma MergeAnaVoid MergeAnaVoid = MergeInfoOld
  merge-ana-lemma (MergeAnaMerge MergeInfoNew) (MergeAnaMerge MergeInfoNew) = MergeInfoOld
  merge-ana-lemma (MergeAnaMerge MergeInfoOld) (MergeAnaMerge MergeInfoOld) = MergeInfoOld
  merge-ana-lemma (MergeAnaMerge (MergeInfoArrow nm1 m1 m2 na1)) (MergeAnaMerge (MergeInfoArrow nm2 m3 m4 na2)) 
    with ▸NArrow-unicity nm1 nm2 | na1 | na2 | merge-same m1 | merge-same m2 | merge-same m3 | merge-same m4
  ... | refl , refl | refl | refl | refl | refl | refl | refl with merge-unicity m1 m3 | merge-unicity m2 m4 
  ... | refl | refl = MergeInfoOld


  update-ana-lemma : 
    ∀ {Γ ana ana' m e t n} ->
    Γ ⊢ ELow ana m e ⇐ (t , n) ->
    MergeAna ana (t , n) ana' ->
    Γ ⊢ ELow (⇓ ana') m e ⇐ (t , Old)
  update-ana-lemma (AnaSubsume x x₁ x₂ x₃) m = AnaSubsume (MergeAnaMerge (merge-ana-lemma x m)) x₁ x₂ x₃
  update-ana-lemma (AnaSubsumeFail x x₁ x₂ x₃) m = AnaSubsumeFail (MergeAnaMerge (merge-ana-lemma x m)) x₁ x₂ x₃
  update-ana-lemma (AnaFun x x₁ x₂ ana x₃) m = AnaFun (MergeAnaMerge (merge-ana-lemma x m)) x₁ x₂ ana x₃
  update-ana-lemma (AnaFunFail1 x x₁ x₂ ana x₃) m = AnaFunFail1 (MergeAnaMerge (merge-ana-lemma x m)) x₁ x₂ ana x₃
  update-ana-lemma (AnaFunFail2 x x₁ x₂ x₃) m = AnaFunFail2 (merge-ana-lemma (MergeAnaMerge x) m) x₁ x₂ x₃

  PreservationStepSyn :  
    ∀ {Γ e e' t} ->
    (Γ ⊢ e ⇒ t) ->
    (e U↦ e') ->   
    (Γ ⊢ e' ⇒ t)
  PreservationStepSyn (SynUp SynConst m1) ()
  PreservationStepSyn (SynUp SynHole m1) ()
  PreservationStepSyn (SynUp (SynFun x x₁) m1) (StepNewAnnFun1 x₂ x₃) = {!   !}
  PreservationStepSyn (SynUp (SynFun x x₁) m1) (StepNewAnnFun2 x₂ x₃ x₄) = {!   !}


  -- this is one to focus on, methinks
  PreservationStepSyn (SynUp (SynFun (SynUp syn m1) refl) m2) (StepNewSynFun n m3) = 
      SynUp (SynFun (SynUp syn {!   !}) refl) {!   !}


  PreservationStepSyn (SynUp (SynFun syn refl) m1) StepVoidSynFun = {!   !}
  PreservationStepSyn (SynUp (SynAp x x₁ x₂ x₃) m1) (StepAp x₄ x₅ x₆ x₇ x₈) = {!   !}
  PreservationStepSyn (SynUp (SynAp x x₁ x₂ x₃) m1) (StepApFail x₄ x₅ x₆ x₇ x₈) = {!   !}
  PreservationStepSyn (SynUp (SynApFail x x₁ x₂ x₃) m1) (StepAp x₄ x₅ x₆ x₇ x₈) = {!   !}
  PreservationStepSyn (SynUp (SynApFail x x₁ x₂ x₃) m1) (StepApFail x₄ x₅ x₆ x₇ x₈) = {!   !}
  PreservationStepSyn (SynUp (SynVar x) m1) ()
  PreservationStepSyn (SynUp (SynVarFail x) m1) ()
  PreservationStepSyn (SynUp (SynAsc ana) m1) (StepAsc _ m2 m3) = SynUp (SynAsc (update-ana-lemma ana m3)) (MergeSynMerge (merge-syn-lemma m1 m2))

  -- PreservationStepSyn :  
  --   ∀ {Γ e e' t} ->
  --   (Γ ⊢ e ⇒ t) ->
  --   (e U↦ e') ->   
  --   (Γ ⊢ e' ⇒ t)
  -- PreservationStepSyn (SynFun syn x x₁) (StepNewAnnFun1 x₂ x₃) = {!   !}

  -- PreservationStepSyn (SynFun syn refl m1) (StepNewSynFun n m2) with oldify-syn syn
  -- ... | n' , syn' = SynFun syn' refl {!   !}

  -- PreservationStepSyn (SynFun {n2 = Old} syn refl MergeSynVoid) (StepNewSynFun n MergeSynVoid) with oldify-syn syn
  -- ... | _ , syn' = SynFun syn' refl (MergeSynMerge {!  !})
  -- PreservationStepSyn (SynFun {n2 = New} syn refl MergeSynVoid) (StepNewSynFun n m) with oldify-syn syn
  -- ... | _ , syn' = SynFun syn' refl (MergeSynMerge {!  !})
  -- PreservationStepSyn (SynFun {n2 = NArrow n2 n3} syn refl MergeSynVoid) (StepNewSynFun n m) = {!   !} --SynFun {!   !} {!   !} (MergeSynMerge {!   !})
  -- PreservationStepSyn (SynFun {n2 = n2} syn refl m1) (StepNewSynFun n m2) = {!   !} 
  
  -- PreservationStepSyn (SynFun syn x x₁) StepVoidSynFun = {!   !}
  -- PreservationStepSyn (SynFun syn x x₁) (StepNewAnnFun2 x₂ x₃ x₄) = {!   !}
  -- PreservationStepSyn {e = EUp syn-info (EAp (ELow ̸⇓ Unmarked (EUp (⇑ (t , nw)) e1)) Unmarked (ELow ana-info mark e2))} 
  --   (SynAp {n = n} syn mt1 mn1 ana m) (StepAp is-new mt2 mn2 m1 m2) with oldify-syn syn | n | mn1 | m
  -- ... | _ , syn' | Old | MNArrowOld | MergeSynVoid = SynAp syn' mt1 {!   !} {!   !} {!   !}
  -- ... | _ , syn' | Old | MNArrowOld | MergeSynMerge x = {!   !}
  -- ... | _ , syn' | New | MNArrowNew | MergeSynVoid = {!   !}
  -- ... | _ , syn' | New | MNArrowNew | MergeSynMerge x = {!   !}
  -- ... | _ , syn' | NArrow n₁ n₂ | MNArrowArrow | MergeSynVoid = {!   !}
  -- ... | _ , syn' | NArrow n₁ n₂ | MNArrowArrow | MergeSynMerge x = {!   !}
  
  -- -- = SynAp syn' mt1 {!   !} (update-ana-lemma ana {!   !}) {!   !}
  -- PreservationStepSyn (SynAp syn x x₁ x₂ x₃) (StepApFail x₄ x₅ x₆ m1 m2) = {!   !}
  -- PreservationStepSyn (SynApFail syn x x₁ x₂ x₃) (StepAp x₄ x₅ x₆ m1 m2) = {!   !}
  -- PreservationStepSyn (SynApFail syn x x₁ x₂ x₃) (StepApFail x₄ x₅ x₆ m1 m2) = {!   !}
  -- PreservationStepSyn (SynAsc ana m) (StepAsc _ m1 m2) = SynAsc (update-ana-lemma ana m2) (MergeSynMerge (merge-syn-lemma m m1))

  -- PreservationStepAna :  
  --   ∀ {Γ e e' t} ->
  --   (Γ ⊢ e ⇐ t) ->
  --   (e L↦ e') ->   
  --   (Γ ⊢ e' ⇐ t)
  -- PreservationStepAna ana step = {!   !}

  PreservationAna :  
    ∀ {Γ e e' t} ->
    (Γ ⊢ e ⇐ t) ->
    (e Low↦ e') ->   
    (Γ ⊢ e' ⇐ t)
  PreservationAna = {!   !}

  -- PreservationSyn :  
  --   ∀ {Γ e e' t} ->
  --   (Γ ⊢ e ⇒ t) ->
  --   (e Up↦ e') ->   
  --   (Γ ⊢ e' ⇒ t)
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