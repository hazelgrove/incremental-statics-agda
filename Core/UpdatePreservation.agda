open import Data.Nat hiding (_+_; _⊓_)
open import Data.Unit 
open import Data.Empty 
open import Data.Bool hiding (_<_; _≟_)
open import Data.Sum renaming (_⊎_ to _+_; inj₁ to Inl ; inj₂ to Inr) hiding (map)
open import Data.Product hiding (map)
open import Relation.Nullary 
open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Prelude

open import Core.Core
open import Core.Environment
open import Core.WellTyped
open import Core.VarsSynthesize
open import Core.Update
open import Core.Lemmas-Preservation

module Core.UpdatePreservation where

  beyond-u↦ : ∀ {e e' syn syn'} -> 
    (e ⇒ syn) u↦ (e' ⇒ syn') -> 
    =▷ syn syn' 
  beyond-u↦ (StepAp _) = =▷New
  beyond-u↦ StepAsc = =▷New

  beyond-u↦-env : ∀ {ε e e' e-in e-in' syn syn'} -> 
    e-in u↦ e-in' -> 
    ε U⟦ e-in ⟧U≡ (e ⇒ syn) ->
    ε U⟦ e-in' ⟧U≡ (e' ⇒ syn') ->
    =▷ syn syn' 
  beyond-u↦-env step FillU⊙ FillU⊙ = beyond-u↦ step
  beyond-u↦-env step (FillUEnvUpRec _) (FillUEnvUpRec _) = =▷Refl

  beyond-l↦ : ∀ {e e' m m' ana ana'} -> 
    (e [ m ]⇐ ana) l↦ (e' [ m' ]⇐ ana') -> 
    ◁▷ ana ana' 
  beyond-l↦ (StepNewSynConsist _) = ◁▷C
  beyond-l↦ (StepNewAnaConsist _ _) = ◁▷C
  beyond-l↦ (StepAnaFun _ _) = ◁▷C
  beyond-l↦ (StepSynFun) = ◁▷C
  beyond-l↦ (StepNewAnnFun _ _ _) = ◁▷C

  beyond-l↦-inner : ∀ {e e' syn syn' m m' n-ana ana'} -> 
    ((e ⇒ syn) [ m ]⇐ (□ , n-ana)) l↦ ((e' ⇒ syn') [ m' ]⇐ ana') -> 
    =▷ syn syn' 
  beyond-l↦-inner (StepNewAnaConsist _ _) = =▷Refl
  beyond-l↦-inner (StepAnaFun _ _) = =▷New
  beyond-l↦-inner (StepNewAnnFun _ _ _) = =▷New
  beyond-l↦-inner StepSynFun = =▷New

  beyond-l↦-env-inner : ∀ {ε e e' e-in e-in' syn syn' m m' n-ana ana'} -> 
    e-in l↦ e-in' -> 
    ε L⟦ e-in ⟧L≡ ((e ⇒ syn) [ m ]⇐ (□ , n-ana)) ->
    ε L⟦ e-in' ⟧L≡ ((e' ⇒ syn') [ m' ]⇐ ana') ->
    =▷ syn syn' 
  beyond-l↦-env-inner step FillL⊙ FillL⊙ = beyond-l↦-inner step
  beyond-l↦-env-inner step (FillLEnvLowRec (FillLEnvUpRec _)) (FillLEnvLowRec (FillLEnvUpRec _)) = =▷Refl

  beyond-l↦-env : ∀ {ε e e' e-in e-in' m m' ana ana'} -> 
    e l↦ e' -> 
    ε L⟦ e ⟧L≡ (e-in [ m ]⇐ ana) ->
    ε L⟦ e' ⟧L≡ (e-in' [ m' ]⇐ ana') ->
    ◁▷ ana ana' 
  beyond-l↦-env step FillL⊙ FillL⊙ = beyond-l↦ step
  beyond-l↦-env step (FillLEnvLowRec _) (FillLEnvLowRec _) = ◁▷C

  void-ana-step-same : ∀ {e n e' m t n'} ->
    (e [ ✔ ]⇐ (□ , n)) l↦ (e' [ m ]⇐ (t , n')) -> 
    (m ≡ ✔) × (t ≡ □)
  void-ana-step-same (StepNewAnaConsist x ~DVoidL) = refl , refl
  void-ana-step-same (StepNewAnaConsist x ~DVoidR) = refl , refl
  void-ana-step-same (StepAnaFun _ _) = refl , refl
  void-ana-step-same (StepNewAnnFun _ _ _) = refl , refl
  void-ana-step-same StepSynFun = refl , refl

  step-subsumable : ∀ {e e' syn syn'} -> 
    (e ⇒ syn) u↦ (e' ⇒ syn') ->
    SubsumableMid e -> 
    SubsumableMid e'
  step-subsumable (StepAp _) SubsumableAp = SubsumableAp
  step-subsumable StepAsc SubsumableAsc = SubsumableAsc

  random-helper : ∀ {t t' d n n'} -> ▷ (NUnless (NArrow (t , Old) (t' , n)) (d , n')) (DUnless (DArrow t t') d , New)
  random-helper {d = □} = ▶Same
  random-helper {d = ■ x} = ▶Same

  PreservationStepSyn :  
    ∀ {Γ e e'} ->
    (Γ ⊢ e ⇒) ->
    (e u↦ e') ->   
    (Γ ⊢ e' ⇒)
  PreservationStepSyn (SynConst _) ()
  PreservationStepSyn (SynHole _) ()
  PreservationStepSyn (SynAp marrow consist-syn consist-ana consist-mark syn ana) (StepAp marrow') = SynAp (NTArrowC marrow') (▶Old) (▶Old) ▶Old (oldify-syn-inner syn) (small-newify-ana ana)
  PreservationStepSyn (SynVar _ _) ()
  PreservationStepSyn (SynAsc consist-syn consist-ana ana) StepAsc = SynAsc (▶Old) (▶Old) (small-newify-ana ana)
  
  PreservationStepAna :  
    ∀ {Γ e e'} ->
    (Γ ⊢ e ⇐) ->
    (e l↦ e') ->   
    (Γ ⊢ e' ⇐)
  PreservationStepAna (AnaSubsume subsumable (~N-pair consist-t) consist-m syn) (StepNewSynConsist consist) with consist-t 
  ... | consist-t rewrite ~D-unicity consist consist-t = AnaSubsume subsumable (~N-pair consist-t) ▶Old (oldify-syn syn)
  PreservationStepAna (AnaSubsume subsumable (~N-pair consist-t) consist-m syn) (StepNewAnaConsist subsumable' consist) with ~D-unicity consist consist-t 
  ... | refl = AnaSubsume subsumable' (~N-pair consist-t) ▶Same (oldify-syn syn)
  PreservationStepAna (AnaFun marrow consist consist-ana consist-asc consist-body consist-syn (~N-pair consist-all) consist-m-all ana) (StepNewSynConsist consist') rewrite ~D-unicity consist' consist-all = AnaFun marrow consist consist-ana consist-asc consist-body consist-syn (~N-pair consist-all) ▶Old ana
  PreservationStepAna (AnaFun {t-asc = t-asc , n-asc} (NTArrowC x) consist (▶New) ▶New consist-body consist-syn consist-all consist-m-all ana) (StepAnaFun marrow' (■~D-pair consist')) = AnaFun (NTArrowC marrow') (■~N-pair (~N-pair consist')) (▶Old) ▶Old ▶Same (consist-unless-lemma {n1 = n-asc}) (~N-pair ~D-unless) ▶Same (newify-ana ana)
  PreservationStepAna (AnaFun (NTArrowC {d} {n} marrow) (■~N-pair {t} (~N-pair consist)) consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) (StepNewAnnFun {syn-body' = syn-body'} marrow' (■~D-pair consist') vars-syn)  with ▸DTArrow-unicity marrow marrow' 
  ... | refl , refl , refl with ~D-unicity consist consist' | ~N-dec (DUnless (DArrow t syn-body') d , New) (d , n)
  ... | refl | _ , (~N-pair consist'') = AnaFun (NTArrowC marrow) (■~N-pair (~N-pair consist)) consist-ana consist-asc ▶Same random-helper (~N-pair consist'') ▶New (preservation-vars-ana? ana vars-syn)
  PreservationStepAna (AnaFun {ana-all = ana-all} (NTArrowC {d} marrow) (■~N-pair {t} {n} (~N-pair consist)) (consistm-m-ana) consist-m-ann consist-body consist-syn consist-all consist-m-all ana) (StepSynFun {t-body = t-body}) with ~N-dec (DUnless (DArrow t t-body) d , New) ana-all
  ... | _ , (~N-pair consist'')  = AnaFun (NTArrowC marrow) (■~N-pair (~N-pair consist)) (consistm-m-ana) consist-m-ann consist-body random-helper (~N-pair consist'') ▶New (oldify-syn-inner ana)

  mutual 

    PreservationSyn :  
      ∀ {Γ e e'} ->
      (Γ ⊢ e ⇒) ->
      (e U↦ e') ->   
      (Γ ⊢ e' ⇒)
    PreservationSyn syn (StepUp FillU⊙ step FillU⊙) = PreservationStepSyn syn step
    PreservationSyn (SynConst _) (StepUp (FillUEnvUpRec ()) step (FillUEnvUpRec fill2))
    PreservationSyn (SynConst _) (StepLow (FillLEnvUpRec ()) _ (FillLEnvUpRec _))
    PreservationSyn (SynHole _) (StepUp (FillUEnvUpRec ()) step (FillUEnvUpRec fill2))
    PreservationSyn (SynHole _) (StepLow (FillLEnvUpRec ()) _ (FillLEnvUpRec _))    
    PreservationSyn (SynVar _ _) (StepUp (FillUEnvUpRec ()) step (FillUEnvUpRec fill2))
    PreservationSyn (SynVar _ _) (StepLow (FillLEnvUpRec ()) _ (FillLEnvUpRec _))
    PreservationSyn (SynAp marrow consist-syn consist-ana consist-mark syn ana) (StepUp {e-in' = e-fun' ⇒ syn-fun'} (FillUEnvUpRec (FillUEnvAp1 (FillUEnvLowRec (FillUEnvUpRec fill1)))) step (FillUEnvUpRec (FillUEnvAp1 (FillUEnvLowRec (FillUEnvUpRec fill2))))) = SynAp marrow consist-syn consist-ana consist-mark (PreservationAna syn (StepUp (FillUEnvLowRec (FillUEnvUpRec fill1)) step (FillUEnvLowRec (FillUEnvUpRec fill2)))) ana 
    PreservationSyn (SynAp marrow consist-syn consist-ana consist-mark syn ana) (StepUp {e-in' = e-fun' ⇒ syn-fun'} (FillUEnvUpRec (FillUEnvAp1 (FillUEnvLowRec FillU⊙))) step (FillUEnvUpRec (FillUEnvAp1 (FillUEnvLowRec FillU⊙)))) with ▸NTArrow-dec syn-fun' 
    ... | t-in-fun' , t-out-fun' , m-fun' , marrow' with beyond-▸NTArrow (beyond-u↦ step) marrow marrow' 
    ... | t-in-beyond , t-out-beyond , m-beyond = SynAp marrow' (beyond-▶ t-out-beyond consist-syn) (beyond-▶ t-in-beyond consist-ana) (beyond-▶ m-beyond consist-mark) (PreservationAna syn (StepUp (FillUEnvLowRec FillU⊙) step (FillUEnvLowRec FillU⊙))) ana 
    PreservationSyn (SynAp marrow consist-syn consist-ana consist-mark syn ana) (StepLow (FillLEnvUpRec (FillLEnvAp1 (FillLEnvLowRec (FillLEnvUpRec fill1)))) step (FillLEnvUpRec (FillLEnvAp1 (FillLEnvLowRec (FillLEnvUpRec fill2))))) = SynAp marrow consist-syn consist-ana consist-mark (PreservationAna syn (StepLow (FillLEnvLowRec (FillLEnvUpRec fill1)) step (FillLEnvLowRec (FillLEnvUpRec fill2)))) ana 
    PreservationSyn (SynAp marrow consist-syn consist-ana consist-mark syn ana) (StepLow {e-in' = (e-fun' ⇒ syn-fun') [ x₁ ]⇐ (fst , snd)} (FillLEnvUpRec (FillLEnvAp1 FillL⊙)) step (FillLEnvUpRec (FillLEnvAp1 FillL⊙))) with ▸NTArrow-dec syn-fun' 
    ... | t-in-fun' , t-out-fun' , m-fun' , marrow' with beyond-▸NTArrow (beyond-l↦-inner step) marrow marrow' 
    ... | t-in-beyond , t-out-beyond , m-beyond with void-ana-step-same step 
    ... | refl , refl = SynAp marrow' (beyond-▶ t-out-beyond consist-syn) (beyond-▶ t-in-beyond consist-ana) (beyond-▶ m-beyond consist-mark) (PreservationAna syn (StepLow FillL⊙ step FillL⊙)) ana -- (beyond-▷-contra (beyond-l↦-env step FillL⊙ FillL⊙) consist-ana)
    PreservationSyn (SynAp marrow consist-syn consist-ana consist-mark syn ana) (StepUp (FillUEnvUpRec (FillUEnvAp2 (FillUEnvLowRec fill1))) step (FillUEnvUpRec (FillUEnvAp2 (FillUEnvLowRec fill2)))) = SynAp marrow consist-syn consist-ana consist-mark syn (PreservationAna ana (StepUp (FillUEnvLowRec fill1) step (FillUEnvLowRec fill2)))
    PreservationSyn (SynAp marrow consist-syn consist-ana consist-mark syn ana) (StepLow {e-in' = e-in' [ m' ]⇐ ana'} (FillLEnvUpRec (FillLEnvAp2 FillL⊙)) step (FillLEnvUpRec (FillLEnvAp2 FillL⊙))) = SynAp marrow consist-syn ? consist-mark syn (PreservationAna ana (StepLow FillL⊙ step FillL⊙))  
    PreservationSyn (SynAp marrow consist-syn consist-ana consist-mark syn ana) (StepLow (FillLEnvUpRec (FillLEnvAp2 (FillLEnvLowRec fill1))) step (FillLEnvUpRec (FillLEnvAp2 (FillLEnvLowRec fill2)))) = SynAp marrow consist-syn consist-ana consist-mark syn (PreservationAna ana (StepLow (FillLEnvLowRec fill1) step (FillLEnvLowRec fill2)))
    PreservationSyn (SynAsc consist-syn consist-ana ana) (StepLow (FillLEnvUpRec (FillLEnvAsc fill1)) step (FillLEnvUpRec (FillLEnvAsc {e' = e-body' [ m-body' ]⇐ ana-body'} fill2))) with beyond-l↦-env step fill1 fill2 
    ... | ◁▷C = SynAsc consist-syn consist-ana (PreservationAna ana (StepLow fill1 step fill2))
    PreservationSyn (SynAsc consist-syn consist-ana ana) (StepUp (FillUEnvUpRec (FillUEnvAsc (FillUEnvLowRec fill1))) step (FillUEnvUpRec (FillUEnvAsc (FillUEnvLowRec fill2)))) = SynAsc consist-syn consist-ana (PreservationAna ana (StepUp (FillUEnvLowRec fill1) step (FillUEnvLowRec fill2)))

    PreservationAna :  
      ∀ {Γ e e'} -> 
      (Γ ⊢ e ⇐) ->
      (e L↦ e') ->   
      (Γ ⊢ e' ⇐) 
    PreservationAna ana (StepLow FillL⊙ step FillL⊙) = PreservationStepAna ana step
    PreservationAna (AnaSubsume {ana-all = ana-all} subsumable consist-t consist-m syn) (StepUp {e-in' = e-all' ⇒ syn-all'} (FillUEnvLowRec FillU⊙) step (FillUEnvLowRec FillU⊙)) with ~N-dec syn-all' ana-all 
    ... | m' , consist-t' = AnaSubsume (step-subsumable step subsumable) consist-t' (beyond-▶ (beyond-through-~N (beyond-u↦ step) consist-t consist-t') consist-m) (PreservationSyn syn (StepUp FillU⊙ step FillU⊙))    
    PreservationAna (AnaSubsume subsumable consist-t consist-m syn) (StepUp (FillUEnvLowRec (FillUEnvUpRec fill1)) step (FillUEnvLowRec (FillUEnvUpRec fill2))) = AnaSubsume (u-env-subsumable fill1 fill2 subsumable) consist-t consist-m (PreservationSyn syn (StepUp (FillUEnvUpRec fill1) step (FillUEnvUpRec fill2)))
    PreservationAna (AnaSubsume subsumable consist-t consist-m syn) (StepLow (FillLEnvLowRec (FillLEnvUpRec fill1)) step (FillLEnvLowRec (FillLEnvUpRec fill2))) = AnaSubsume (l-env-subsumable fill1 fill2 subsumable) consist-t consist-m (PreservationSyn syn (StepLow (FillLEnvUpRec fill1) step (FillLEnvUpRec fill2))) 
    PreservationAna (AnaFun {t-asc = t-asc} marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) (StepUp (FillUEnvLowRec (FillUEnvUpRec (FillUEnvFun (FillUEnvLowRec fill1)))) step (FillUEnvLowRec (FillUEnvUpRec (FillUEnvFun (FillUEnvLowRec {e' = e' ⇒ syn'} fill2))))) = AnaFun marrow consist consist-ana consist-asc consist-body (preservation-lambda-lemma-3 {t = t-asc} (beyond-u↦-env step fill1 fill2) consist-syn) consist-all consist-m-all (PreservationAna ana (StepUp (FillUEnvLowRec fill1) step (FillUEnvLowRec fill2))) 
    PreservationAna (AnaFun {ana-all = ana-all , New} {t-asc = (t-asc , n-asc)} marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) (StepLow (FillLEnvLowRec (FillLEnvUpRec (FillLEnvFun fill1))) step (FillLEnvLowRec (FillLEnvUpRec (FillLEnvFun {e' = (e' ⇒ (syn' , n-syn')) [ m' ]⇐ ana'} fill2)))) = AnaFun marrow consist (beyond-▷-contra (beyond-l↦-env step fill1 fill2) consist-ana) consist-asc consist-body NUnless-new-▷ consist-all consist-m-all (PreservationAna ana (StepLow fill1 step fill2))
    PreservationAna (AnaFun {ana-all = ■ ana-all , Old} {t-asc = (t-asc , n-asc)} marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) (StepLow (FillLEnvLowRec (FillLEnvUpRec (FillLEnvFun fill1))) step (FillLEnvLowRec (FillLEnvUpRec (FillLEnvFun {e' = (e' ⇒ (syn' , n-syn')) [ m' ]⇐ ana'} fill2)))) =  AnaFun marrow consist (beyond-▷-contra (beyond-l↦-env step fill1 fill2) consist-ana) consist-asc consist-body consist-syn consist-all consist-m-all (PreservationAna ana (StepLow fill1 step fill2))
    PreservationAna (AnaFun {syn-body = syn-body} {ana-all = □ , Old} {t-asc = t-asc , n-asc} (NTArrowC DTArrowNone) (■~N-pair (~N-pair ~DVoidR)) (▶Old) ▶Old consist-body consist-syn (~N-pair {d1} {n1 = n1} consist) consist-m-all ana) (StepLow (FillLEnvLowRec (FillLEnvUpRec (FillLEnvFun fill1))) step (FillLEnvLowRec (FillLEnvUpRec (FillLEnvFun {e' = (e' ⇒ (syn' , n-syn')) [ m' ]⇐ ana'} fill2)))) --= ?
      = AnaFun (NTArrowC DTArrowNone) (■~N-pair (~N-pair ~DVoidR)) ? ▶Old consist-body (preservation-lambda-lemma-3 {t = (t-asc , n-asc)} {syn1 = syn-body} {syn1' = (syn' , n-syn')} {syn2 = (d1 , n1)} {ana = □ , Old} (beyond-l↦-env-inner step fill1 fill2) consist-syn) (~N-pair consist) consist-m-all (PreservationAna ana (StepLow fill1 step fill2))

  PreservationProgram :  -- (beyond-▷-contra (beyond-l↦-env step fill1 fill2) (▶Old))
    ∀ {p p'} ->
    (WellTypedProgram p) ->
    (p P↦ p') ->   
    (WellTypedProgram p')
  PreservationProgram (WTProg ana) (InsideStep step) = WTProg (PreservationAna ana step)
  PreservationProgram (WTProg ana) TopStep = WTProg (oldify-syn-inner ana)

  InitProgram : Program 
  InitProgram = Root (EHole ⇒ (■ THole , Old)) Old
 
  InitWellTyped : WellTypedProgram InitProgram 
  InitWellTyped = WTProg (AnaSubsume SubsumableHole (~N-pair ~DVoidR) ▶Old (SynHole (▶Old)))

    