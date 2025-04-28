
open import Data.Product
open import Relation.Binary.PropositionalEquality

open import Prelude
open import Core.Core
open import Core.Environment
open import Core.WellFormed
open import Core.Update
open import Core.Lemmas
open import Core.VariableUpdatePreservation

module Core.UpdatePreservation where

  beyond-u↦ : ∀ {e e' syn syn'} -> 
    (e ⇒ syn) u↦ (e' ⇒ syn') -> 
    =▷ syn syn' 
  beyond-u↦ (StepAp _) = =▷★
  beyond-u↦ StepAsc = =▷★
  beyond-u↦ (StepProj _) = =▷★

  beyond-u↦-env : ∀ {ε e e' e-in e-in' syn syn'} -> 
    e-in u↦ e-in' -> 
    ε S⟦ e-in ⟧S≡ (e ⇒ syn) ->
    ε S⟦ e-in' ⟧S≡ (e' ⇒ syn') ->
    =▷ syn syn' 
  beyond-u↦-env step FillS⊙ FillS⊙ = beyond-u↦ step
  beyond-u↦-env step (FillSynEnvSynRec _) (FillSynEnvSynRec _) = =▷Refl

  beyond-l↦ : ∀ {e e' m m' ana ana'} -> 
    (e [ m ]⇐ ana) l↦ (e' [ m' ]⇐ ana') -> 
    ◁▷ ana ana' 
  beyond-l↦ (StepSyn _) = ◁▷C
  beyond-l↦ (StepAna _ _) = ◁▷C
  beyond-l↦ (StepAnaFun _ _) = ◁▷C
  beyond-l↦ (StepSynFun) = ◁▷C
  beyond-l↦ (StepAnnFun _) = ◁▷C
  beyond-l↦ (StepAnaPair _) = ◁▷C
  beyond-l↦ StepSynPairFst = ◁▷C
  beyond-l↦ StepSynPairSnd = ◁▷C

  beyond-l↦-inner : ∀ {e e' syn syn' m m' n-ana ana'} -> 
    ((e ⇒ syn) [ m ]⇐ (□ , n-ana)) l↦ ((e' ⇒ syn') [ m' ]⇐ ana') -> 
    =▷ syn syn' 
  beyond-l↦-inner (StepAna _ _) = =▷Refl
  beyond-l↦-inner (StepAnaFun _ _) = =▷★
  beyond-l↦-inner (StepAnnFun _) = =▷Refl
  beyond-l↦-inner StepSynFun = =▷★
  beyond-l↦-inner (StepAnaPair _) = =▷★
  beyond-l↦-inner StepSynPairFst = =▷★
  beyond-l↦-inner StepSynPairSnd = =▷★

  beyond-l↦-env-inner : ∀ {ε e e' e-in e-in' syn syn' m m' n-ana ana'} -> 
    e-in l↦ e-in' -> 
    ε A⟦ e-in ⟧A≡ ((e ⇒ syn) [ m ]⇐ (□ , n-ana)) ->
    ε A⟦ e-in' ⟧A≡ ((e' ⇒ syn') [ m' ]⇐ ana') ->
    =▷ syn syn' 
  beyond-l↦-env-inner step FillA⊙ FillA⊙ = beyond-l↦-inner step
  beyond-l↦-env-inner step (FillAnaEnvAnaRec (FillAnaEnvSynRec _)) (FillAnaEnvAnaRec (FillAnaEnvSynRec _)) = =▷Refl

  beyond-l↦-env : ∀ {ε e e' e-in e-in' m m' ana ana'} -> 
    e l↦ e' -> 
    ε A⟦ e ⟧A≡ (e-in [ m ]⇐ ana) ->
    ε A⟦ e' ⟧A≡ (e-in' [ m' ]⇐ ana') ->
    ◁▷ ana ana' 
  beyond-l↦-env step FillA⊙ FillA⊙ = beyond-l↦ step
  beyond-l↦-env step (FillAnaEnvAnaRec _) (FillAnaEnvAnaRec _) = ◁▷C

  void-ana-step-same : ∀ {e n e' m t n'} ->
    (e [ ✔ ]⇐ (□ , n)) l↦ (e' [ m ]⇐ (t , n')) -> 
    (m ≡ ✔) × (t ≡ □)
  void-ana-step-same (StepAna x ~DVoidL) = refl , refl
  void-ana-step-same (StepAna x ~DVoidR) = refl , refl
  void-ana-step-same (StepAnaFun _ _) = refl , refl
  void-ana-step-same (StepAnnFun _) = refl , refl
  void-ana-step-same StepSynFun = refl , refl
  void-ana-step-same (StepAnaPair _) = refl , refl
  void-ana-step-same StepSynPairFst = refl , refl
  void-ana-step-same StepSynPairSnd = refl , refl

  step-subsumable : ∀ {e e' syn syn'} -> 
    (e ⇒ syn) u↦ (e' ⇒ syn') ->
    SubsumableMid e -> 
    SubsumableMid e'
  step-subsumable (StepAp _) SubsumableAp = SubsumableAp
  step-subsumable StepAsc SubsumableAsc = SubsumableAsc
  step-subsumable (StepProj _) SubsumableProj = SubsumableProj

  random-helper : ∀ {t t' d n n'} -> ▷ (NUnless (NArrow (t , •) (t' , n)) (d , n')) (DUnless (DArrow t t') d , ★)
  random-helper {d = □} = ▷Pair ▶Same
  random-helper {d = ■ x} = ▷Pair ▶Same

  random-helper-prod : ∀ {t t' d n n'} -> ▷ (NUnless (NProd (t , •) (t' , n)) (d , n')) (DUnless (DProd t t') d , ★)
  random-helper-prod {d = □} = ▷Pair ▶Same
  random-helper-prod {d = ■ x} = ▷Pair ▶Same

  other-random-helper : ∀ {t d d'} -> ▷ (NUnless t (d , ★)) d'
  other-random-helper {d = □} = ▷Pair ▶★-max-r
  other-random-helper {d = ■ x} = ▷Pair ▶★

  PreservationStepSyn :  
    ∀ {Γ e e'} ->
    (Γ S⊢ e) ->
    (e u↦ e') ->   
    (Γ S⊢ e')
  PreservationStepSyn (WFConst _) ()
  PreservationStepSyn (WFHole _) ()
  PreservationStepSyn (WFAp marrow consist-syn consist-ana consist-mark syn ana) (StepAp marrow') = WFAp (NTArrowC marrow') (▷Pair ▶•) (▷Pair ▶•) ▶• (oldify-syn-inner syn) (small-dirty-ana ana)
  PreservationStepSyn (WFVar _ _) ()
  PreservationStepSyn (WFAsc wf consist-syn consist-ana ana) StepAsc = WFAsc wf (▷Pair ▶•) (▷Pair ▶•) (small-dirty-ana ana)
  PreservationStepSyn (WFProj (NTProjC mproj) x₁ x₂ syn) (StepProj mproj') with ▸DTProj-unicity mproj mproj' 
  ... | refl , refl = WFProj (NTProjC mproj) (▷Pair ▶•) ▶• (oldify-syn-inner syn)

  PreservationStepAna :  
    ∀ {Γ e e'} ->
    (Γ L⊢ e) ->
    (e l↦ e') ->   
    (Γ L⊢ e')
  PreservationStepAna (WFSubsume subsumable (~N-pair consist-t) consist-m syn) (StepSyn consist) with consist-t 
  ... | consist-t rewrite ~D-unicity consist consist-t = WFSubsume subsumable (~N-pair consist-t) ▶Same (oldify-syn syn)
  PreservationStepAna (WFSubsume subsumable (~N-pair consist-t) consist-m syn) (StepAna subsumable' consist) with ~D-unicity consist consist-t 
  ... | refl = WFSubsume subsumable' (~N-pair consist-t) ▶Same (oldify-syn syn)
  PreservationStepAna (WFFun wf marrow consist consist-ana consist-asc consist-body consist-syn (~N-pair consist-all) consist-m-all ana) (StepSyn consist') rewrite ~D-unicity consist' consist-all = WFFun wf marrow consist consist-ana consist-asc consist-body (beyond-▷-contra ◁▷C consist-syn) (~N-pair consist-all) ▶Same ana
  PreservationStepAna (WFFun {t-asc = t-asc , n-asc} wf (NTArrowC x) consist (▷Pair ▶★) ▶★ consist-body consist-syn consist-all consist-m-all ana) (StepAnaFun marrow' (■~D-pair consist')) = WFFun wf (NTArrowC marrow') (■~N-pair (~N-pair consist')) (▷Pair ▶•) ▶• ▶Same (consist-unless-lemma {n1 = n-asc}) (~N-pair ~D-unless) ▶Same (dirty-ana ana)
  PreservationStepAna (WFFun wf (NTArrowC {d} {n} marrow) (■~N-pair {t} (~N-pair consist)) consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) (StepAnnFun {e-body' = _ ⇒ (syn-body' , _)} var-update) 
    = WFFun wf (NTArrowC marrow) (■~N-pair (~N-pair consist)) (▷Pair ▶★)  ▶★ ▶★ other-random-helper (~N-pair (proj₂ (~D-dec _ _))) ▶★-max-r (preservation-vars-ana?-step ana var-update)
  PreservationStepAna (WFFun {ana-all = ana-all} wf (NTArrowC {d} marrow) (■~N-pair {t} {n} (~N-pair consist)) (▷Pair consistm-m-ana) consist-m-ann consist-body consist-syn consist-all consist-m-all ana) (StepSynFun {t-body = t-body}) with ~N-dec (DUnless (DArrow t t-body) d , ★) ana-all
  ... | _ , (~N-pair consist'') = WFFun wf (NTArrowC marrow) (■~N-pair (~N-pair consist)) (▷Pair consistm-m-ana) consist-m-ann consist-body random-helper (~N-pair consist'') ▶★ (oldify-syn-inner ana)
  PreservationStepAna (WFPair mprod con1 con2 con3 (▷Pair con4) (~N-pair consist) con5 wt1 wt2) (StepSyn consist') 
    with ~D-unicity consist consist' 
  ... | refl = WFPair mprod con1 con2 con3 (▷Pair con4) (~N-pair consist) ▶Same wt1 wt2
  PreservationStepAna (WFPair (NTProdC {n = n} mprod) con1 con2 con3 con4 (~N-pair consist) con5 wt1 wt2) (StepAnaPair {n-fst = n-fst} mprod') 
    with ▸DTProd-unicity mprod mprod' 
  ... | refl , refl , refl = WFPair (NTProdC mprod) (▷Pair ▶•) (▷Pair ▶•) ▶• (consist-unless-prod {n1 = n-fst}) (~N-pair (proj₂ (~D-dec _ _))) ▶★ (dirty-ana wt1) (dirty-ana wt2)
  PreservationStepAna (WFPair mprod con1 con2 con3 con4 consist con5 wt1 wt2) StepSynPairFst = WFPair mprod con1 con2 con3 random-helper-prod (~N-pair (proj₂ (~D-dec _ _))) ▶★ (oldify-syn-inner wt1) wt2
  PreservationStepAna (WFPair mprod con1 con2 con3 con4 consist con5 wt1 wt2) StepSynPairSnd = WFPair mprod con1 con2 con3 random-helper-prod (~N-pair (proj₂ (~D-dec _ _))) ▶★ wt1 (oldify-syn-inner wt2)
  PreservationStepAna (WFTypFun x x₁ x₂ x₃ x₄ x₅ wf) (StepSyn x₆) = {!   !}

  mutual 

    PreservationWF :  
      ∀ {Γ e e'} ->
      (Γ S⊢ e) ->
      (e U↦ e') ->   
      (Γ S⊢ e')
    PreservationWF syn (StepUp FillS⊙ step FillS⊙) = PreservationStepSyn syn step
    PreservationWF (WFConst _) (StepUp (FillSynEnvSynRec ()) step (FillSynEnvSynRec fill2))
    PreservationWF (WFConst _) (StepLow (FillAnaEnvSynRec ()) _ (FillAnaEnvSynRec _))
    PreservationWF (WFHole _) (StepUp (FillSynEnvSynRec ()) step (FillSynEnvSynRec fill2))
    PreservationWF (WFHole _) (StepLow (FillAnaEnvSynRec ()) _ (FillAnaEnvSynRec _))    
    PreservationWF (WFVar _ _) (StepUp (FillSynEnvSynRec ()) step (FillSynEnvSynRec fill2))
    PreservationWF (WFVar _ _) (StepLow (FillAnaEnvSynRec ()) _ (FillAnaEnvSynRec _))
    PreservationWF (WFAp marrow consist-syn consist-ana consist-mark syn ana) (StepUp {e-in' = e-fun' ⇒ syn-fun'} (FillSynEnvSynRec (FillSynEnvAp1 (FillSynEnvAnaRec (FillSynEnvSynRec fill1)))) step (FillSynEnvSynRec (FillSynEnvAp1 (FillSynEnvAnaRec (FillSynEnvSynRec fill2))))) = WFAp marrow consist-syn consist-ana consist-mark (PreservationAna syn (StepUp (FillSynEnvAnaRec (FillSynEnvSynRec fill1)) step (FillSynEnvAnaRec (FillSynEnvSynRec fill2)))) ana 
    PreservationWF (WFAp marrow consist-syn consist-ana consist-mark syn ana) (StepUp {e-in' = e-fun' ⇒ syn-fun'} (FillSynEnvSynRec (FillSynEnvAp1 (FillSynEnvAnaRec FillS⊙))) step (FillSynEnvSynRec (FillSynEnvAp1 (FillSynEnvAnaRec FillS⊙)))) with ▸NTArrow-dec syn-fun' 
    ... | t-in-fun' , t-out-fun' , m-fun' , marrow' with beyond-▸NTArrow (beyond-u↦ step) marrow marrow' 
    ... | t-in-beyond , t-out-beyond , m-beyond = WFAp marrow' (beyond-▷ t-out-beyond consist-syn) (beyond-▷ t-in-beyond consist-ana) (beyond-▶ m-beyond consist-mark) (PreservationAna syn (StepUp (FillSynEnvAnaRec FillS⊙) step (FillSynEnvAnaRec FillS⊙))) ana 
    PreservationWF (WFAp marrow consist-syn consist-ana consist-mark syn ana) (StepLow (FillAnaEnvSynRec (FillAnaEnvAp1 (FillAnaEnvAnaRec (FillAnaEnvSynRec fill1)))) step (FillAnaEnvSynRec (FillAnaEnvAp1 (FillAnaEnvAnaRec (FillAnaEnvSynRec fill2))))) = WFAp marrow consist-syn consist-ana consist-mark (PreservationAna syn (StepLow (FillAnaEnvAnaRec (FillAnaEnvSynRec fill1)) step (FillAnaEnvAnaRec (FillAnaEnvSynRec fill2)))) ana 
    PreservationWF (WFAp marrow consist-syn consist-ana consist-mark syn ana) (StepLow {e-in' = (e-fun' ⇒ syn-fun') [ x₁ ]⇐ (fst , snd)} (FillAnaEnvSynRec (FillAnaEnvAp1 FillA⊙)) step (FillAnaEnvSynRec (FillAnaEnvAp1 FillA⊙))) with ▸NTArrow-dec syn-fun' 
    ... | t-in-fun' , t-out-fun' , m-fun' , marrow' with beyond-▸NTArrow (beyond-l↦-inner step) marrow marrow' 
    ... | t-in-beyond , t-out-beyond , m-beyond with void-ana-step-same step 
    ... | refl , refl = WFAp marrow' (beyond-▷ t-out-beyond consist-syn) (beyond-▷ t-in-beyond consist-ana) (beyond-▶ m-beyond consist-mark) (PreservationAna syn (StepLow FillA⊙ step FillA⊙)) ana 
    PreservationWF (WFAp marrow consist-syn consist-ana consist-mark syn ana) (StepUp (FillSynEnvSynRec (FillSynEnvAp2 (FillSynEnvAnaRec fill1))) step (FillSynEnvSynRec (FillSynEnvAp2 (FillSynEnvAnaRec fill2)))) = WFAp marrow consist-syn consist-ana consist-mark syn (PreservationAna ana (StepUp (FillSynEnvAnaRec fill1) step (FillSynEnvAnaRec fill2)))
    PreservationWF (WFAp marrow consist-syn consist-ana consist-mark syn ana) (StepLow {e-in' = e-in' [ m' ]⇐ ana'} (FillAnaEnvSynRec (FillAnaEnvAp2 FillA⊙)) step (FillAnaEnvSynRec (FillAnaEnvAp2 FillA⊙))) = WFAp marrow consist-syn (beyond-▷-contra (beyond-l↦-env step FillA⊙ FillA⊙) consist-ana) consist-mark syn (PreservationAna ana (StepLow FillA⊙ step FillA⊙))  
    PreservationWF (WFAp marrow consist-syn consist-ana consist-mark syn ana) (StepLow (FillAnaEnvSynRec (FillAnaEnvAp2 (FillAnaEnvAnaRec fill1))) step (FillAnaEnvSynRec (FillAnaEnvAp2 (FillAnaEnvAnaRec fill2)))) = WFAp marrow consist-syn consist-ana consist-mark syn (PreservationAna ana (StepLow (FillAnaEnvAnaRec fill1) step (FillAnaEnvAnaRec fill2)))
    PreservationWF (WFAsc wf consist-syn consist-ana ana) (StepLow (FillAnaEnvSynRec (FillAnaEnvAsc fill1)) step (FillAnaEnvSynRec (FillAnaEnvAsc {e' = e-body' [ m-body' ]⇐ ana-body'} fill2))) with beyond-l↦-env step fill1 fill2 
    ... | ◁▷C = WFAsc wf consist-syn (beyond-▷-contra ◁▷C consist-ana) (PreservationAna ana (StepLow fill1 step fill2))
    PreservationWF (WFAsc wf consist-syn consist-ana ana) (StepUp (FillSynEnvSynRec (FillSynEnvAsc (FillSynEnvAnaRec fill1))) step (FillSynEnvSynRec (FillSynEnvAsc (FillSynEnvAnaRec fill2)))) = WFAsc wf consist-syn consist-ana (PreservationAna ana (StepUp (FillSynEnvAnaRec fill1) step (FillSynEnvAnaRec fill2)))
    PreservationWF (WFProj mproj con1 con2 wt) (StepUp {e-in' = e-body' ⇒ syn-body'} (FillSynEnvSynRec (FillSynEnvProj (FillSynEnvAnaRec FillS⊙))) step (FillSynEnvSynRec (FillSynEnvProj (FillSynEnvAnaRec FillS⊙)))) with ▸NTProj-dec _ syn-body'
    ... | t-side-body' , m-body' , mproj' with beyond-▸NTProj (beyond-u↦ step) mproj mproj' 
    ... | t-side-beyond , m-beyond = WFProj mproj' (beyond-▷ t-side-beyond con1) (beyond-▶ m-beyond con2) (PreservationAna wt (StepUp (FillSynEnvAnaRec FillS⊙) step (FillSynEnvAnaRec FillS⊙)))
    PreservationWF (WFProj mproj con1 con2 wt) (StepUp (FillSynEnvSynRec (FillSynEnvProj (FillSynEnvAnaRec (FillSynEnvSynRec fill1)))) step (FillSynEnvSynRec (FillSynEnvProj (FillSynEnvAnaRec (FillSynEnvSynRec fill2))))) = WFProj mproj con1 con2 (PreservationAna wt (StepUp (FillSynEnvAnaRec (FillSynEnvSynRec fill1)) step (FillSynEnvAnaRec (FillSynEnvSynRec fill2))))
    PreservationWF (WFProj mproj con1 con2 wt) (StepLow (FillAnaEnvSynRec (FillAnaEnvProj (FillAnaEnvAnaRec (FillAnaEnvSynRec fill1)))) step (FillAnaEnvSynRec (FillAnaEnvProj (FillAnaEnvAnaRec (FillAnaEnvSynRec fill2))))) = WFProj mproj con1 con2 (PreservationAna wt (StepLow (FillAnaEnvAnaRec (FillAnaEnvSynRec fill1)) step (FillAnaEnvAnaRec (FillAnaEnvSynRec fill2))))
    PreservationWF (WFProj mproj con1 con2 wt) (StepLow {e-in' = (e-body' ⇒ syn-body') [ m' ]⇐ ana'} (FillAnaEnvSynRec (FillAnaEnvProj FillA⊙)) step (FillAnaEnvSynRec (FillAnaEnvProj FillA⊙))) with ▸NTProj-dec _ syn-body' 
    ... | t-side-body' , m-body' , mproj' with beyond-▸NTProj (beyond-l↦-inner step) mproj mproj' 
    ... | t-side-beyond , m-beyond with void-ana-step-same step 
    ... | refl , refl = WFProj mproj' (beyond-▷ t-side-beyond con1) (beyond-▶ m-beyond con2) (PreservationAna wt (StepLow FillA⊙ step FillA⊙))
    PreservationWF wf step = {!   !}

    PreservationAna :  
      ∀ {Γ e e'} -> 
      (Γ L⊢ e) ->
      (e L↦ e') ->   
      (Γ L⊢ e') 
    PreservationAna ana (StepLow FillA⊙ step FillA⊙) = PreservationStepAna ana step
    PreservationAna (WFSubsume {ana-all = ana-all} subsumable consist-t consist-m syn) (StepUp {e-in' = e-all' ⇒ syn-all'} (FillSynEnvAnaRec FillS⊙) step (FillSynEnvAnaRec FillS⊙)) with ~N-dec syn-all' ana-all 
    ... | m' , consist-t' = WFSubsume (step-subsumable step subsumable) consist-t' (beyond-▶ (beyond-through-~N (beyond-u↦ step) consist-t consist-t') consist-m) (PreservationWF syn (StepUp FillS⊙ step FillS⊙))    
    PreservationAna (WFSubsume subsumable consist-t consist-m syn) (StepUp (FillSynEnvAnaRec (FillSynEnvSynRec fill1)) step (FillSynEnvAnaRec (FillSynEnvSynRec fill2))) = WFSubsume (u-env-subsumable fill1 fill2 subsumable) consist-t consist-m (PreservationWF syn (StepUp (FillSynEnvSynRec fill1) step (FillSynEnvSynRec fill2)))
    PreservationAna (WFSubsume subsumable consist-t consist-m syn) (StepLow (FillAnaEnvAnaRec (FillAnaEnvSynRec fill1)) step (FillAnaEnvAnaRec (FillAnaEnvSynRec fill2))) = WFSubsume (l-env-subsumable fill1 fill2 subsumable) consist-t consist-m (PreservationWF syn (StepLow (FillAnaEnvSynRec fill1) step (FillAnaEnvSynRec fill2))) 
    PreservationAna (WFFun {t-asc = t-asc} wf marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) (StepUp (FillSynEnvAnaRec (FillSynEnvSynRec (FillSynEnvFun (FillSynEnvAnaRec fill1)))) step (FillSynEnvAnaRec (FillSynEnvSynRec (FillSynEnvFun (FillSynEnvAnaRec {e' = e' ⇒ syn'} fill2))))) = WFFun wf marrow consist consist-ana consist-asc consist-body (preservation-lambda-lemma {t = t-asc} (beyond-u↦-env step fill1 fill2) consist-syn) consist-all consist-m-all (PreservationAna ana (StepUp (FillSynEnvAnaRec fill1) step (FillSynEnvAnaRec fill2))) 
    
    PreservationAna (WFFun {ana-all = ana-all , ★} {t-asc = (t-asc , n-asc)} wf marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) (StepLow (FillAnaEnvAnaRec (FillAnaEnvSynRec (FillAnaEnvFun fill1))) step (FillAnaEnvAnaRec (FillAnaEnvSynRec (FillAnaEnvFun {e' = (e' ⇒ (syn' , n-syn')) [ m' ]⇐ ana'} fill2)))) = WFFun wf marrow consist (beyond-▷-contra (beyond-l↦-env step fill1 fill2) consist-ana) consist-asc consist-body NUnless-dirty-▷ consist-all consist-m-all (PreservationAna ana (StepLow fill1 step fill2))
    PreservationAna (WFFun {ana-all = ■ ana-all , •} {t-asc = (t-asc , n-asc)} wf marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) (StepLow (FillAnaEnvAnaRec (FillAnaEnvSynRec (FillAnaEnvFun fill1))) step (FillAnaEnvAnaRec (FillAnaEnvSynRec (FillAnaEnvFun {e' = (e' ⇒ (syn' , n-syn')) [ m' ]⇐ ana'} fill2)))) =  WFFun wf marrow consist (beyond-▷-contra (beyond-l↦-env step fill1 fill2) consist-ana) consist-asc consist-body consist-syn consist-all consist-m-all (PreservationAna ana (StepLow fill1 step fill2))
    PreservationAna (WFFun {syn-body = syn-body} {ana-all = □ , •} {t-asc = t-asc , n-asc} wf (NTArrowC DTArrowNone) (■~N-pair (~N-pair ~DVoidR)) (▷Pair ▶•) ▶• consist-body consist-syn (~N-pair {d1} {n1 = n1} consist) consist-m-all ana) (StepLow (FillAnaEnvAnaRec (FillAnaEnvSynRec (FillAnaEnvFun fill1))) step (FillAnaEnvAnaRec (FillAnaEnvSynRec (FillAnaEnvFun {e' = (e' ⇒ (syn' , n-syn')) [ m' ]⇐ ana'} fill2)))) --= ?
      = WFFun wf (NTArrowC DTArrowNone) (■~N-pair (~N-pair ~DVoidR)) (beyond-▷-contra (beyond-l↦-env step fill1 fill2) (▷Pair ▶•)) ▶• consist-body (preservation-lambda-lemma {t = (t-asc , n-asc)} {syn1 = syn-body} {syn1' = (syn' , n-syn')} {syn2 = (d1 , n1)} {ana = □ , •} (beyond-l↦-env-inner step fill1 fill2) consist-syn) (~N-pair consist) consist-m-all (PreservationAna ana (StepLow fill1 step fill2))
    
    PreservationAna (WFPair mprod con1 con2 con3 con4 consist con5 wt1 wt2) (StepUp (FillSynEnvAnaRec (FillSynEnvSynRec (FillSynEnvPair1 (FillSynEnvAnaRec fill1)))) step (FillSynEnvAnaRec (FillSynEnvSynRec (FillSynEnvPair1 (FillSynEnvAnaRec {e' = e' ⇒ syn'} fill2))))) = WFPair mprod con1 con2 con3 (preservation-pair-lemma (beyond-u↦-env step fill1 fill2) =▷Refl con4) consist con5 (PreservationAna wt1 (StepUp (FillSynEnvAnaRec fill1) step (FillSynEnvAnaRec fill2))) wt2
    PreservationAna (WFPair mprod con1 con2 con3 con4 consist con5 wt1 wt2) (StepUp (FillSynEnvAnaRec (FillSynEnvSynRec (FillSynEnvPair2 (FillSynEnvAnaRec fill1)))) step (FillSynEnvAnaRec (FillSynEnvSynRec (FillSynEnvPair2 (FillSynEnvAnaRec {e' = e' ⇒ syn'} fill2))))) = WFPair mprod con1 con2 con3 (preservation-pair-lemma =▷Refl (beyond-u↦-env step fill1 fill2) con4) consist con5 wt1 (PreservationAna wt2 (StepUp (FillSynEnvAnaRec fill1) step (FillSynEnvAnaRec fill2))) 
    
    PreservationAna (WFPair {ana-all = ana-all , ★} mprod con1 con2 con3 con4 consist con5 wt1 wt2) (StepLow (FillAnaEnvAnaRec (FillAnaEnvSynRec (FillAnaEnvPair1 fill1))) step (FillAnaEnvAnaRec (FillAnaEnvSynRec (FillAnaEnvPair1 {e' = (e' ⇒ (syn' , n-syn')) [ m' ]⇐ ana'} fill2)))) = WFPair mprod (beyond-▷-contra (beyond-l↦-env step fill1 fill2) con1) con2 con3 NUnless-dirty-▷ consist con5 (PreservationAna wt1 (StepLow fill1 step fill2)) wt2
    PreservationAna (WFPair {ana-all = ■ ana-all , •} mprod con1 con2 con3 con4 consist con5 wt1 wt2) (StepLow (FillAnaEnvAnaRec (FillAnaEnvSynRec (FillAnaEnvPair1 fill1))) step (FillAnaEnvAnaRec (FillAnaEnvSynRec (FillAnaEnvPair1 {e' = (e' ⇒ (syn' , n-syn')) [ m' ]⇐ ana'} fill2)))) = WFPair mprod (beyond-▷-contra (beyond-l↦-env step fill1 fill2) con1) con2 con3 con4 consist con5 (PreservationAna wt1 (StepLow fill1 step fill2)) wt2
    PreservationAna (WFPair {syn-snd = syn-snd} {ana-all = □ , •} (NTProdC DTProdNone) (▷Pair ▶•) (▷Pair ▶•) ▶• con4 (~N-pair consist) con5 wt1 wt2) (StepLow (FillAnaEnvAnaRec (FillAnaEnvSynRec (FillAnaEnvPair1 fill1))) step (FillAnaEnvAnaRec (FillAnaEnvSynRec (FillAnaEnvPair1 {e' = (e' ⇒ (syn' , n-syn')) [ m' ]⇐ ana'} fill2)))) rewrite ~DVoid-right consist = 
      WFPair (NTProdC DTProdNone) (beyond-▷-contra (beyond-l↦-env step fill1 fill2) (▷Pair ▶•)) (▷Pair ▶•) ▶• (preservation-pair-lemma {syn2 = syn-snd} {ana = □ , •} (beyond-l↦-env-inner step fill1 fill2) =▷Refl con4) (~N-pair ~DVoidR) con5 (PreservationAna wt1 (StepLow fill1 step fill2)) wt2

    PreservationAna (WFPair {ana-all = ana-all , ★} mprod con1 con2 con3 con4 consist con5 wt1 wt2) (StepLow (FillAnaEnvAnaRec (FillAnaEnvSynRec (FillAnaEnvPair2 fill1))) step (FillAnaEnvAnaRec (FillAnaEnvSynRec (FillAnaEnvPair2 {e' = (e' ⇒ (syn' , n-syn')) [ m' ]⇐ ana'} fill2)))) = WFPair mprod con1 (beyond-▷-contra (beyond-l↦-env step fill1 fill2) con2) con3 NUnless-dirty-▷ consist con5 wt1 (PreservationAna wt2 (StepLow fill1 step fill2))
    PreservationAna (WFPair {ana-all = ■ ana-all , •} mprod con1 con2 con3 con4 consist con5 wt1 wt2) (StepLow (FillAnaEnvAnaRec (FillAnaEnvSynRec (FillAnaEnvPair2 fill1))) step (FillAnaEnvAnaRec (FillAnaEnvSynRec (FillAnaEnvPair2 {e' = (e' ⇒ (syn' , n-syn')) [ m' ]⇐ ana'} fill2)))) = WFPair mprod con1 (beyond-▷-contra (beyond-l↦-env step fill1 fill2) con2) con3 con4 consist con5 wt1 (PreservationAna wt2 (StepLow fill1 step fill2))
    PreservationAna (WFPair {syn-fst = syn-fst} {ana-all = □ , •} (NTProdC DTProdNone) (▷Pair ▶•) (▷Pair ▶•) ▶• con4 (~N-pair consist) con5 wt1 wt2) (StepLow (FillAnaEnvAnaRec (FillAnaEnvSynRec (FillAnaEnvPair2 fill1))) step (FillAnaEnvAnaRec (FillAnaEnvSynRec (FillAnaEnvPair2 {e' = (e' ⇒ (syn' , n-syn')) [ m' ]⇐ ana'} fill2)))) rewrite ~DVoid-right consist = 
      WFPair (NTProdC DTProdNone) (▷Pair ▶•) (beyond-▷-contra (beyond-l↦-env step fill1 fill2) (▷Pair ▶•)) ▶• (preservation-pair-lemma {syn1 = syn-fst} {ana = □ , •} =▷Refl (beyond-l↦-env-inner step fill1 fill2) con4) (~N-pair ~DVoidR) con5 wt1 (PreservationAna wt2 (StepLow fill1 step fill2))
    PreservationAna wf step = {!   !}

  PreservationProgram :  
    ∀ {p p'} ->
    (P⊢ p) ->
    (p P↦ p') ->     
    (P⊢ p') 
  PreservationProgram (WFProgram ana) (InsideStep step) = WFProgram (PreservationAna ana step)
  PreservationProgram (WFProgram ana) TopStep = WFProgram (oldify-syn-inner ana)  