
open import Data.Product
open import Relation.Binary.PropositionalEquality

open import Prelude
open import Core.Core
open import Core.Environment
open import Core.WellTyped
open import Core.Update
open import Core.Lemmas
open import Core.VarsSynthesizePreservation

module Core.UpdatePreservation where

  beyond-u↦ : ∀ {e e' syn syn'} -> 
    (e ⇒ syn) u↦ (e' ⇒ syn') -> 
    =▷ syn syn' 
  beyond-u↦ (StepAp _) = =▷New
  beyond-u↦ StepAsc = =▷New
  beyond-u↦ (StepProj _) = =▷New

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
  beyond-l↦ (StepSynConsist _) = ◁▷C
  beyond-l↦ (StepAnaConsist _ _) = ◁▷C
  beyond-l↦ (StepAnaFun _ _) = ◁▷C
  beyond-l↦ (StepSynFun) = ◁▷C
  beyond-l↦ (StepAnnFun _) = ◁▷C
  beyond-l↦ (StepAnaPair _) = ◁▷C
  beyond-l↦ StepSynPairFst = ◁▷C
  beyond-l↦ StepSynPairSnd = ◁▷C

  beyond-l↦-inner : ∀ {e e' syn syn' m m' n-ana ana'} -> 
    ((e ⇒ syn) [ m ]⇐ (□ , n-ana)) l↦ ((e' ⇒ syn') [ m' ]⇐ ana') -> 
    =▷ syn syn' 
  beyond-l↦-inner (StepAnaConsist _ _) = =▷Refl
  beyond-l↦-inner (StepAnaFun _ _) = =▷New
  beyond-l↦-inner (StepAnnFun _) = =▷Refl
  beyond-l↦-inner StepSynFun = =▷New
  beyond-l↦-inner (StepAnaPair _) = =▷New
  beyond-l↦-inner StepSynPairFst = =▷New
  beyond-l↦-inner StepSynPairSnd = =▷New

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
  void-ana-step-same (StepAnaConsist x ~DVoidL) = refl , refl
  void-ana-step-same (StepAnaConsist x ~DVoidR) = refl , refl
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

  random-helper : ∀ {t t' d n n'} -> ▷ (NUnless (NArrow (t , Old) (t' , n)) (d , n')) (DUnless (DArrow t t') d , New)
  random-helper {d = □} = ▷Pair ▶Same
  random-helper {d = ■ x} = ▷Pair ▶Same

  random-helper-prod : ∀ {t t' d n n'} -> ▷ (NUnless (NProd (t , Old) (t' , n)) (d , n')) (DUnless (DProd t t') d , New)
  random-helper-prod {d = □} = ▷Pair ▶Same
  random-helper-prod {d = ■ x} = ▷Pair ▶Same

  other-random-helper : ∀ {t d d'} -> ▷ (NUnless t (d , New)) d'
  other-random-helper {d = □} = ▷Pair ▶New-max-r
  other-random-helper {d = ■ x} = ▷Pair ▶New

  PreservationStepSyn :  
    ∀ {Γ e e'} ->
    (Γ U⊢ e) ->
    (e u↦ e') ->   
    (Γ U⊢ e')
  PreservationStepSyn (WTConst _) ()
  PreservationStepSyn (WTHole _) ()
  PreservationStepSyn (WTAp marrow consist-syn consist-ana consist-mark syn ana) (StepAp marrow') = WTAp (NTArrowC marrow') (▷Pair ▶Old) (▷Pair ▶Old) ▶Old (oldify-syn-inner syn) (small-newify-ana ana)
  PreservationStepSyn (WTVar _ _) ()
  PreservationStepSyn (WTAsc consist-syn consist-ana ana) StepAsc = WTAsc (▷Pair ▶Old) (▷Pair ▶Old) (small-newify-ana ana)
  PreservationStepSyn (WTProj (NTProjC mproj) x₁ x₂ syn) (StepProj mproj') with ▸DTProj-unicity mproj mproj' 
  ... | refl , refl = WTProj (NTProjC mproj) (▷Pair ▶Old) ▶Old (oldify-syn-inner syn)

  PreservationStepAna :  
    ∀ {Γ e e'} ->
    (Γ L⊢ e) ->
    (e l↦ e') ->   
    (Γ L⊢ e')
  PreservationStepAna (WTUp subsumable (~N-pair consist-t) consist-m syn) (StepSynConsist consist) with consist-t 
  ... | consist-t rewrite ~D-unicity consist consist-t = WTUp subsumable (~N-pair consist-t) ▶Same (oldify-syn syn)
  PreservationStepAna (WTUp subsumable (~N-pair consist-t) consist-m syn) (StepAnaConsist subsumable' consist) with ~D-unicity consist consist-t 
  ... | refl = WTUp subsumable' (~N-pair consist-t) ▶Same (oldify-syn syn)
  PreservationStepAna (WTFun marrow consist consist-ana consist-asc consist-body consist-syn (~N-pair consist-all) consist-m-all ana) (StepSynConsist consist') rewrite ~D-unicity consist' consist-all = WTFun marrow consist consist-ana consist-asc consist-body (beyond-▷-contra ◁▷C consist-syn) (~N-pair consist-all) ▶Same ana
  PreservationStepAna (WTFun {t-asc = t-asc , n-asc} (NTArrowC x) consist (▷Pair ▶New) ▶New consist-body consist-syn consist-all consist-m-all ana) (StepAnaFun marrow' (■~D-pair consist')) = WTFun (NTArrowC marrow') (■~N-pair (~N-pair consist')) (▷Pair ▶Old) ▶Old ▶Same (consist-unless-lemma {n1 = n-asc}) (~N-pair ~D-unless) ▶Same (newify-ana ana)
  PreservationStepAna (WTFun (NTArrowC {d} {n} marrow) (■~N-pair {t} (~N-pair consist)) consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) (StepAnnFun {syn-body' = syn-body'} vars-syn) 
    = WTFun (NTArrowC marrow) (■~N-pair (~N-pair consist)) (▷Pair ▶New)  ▶New ▶New other-random-helper (~N-pair (proj₂ (~D-dec _ _))) ▶New-max-r (preservation-vars-ana? ana vars-syn)
  PreservationStepAna (WTFun {ana-all = ana-all} (NTArrowC {d} marrow) (■~N-pair {t} {n} (~N-pair consist)) (▷Pair consistm-m-ana) consist-m-ann consist-body consist-syn consist-all consist-m-all ana) (StepSynFun {t-body = t-body}) with ~N-dec (DUnless (DArrow t t-body) d , New) ana-all
  ... | _ , (~N-pair consist'')  = WTFun (NTArrowC marrow) (■~N-pair (~N-pair consist)) (▷Pair consistm-m-ana) consist-m-ann consist-body random-helper (~N-pair consist'') ▶New (oldify-syn-inner ana)
  PreservationStepAna (WTPair mprod con1 con2 con3 (▷Pair con4) (~N-pair consist) con5 wt1 wt2) (StepSynConsist consist') 
    with ~D-unicity consist consist' 
  ... | refl = WTPair mprod con1 con2 con3 (▷Pair con4) (~N-pair consist) ▶Same wt1 wt2
  PreservationStepAna (WTPair (NTProdC {n = n} mprod) con1 con2 con3 con4 (~N-pair consist) con5 wt1 wt2) (StepAnaPair {n-fst = n-fst} mprod') 
    with ▸DTProd-unicity mprod mprod' 
  ... | refl , refl , refl = WTPair (NTProdC mprod) (▷Pair ▶Old) (▷Pair ▶Old) ▶Old (consist-unless-prod {n1 = n-fst}) (~N-pair (proj₂ (~D-dec _ _))) ▶New (newify-ana wt1) (newify-ana wt2)
  PreservationStepAna (WTPair mprod con1 con2 con3 con4 consist con5 wt1 wt2) StepSynPairFst = WTPair mprod con1 con2 con3 random-helper-prod (~N-pair (proj₂ (~D-dec _ _))) ▶New (oldify-syn-inner wt1) wt2
  PreservationStepAna (WTPair mprod con1 con2 con3 con4 consist con5 wt1 wt2) StepSynPairSnd = WTPair mprod con1 con2 con3 random-helper-prod (~N-pair (proj₂ (~D-dec _ _))) ▶New wt1 (oldify-syn-inner wt2)

  mutual 

    PreservationWT :  
      ∀ {Γ e e'} ->
      (Γ U⊢ e) ->
      (e U↦ e') ->   
      (Γ U⊢ e')
    PreservationWT syn (StepUp FillU⊙ step FillU⊙) = PreservationStepSyn syn step
    PreservationWT (WTConst _) (StepUp (FillUEnvUpRec ()) step (FillUEnvUpRec fill2))
    PreservationWT (WTConst _) (StepLow (FillLEnvUpRec ()) _ (FillLEnvUpRec _))
    PreservationWT (WTHole _) (StepUp (FillUEnvUpRec ()) step (FillUEnvUpRec fill2))
    PreservationWT (WTHole _) (StepLow (FillLEnvUpRec ()) _ (FillLEnvUpRec _))    
    PreservationWT (WTVar _ _) (StepUp (FillUEnvUpRec ()) step (FillUEnvUpRec fill2))
    PreservationWT (WTVar _ _) (StepLow (FillLEnvUpRec ()) _ (FillLEnvUpRec _))
    PreservationWT (WTAp marrow consist-syn consist-ana consist-mark syn ana) (StepUp {e-in' = e-fun' ⇒ syn-fun'} (FillUEnvUpRec (FillUEnvAp1 (FillUEnvLowRec (FillUEnvUpRec fill1)))) step (FillUEnvUpRec (FillUEnvAp1 (FillUEnvLowRec (FillUEnvUpRec fill2))))) = WTAp marrow consist-syn consist-ana consist-mark (PreservationAna syn (StepUp (FillUEnvLowRec (FillUEnvUpRec fill1)) step (FillUEnvLowRec (FillUEnvUpRec fill2)))) ana 
    PreservationWT (WTAp marrow consist-syn consist-ana consist-mark syn ana) (StepUp {e-in' = e-fun' ⇒ syn-fun'} (FillUEnvUpRec (FillUEnvAp1 (FillUEnvLowRec FillU⊙))) step (FillUEnvUpRec (FillUEnvAp1 (FillUEnvLowRec FillU⊙)))) with ▸NTArrow-dec syn-fun' 
    ... | t-in-fun' , t-out-fun' , m-fun' , marrow' with beyond-▸NTArrow (beyond-u↦ step) marrow marrow' 
    ... | t-in-beyond , t-out-beyond , m-beyond = WTAp marrow' (beyond-▷ t-out-beyond consist-syn) (beyond-▷ t-in-beyond consist-ana) (beyond-▶ m-beyond consist-mark) (PreservationAna syn (StepUp (FillUEnvLowRec FillU⊙) step (FillUEnvLowRec FillU⊙))) ana 
    PreservationWT (WTAp marrow consist-syn consist-ana consist-mark syn ana) (StepLow (FillLEnvUpRec (FillLEnvAp1 (FillLEnvLowRec (FillLEnvUpRec fill1)))) step (FillLEnvUpRec (FillLEnvAp1 (FillLEnvLowRec (FillLEnvUpRec fill2))))) = WTAp marrow consist-syn consist-ana consist-mark (PreservationAna syn (StepLow (FillLEnvLowRec (FillLEnvUpRec fill1)) step (FillLEnvLowRec (FillLEnvUpRec fill2)))) ana 
    PreservationWT (WTAp marrow consist-syn consist-ana consist-mark syn ana) (StepLow {e-in' = (e-fun' ⇒ syn-fun') [ x₁ ]⇐ (fst , snd)} (FillLEnvUpRec (FillLEnvAp1 FillL⊙)) step (FillLEnvUpRec (FillLEnvAp1 FillL⊙))) with ▸NTArrow-dec syn-fun' 
    ... | t-in-fun' , t-out-fun' , m-fun' , marrow' with beyond-▸NTArrow (beyond-l↦-inner step) marrow marrow' 
    ... | t-in-beyond , t-out-beyond , m-beyond with void-ana-step-same step 
    ... | refl , refl = WTAp marrow' (beyond-▷ t-out-beyond consist-syn) (beyond-▷ t-in-beyond consist-ana) (beyond-▶ m-beyond consist-mark) (PreservationAna syn (StepLow FillL⊙ step FillL⊙)) ana 
    PreservationWT (WTAp marrow consist-syn consist-ana consist-mark syn ana) (StepUp (FillUEnvUpRec (FillUEnvAp2 (FillUEnvLowRec fill1))) step (FillUEnvUpRec (FillUEnvAp2 (FillUEnvLowRec fill2)))) = WTAp marrow consist-syn consist-ana consist-mark syn (PreservationAna ana (StepUp (FillUEnvLowRec fill1) step (FillUEnvLowRec fill2)))
    PreservationWT (WTAp marrow consist-syn consist-ana consist-mark syn ana) (StepLow {e-in' = e-in' [ m' ]⇐ ana'} (FillLEnvUpRec (FillLEnvAp2 FillL⊙)) step (FillLEnvUpRec (FillLEnvAp2 FillL⊙))) = WTAp marrow consist-syn (beyond-▷-contra (beyond-l↦-env step FillL⊙ FillL⊙) consist-ana) consist-mark syn (PreservationAna ana (StepLow FillL⊙ step FillL⊙))  
    PreservationWT (WTAp marrow consist-syn consist-ana consist-mark syn ana) (StepLow (FillLEnvUpRec (FillLEnvAp2 (FillLEnvLowRec fill1))) step (FillLEnvUpRec (FillLEnvAp2 (FillLEnvLowRec fill2)))) = WTAp marrow consist-syn consist-ana consist-mark syn (PreservationAna ana (StepLow (FillLEnvLowRec fill1) step (FillLEnvLowRec fill2)))
    PreservationWT (WTAsc consist-syn consist-ana ana) (StepLow (FillLEnvUpRec (FillLEnvAsc fill1)) step (FillLEnvUpRec (FillLEnvAsc {e' = e-body' [ m-body' ]⇐ ana-body'} fill2))) with beyond-l↦-env step fill1 fill2 
    ... | ◁▷C = WTAsc consist-syn (beyond-▷-contra ◁▷C consist-ana) (PreservationAna ana (StepLow fill1 step fill2))
    PreservationWT (WTAsc consist-syn consist-ana ana) (StepUp (FillUEnvUpRec (FillUEnvAsc (FillUEnvLowRec fill1))) step (FillUEnvUpRec (FillUEnvAsc (FillUEnvLowRec fill2)))) = WTAsc consist-syn consist-ana (PreservationAna ana (StepUp (FillUEnvLowRec fill1) step (FillUEnvLowRec fill2)))
    PreservationWT (WTProj mproj con1 con2 wt) (StepUp {e-in' = e-body' ⇒ syn-body'} (FillUEnvUpRec (FillUEnvProj (FillUEnvLowRec FillU⊙))) step (FillUEnvUpRec (FillUEnvProj (FillUEnvLowRec FillU⊙)))) with ▸NTProj-dec _ syn-body'
    ... | t-side-body' , m-body' , mproj' with beyond-▸NTProj (beyond-u↦ step) mproj mproj' 
    ... | t-side-beyond , m-beyond = WTProj mproj' (beyond-▷ t-side-beyond con1) (beyond-▶ m-beyond con2) (PreservationAna wt (StepUp (FillUEnvLowRec FillU⊙) step (FillUEnvLowRec FillU⊙)))
    PreservationWT (WTProj mproj con1 con2 wt) (StepUp (FillUEnvUpRec (FillUEnvProj (FillUEnvLowRec (FillUEnvUpRec fill1)))) step (FillUEnvUpRec (FillUEnvProj (FillUEnvLowRec (FillUEnvUpRec fill2))))) = WTProj mproj con1 con2 (PreservationAna wt (StepUp (FillUEnvLowRec (FillUEnvUpRec fill1)) step (FillUEnvLowRec (FillUEnvUpRec fill2))))
    PreservationWT (WTProj mproj con1 con2 wt) (StepLow (FillLEnvUpRec (FillLEnvProj (FillLEnvLowRec (FillLEnvUpRec fill1)))) step (FillLEnvUpRec (FillLEnvProj (FillLEnvLowRec (FillLEnvUpRec fill2))))) = WTProj mproj con1 con2 (PreservationAna wt (StepLow (FillLEnvLowRec (FillLEnvUpRec fill1)) step (FillLEnvLowRec (FillLEnvUpRec fill2))))
    PreservationWT (WTProj mproj con1 con2 wt) (StepLow {e-in' = (e-body' ⇒ syn-body') [ m' ]⇐ ana'} (FillLEnvUpRec (FillLEnvProj FillL⊙)) step (FillLEnvUpRec (FillLEnvProj FillL⊙))) with ▸NTProj-dec _ syn-body' 
    ... | t-side-body' , m-body' , mproj' with beyond-▸NTProj (beyond-l↦-inner step) mproj mproj' 
    ... | t-side-beyond , m-beyond with void-ana-step-same step 
    ... | refl , refl = WTProj mproj' (beyond-▷ t-side-beyond con1) (beyond-▶ m-beyond con2) (PreservationAna wt (StepLow FillL⊙ step FillL⊙))


    PreservationAna :  
      ∀ {Γ e e'} -> 
      (Γ L⊢ e) ->
      (e L↦ e') ->   
      (Γ L⊢ e') 
    PreservationAna ana (StepLow FillL⊙ step FillL⊙) = PreservationStepAna ana step
    PreservationAna (WTUp {ana-all = ana-all} subsumable consist-t consist-m syn) (StepUp {e-in' = e-all' ⇒ syn-all'} (FillUEnvLowRec FillU⊙) step (FillUEnvLowRec FillU⊙)) with ~N-dec syn-all' ana-all 
    ... | m' , consist-t' = WTUp (step-subsumable step subsumable) consist-t' (beyond-▶ (beyond-through-~N (beyond-u↦ step) consist-t consist-t') consist-m) (PreservationWT syn (StepUp FillU⊙ step FillU⊙))    
    PreservationAna (WTUp subsumable consist-t consist-m syn) (StepUp (FillUEnvLowRec (FillUEnvUpRec fill1)) step (FillUEnvLowRec (FillUEnvUpRec fill2))) = WTUp (u-env-subsumable fill1 fill2 subsumable) consist-t consist-m (PreservationWT syn (StepUp (FillUEnvUpRec fill1) step (FillUEnvUpRec fill2)))
    PreservationAna (WTUp subsumable consist-t consist-m syn) (StepLow (FillLEnvLowRec (FillLEnvUpRec fill1)) step (FillLEnvLowRec (FillLEnvUpRec fill2))) = WTUp (l-env-subsumable fill1 fill2 subsumable) consist-t consist-m (PreservationWT syn (StepLow (FillLEnvUpRec fill1) step (FillLEnvUpRec fill2))) 
    PreservationAna (WTFun {t-asc = t-asc} marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) (StepUp (FillUEnvLowRec (FillUEnvUpRec (FillUEnvFun (FillUEnvLowRec fill1)))) step (FillUEnvLowRec (FillUEnvUpRec (FillUEnvFun (FillUEnvLowRec {e' = e' ⇒ syn'} fill2))))) = WTFun marrow consist consist-ana consist-asc consist-body (preservation-lambda-lemma {t = t-asc} (beyond-u↦-env step fill1 fill2) consist-syn) consist-all consist-m-all (PreservationAna ana (StepUp (FillUEnvLowRec fill1) step (FillUEnvLowRec fill2))) 
    
    PreservationAna (WTFun {ana-all = ana-all , New} {t-asc = (t-asc , n-asc)} marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) (StepLow (FillLEnvLowRec (FillLEnvUpRec (FillLEnvFun fill1))) step (FillLEnvLowRec (FillLEnvUpRec (FillLEnvFun {e' = (e' ⇒ (syn' , n-syn')) [ m' ]⇐ ana'} fill2)))) = WTFun marrow consist (beyond-▷-contra (beyond-l↦-env step fill1 fill2) consist-ana) consist-asc consist-body NUnless-new-▷ consist-all consist-m-all (PreservationAna ana (StepLow fill1 step fill2))
    PreservationAna (WTFun {ana-all = ■ ana-all , Old} {t-asc = (t-asc , n-asc)} marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) (StepLow (FillLEnvLowRec (FillLEnvUpRec (FillLEnvFun fill1))) step (FillLEnvLowRec (FillLEnvUpRec (FillLEnvFun {e' = (e' ⇒ (syn' , n-syn')) [ m' ]⇐ ana'} fill2)))) =  WTFun marrow consist (beyond-▷-contra (beyond-l↦-env step fill1 fill2) consist-ana) consist-asc consist-body consist-syn consist-all consist-m-all (PreservationAna ana (StepLow fill1 step fill2))
    PreservationAna (WTFun {syn-body = syn-body} {ana-all = □ , Old} {t-asc = t-asc , n-asc} (NTArrowC DTArrowNone) (■~N-pair (~N-pair ~DVoidR)) (▷Pair ▶Old) ▶Old consist-body consist-syn (~N-pair {d1} {n1 = n1} consist) consist-m-all ana) (StepLow (FillLEnvLowRec (FillLEnvUpRec (FillLEnvFun fill1))) step (FillLEnvLowRec (FillLEnvUpRec (FillLEnvFun {e' = (e' ⇒ (syn' , n-syn')) [ m' ]⇐ ana'} fill2)))) --= ?
      = WTFun (NTArrowC DTArrowNone) (■~N-pair (~N-pair ~DVoidR)) (beyond-▷-contra (beyond-l↦-env step fill1 fill2) (▷Pair ▶Old)) ▶Old consist-body (preservation-lambda-lemma {t = (t-asc , n-asc)} {syn1 = syn-body} {syn1' = (syn' , n-syn')} {syn2 = (d1 , n1)} {ana = □ , Old} (beyond-l↦-env-inner step fill1 fill2) consist-syn) (~N-pair consist) consist-m-all (PreservationAna ana (StepLow fill1 step fill2))
    
    PreservationAna (WTPair mprod con1 con2 con3 con4 consist con5 wt1 wt2) (StepUp (FillUEnvLowRec (FillUEnvUpRec (FillUEnvPair1 (FillUEnvLowRec fill1)))) step (FillUEnvLowRec (FillUEnvUpRec (FillUEnvPair1 (FillUEnvLowRec {e' = e' ⇒ syn'} fill2))))) = WTPair mprod con1 con2 con3 (preservation-pair-lemma (beyond-u↦-env step fill1 fill2) =▷Refl con4) consist con5 (PreservationAna wt1 (StepUp (FillUEnvLowRec fill1) step (FillUEnvLowRec fill2))) wt2
    PreservationAna (WTPair mprod con1 con2 con3 con4 consist con5 wt1 wt2) (StepUp (FillUEnvLowRec (FillUEnvUpRec (FillUEnvPair2 (FillUEnvLowRec fill1)))) step (FillUEnvLowRec (FillUEnvUpRec (FillUEnvPair2 (FillUEnvLowRec {e' = e' ⇒ syn'} fill2))))) = WTPair mprod con1 con2 con3 (preservation-pair-lemma =▷Refl (beyond-u↦-env step fill1 fill2) con4) consist con5 wt1 (PreservationAna wt2 (StepUp (FillUEnvLowRec fill1) step (FillUEnvLowRec fill2))) 
    
    PreservationAna (WTPair {ana-all = ana-all , New} mprod con1 con2 con3 con4 consist con5 wt1 wt2) (StepLow (FillLEnvLowRec (FillLEnvUpRec (FillLEnvPair1 fill1))) step (FillLEnvLowRec (FillLEnvUpRec (FillLEnvPair1 {e' = (e' ⇒ (syn' , n-syn')) [ m' ]⇐ ana'} fill2)))) = WTPair mprod (beyond-▷-contra (beyond-l↦-env step fill1 fill2) con1) con2 con3 NUnless-new-▷ consist con5 (PreservationAna wt1 (StepLow fill1 step fill2)) wt2
    PreservationAna (WTPair {ana-all = ■ ana-all , Old} mprod con1 con2 con3 con4 consist con5 wt1 wt2) (StepLow (FillLEnvLowRec (FillLEnvUpRec (FillLEnvPair1 fill1))) step (FillLEnvLowRec (FillLEnvUpRec (FillLEnvPair1 {e' = (e' ⇒ (syn' , n-syn')) [ m' ]⇐ ana'} fill2)))) = WTPair mprod (beyond-▷-contra (beyond-l↦-env step fill1 fill2) con1) con2 con3 con4 consist con5 (PreservationAna wt1 (StepLow fill1 step fill2)) wt2
    PreservationAna (WTPair {syn-snd = syn-snd} {ana-all = □ , Old} (NTProdC DTProdNone) (▷Pair ▶Old) (▷Pair ▶Old) ▶Old con4 (~N-pair consist) con5 wt1 wt2) (StepLow (FillLEnvLowRec (FillLEnvUpRec (FillLEnvPair1 fill1))) step (FillLEnvLowRec (FillLEnvUpRec (FillLEnvPair1 {e' = (e' ⇒ (syn' , n-syn')) [ m' ]⇐ ana'} fill2)))) rewrite ~DVoid-right consist = 
      WTPair (NTProdC DTProdNone) (beyond-▷-contra (beyond-l↦-env step fill1 fill2) (▷Pair ▶Old)) (▷Pair ▶Old) ▶Old (preservation-pair-lemma {syn2 = syn-snd} {ana = □ , Old} (beyond-l↦-env-inner step fill1 fill2) =▷Refl con4) (~N-pair ~DVoidR) con5 (PreservationAna wt1 (StepLow fill1 step fill2)) wt2

    PreservationAna (WTPair {ana-all = ana-all , New} mprod con1 con2 con3 con4 consist con5 wt1 wt2) (StepLow (FillLEnvLowRec (FillLEnvUpRec (FillLEnvPair2 fill1))) step (FillLEnvLowRec (FillLEnvUpRec (FillLEnvPair2 {e' = (e' ⇒ (syn' , n-syn')) [ m' ]⇐ ana'} fill2)))) = WTPair mprod con1 (beyond-▷-contra (beyond-l↦-env step fill1 fill2) con2) con3 NUnless-new-▷ consist con5 wt1 (PreservationAna wt2 (StepLow fill1 step fill2))
    PreservationAna (WTPair {ana-all = ■ ana-all , Old} mprod con1 con2 con3 con4 consist con5 wt1 wt2) (StepLow (FillLEnvLowRec (FillLEnvUpRec (FillLEnvPair2 fill1))) step (FillLEnvLowRec (FillLEnvUpRec (FillLEnvPair2 {e' = (e' ⇒ (syn' , n-syn')) [ m' ]⇐ ana'} fill2)))) = WTPair mprod con1 (beyond-▷-contra (beyond-l↦-env step fill1 fill2) con2) con3 con4 consist con5 wt1 (PreservationAna wt2 (StepLow fill1 step fill2))
    PreservationAna (WTPair {syn-fst = syn-fst} {ana-all = □ , Old} (NTProdC DTProdNone) (▷Pair ▶Old) (▷Pair ▶Old) ▶Old con4 (~N-pair consist) con5 wt1 wt2) (StepLow (FillLEnvLowRec (FillLEnvUpRec (FillLEnvPair2 fill1))) step (FillLEnvLowRec (FillLEnvUpRec (FillLEnvPair2 {e' = (e' ⇒ (syn' , n-syn')) [ m' ]⇐ ana'} fill2)))) rewrite ~DVoid-right consist = 
      WTPair (NTProdC DTProdNone) (▷Pair ▶Old) (beyond-▷-contra (beyond-l↦-env step fill1 fill2) (▷Pair ▶Old)) ▶Old (preservation-pair-lemma {syn1 = syn-fst} {ana = □ , Old} =▷Refl (beyond-l↦-env-inner step fill1 fill2) con4) (~N-pair ~DVoidR) con5 wt1 (PreservationAna wt2 (StepLow fill1 step fill2))

  PreservationProgram :  
    ∀ {p p'} ->
    (P⊢ p) ->
    (p P↦ p') ->     
    (P⊢ p') 
  PreservationProgram (WTProgram ana) (InsideStep step) = WTProgram (PreservationAna ana step)
  PreservationProgram (WTProgram ana) TopStep = WTProgram (oldify-syn-inner ana)  