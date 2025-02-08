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

  beyond-U↦ : ∀ {e e' syn syn'} -> 
    (e ⇒ syn) U↦ (e' ⇒ syn') -> 
    =▷ syn syn' 
  beyond-U↦ (StepAp _) = =▷New
  beyond-U↦ StepAsc = =▷New

  beyond-U↦-env : ∀ {ε e e' e-in e-in' syn syn'} -> 
    e-in U↦ e-in' -> 
    ε U⟦ e-in ⟧Up== (e ⇒ syn) ->
    ε U⟦ e-in' ⟧Up== (e' ⇒ syn') ->
    =▷ syn syn' 
  beyond-U↦-env step FillU⊙ FillU⊙ = beyond-U↦ step
  beyond-U↦-env step (FillUEnvUpRec _) (FillUEnvUpRec _) = =▷Refl

  beyond-L↦ : ∀ {e e' m m' ana ana'} -> 
    (e [ m ]⇐ ana) L↦ (e' [ m' ]⇐ ana') -> 
    ◁▷ ana ana' 
  beyond-L↦ (StepNewSynConsist _) = ◁▷C
  beyond-L↦ (StepNewAnaConsist _ _) = ◁▷C
  beyond-L↦ (StepAnaFun _ _) = ◁▷C
  beyond-L↦ (StepSynFun) = ◁▷C
  beyond-L↦ (StepNewAnnFun _) = ◁▷C

  beyond-L↦-inner : ∀ {e e' syn syn' m m' n-ana ana'} -> 
    ((e ⇒ syn) [ m ]⇐ (□ , n-ana)) L↦ ((e' ⇒ syn') [ m' ]⇐ ana') -> 
    =▷ syn syn' 
  beyond-L↦-inner (StepNewAnaConsist x x₁) = =▷Refl
  beyond-L↦-inner (StepAnaFun x x₁) = =▷New
  beyond-L↦-inner (StepNewAnnFun x) = =▷New
  beyond-L↦-inner StepSynFun = =▷New

  beyond-L↦-env-inner : ∀ {ε e e' e-in e-in' syn syn' m m' n-ana ana'} -> 
    e-in L↦ e-in' -> 
    ε L⟦ e-in ⟧Low== ((e ⇒ syn) [ m ]⇐ (□ , n-ana)) ->
    ε L⟦ e-in' ⟧Low== ((e' ⇒ syn') [ m' ]⇐ ana') ->
    =▷ syn syn' 
  beyond-L↦-env-inner step FillL⊙ FillL⊙ = beyond-L↦-inner step
  beyond-L↦-env-inner step (FillLEnvLowRec (FillLEnvUpRec _)) (FillLEnvLowRec (FillLEnvUpRec _)) = =▷Refl

  beyond-L↦-env : ∀ {ε e e' e-in e-in' m m' ana ana'} -> 
    e L↦ e' -> 
    ε L⟦ e ⟧Low== (e-in [ m ]⇐ ana) ->
    ε L⟦ e' ⟧Low== (e-in' [ m' ]⇐ ana') ->
    ◁▷ ana ana' 
  beyond-L↦-env step FillL⊙ FillL⊙ = beyond-L↦ step
  beyond-L↦-env step (FillLEnvLowRec _) (FillLEnvLowRec _) = ◁▷C

  void-ana-step-same : ∀ {e n e' m t n'} ->
    (e [ ✔ ]⇐ (□ , n)) L↦ (e' [ m ]⇐ (t , n')) -> 
    (m ≡ ✔) × (t ≡ □)
  void-ana-step-same (StepNewAnaConsist x ~DVoidR) = refl , refl
  void-ana-step-same (StepAnaFun x x₁) = refl , refl
  void-ana-step-same (StepNewAnnFun x) = refl , refl
  void-ana-step-same StepSynFun = refl , refl

  step-subsumable : ∀ {e e' syn syn'} -> 
    (e ⇒ syn) U↦ (e' ⇒ syn') ->
    SubsumableMid e -> 
    SubsumableMid e'
  step-subsumable (StepAp _) SubsumableAp = SubsumableAp
  step-subsumable StepAsc SubsumableAsc = SubsumableAsc

  PreservationStepSyn :  
    ∀ {Γ e e'} ->
    (Γ ⊢ e ⇒) ->
    (e U↦ e') ->   
    (Γ ⊢ e' ⇒)
  PreservationStepSyn (SynConst _) ()
  PreservationStepSyn (SynHole _) ()
  PreservationStepSyn (SynAp marrow consist-syn consist-ana consist-mark syn ana) (StepAp marrow') = SynAp (NTArrowC (DTArrowSome marrow')) (▷Pair ▶Old) (▷Pair ▶Old) ▶Old (oldify-syn-inner syn) (small-newify-ana ana)
  PreservationStepSyn (SynVar _ _) ()
  PreservationStepSyn (SynAsc consist-syn consist-ana ana) StepAsc = SynAsc (▷■Pair (▷Pair ▶Old)) (▷■Pair (▷Pair ▶Old)) (small-newify-ana ana)
  
  PreservationStepAna :  
    ∀ {Γ e e'} ->
    (Γ ⊢ e ⇐) ->
    (e L↦ e') ->   
    (Γ ⊢ e' ⇐)
  PreservationStepAna (AnaSubsume subsumable (~N-pair consist-t) consist-m syn) (StepNewSynConsist consist) with consist-t 
  ... | ~DSome consist-t rewrite ~-unicity consist consist-t = AnaSubsume subsumable (~N-pair (~DSome consist-t)) ▶Old (oldify-syn syn)
  PreservationStepAna (AnaSubsume subsumable (~N-pair consist-t) consist-m syn) (StepNewAnaConsist subsumable' consist) with ~D-unicity consist consist-t 
  ... | refl = AnaSubsume subsumable' (~N-pair consist-t) ▶Same (oldify-syn syn)
  PreservationStepAna (AnaFun marrow consist consist-ana consist-asc consist-body consist-syn (~N-pair (~DSome consist-all)) consist-m-all ana) (StepNewSynConsist consist') rewrite ~-unicity consist' consist-all  = AnaFun marrow consist consist-ana consist-asc consist-body (beyond-▷-contra ◁▷C consist-syn) (~N-pair (~DSome consist-all)) ▶Old ana
  PreservationStepAna (AnaFun {t-asc = t-asc , n-asc} (NTArrowC x) consist (▷Pair ▶New) ▶New consist-body consist-syn consist-all consist-m-all ana) (StepAnaFun marrow' (■~D-pair consist')) = AnaFun (NTArrowC marrow') (■~N-pair (~N-pair consist')) (▷Pair ▶Old) ▶Old ▶Same (consist-unless-lemma {n1 = n-asc}) (~N-pair ~D-unless) ▶Same (newify-ana ana)
  PreservationStepAna (AnaFun {x = x} {e-body = e-body} marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) (StepNewAnnFun {e-body' = e-body' ⇒ (syn-body' , n-syn-body')} {t-asc} {t-body} {n-body} vars-syn) 
    = AnaFun (NTArrowC DTArrowNone) (■~N-pair (~N-pair ~DVoidR)) (▷Pair ▶Old) ▶Old ▶Old (preservation-lambda-lemma-2 (vars-syn?-beyond vars-syn')) (~N-pair ~DVoidR) ▶New (preservation-vars-ana? ana vars-syn) 
    where 
    vars-syn' : VarsSynthesize? x t-asc ✔ (e-body ⇒ (■ t-body , n-body)) (e-body' ⇒ (syn-body' , n-syn-body' ⊓ Old))
    vars-syn' rewrite max-old n-syn-body' = vars-syn
  PreservationStepAna (AnaFun marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) StepSynFun = AnaFun (NTArrowC DTArrowNone) (■~N-pair (~N-pair ~DVoidR)) (▷Pair ▶Old) ▶Old ▶Same (▷Pair ▶Same) (~N-pair ~DVoidR) ▶New (oldify-syn-inner ana)

  mutual 

    PreservationSyn :  
      ∀ {Γ e e'} ->
      (Γ ⊢ e ⇒) ->
      (e Up↦ e') ->   
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
    ... | t-in-fun' , t-out-fun' , m-fun' , marrow' with beyond-▸NTArrow (beyond-U↦ step) marrow marrow' 
    ... | t-in-beyond , t-out-beyond , m-beyond = SynAp marrow' (beyond-▷ t-out-beyond consist-syn) (beyond-▷ t-in-beyond consist-ana) (beyond-▶ m-beyond consist-mark) (PreservationAna syn (StepUp (FillUEnvLowRec FillU⊙) step (FillUEnvLowRec FillU⊙))) ana 
    PreservationSyn (SynAp marrow consist-syn consist-ana consist-mark syn ana) (StepLow (FillLEnvUpRec (FillLEnvAp1 (FillLEnvLowRec (FillLEnvUpRec fill1)))) step (FillLEnvUpRec (FillLEnvAp1 (FillLEnvLowRec (FillLEnvUpRec fill2))))) = SynAp marrow consist-syn consist-ana consist-mark (PreservationAna syn (StepLow (FillLEnvLowRec (FillLEnvUpRec fill1)) step (FillLEnvLowRec (FillLEnvUpRec fill2)))) ana 
    PreservationSyn (SynAp marrow consist-syn consist-ana consist-mark syn ana) (StepLow {e-in' = (e-fun' ⇒ syn-fun') [ x₁ ]⇐ (fst , snd)} (FillLEnvUpRec (FillLEnvAp1 FillL⊙)) step (FillLEnvUpRec (FillLEnvAp1 FillL⊙))) with ▸NTArrow-dec syn-fun' 
    ... | t-in-fun' , t-out-fun' , m-fun' , marrow' with beyond-▸NTArrow (beyond-L↦-inner step) marrow marrow' 
    ... | t-in-beyond , t-out-beyond , m-beyond with void-ana-step-same step 
    ... | refl , refl = SynAp marrow' (beyond-▷ t-out-beyond consist-syn) (beyond-▷ t-in-beyond consist-ana) (beyond-▶ m-beyond consist-mark) (PreservationAna syn (StepLow FillL⊙ step FillL⊙)) ana 
    PreservationSyn (SynAp marrow consist-syn consist-ana consist-mark syn ana) (StepUp (FillUEnvUpRec (FillUEnvAp2 (FillUEnvLowRec fill1))) step (FillUEnvUpRec (FillUEnvAp2 (FillUEnvLowRec fill2)))) = SynAp marrow consist-syn consist-ana consist-mark syn (PreservationAna ana (StepUp (FillUEnvLowRec fill1) step (FillUEnvLowRec fill2)))
    PreservationSyn (SynAp marrow consist-syn consist-ana consist-mark syn ana) (StepLow {e-in' = e-in' [ m' ]⇐ ana'} (FillLEnvUpRec (FillLEnvAp2 FillL⊙)) step (FillLEnvUpRec (FillLEnvAp2 FillL⊙))) = SynAp marrow consist-syn (beyond-▷-contra (beyond-L↦-env step FillL⊙ FillL⊙) consist-ana) consist-mark syn (PreservationAna ana (StepLow FillL⊙ step FillL⊙))  
    PreservationSyn (SynAp marrow consist-syn consist-ana consist-mark syn ana) (StepLow (FillLEnvUpRec (FillLEnvAp2 (FillLEnvLowRec fill1))) step (FillLEnvUpRec (FillLEnvAp2 (FillLEnvLowRec fill2)))) = SynAp marrow consist-syn consist-ana consist-mark syn (PreservationAna ana (StepLow (FillLEnvLowRec fill1) step (FillLEnvLowRec fill2)))
    PreservationSyn (SynAsc consist-syn consist-ana ana) (StepLow (FillLEnvUpRec (FillLEnvAsc fill1)) step (FillLEnvUpRec (FillLEnvAsc {e' = e-body' [ m-body' ]⇐ ana-body'} fill2))) = SynAsc consist-syn (beyond-▷■-contra (beyond-L↦-env step fill1 fill2) consist-ana) (PreservationAna ana (StepLow fill1 step fill2))
    PreservationSyn (SynAsc consist-syn consist-ana ana) (StepUp (FillUEnvUpRec (FillUEnvAsc (FillUEnvLowRec fill1))) step (FillUEnvUpRec (FillUEnvAsc (FillUEnvLowRec fill2)))) = SynAsc consist-syn consist-ana (PreservationAna ana (StepUp (FillUEnvLowRec fill1) step (FillUEnvLowRec fill2)))

    PreservationAna :  
      ∀ {Γ e e'} -> 
      (Γ ⊢ e ⇐) ->
      (e Low↦ e') ->   
      (Γ ⊢ e' ⇐) 
    PreservationAna ana (StepLow FillL⊙ step FillL⊙) = PreservationStepAna ana step
    PreservationAna (AnaSubsume {ana-all = ana-all} subsumable consist-t consist-m syn) (StepUp {e-in' = e-all' ⇒ syn-all'} (FillUEnvLowRec FillU⊙) step (FillUEnvLowRec FillU⊙)) with ~N-dec syn-all' ana-all 
    ... | m' , consist-t' = AnaSubsume (step-subsumable step subsumable) consist-t' (beyond-▶ (beyond-through-~N (beyond-U↦ step) consist-t consist-t') consist-m) (PreservationSyn syn (StepUp FillU⊙ step FillU⊙))    
    PreservationAna (AnaSubsume subsumable consist-t consist-m syn) (StepUp (FillUEnvLowRec (FillUEnvUpRec fill1)) step (FillUEnvLowRec (FillUEnvUpRec fill2))) = AnaSubsume (u-env-subsumable fill1 fill2 subsumable) consist-t consist-m (PreservationSyn syn (StepUp (FillUEnvUpRec fill1) step (FillUEnvUpRec fill2)))
    PreservationAna (AnaSubsume subsumable consist-t consist-m syn) (StepLow (FillLEnvLowRec (FillLEnvUpRec fill1)) step (FillLEnvLowRec (FillLEnvUpRec fill2))) = AnaSubsume (l-env-subsumable fill1 fill2 subsumable) consist-t consist-m (PreservationSyn syn (StepLow (FillLEnvUpRec fill1) step (FillLEnvUpRec fill2))) 
    PreservationAna (AnaFun {t-asc = t-asc} marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) (StepUp (FillUEnvLowRec (FillUEnvUpRec (FillUEnvFun (FillUEnvLowRec fill1)))) step (FillUEnvLowRec (FillUEnvUpRec (FillUEnvFun (FillUEnvLowRec {e' = e' ⇒ syn'} fill2))))) = AnaFun marrow consist consist-ana consist-asc consist-body (preservation-lambda-lemma-3 {t = t-asc} (beyond-U↦-env step fill1 fill2) consist-syn) consist-all consist-m-all (PreservationAna ana (StepUp (FillUEnvLowRec fill1) step (FillUEnvLowRec fill2))) 
    PreservationAna (AnaFun {ana-all = ana-all , New} {t-asc = (t-asc , n-asc)} marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) (StepLow (FillLEnvLowRec (FillLEnvUpRec (FillLEnvFun fill1))) step (FillLEnvLowRec (FillLEnvUpRec (FillLEnvFun {e' = (e' ⇒ (syn' , n-syn')) [ m' ]⇐ ana'} fill2)))) = AnaFun marrow consist (beyond-▷-contra (beyond-L↦-env step fill1 fill2) consist-ana) consist-asc consist-body NUnless-new-▷ consist-all consist-m-all (PreservationAna ana (StepLow fill1 step fill2))
    PreservationAna (AnaFun {ana-all = ■ ana-all , Old} {t-asc = (t-asc , n-asc)} marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) (StepLow (FillLEnvLowRec (FillLEnvUpRec (FillLEnvFun fill1))) step (FillLEnvLowRec (FillLEnvUpRec (FillLEnvFun {e' = (e' ⇒ (syn' , n-syn')) [ m' ]⇐ ana'} fill2)))) =  AnaFun marrow consist (beyond-▷-contra (beyond-L↦-env step fill1 fill2) consist-ana) consist-asc consist-body consist-syn consist-all consist-m-all (PreservationAna ana (StepLow fill1 step fill2))
    PreservationAna (AnaFun {syn-body = syn-body} {ana-all = □ , Old} {t-asc = t-asc , n-asc} (NTArrowC DTArrowNone) (■~N-pair (~N-pair ~DVoidR)) (▷Pair ▶Old) ▶Old consist-body consist-syn (~N-pair {d1} {n1 = n1} consist) consist-m-all ana) (StepLow (FillLEnvLowRec (FillLEnvUpRec (FillLEnvFun fill1))) step (FillLEnvLowRec (FillLEnvUpRec (FillLEnvFun {e' = (e' ⇒ (syn' , n-syn')) [ m' ]⇐ ana'} fill2)))) --= ?
      = AnaFun (NTArrowC DTArrowNone) (■~N-pair (~N-pair ~DVoidR)) (beyond-▷-contra (beyond-L↦-env step fill1 fill2) (▷Pair ▶Old)) ▶Old consist-body (preservation-lambda-lemma-3 {t = (t-asc , n-asc)} {syn1 = syn-body} {syn1' = (syn' , n-syn')} {syn2 = (d1 , n1)} {ana = □ , Old} (beyond-L↦-env-inner step fill1 fill2) consist-syn) (~N-pair consist) consist-m-all (PreservationAna ana (StepLow fill1 step fill2))

  PreservationProgram :  
    ∀ {p p'} ->
    (WellTypedProgram p) ->
    (p P↦ p') ->   
    (WellTypedProgram p')
  PreservationProgram (WTProg ana) (TopStep step) = WTProg (PreservationAna ana step)
  