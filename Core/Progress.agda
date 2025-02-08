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
open import Core.Lemmas-Preservation
open import Core.VarsSynthesize
open import Core.Update
open import Core.Settled

module Core.Progress where

  mutual 

    productive-syn-syn : ∀{Γ e t n} ->
      SubsumableMid e ->
      SettledMid e -> 
      Γ ⊢ (e ⇒ (t , n)) ⇒ ->
      ∃[ t' ] (t ≡ ■ t') 
    productive-syn-syn SubsumableConst SettledConst (SynConst (▷Pair ▶Old)) = _ , refl
    productive-syn-syn SubsumableHole SettledHole (SynHole (▷Pair ▶Old)) = _ , refl
    productive-syn-syn SubsumableVar SettledVar (SynVar x x₁) = _ , refl
    productive-syn-syn SubsumableAsc (SettledAsc x) (SynAsc x₁ x₂ x₃) = _ , refl
    productive-syn-syn SubsumableAp (SettledAp (SettledLowC (SettledUpC settled)) _) (SynAp marrow consist x₄ x₅ syn ana)  with productive-syn-ana settled syn | marrow | consist
    ... | _ , refl | NTArrowC (DTArrowSome x) | ▷Pair ▶Old = _ , refl

    productive-syn-ana : ∀{Γ e t m n} ->
      SettledMid e -> 
      Γ ⊢ (e ⇒ (t , n)) [ m ]⇐ (□ , Old) ⇐ ->
      ∃[ t' ] (t ≡ ■ t') 
    productive-syn-ana settled (AnaSubsume x x₁ x₂ x₃) = productive-syn-syn x settled x₃
    productive-syn-ana (SettledFun (SettledLowC (SettledUpC settled))) (AnaFun (NTArrowC DTArrowNone) a2 (▷Pair ▶Old) a4 a5 a6 a7 a8 ana) with productive-syn-ana settled ana | a6
    ... | t , refl | ▷Pair ▶Old = _ , refl

  new-ana-steps-syn-inner : ∀ {Γ e m t} ->
    Γ ⊢ e ⇒ ->
    ∃[ e' ] (e [ m ]⇐ (t , New)) L↦ e' 
  new-ana-steps-syn-inner (SynConst (▷Pair x)) = _ , StepNewAnaConsist SubsumableConst (proj₂ (~D-dec _ _)) 
  new-ana-steps-syn-inner (SynHole x) = _ , StepNewAnaConsist SubsumableHole (proj₂ (~D-dec _ _)) 
  new-ana-steps-syn-inner (SynAp x x₁ x₂ x₃ x₄ x₅) = _ , StepNewAnaConsist SubsumableAp (proj₂ (~D-dec _ _)) 
  new-ana-steps-syn-inner (SynVar x x₁) = _ , StepNewAnaConsist SubsumableVar  (proj₂ (~D-dec _ _)) 
  new-ana-steps-syn-inner (SynAsc x x₁ x₂) = _ , StepNewAnaConsist SubsumableAsc (proj₂ (~D-dec _ _)) 

  new-ana-steps-syn : ∀ {Γ e m t} ->
    Γ ⊢ e ⇒ ->
    ∃[ e' ] (e [ m ]⇐ (t , New)) Low↦ e' 
  new-ana-steps-syn syn with new-ana-steps-syn-inner syn 
  ... | e' , step = e' , (StepLow FillL⊙ step FillL⊙)

  new-ana-steps-inner : ∀ {Γ e m t} ->
    Γ ⊢ (e [ m ]⇐ (t , New)) ⇐ ->
    ∃[ e' ] (e [ m ]⇐ (t , New)) L↦ e' 
  new-ana-steps-inner (AnaSubsume x x₁ x₂ syn) = new-ana-steps-syn-inner syn
  new-ana-steps-inner (AnaFun x x₁ x₂ x₃ x₄ x₅ x₆ x₇ ana) = _ , (StepAnaFun (proj₂ (proj₂ (proj₂ (▸DTArrow-dec _)))) (■~D-pair (proj₂ (~D-dec _ _))))

  new-ana-steps : ∀ {Γ e m t} ->
    Γ ⊢ (e [ m ]⇐ (t , New)) ⇐ ->
    ∃[ e' ] (e [ m ]⇐ (t , New)) Low↦ e' 
  new-ana-steps ana with new-ana-steps-inner ana 
  ... | e' , step = e' , (StepLow FillL⊙ step FillL⊙)


  _≡B?_ : (x y : Binding) -> Dec (x ≡ y) 
  BHole ≡B? BHole = yes refl
  BHole ≡B? BVar x = no (λ ())
  BVar x ≡B? BHole = no (λ ())
  BVar x ≡B? BVar y with x ≡? y 
  ... | yes refl = yes refl 
  ... | no neq = no (λ eq → neq (helper eq))
    where 
    helper : BVar x ≡ BVar y -> x ≡ y
    helper refl = refl 

  vars-syn-dec : ∀ {e x t m} ->
    ∃[ e' ] (VarsSynthesize x t m e e')
  vars-syn-dec {EConst ⇒ x₁} = (EConst ⇒ x₁) , VSConst
  vars-syn-dec {EHole ⇒ x₁} = (EHole ⇒ x₁) , VSHole
  vars-syn-dec {EAp (x [ x₄ ]⇐ x₅) x₂ (x₃ [ x₆ ]⇐ x₇) ⇒ x₁} = _ , (VSAp (proj₂ vars-syn-dec) (proj₂ vars-syn-dec))
  vars-syn-dec {EAsc x (x₂ [ x₃ ]⇐ x₄) ⇒ x₁} = _ , (VSAsc (proj₂ vars-syn-dec))
  vars-syn-dec {EFun x x₂ x₃ x₄ (x₅ [ x₆ ]⇐ x₇) ⇒ x₁} {y} with ((BVar y) ≡B? x) 
  ... | yes refl = _ , VSFunEq 
  ... | no neq = _ , VSFunNeq neq (proj₂ vars-syn-dec)
  vars-syn-dec {EVar x x₂ ⇒ x₁} {y} with (y ≡? x) 
  ... | yes refl = _ , VSVarEq 
  ... | no neq = _ , VSVarNeq neq

  vars-syn?-dec : ∀ {x e t m} ->
    ∃[ e' ] (VarsSynthesize? x t m e e')
  vars-syn?-dec {BHole} = _ , refl
  vars-syn?-dec {BVar x} = vars-syn-dec

  vars-syn?-dec-elaborate : ∀ {x e t m} ->
    ∃[ e' ] ∃[ t' ] ∃[ n' ] (VarsSynthesize? x t m e (e' ⇒ (t' , n')))
  vars-syn?-dec-elaborate {x} {e} {t} {m} with vars-syn?-dec {x} {e} {t} {m} 
  ... | e' ⇒ (t' , n') , vars-syn = e' , t' , n' , vars-syn

  mutual 
    
    ProgressUp :  
      ∀ {Γ e} ->
      (Γ ⊢ e ⇒) ->      
      (∃[ e' ] (e Up↦ e')) + (AlmostSettledUp e)
    ProgressUp (SynConst consist) = Inr (AlmostSettledUpC SettledConst)
    ProgressUp (SynHole consist) = Inr (AlmostSettledUpC SettledHole)
    ProgressUp (SynAp marrow x₁ x₂ x₃ syn ana) with ProgressLow syn | ProgressLow ana 
    ProgressUp (SynAp marrow x₁ x₂ x₃ syn ana) | Inl (e' , step) | progress = Inl (_ , StepLowUp (FillLEnvUpRec (FillLEnvAp1 FillL⊙)) step (FillLEnvUpRec (FillLEnvAp1 FillL⊙)))
    ProgressUp (SynAp marrow x₁ x₂ x₃ syn ana) | Inr (AlmostSettledLowC (AlmostSettledUpC {New} settled1)) | progress = Inl (_ , StepUp FillU⊙ (StepAp (proj₂ (proj₂ (proj₂ (▸DTArrow-dec _))))) FillU⊙)
    ProgressUp (SynAp marrow x₁ x₂ x₃ syn ana) | Inr (AlmostSettledLowC (AlmostSettledUpC {Old} settled1)) | Inl (e' , step) = Inl (_ , StepLowUp (FillLEnvUpRec (FillLEnvAp2 FillL⊙)) step (FillLEnvUpRec (FillLEnvAp2 FillL⊙)))
    ProgressUp (SynAp marrow x₁ x₂ x₃ syn ana) | Inr (AlmostSettledLowC (AlmostSettledUpC {Old} settled1)) | Inr (AlmostSettledLowC (AlmostSettledUpC {n} settled2)) with productive-syn-ana settled1 syn | marrow | x₂
    ProgressUp (SynAp marrow x₁ x₂ x₃ syn ana) | Inr (AlmostSettledLowC (AlmostSettledUpC {.Old} settled1)) | Inr (AlmostSettledLowC (AlmostSettledUpC {New} settled2)) | t , refl | NTArrowC (DTArrowSome x) | ▷Pair ▶Old = Inl (_ , StepLow (FillLEnvUpRec (FillLEnvAp2 FillL⊙)) (StepNewSynConsist (proj₂ (~D-dec _ _))) (FillLEnvUpRec (FillLEnvAp2 FillL⊙))) 
    ProgressUp (SynAp marrow x₁ x₂ x₃ syn ana) | Inr (AlmostSettledLowC (AlmostSettledUpC {.Old} settled1)) | Inr (AlmostSettledLowC (AlmostSettledUpC {Old} settled2)) | t , refl | NTArrowC (DTArrowSome x) | ▷Pair ▶Old = Inr (AlmostSettledUpC (SettledAp (SettledLowC (SettledUpC settled1)) (SettledLowC (SettledUpC settled2)))) 
    ProgressUp (SynVar x x₁) = Inr (AlmostSettledUpC SettledVar)
    ProgressUp (SynAsc {t-asc = (t-asc , New)} x x₁ ana) = Inl (_ , StepUp FillU⊙ StepAsc FillU⊙) 
    ProgressUp (SynAsc {t-asc = (t-asc , Old)} x x₁ ana) with ProgressLow ana 
    ... | Inl (e' , step) = Inl (_ , StepLowUp (FillLEnvUpRec (FillLEnvAsc FillL⊙)) step (FillLEnvUpRec (FillLEnvAsc FillL⊙))) 
    ... | Inr (AlmostSettledLowC (AlmostSettledUpC {New} settled)) = Inl (_ , StepLow (FillLEnvUpRec (FillLEnvAsc FillL⊙)) (StepNewSynConsist (proj₂ (~D-dec _ _))) (FillLEnvUpRec (FillLEnvAsc FillL⊙))) 
    ... | Inr (AlmostSettledLowC (AlmostSettledUpC {Old} settled)) = Inr (AlmostSettledUpC (SettledAsc (SettledLowC (SettledUpC settled)))) 

    ProgressLow :  
      ∀ {Γ e} ->
      (Γ ⊢ e ⇐) ->      
      (∃[ e' ] (e Low↦ e')) + (AlmostSettledLow e)
    ProgressLow (AnaSubsume subsumable consist m-consist syn) with ProgressUp syn 
    ProgressLow (AnaSubsume subsumable consist m-consist syn) | Inl (e' , step) = Inl (_ , StepUpLow (FillUEnvLowRec FillU⊙) step (FillUEnvLowRec FillU⊙))
    ProgressLow (AnaSubsume {ana-all = t , New} subsumable consist m-consist syn) | Inr settled = Inl (new-ana-steps-syn syn)
    ProgressLow (AnaSubsume {ana-all = t , Old}  subsumable consist m-consist syn) | Inr settled = Inr (AlmostSettledLowC settled)
    ProgressLow (AnaFun {ana-all = t , New} (NTArrowC marrow) (■~N-pair (~N-pair consist)) consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) = Inl (_ , StepLow FillL⊙ (StepAnaFun marrow (■~D-pair consist)) FillL⊙) 
    ProgressLow (AnaFun {ana-all = ana-all , Old} {t-asc = t-asc , New} (NTArrowC marrow) (■~N-pair (~N-pair consist)) consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) = Inl (_ , StepLow FillL⊙ (StepNewAnnFun marrow (■~D-pair consist) (proj₂ (proj₂ (proj₂ vars-syn?-dec-elaborate)))) FillL⊙)
    
    ProgressLow (AnaFun {ana-all = ana-all , Old} {ana-body = ana-body , New} {t-asc = t-asc , Old} marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) = Inl (_ , StepLow (FillLEnvLowRec (FillLEnvUpRec (FillLEnvFun FillL⊙))) (proj₂ (new-ana-steps-inner ana)) (FillLEnvLowRec (FillLEnvUpRec (FillLEnvFun FillL⊙))))
    ProgressLow (AnaFun {ana-all = ana-all , Old} {ana-body = ana-body , Old} {t-asc = t-asc , Old} marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) with ProgressLow ana  
    ProgressLow (AnaFun {ana-all = ana-all , Old} {ana-body = ana-body , Old} {t-asc = t-asc , Old} marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) | Inl (e' , step) = Inl (_ , StepLowLow (FillLEnvLowRec (FillLEnvUpRec (FillLEnvFun FillL⊙))) step (FillLEnvLowRec (FillLEnvUpRec (FillLEnvFun FillL⊙))))
    ProgressLow (AnaFun {ana-all = ana-all , Old} {ana-body = ana-body , Old} {t-asc = t-asc , Old} marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) | Inr (AlmostSettledLowC (AlmostSettledUpC {New} settled)) with ana-body 
    ProgressLow (AnaFun {ana-all = ana-all , Old} {ana-body = ana-body , Old} {t-asc = t-asc , Old} marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) | Inr (AlmostSettledLowC (AlmostSettledUpC {New} settled)) | □ = Inl (_ , StepLow FillL⊙ StepSynFun FillL⊙)
    ProgressLow (AnaFun {ana-all = ana-all , Old} {ana-body = ana-body , Old} {t-asc = t-asc , Old} marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) | Inr (AlmostSettledLowC (AlmostSettledUpC {New} settled)) | ■ _ = Inl (_ , StepLow (FillLEnvLowRec (FillLEnvUpRec (FillLEnvFun FillL⊙))) (StepNewSynConsist (proj₂ (~D-dec _ _))) (FillLEnvLowRec (FillLEnvUpRec (FillLEnvFun FillL⊙)))) 
    ProgressLow (AnaFun {ana-all = ana-all , Old} {ana-body = ana-body , Old} {t-asc = t-asc , Old} marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) | Inr (AlmostSettledLowC (AlmostSettledUpC {Old} settled)) = Inr (AlmostSettledLowC (AlmostSettledUpC (SettledFun (SettledLowC (SettledUpC settled)))))

  step-preserves-program : ∀ {p e} -> 
    ExpLowOfProgram p Low↦ e -> 
    ∃[ p' ] (e ≡ ExpLowOfProgram p')
  step-preserves-program {p = Root e n} (StepUp (FillUEnvLowRec x) step (FillUEnvLowRec x₁)) = Root _ _ , refl
  step-preserves-program {p = Root e n} (StepLow (FillLEnvLowRec x) step (FillLEnvLowRec x₁)) = Root _ _ , refl
  step-preserves-program {p = Root e n} (StepLow FillL⊙ (StepNewAnaConsist x consist) FillL⊙) with ~DVoid-right consist 
  ... | refl = Root _ _ , refl
  step-preserves-program {p = Root e n} (StepLow FillL⊙ (StepAnaFun _ _) FillL⊙) = Root _ _ , refl
  step-preserves-program {p = Root e n} (StepLow FillL⊙ (StepNewAnnFun _ _ _) FillL⊙) = Root _ _ , refl
  step-preserves-program {p = Root e n} (StepLow FillL⊙ StepSynFun FillL⊙) = Root _ _ , refl

  ProgressProgram : ∀ {p} ->
    WellTypedProgram p ->   
    (∃[ p' ] (p P↦ p')) + (SettledProgram p)   
  ProgressProgram (WTProg ana) with ProgressLow ana   
  ProgressProgram (WTProg ana) | Inl (e' , step) with step-preserves-program step 
  ProgressProgram (WTProg ana) | Inl (e' , step) | p' , refl = Inl (p' , (InsideStep step)) 
  ProgressProgram {p = Root e n} (WTProg ana) | Inr (AlmostSettledLowC (AlmostSettledUpC {Old} settled)) = Inr (SettledRoot (SettledLowC (SettledUpC settled))) 
  ProgressProgram {p = Root e n} (WTProg ana) | Inr (AlmostSettledLowC (AlmostSettledUpC {New} settled)) = Inl (_ , TopStep) 

  mutual 
    
    UnProgressUp : ∀ {Γ e e'} ->
      (Γ ⊢ e ⇒) ->  
      (e Up↦ e') -> 
      (SettledUp e) ->
      ⊥ 
    UnProgressUp (SynConst x) (StepUp FillU⊙ () FillU⊙) settled
    UnProgressUp (SynHole x) (StepUp FillU⊙ () FillU⊙) settled
    UnProgressUp (SynVar x x₁) (StepUp FillU⊙ () FillU⊙) settled
    UnProgressUp (SynAp _ _ _ _ _ _) (StepUp FillU⊙ (StepAp _) FillU⊙) (SettledUpC (SettledAp (SettledLowC ()) _))
    UnProgressUp (SynAsc _ _ ana) (StepUp FillU⊙ StepAsc FillU⊙) (SettledUpC ())
    UnProgressUp (SynConst x) (StepUp (FillUEnvUpRec ()) step (FillUEnvUpRec x₁)) settled
    UnProgressUp (SynHole x) (StepUp (FillUEnvUpRec ()) step (FillUEnvUpRec x₁)) settled
    UnProgressUp (SynVar _ _) (StepUp (FillUEnvUpRec ()) step (FillUEnvUpRec x₁)) settled
    UnProgressUp (SynAp _ _ _ _ syn ana) (StepUp (FillUEnvUpRec (FillUEnvAp1 fill1)) step (FillUEnvUpRec (FillUEnvAp1 fill2))) (SettledUpC (SettledAp settled _)) = UnProgressLow syn (StepUp fill1 step fill2) settled
    UnProgressUp (SynAp _ _ _ _ syn ana) (StepUp (FillUEnvUpRec (FillUEnvAp2 fill1)) step (FillUEnvUpRec (FillUEnvAp2 fill2))) (SettledUpC (SettledAp _ settled)) = UnProgressLow ana (StepUp fill1 step fill2) settled
    UnProgressUp (SynAsc _ _ ana) (StepUp (FillUEnvUpRec (FillUEnvAsc fill1)) step (FillUEnvUpRec (FillUEnvAsc fill2))) (SettledUpC (SettledAsc settled)) = UnProgressLow ana (StepUp fill1 step fill2) settled
    
    UnProgressUp (SynConst x) (StepLow (FillLEnvUpRec ()) step (FillLEnvUpRec fill2)) (SettledUpC settled)
    UnProgressUp (SynHole x) (StepLow (FillLEnvUpRec ()) step (FillLEnvUpRec fill2)) (SettledUpC settled)
    UnProgressUp (SynVar _ _) (StepLow (FillLEnvUpRec ()) step (FillLEnvUpRec fill2)) (SettledUpC settled)
    UnProgressUp (SynAp _ _ _ _ syn ana) (StepLow (FillLEnvUpRec (FillLEnvAp1 fill1)) step (FillLEnvUpRec (FillLEnvAp1 fill2))) (SettledUpC (SettledAp settled _)) = UnProgressLow syn (StepLow fill1 step fill2) settled
    UnProgressUp (SynAp _ _ _ _ syn ana) (StepLow (FillLEnvUpRec (FillLEnvAp2 fill1)) step (FillLEnvUpRec (FillLEnvAp2 fill2))) (SettledUpC (SettledAp _ settled)) = UnProgressLow ana (StepLow fill1 step fill2) settled
    UnProgressUp (SynAsc _ _ ana) (StepLow (FillLEnvUpRec (FillLEnvAsc fill1)) step (FillLEnvUpRec (FillLEnvAsc fill2))) (SettledUpC (SettledAsc settled)) = UnProgressLow ana (StepLow fill1 step fill2) settled

    UnProgressLow : ∀ {Γ e e'} ->
      (Γ ⊢ e ⇐) ->  
      (e Low↦ e') -> 
      (SettledLow e) ->
      ⊥ 
    UnProgressLow (AnaSubsume _ _ _ syn) (StepLow FillL⊙ (StepNewSynConsist _) FillL⊙) (SettledLowC ())
    UnProgressLow (AnaSubsume _ _ _ syn) (StepLow (FillLEnvLowRec fill1) step (FillLEnvLowRec fill2)) (SettledLowC settled) = UnProgressUp syn (StepLow fill1 step fill2) settled
    UnProgressLow (AnaSubsume _ _ _ syn) (StepUp (FillUEnvLowRec fill1) step (FillUEnvLowRec fill2)) (SettledLowC settled) = UnProgressUp syn (StepUp fill1 step fill2) settled
    UnProgressLow (AnaFun _ _ _ _ _ _ _ _ ana) (StepLow FillL⊙ StepSynFun FillL⊙) (SettledLowC (SettledUpC (SettledFun (SettledLowC ()))))
    UnProgressLow (AnaFun _ _ _ _ _ _ _ _ ana) (StepUp (FillUEnvLowRec (FillUEnvUpRec (FillUEnvFun fill1))) step (FillUEnvLowRec (FillUEnvUpRec (FillUEnvFun fill2)))) (SettledLowC (SettledUpC (SettledFun settled))) = UnProgressLow ana (StepUp fill1 step fill2) settled
    UnProgressLow (AnaFun _ _ _ _ _ _ _ _ ana) (StepLow (FillLEnvLowRec (FillLEnvUpRec (FillLEnvFun fill1))) step (FillLEnvLowRec (FillLEnvUpRec (FillLEnvFun fill2)))) (SettledLowC (SettledUpC (SettledFun settled))) = UnProgressLow ana (StepLow fill1 step fill2) settled

  UnProgressProgram : ∀ {p p'} ->  
    WellTypedProgram p ->   
    (p P↦ p') ->   
    (SettledProgram p) ->
    ⊥       
  UnProgressProgram {p = Root e .Old} (WTProg ana) (InsideStep step) (SettledRoot (SettledLowC settled)) = UnProgressLow ana step (SettledLowC settled)   