
open import Data.Empty 
open import Data.Sum renaming (_⊎_ to _+_; inj₁ to Inl ; inj₂ to Inr) 
open import Data.Product 
open import Relation.Nullary 
open import Relation.Binary.PropositionalEquality

open import Prelude
open import Core.Core
open import Core.Environment
open import Core.WellTyped
open import Core.Settled
open import Core.Lemmas
open import Core.VarsSynthesize
open import Core.Update

module Core.Progress where

  mutual 

    productive-syn-syn : ∀{Γ e t n} ->
      SubsumableMid e ->
      e M̸↦ -> 
      Γ U⊢ (e ⇒ (t , n)) ->
      ∃[ t' ] (t ≡ ■ t') 
    productive-syn-syn SubsumableConst SettledConst (WTConst (▷Pair ▶Old)) = _ , refl
    productive-syn-syn SubsumableHole SettledHole (WTHole (▷Pair ▶Old)) = _ , refl
    productive-syn-syn SubsumableVar SettledVar (WTVar x x₁) = _ , refl
    productive-syn-syn SubsumableAsc (SettledAsc x) (WTAsc x₁ x₂ x₃) = _ , refl
    productive-syn-syn SubsumableAp (SettledAp (SettledLow (SettledUp settled)) _) (WTAp marrow consist x₄ x₅ syn ana)  with productive-syn-ana settled syn | marrow | consist
    ... | _ , refl | NTArrowC (DTArrowSome x) | ▷Pair ▶Old = _ , refl

    productive-syn-ana : ∀{Γ e t m n} ->
      e M̸↦ -> 
      Γ L⊢ ((e ⇒ (t , n)) [ m ]⇐ (□ , Old)) ->
      ∃[ t' ] (t ≡ ■ t') 
    productive-syn-ana settled (WTUp x x₁ x₂ x₃) = productive-syn-syn x settled x₃
    productive-syn-ana (SettledFun (SettledLow (SettledUp settled))) (WTFun (NTArrowC DTArrowNone) a2 (▷Pair ▶Old) a4 a5 a6 a7 a8 ana) with productive-syn-ana settled ana | a6
    ... | t , refl | ▷Pair ▶Old = _ , refl

  new-ana-steps-syn-inner : ∀ {Γ e m t} ->
    Γ U⊢ e ->
    ∃[ e' ] (e [ m ]⇐ (t , New)) l↦ e' 
  new-ana-steps-syn-inner (WTConst (▷Pair x)) = _ , StepAnaConsist SubsumableConst (proj₂ (~D-dec _ _)) 
  new-ana-steps-syn-inner (WTHole x) = _ , StepAnaConsist SubsumableHole (proj₂ (~D-dec _ _)) 
  new-ana-steps-syn-inner (WTAp x x₁ x₂ x₃ x₄ x₅) = _ , StepAnaConsist SubsumableAp (proj₂ (~D-dec _ _)) 
  new-ana-steps-syn-inner (WTVar x x₁) = _ , StepAnaConsist SubsumableVar  (proj₂ (~D-dec _ _)) 
  new-ana-steps-syn-inner (WTAsc x x₁ x₂) = _ , StepAnaConsist SubsumableAsc (proj₂ (~D-dec _ _)) 

  new-ana-steps-syn : ∀ {Γ e m t} ->
    Γ U⊢ e ->
    ∃[ e' ] (e [ m ]⇐ (t , New)) L↦ e' 
  new-ana-steps-syn syn with new-ana-steps-syn-inner syn 
  ... | e' , step = e' , (StepLow FillL⊙ step FillL⊙)

  new-ana-steps-inner : ∀ {Γ e m t} ->
    Γ L⊢ ((e [ m ]⇐ (t , New))) ->
    ∃[ e' ] (e [ m ]⇐ (t , New)) l↦ e' 
  new-ana-steps-inner (WTUp x x₁ x₂ syn) = new-ana-steps-syn-inner syn
  new-ana-steps-inner (WTFun x x₁ x₂ x₃ x₄ x₅ x₆ x₇ ana) = _ , (StepAnaFun (proj₂ (proj₂ (proj₂ (▸DTArrow-dec _)))) (■~D-pair (proj₂ (~D-dec _ _))))

  new-ana-steps : ∀ {Γ e m t} ->
    Γ L⊢ (e [ m ]⇐ (t , New)) ->
    ∃[ e' ] (e [ m ]⇐ (t , New)) L↦ e' 
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
      (Γ U⊢ e) ->      
      (∃[ e' ] (e U↦ e')) + (e almost-U̸↦)
    ProgressUp (WTConst consist) = Inr (AlmostSettledUp SettledConst)
    ProgressUp (WTHole consist) = Inr (AlmostSettledUp SettledHole)
    ProgressUp (WTAp marrow x₁ x₂ x₃ syn ana) with ProgressLow syn | ProgressLow ana 
    ProgressUp (WTAp marrow x₁ x₂ x₃ syn ana) | Inl (e' , step) | progress = Inl (_ , StepLowUp (FillLEnvUpRec (FillLEnvAp1 FillL⊙)) step (FillLEnvUpRec (FillLEnvAp1 FillL⊙)))
    ProgressUp (WTAp marrow x₁ x₂ x₃ syn ana) | Inr (AlmostSettledLow (AlmostSettledUp {New} settled1)) | progress = Inl (_ , StepUp FillU⊙ (StepAp (proj₂ (proj₂ (proj₂ (▸DTArrow-dec _))))) FillU⊙)
    ProgressUp (WTAp marrow x₁ x₂ x₃ syn ana) | Inr (AlmostSettledLow (AlmostSettledUp {Old} settled1)) | Inl (e' , step) = Inl (_ , StepLowUp (FillLEnvUpRec (FillLEnvAp2 FillL⊙)) step (FillLEnvUpRec (FillLEnvAp2 FillL⊙)))
    ProgressUp (WTAp marrow x₁ x₂ x₃ syn ana) | Inr (AlmostSettledLow (AlmostSettledUp {Old} settled1)) | Inr (AlmostSettledLow (AlmostSettledUp {n} settled2)) with productive-syn-ana settled1 syn | marrow | x₂
    ProgressUp (WTAp marrow x₁ x₂ x₃ syn ana) | Inr (AlmostSettledLow (AlmostSettledUp {.Old} settled1)) | Inr (AlmostSettledLow (AlmostSettledUp {New} settled2)) | t , refl | NTArrowC (DTArrowSome x) | ▷Pair ▶Old = Inl (_ , StepLow (FillLEnvUpRec (FillLEnvAp2 FillL⊙)) (StepSynConsist (proj₂ (~D-dec _ _))) (FillLEnvUpRec (FillLEnvAp2 FillL⊙))) 
    ProgressUp (WTAp marrow x₁ x₂ x₃ syn ana) | Inr (AlmostSettledLow (AlmostSettledUp {.Old} settled1)) | Inr (AlmostSettledLow (AlmostSettledUp {Old} settled2)) | t , refl | NTArrowC (DTArrowSome x) | ▷Pair ▶Old = Inr (AlmostSettledUp (SettledAp (SettledLow (SettledUp settled1)) (SettledLow (SettledUp settled2)))) 
    ProgressUp (WTVar x x₁) = Inr (AlmostSettledUp SettledVar)
    ProgressUp (WTAsc {t-asc = (t-asc , New)} x x₁ ana) = Inl (_ , StepUp FillU⊙ StepAsc FillU⊙) 
    ProgressUp (WTAsc {t-asc = (t-asc , Old)} x x₁ ana) with ProgressLow ana 
    ... | Inl (e' , step) = Inl (_ , StepLowUp (FillLEnvUpRec (FillLEnvAsc FillL⊙)) step (FillLEnvUpRec (FillLEnvAsc FillL⊙))) 
    ... | Inr (AlmostSettledLow (AlmostSettledUp {New} settled)) = Inl (_ , StepLow (FillLEnvUpRec (FillLEnvAsc FillL⊙)) (StepSynConsist (proj₂ (~D-dec _ _))) (FillLEnvUpRec (FillLEnvAsc FillL⊙))) 
    ... | Inr (AlmostSettledLow (AlmostSettledUp {Old} settled)) = Inr (AlmostSettledUp (SettledAsc (SettledLow (SettledUp settled)))) 

    ProgressLow :  
      ∀ {Γ e} ->
      (Γ L⊢ e) ->      
      (∃[ e' ] (e L↦ e')) + (e almost-L̸↦)
    ProgressLow (WTUp subsumable consist m-consist syn) with ProgressUp syn 
    ProgressLow (WTUp subsumable consist m-consist syn) | Inl (e' , step) = Inl (_ , StepUpLow (FillUEnvLowRec FillU⊙) step (FillUEnvLowRec FillU⊙))
    ProgressLow (WTUp {ana-all = t , New} subsumable consist m-consist syn) | Inr settled = Inl (new-ana-steps-syn syn)
    ProgressLow (WTUp {ana-all = t , Old}  subsumable consist m-consist syn) | Inr settled = Inr (AlmostSettledLow settled)
    ProgressLow (WTFun {ana-all = t , New} (NTArrowC marrow) (■~N-pair (~N-pair consist)) consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) = Inl (_ , StepLow FillL⊙ (StepAnaFun marrow (■~D-pair consist)) FillL⊙) 
    ProgressLow (WTFun {ana-all = ana-all , Old} {t-asc = t-asc , New} (NTArrowC marrow) (■~N-pair (~N-pair consist)) consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) = Inl (_ , StepLow FillL⊙ (StepAnnFun (proj₂ (proj₂ (proj₂ vars-syn?-dec-elaborate)))) FillL⊙)
    
    ProgressLow (WTFun {ana-all = ana-all , Old} {ana-body = ana-body , New} {t-asc = t-asc , Old} marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) = Inl (_ , StepLow (FillLEnvLowRec (FillLEnvUpRec (FillLEnvFun FillL⊙))) (proj₂ (new-ana-steps-inner ana)) (FillLEnvLowRec (FillLEnvUpRec (FillLEnvFun FillL⊙))))
    ProgressLow (WTFun {ana-all = ana-all , Old} {ana-body = ana-body , Old} {t-asc = t-asc , Old} marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) with ProgressLow ana  
    ProgressLow (WTFun {ana-all = ana-all , Old} {ana-body = ana-body , Old} {t-asc = t-asc , Old} marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) | Inl (e' , step) = Inl (_ , StepLowLow (FillLEnvLowRec (FillLEnvUpRec (FillLEnvFun FillL⊙))) step (FillLEnvLowRec (FillLEnvUpRec (FillLEnvFun FillL⊙))))
    ProgressLow (WTFun {ana-all = ana-all , Old} {ana-body = ana-body , Old} {t-asc = t-asc , Old} marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) | Inr (AlmostSettledLow (AlmostSettledUp {New} settled)) with ana-body 
    ProgressLow (WTFun {ana-all = ana-all , Old} {ana-body = ana-body , Old} {t-asc = t-asc , Old} marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) | Inr (AlmostSettledLow (AlmostSettledUp {New} settled)) | □ = Inl (_ , StepLow FillL⊙ StepSynFun FillL⊙)
    ProgressLow (WTFun {ana-all = ana-all , Old} {ana-body = ana-body , Old} {t-asc = t-asc , Old} marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) | Inr (AlmostSettledLow (AlmostSettledUp {New} settled)) | ■ _ = Inl (_ , StepLow (FillLEnvLowRec (FillLEnvUpRec (FillLEnvFun FillL⊙))) (StepSynConsist (proj₂ (~D-dec _ _))) (FillLEnvLowRec (FillLEnvUpRec (FillLEnvFun FillL⊙)))) 
    ProgressLow (WTFun {ana-all = ana-all , Old} {ana-body = ana-body , Old} {t-asc = t-asc , Old} marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) | Inr (AlmostSettledLow (AlmostSettledUp {Old} settled)) = Inr (AlmostSettledLow (AlmostSettledUp (SettledFun (SettledLow (SettledUp settled)))))

  step-preserves-program : ∀ {p e} -> 
    ExpLowOfProgram p L↦ e -> 
    ∃[ p' ] (e ≡ ExpLowOfProgram p')
  step-preserves-program {p = Root e n} (StepUp (FillUEnvLowRec x) step (FillUEnvLowRec x₁)) = Root _ _ , refl
  step-preserves-program {p = Root e n} (StepLow (FillLEnvLowRec x) step (FillLEnvLowRec x₁)) = Root _ _ , refl
  step-preserves-program {p = Root e n} (StepLow FillL⊙ (StepAnaConsist x consist) FillL⊙) with ~DVoid-right consist 
  ... | refl = Root _ _ , refl
  step-preserves-program {p = Root e n} (StepLow FillL⊙ (StepAnaFun _ _) FillL⊙) = Root _ _ , refl
  step-preserves-program {p = Root e n} (StepLow FillL⊙ (StepAnnFun _) FillL⊙) = Root _ _ , refl
  step-preserves-program {p = Root e n} (StepLow FillL⊙ StepSynFun FillL⊙) = Root _ _ , refl

  ProgressProgram : ∀ {p} ->
    P⊢ p ->   
    (∃[ p' ] (p P↦ p')) + (p P̸↦)   
  ProgressProgram (WTProgram ana) with ProgressLow ana   
  ProgressProgram (WTProgram ana) | Inl (e' , step) with step-preserves-program step 
  ProgressProgram (WTProgram ana) | Inl (e' , step) | p' , refl = Inl (p' , (InsideStep step)) 
  ProgressProgram {p = Root e n} (WTProgram ana) | Inr (AlmostSettledLow (AlmostSettledUp {Old} settled)) = Inr (SettledProgram (SettledLow (SettledUp settled))) 
  ProgressProgram {p = Root e n} (WTProgram ana) | Inr (AlmostSettledLow (AlmostSettledUp {New} settled)) = Inl (_ , TopStep) 

  mutual 
    
    UnProgressUp : ∀ {Γ e e'} ->
      (Γ U⊢ e) ->  
      (e U↦ e') -> 
      (e U̸↦) ->
      ⊥ 
    UnProgressUp (WTConst x) (StepUp FillU⊙ () FillU⊙) settled
    UnProgressUp (WTHole x) (StepUp FillU⊙ () FillU⊙) settled
    UnProgressUp (WTVar x x₁) (StepUp FillU⊙ () FillU⊙) settled
    UnProgressUp (WTAp _ _ _ _ _ _) (StepUp FillU⊙ (StepAp _) FillU⊙) (SettledUp (SettledAp (SettledLow ()) _))
    UnProgressUp (WTAsc _ _ ana) (StepUp FillU⊙ StepAsc FillU⊙) (SettledUp ())
    UnProgressUp (WTConst x) (StepUp (FillUEnvUpRec ()) step (FillUEnvUpRec x₁)) settled
    UnProgressUp (WTHole x) (StepUp (FillUEnvUpRec ()) step (FillUEnvUpRec x₁)) settled
    UnProgressUp (WTVar _ _) (StepUp (FillUEnvUpRec ()) step (FillUEnvUpRec x₁)) settled
    UnProgressUp (WTAp _ _ _ _ syn ana) (StepUp (FillUEnvUpRec (FillUEnvAp1 fill1)) step (FillUEnvUpRec (FillUEnvAp1 fill2))) (SettledUp (SettledAp settled _)) = UnProgressLow syn (StepUp fill1 step fill2) settled
    UnProgressUp (WTAp _ _ _ _ syn ana) (StepUp (FillUEnvUpRec (FillUEnvAp2 fill1)) step (FillUEnvUpRec (FillUEnvAp2 fill2))) (SettledUp (SettledAp _ settled)) = UnProgressLow ana (StepUp fill1 step fill2) settled
    UnProgressUp (WTAsc _ _ ana) (StepUp (FillUEnvUpRec (FillUEnvAsc fill1)) step (FillUEnvUpRec (FillUEnvAsc fill2))) (SettledUp (SettledAsc settled)) = UnProgressLow ana (StepUp fill1 step fill2) settled
    
    UnProgressUp (WTConst x) (StepLow (FillLEnvUpRec ()) step (FillLEnvUpRec fill2)) (SettledUp settled)
    UnProgressUp (WTHole x) (StepLow (FillLEnvUpRec ()) step (FillLEnvUpRec fill2)) (SettledUp settled)
    UnProgressUp (WTVar _ _) (StepLow (FillLEnvUpRec ()) step (FillLEnvUpRec fill2)) (SettledUp settled)
    UnProgressUp (WTAp _ _ _ _ syn ana) (StepLow (FillLEnvUpRec (FillLEnvAp1 fill1)) step (FillLEnvUpRec (FillLEnvAp1 fill2))) (SettledUp (SettledAp settled _)) = UnProgressLow syn (StepLow fill1 step fill2) settled
    UnProgressUp (WTAp _ _ _ _ syn ana) (StepLow (FillLEnvUpRec (FillLEnvAp2 fill1)) step (FillLEnvUpRec (FillLEnvAp2 fill2))) (SettledUp (SettledAp _ settled)) = UnProgressLow ana (StepLow fill1 step fill2) settled
    UnProgressUp (WTAsc _ _ ana) (StepLow (FillLEnvUpRec (FillLEnvAsc fill1)) step (FillLEnvUpRec (FillLEnvAsc fill2))) (SettledUp (SettledAsc settled)) = UnProgressLow ana (StepLow fill1 step fill2) settled

    UnProgressLow : ∀ {Γ e e'} ->
      (Γ L⊢ e) ->  
      (e L↦ e') -> 
      (e L̸↦) ->
      ⊥ 
    UnProgressLow (WTUp _ _ _ syn) (StepLow FillL⊙ (StepSynConsist _) FillL⊙) (SettledLow ())
    UnProgressLow (WTUp _ _ _ syn) (StepLow (FillLEnvLowRec fill1) step (FillLEnvLowRec fill2)) (SettledLow settled) = UnProgressUp syn (StepLow fill1 step fill2) settled
    UnProgressLow (WTUp _ _ _ syn) (StepUp (FillUEnvLowRec fill1) step (FillUEnvLowRec fill2)) (SettledLow settled) = UnProgressUp syn (StepUp fill1 step fill2) settled
    UnProgressLow (WTFun _ _ _ _ _ _ _ _ ana) (StepLow FillL⊙ StepSynFun FillL⊙) (SettledLow (SettledUp (SettledFun (SettledLow ()))))
    UnProgressLow (WTFun _ _ _ _ _ _ _ _ ana) (StepUp (FillUEnvLowRec (FillUEnvUpRec (FillUEnvFun fill1))) step (FillUEnvLowRec (FillUEnvUpRec (FillUEnvFun fill2)))) (SettledLow (SettledUp (SettledFun settled))) = UnProgressLow ana (StepUp fill1 step fill2) settled
    UnProgressLow (WTFun _ _ _ _ _ _ _ _ ana) (StepLow (FillLEnvLowRec (FillLEnvUpRec (FillLEnvFun fill1))) step (FillLEnvLowRec (FillLEnvUpRec (FillLEnvFun fill2)))) (SettledLow (SettledUp (SettledFun settled))) = UnProgressLow ana (StepLow fill1 step fill2) settled

  UnProgressProgram : ∀ {p p'} ->  
    P⊢ p ->   
    (p P↦ p') ->   
    (p P̸↦) ->
    ⊥       
  UnProgressProgram {p = Root e .Old} (WTProgram ana) (InsideStep step) (SettledProgram (SettledLow settled)) = UnProgressLow ana step (SettledLow settled)   

