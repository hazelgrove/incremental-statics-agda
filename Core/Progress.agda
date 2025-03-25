
open import Data.Empty 
open import Data.Sum renaming (_⊎_ to _+_; inj₁ to Inl ; inj₂ to Inr) 
open import Data.Product 
open import Relation.Nullary 
open import Relation.Binary.PropositionalEquality

open import Prelude
open import Core.Core
open import Core.Environment
open import Core.WellFormed
open import Core.Settled
open import Core.Lemmas
open import Core.VariableUpdate
open import Core.Update

module Core.Progress where

  mutual 

    productive-syn-syn : ∀{Γ e t n} ->
      SubsumableMid e ->
      e M̸↦ -> 
      Γ U⊢ (e ⇒ (t , n)) ->
      ∃[ t' ] (t ≡ ■ t') 
    productive-syn-syn SubsumableConst SettledConst (WFConst (▷Pair ▶•)) = _ , refl
    productive-syn-syn SubsumableHole SettledHole (WFHole (▷Pair ▶•)) = _ , refl
    productive-syn-syn SubsumableVar SettledVar (WFVar x x₁) = _ , refl
    productive-syn-syn SubsumableAsc (SettledAsc x) (WFAsc x₁ x₂ x₃) = _ , refl
    productive-syn-syn SubsumableAp (SettledAp (SettledLow (SettledUp settled)) _) (WFAp marrow consist x₄ x₅ syn ana) with productive-syn-ana settled syn | marrow | consist
    ... | _ , refl | NTArrowC (DTArrowSome x) | ▷Pair ▶• = _ , refl
    productive-syn-syn SubsumableProj (SettledProj (SettledLow (SettledUp settled))) (WFProj mproj consist _ wt) with productive-syn-ana settled wt | mproj | consist
    ... | _ , refl | NTProjC (DTProjSome x) | ▷Pair ▶• = _ , refl

    productive-syn-ana : ∀{Γ e t m n} ->
      e M̸↦ -> 
      Γ L⊢ ((e ⇒ (t , n)) [ m ]⇐ (□ , •)) ->
      ∃[ t' ] (t ≡ ■ t') 
    productive-syn-ana settled (WFSubsume x x₁ x₂ x₃) = productive-syn-syn x settled x₃
    productive-syn-ana (SettledFun (SettledLow (SettledUp settled))) (WFFun (NTArrowC DTArrowNone) a2 (▷Pair ▶•) a4 a5 a6 a7 a8 ana) with productive-syn-ana settled ana | a6
    ... | t , refl | ▷Pair ▶• = _ , refl
    productive-syn-ana (SettledPair (SettledLow (SettledUp settled1)) (SettledLow (SettledUp settled2))) (WFPair (NTProdC DTProdNone) (▷Pair ▶•) (▷Pair ▶•) ▶• con4 consist con5 wt1 wt2) with productive-syn-ana settled1 wt1 | productive-syn-ana settled2 wt2 | con4
    ... | _ , refl | _ , refl | ▷Pair ▶• = _ , refl 

  dirty-ana-steps-syn-inner : ∀ {Γ e m t} ->
    Γ U⊢ e ->
    ∃[ e' ] (e [ m ]⇐ (t , ★)) l↦ e' 
  dirty-ana-steps-syn-inner (WFConst (▷Pair x)) = _ , StepAna SubsumableConst (proj₂ (~D-dec _ _)) 
  dirty-ana-steps-syn-inner (WFHole x) = _ , StepAna SubsumableHole (proj₂ (~D-dec _ _)) 
  dirty-ana-steps-syn-inner (WFAp x x₁ x₂ x₃ x₄ x₅) = _ , StepAna SubsumableAp (proj₂ (~D-dec _ _)) 
  dirty-ana-steps-syn-inner (WFVar x x₁) = _ , StepAna SubsumableVar  (proj₂ (~D-dec _ _)) 
  dirty-ana-steps-syn-inner (WFAsc x x₁ x₂) = _ , StepAna SubsumableAsc (proj₂ (~D-dec _ _)) 
  dirty-ana-steps-syn-inner (WFProj x x₁ x₂ x₄) = _ , StepAna SubsumableProj (proj₂ (~D-dec _ _))

  dirty-ana-steps-syn : ∀ {Γ e m t} ->
    Γ U⊢ e ->
    ∃[ e' ] (e [ m ]⇐ (t , ★)) L↦ e' 
  dirty-ana-steps-syn syn with dirty-ana-steps-syn-inner syn 
  ... | e' , step = e' , (StepLow FillL⊙ step FillL⊙)

  dirty-ana-steps-inner : ∀ {Γ e m t} ->
    Γ L⊢ ((e [ m ]⇐ (t , ★))) ->
    ∃[ e' ] (e [ m ]⇐ (t , ★)) l↦ e' 
  dirty-ana-steps-inner (WFSubsume x x₁ x₂ syn) = dirty-ana-steps-syn-inner syn
  dirty-ana-steps-inner (WFFun x x₁ x₂ x₃ x₄ x₅ x₆ x₇ ana) = _ , (StepAnaFun (proj₂ (proj₂ (proj₂ (▸DTArrow-dec _)))) (■~D-pair (proj₂ (~D-dec _ _))))
  dirty-ana-steps-inner (WFPair x x₁ x₂ x₃ x₄ x₅ x₆ wt wt₁) = _ , StepAnaPair (proj₂ (proj₂ (proj₂ (▸DTProd-dec _))))
  
  dirty-ana-steps : ∀ {Γ e m t} ->
    Γ L⊢ (e [ m ]⇐ (t , ★)) ->
    ∃[ e' ] (e [ m ]⇐ (t , ★)) L↦ e' 
  dirty-ana-steps ana with dirty-ana-steps-inner ana 
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

  var-update-dec : ∀ {e x t m} ->
    ∃[ e' ] (VariableUpdate x t m e e')
  var-update-dec {EConst ⇒ x₁} = (EConst ⇒ x₁) , VSConst
  var-update-dec {EHole ⇒ x₁} = (EHole ⇒ x₁) , VSHole
  var-update-dec {EAp (x [ x₄ ]⇐ x₅) x₂ (x₃ [ x₆ ]⇐ x₇) ⇒ x₁} = _ , (VSAp (proj₂ var-update-dec) (proj₂ var-update-dec))
  var-update-dec {EAsc x (x₂ [ x₃ ]⇐ x₄) ⇒ x₁} = _ , (VSAsc (proj₂ var-update-dec))
  var-update-dec {EFun x x₂ x₃ x₄ (x₅ [ x₆ ]⇐ x₇) ⇒ x₁} {y} with ((BVar y) ≡B? x) 
  ... | yes refl = _ , VSFunEq 
  ... | no neq = _ , VSFunNeq neq (proj₂ var-update-dec)
  var-update-dec {EVar x x₂ ⇒ x₁} {y} with (y ≡? x) 
  ... | yes refl = _ , VSVarEq 
  ... | no neq = _ , VSVarNeq neq
  var-update-dec {EPair (x [ x₂ ]⇐ x₄) (x₅ [ x₆ ]⇐ x₇) x₃ ⇒ x₁} = _ , (VSPair (proj₂ var-update-dec) (proj₂ var-update-dec))
  var-update-dec {EProj x (x₂ [ x₄ ]⇐ x₅) x₃ ⇒ x₁} = _ , VSProj (proj₂ var-update-dec)

  var-update?-dec : ∀ {x e t m} ->
    ∃[ e' ] (VariableUpdate? x t m e e')
  var-update?-dec {BHole} = _ , refl
  var-update?-dec {BVar x} = var-update-dec

  var-update?-dec-elaborate : ∀ {x e t m} ->
    ∃[ e' ] ∃[ t' ] ∃[ n' ] (VariableUpdate? x t m e (e' ⇒ (t' , n')))
  var-update?-dec-elaborate {x} {e} {t} {m} with var-update?-dec {x} {e} {t} {m} 
  ... | e' ⇒ (t' , n') , var-update = e' , t' , n' , var-update

  mutual 
    
    ProgressUp :  
      ∀ {Γ e} ->
      (Γ U⊢ e) ->      
      (∃[ e' ] (e U↦ e')) + (e almost-U̸↦)
    ProgressUp (WFConst consist) = Inr (AlmostSettledUp SettledConst)
    ProgressUp (WFHole consist) = Inr (AlmostSettledUp SettledHole)
    ProgressUp (WFAp marrow x₁ x₂ x₃ syn ana) with ProgressLow syn | ProgressLow ana 
    ProgressUp (WFAp marrow x₁ x₂ x₃ syn ana) | Inl (e' , step) | progress = Inl (_ , StepLowUp (FillLEnvUpRec (FillLEnvAp1 FillL⊙)) step (FillLEnvUpRec (FillLEnvAp1 FillL⊙)))
    ProgressUp (WFAp marrow x₁ x₂ x₃ syn ana) | Inr (AlmostSettledLow (AlmostSettledUp {★} settled1)) | progress = Inl (_ , StepUp FillU⊙ (StepAp (proj₂ (proj₂ (proj₂ (▸DTArrow-dec _))))) FillU⊙)
    ProgressUp (WFAp marrow x₁ x₂ x₃ syn ana) | Inr (AlmostSettledLow (AlmostSettledUp {•} settled1)) | Inl (e' , step) = Inl (_ , StepLowUp (FillLEnvUpRec (FillLEnvAp2 FillL⊙)) step (FillLEnvUpRec (FillLEnvAp2 FillL⊙)))
    ProgressUp (WFAp marrow x₁ x₂ x₃ syn ana) | Inr (AlmostSettledLow (AlmostSettledUp {•} settled1)) | Inr (AlmostSettledLow (AlmostSettledUp {n} settled2)) with productive-syn-ana settled1 syn | marrow | x₂
    ProgressUp (WFAp marrow x₁ x₂ x₃ syn ana) | Inr (AlmostSettledLow (AlmostSettledUp {.•} settled1)) | Inr (AlmostSettledLow (AlmostSettledUp {★} settled2)) | t , refl | NTArrowC (DTArrowSome x) | ▷Pair ▶• = Inl (_ , StepLow (FillLEnvUpRec (FillLEnvAp2 FillL⊙)) (StepSyn (proj₂ (~D-dec _ _))) (FillLEnvUpRec (FillLEnvAp2 FillL⊙))) 
    ProgressUp (WFAp marrow x₁ x₂ x₃ syn ana) | Inr (AlmostSettledLow (AlmostSettledUp {.•} settled1)) | Inr (AlmostSettledLow (AlmostSettledUp {•} settled2)) | t , refl | NTArrowC (DTArrowSome x) | ▷Pair ▶• = Inr (AlmostSettledUp (SettledAp (SettledLow (SettledUp settled1)) (SettledLow (SettledUp settled2)))) 
    ProgressUp (WFVar x x₁) = Inr (AlmostSettledUp SettledVar)
    ProgressUp (WFAsc {t-asc = (t-asc , ★)} x x₁ ana) = Inl (_ , StepUp FillU⊙ StepAsc FillU⊙) 
    ProgressUp (WFAsc {t-asc = (t-asc , •)} x x₁ ana) with ProgressLow ana 
    ... | Inl (e' , step) = Inl (_ , StepLowUp (FillLEnvUpRec (FillLEnvAsc FillL⊙)) step (FillLEnvUpRec (FillLEnvAsc FillL⊙))) 
    ... | Inr (AlmostSettledLow (AlmostSettledUp {★} settled)) = Inl (_ , StepLow (FillLEnvUpRec (FillLEnvAsc FillL⊙)) (StepSyn (proj₂ (~D-dec _ _))) (FillLEnvUpRec (FillLEnvAsc FillL⊙))) 
    ... | Inr (AlmostSettledLow (AlmostSettledUp {•} settled)) = Inr (AlmostSettledUp (SettledAsc (SettledLow (SettledUp settled)))) 
    ProgressUp (WFProj mproj con1 con2 wt) with ProgressLow wt 
    ... | Inl (e' , step ) = Inl (_ , StepLowUp (FillLEnvUpRec (FillLEnvProj FillL⊙)) step (FillLEnvUpRec (FillLEnvProj FillL⊙))) 
    ... | Inr (AlmostSettledLow (AlmostSettledUp {★} settled)) = Inl (_ , StepUp FillU⊙ (StepProj (proj₂ (proj₂ (▸DTProj-dec _ _)))) FillU⊙)
    ... | Inr (AlmostSettledLow (AlmostSettledUp {•} settled)) = Inr (AlmostSettledUp (SettledProj (SettledLow (SettledUp settled))))


    ProgressLow :  
      ∀ {Γ e} ->
      (Γ L⊢ e) ->      
      (∃[ e' ] (e L↦ e')) + (e almost-L̸↦)
    ProgressLow (WFSubsume subsumable consist m-consist syn) with ProgressUp syn 
    ProgressLow (WFSubsume subsumable consist m-consist syn) | Inl (e' , step) = Inl (_ , StepUpLow (FillUEnvLowRec FillU⊙) step (FillUEnvLowRec FillU⊙))
    ProgressLow (WFSubsume {ana-all = t , ★} subsumable consist m-consist syn) | Inr settled = Inl (dirty-ana-steps-syn syn)
    ProgressLow (WFSubsume {ana-all = t , •}  subsumable consist m-consist syn) | Inr settled = Inr (AlmostSettledLow settled)
    ProgressLow (WFFun {ana-all = t , ★} (NTArrowC marrow) (■~N-pair (~N-pair consist)) consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) = Inl (_ , StepLow FillL⊙ (StepAnaFun marrow (■~D-pair consist)) FillL⊙) 
    ProgressLow (WFFun {ana-all = ana-all , •} {t-asc = t-asc , ★} (NTArrowC marrow) (■~N-pair (~N-pair consist)) consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) = Inl (_ , StepLow FillL⊙ (StepAnnFun (proj₂ (proj₂ (proj₂ var-update?-dec-elaborate)))) FillL⊙)
    
    ProgressLow (WFFun {ana-all = ana-all , •} {ana-body = ana-body , ★} {t-asc = t-asc , •} marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) = Inl (_ , StepLow (FillLEnvLowRec (FillLEnvUpRec (FillLEnvFun FillL⊙))) (proj₂ (dirty-ana-steps-inner ana)) (FillLEnvLowRec (FillLEnvUpRec (FillLEnvFun FillL⊙))))
    ProgressLow (WFFun {ana-all = ana-all , •} {ana-body = ana-body , •} {t-asc = t-asc , •} marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) with ProgressLow ana  
    ProgressLow (WFFun {ana-all = ana-all , •} {ana-body = ana-body , •} {t-asc = t-asc , •} marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) | Inl (e' , step) = Inl (_ , StepLowLow (FillLEnvLowRec (FillLEnvUpRec (FillLEnvFun FillL⊙))) step (FillLEnvLowRec (FillLEnvUpRec (FillLEnvFun FillL⊙))))
    ProgressLow (WFFun {ana-all = ana-all , •} {ana-body = ana-body , •} {t-asc = t-asc , •} marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) | Inr (AlmostSettledLow (AlmostSettledUp {★} settled)) with ana-body 
    ProgressLow (WFFun {ana-all = ana-all , •} {ana-body = ana-body , •} {t-asc = t-asc , •} marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) | Inr (AlmostSettledLow (AlmostSettledUp {★} settled)) | □ = Inl (_ , StepLow FillL⊙ StepSynFun FillL⊙)
    ProgressLow (WFFun {ana-all = ana-all , •} {ana-body = ana-body , •} {t-asc = t-asc , •} marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) | Inr (AlmostSettledLow (AlmostSettledUp {★} settled)) | ■ _ = Inl (_ , StepLow (FillLEnvLowRec (FillLEnvUpRec (FillLEnvFun FillL⊙))) (StepSyn (proj₂ (~D-dec _ _))) (FillLEnvLowRec (FillLEnvUpRec (FillLEnvFun FillL⊙)))) 
    ProgressLow (WFFun {ana-all = ana-all , •} {ana-body = ana-body , •} {t-asc = t-asc , •} marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) | Inr (AlmostSettledLow (AlmostSettledUp {•} settled)) = Inr (AlmostSettledLow (AlmostSettledUp (SettledFun (SettledLow (SettledUp settled)))))
    ProgressLow (WFPair {ana-all = t , ★} mprod con1 con2 con3 con4 consist con5 wt1 wt2) = Inl (_ , StepLow FillL⊙ (StepAnaPair (proj₂ (proj₂ (proj₂ (▸DTProd-dec _))))) FillL⊙) 
    ProgressLow (WFPair {ana-all = t , •} {ana-fst = ana-fst , ★} mprod con1 con2 con3 con4 consist con5 wt1 wt2) = Inl (_ , StepLow (FillLEnvLowRec (FillLEnvUpRec (FillLEnvPair1 FillL⊙))) (proj₂ (dirty-ana-steps-inner wt1)) (FillLEnvLowRec (FillLEnvUpRec (FillLEnvPair1 FillL⊙))))
    ProgressLow (WFPair {ana-all = t , •} {ana-fst = ana-fst , •} {ana-snd = ana-snd , ★} mprod con1 con2 con3 con4 consist con5 wt1 wt2) = Inl (_ , StepLow (FillLEnvLowRec (FillLEnvUpRec (FillLEnvPair2 FillL⊙))) (proj₂ (dirty-ana-steps-inner wt2)) (FillLEnvLowRec (FillLEnvUpRec (FillLEnvPair2 FillL⊙))))
    ProgressLow (WFPair {ana-all = t , •} {ana-fst = ana-fst , •} {ana-snd = ana-snd , •} mprod con1 con2 con3 con4 consist con5 wt1 wt2) with ProgressLow wt1 | ProgressLow wt2 
    ProgressLow (WFPair {ana-all = t , •} {ana-fst = ana-fst , •} {ana-snd = ana-snd , •} mprod con1 con2 con3 con4 consist con5 wt1 wt2) | Inl (e' , step) | p2 = Inl (_ , StepLowLow (FillLEnvLowRec (FillLEnvUpRec (FillLEnvPair1 FillL⊙))) step (FillLEnvLowRec (FillLEnvUpRec (FillLEnvPair1 FillL⊙))))
    ProgressLow (WFPair {ana-all = t , •} {ana-fst = ana-fst , •} {ana-snd = ana-snd , •} mprod con1 con2 con3 con4 consist con5 wt1 wt2) | Inr (AlmostSettledLow (AlmostSettledUp {★} settled)) | p2 with ana-fst 
    ProgressLow (WFPair {ana-all = t , •} {ana-fst = ana-fst , •} {ana-snd = ana-snd , •} mprod con1 con2 con3 con4 consist con5 wt1 wt2) | Inr (AlmostSettledLow (AlmostSettledUp {★} settled)) | p2 | □ = Inl (_ , StepLow FillL⊙ StepSynPairFst FillL⊙) 
    ProgressLow (WFPair {ana-all = t , •} {ana-fst = ana-fst , •} {ana-snd = ana-snd , •} mprod con1 con2 con3 con4 consist con5 wt1 wt2) | Inr (AlmostSettledLow (AlmostSettledUp {★} settled)) | p2 | ■ _ = Inl (_ , StepLow (FillLEnvLowRec (FillLEnvUpRec (FillLEnvPair1 FillL⊙))) (StepSyn (proj₂ (~D-dec _ _))) (FillLEnvLowRec (FillLEnvUpRec (FillLEnvPair1 FillL⊙)))) 
    ProgressLow (WFPair {ana-all = t , •} {ana-fst = ana-fst , •} {ana-snd = ana-snd , •} mprod con1 con2 con3 con4 consist con5 wt1 wt2) | Inr (AlmostSettledLow (AlmostSettledUp {•} settled)) | Inl (e' , step) = Inl (_ , StepLowLow (FillLEnvLowRec (FillLEnvUpRec (FillLEnvPair2 FillL⊙))) step (FillLEnvLowRec (FillLEnvUpRec (FillLEnvPair2 FillL⊙))))
    ProgressLow (WFPair {ana-all = t , •} {ana-fst = ana-fst , •} {ana-snd = ana-snd , •} mprod con1 con2 con3 con4 consist con5 wt1 wt2) | Inr (AlmostSettledLow (AlmostSettledUp {•} settled1)) | Inr (AlmostSettledLow (AlmostSettledUp {★} settled2)) with ana-snd
    ProgressLow (WFPair {ana-all = t , •} {ana-fst = ana-fst , •} {ana-snd = ana-snd , •} mprod con1 con2 con3 con4 consist con5 wt1 wt2) | Inr (AlmostSettledLow (AlmostSettledUp {•} settled1)) | Inr (AlmostSettledLow (AlmostSettledUp {★} settled2)) | □ = Inl (_ , StepLow FillL⊙ StepSynPairSnd FillL⊙) 
    ProgressLow (WFPair {ana-all = t , •} {ana-fst = ana-fst , •} {ana-snd = ana-snd , •} mprod con1 con2 con3 con4 consist con5 wt1 wt2) | Inr (AlmostSettledLow (AlmostSettledUp {•} settled1)) | Inr (AlmostSettledLow (AlmostSettledUp {★} settled2)) | ■ _ = Inl (_ , StepLow (FillLEnvLowRec (FillLEnvUpRec (FillLEnvPair2 FillL⊙))) (StepSyn (proj₂ (~D-dec _ _))) (FillLEnvLowRec (FillLEnvUpRec (FillLEnvPair2 FillL⊙)))) 
    ProgressLow (WFPair {ana-all = t , •} {ana-fst = ana-fst , •} {ana-snd = ana-snd , •} mprod con1 con2 con3 con4 consist con5 wt1 wt2) | Inr (AlmostSettledLow (AlmostSettledUp {•} settled1)) | Inr (AlmostSettledLow (AlmostSettledUp {•} settled2)) = Inr (AlmostSettledLow (AlmostSettledUp (SettledPair (SettledLow (SettledUp settled1)) (SettledLow (SettledUp settled2))))) 
    
  step-preserves-program : ∀ {p e} -> 
    ExpLowOfProgram p L↦ e -> 
    ∃[ p' ] (e ≡ ExpLowOfProgram p')
  step-preserves-program {p = Root e n} (StepUp (FillUEnvLowRec x) step (FillUEnvLowRec x₁)) = Root _ _ , refl
  step-preserves-program {p = Root e n} (StepLow (FillLEnvLowRec x) step (FillLEnvLowRec x₁)) = Root _ _ , refl
  step-preserves-program {p = Root e n} (StepLow FillL⊙ (StepAna x consist) FillL⊙) with ~DVoid-right consist 
  ... | refl = Root _ _ , refl
  step-preserves-program {p = Root e n} (StepLow FillL⊙ (StepAnaFun _ _) FillL⊙) = Root _ _ , refl
  step-preserves-program {p = Root e n} (StepLow FillL⊙ (StepAnnFun _) FillL⊙) = Root _ _ , refl
  step-preserves-program {p = Root e n} (StepLow FillL⊙ StepSynFun FillL⊙) = Root _ _ , refl
  step-preserves-program {p = Root e n} (StepLow FillL⊙ (StepAnaPair _) FillL⊙) = Root _ _ , refl
  step-preserves-program {p = Root e n} (StepLow FillL⊙ StepSynPairFst FillL⊙) = Root _ _ , refl
  step-preserves-program {p = Root e n} (StepLow FillL⊙ StepSynPairSnd FillL⊙) = Root _ _ , refl

  ProgressProgram : ∀ {p} ->
    P⊢ p ->   
    (∃[ p' ] (p P↦ p')) + (p P̸↦)   
  ProgressProgram (WFProgram ana) with ProgressLow ana   
  ProgressProgram (WFProgram ana) | Inl (e' , step) with step-preserves-program step 
  ProgressProgram (WFProgram ana) | Inl (e' , step) | p' , refl = Inl (p' , (InsideStep step)) 
  ProgressProgram {p = Root e n} (WFProgram ana) | Inr (AlmostSettledLow (AlmostSettledUp {•} settled)) = Inr (SettledProgram (SettledLow (SettledUp settled))) 
  ProgressProgram {p = Root e n} (WFProgram ana) | Inr (AlmostSettledLow (AlmostSettledUp {★} settled)) = Inl (_ , TopStep) 

  mutual 
    
    UnProgressUp : ∀ {Γ e e'} ->
      (Γ U⊢ e) ->  
      (e U↦ e') -> 
      (e U̸↦) ->
      ⊥ 
    UnProgressUp (WFConst x) (StepUp FillU⊙ () FillU⊙) settled
    UnProgressUp (WFHole x) (StepUp FillU⊙ () FillU⊙) settled
    UnProgressUp (WFVar x x₁) (StepUp FillU⊙ () FillU⊙) settled
    UnProgressUp (WFAp _ _ _ _ _ _) (StepUp FillU⊙ (StepAp _) FillU⊙) (SettledUp (SettledAp (SettledLow ()) _))
    UnProgressUp (WFAsc _ _ ana) (StepUp FillU⊙ StepAsc FillU⊙) (SettledUp ())
    UnProgressUp (WFConst x) (StepUp (FillUEnvUpRec ()) step (FillUEnvUpRec x₁)) settled
    UnProgressUp (WFHole x) (StepUp (FillUEnvUpRec ()) step (FillUEnvUpRec x₁)) settled
    UnProgressUp (WFVar _ _) (StepUp (FillUEnvUpRec ()) step (FillUEnvUpRec x₁)) settled
    UnProgressUp (WFAp _ _ _ _ syn ana) (StepUp (FillUEnvUpRec (FillUEnvAp1 fill1)) step (FillUEnvUpRec (FillUEnvAp1 fill2))) (SettledUp (SettledAp settled _)) = UnProgressLow syn (StepUp fill1 step fill2) settled
    UnProgressUp (WFAp _ _ _ _ syn ana) (StepUp (FillUEnvUpRec (FillUEnvAp2 fill1)) step (FillUEnvUpRec (FillUEnvAp2 fill2))) (SettledUp (SettledAp _ settled)) = UnProgressLow ana (StepUp fill1 step fill2) settled
    UnProgressUp (WFAsc _ _ ana) (StepUp (FillUEnvUpRec (FillUEnvAsc fill1)) step (FillUEnvUpRec (FillUEnvAsc fill2))) (SettledUp (SettledAsc settled)) = UnProgressLow ana (StepUp fill1 step fill2) settled
    UnProgressUp (WFProj _ _ _ _) (StepUp FillU⊙ (StepProj _) FillU⊙) (SettledUp (SettledProj (SettledLow ())))
    UnProgressUp (WFProj _ _ _ wt) (StepUp (FillUEnvUpRec (FillUEnvProj fill1)) step (FillUEnvUpRec (FillUEnvProj fill2))) (SettledUp (SettledProj settled)) = UnProgressLow wt (StepUp fill1 step fill2) settled
    
    UnProgressUp (WFConst x) (StepLow (FillLEnvUpRec ()) step (FillLEnvUpRec fill2)) (SettledUp settled)
    UnProgressUp (WFHole x) (StepLow (FillLEnvUpRec ()) step (FillLEnvUpRec fill2)) (SettledUp settled)
    UnProgressUp (WFVar _ _) (StepLow (FillLEnvUpRec ()) step (FillLEnvUpRec fill2)) (SettledUp settled)
    UnProgressUp (WFAp _ _ _ _ syn ana) (StepLow (FillLEnvUpRec (FillLEnvAp1 fill1)) step (FillLEnvUpRec (FillLEnvAp1 fill2))) (SettledUp (SettledAp settled _)) = UnProgressLow syn (StepLow fill1 step fill2) settled
    UnProgressUp (WFAp _ _ _ _ syn ana) (StepLow (FillLEnvUpRec (FillLEnvAp2 fill1)) step (FillLEnvUpRec (FillLEnvAp2 fill2))) (SettledUp (SettledAp _ settled)) = UnProgressLow ana (StepLow fill1 step fill2) settled
    UnProgressUp (WFAsc _ _ ana) (StepLow (FillLEnvUpRec (FillLEnvAsc fill1)) step (FillLEnvUpRec (FillLEnvAsc fill2))) (SettledUp (SettledAsc settled)) = UnProgressLow ana (StepLow fill1 step fill2) settled
    UnProgressUp (WFProj _ _ _ wt) (StepLow (FillLEnvUpRec (FillLEnvProj fill1)) step (FillLEnvUpRec (FillLEnvProj fill2))) (SettledUp (SettledProj settled)) = UnProgressLow wt (StepLow fill1 step fill2) settled 

    UnProgressLow : ∀ {Γ e e'} ->
      (Γ L⊢ e) ->  
      (e L↦ e') -> 
      (e L̸↦) ->
      ⊥ 
    UnProgressLow (WFSubsume _ _ _ syn) (StepLow FillL⊙ (StepSyn _) FillL⊙) (SettledLow ())
    UnProgressLow (WFSubsume _ _ _ syn) (StepLow (FillLEnvLowRec fill1) step (FillLEnvLowRec fill2)) (SettledLow settled) = UnProgressUp syn (StepLow fill1 step fill2) settled
    UnProgressLow (WFSubsume _ _ _ syn) (StepUp (FillUEnvLowRec fill1) step (FillUEnvLowRec fill2)) (SettledLow settled) = UnProgressUp syn (StepUp fill1 step fill2) settled
    UnProgressLow (WFFun _ _ _ _ _ _ _ _ ana) (StepLow FillL⊙ StepSynFun FillL⊙) (SettledLow (SettledUp (SettledFun (SettledLow ()))))
    UnProgressLow (WFFun _ _ _ _ _ _ _ _ ana) (StepUp (FillUEnvLowRec (FillUEnvUpRec (FillUEnvFun fill1))) step (FillUEnvLowRec (FillUEnvUpRec (FillUEnvFun fill2)))) (SettledLow (SettledUp (SettledFun settled))) = UnProgressLow ana (StepUp fill1 step fill2) settled
    UnProgressLow (WFFun _ _ _ _ _ _ _ _ ana) (StepLow (FillLEnvLowRec (FillLEnvUpRec (FillLEnvFun fill1))) step (FillLEnvLowRec (FillLEnvUpRec (FillLEnvFun fill2)))) (SettledLow (SettledUp (SettledFun settled))) = UnProgressLow ana (StepLow fill1 step fill2) settled
    UnProgressLow (WFPair _ _ _ _ _ _ _ wt1 wt2) (StepUp (FillUEnvLowRec (FillUEnvUpRec (FillUEnvPair1 fill1))) step (FillUEnvLowRec (FillUEnvUpRec (FillUEnvPair1 fill2)))) (SettledLow (SettledUp (SettledPair settled1 settled2))) = UnProgressLow wt1 (StepUp fill1 step fill2) settled1
    UnProgressLow (WFPair _ _ _ _ _ _ _ wt1 wt2) (StepUp (FillUEnvLowRec (FillUEnvUpRec (FillUEnvPair2 fill1))) step (FillUEnvLowRec (FillUEnvUpRec (FillUEnvPair2 fill2)))) (SettledLow (SettledUp (SettledPair settled1 settled2))) = UnProgressLow wt2 (StepUp fill1 step fill2) settled2
    UnProgressLow (WFPair _ _ _ _ _ _ _ wt1 wt2) (StepLow FillL⊙ StepSynPairFst FillL⊙) (SettledLow (SettledUp (SettledPair (SettledLow ()) settled2))) 
    UnProgressLow (WFPair _ _ _ _ _ _ _ wt1 wt2) (StepLow FillL⊙ StepSynPairSnd FillL⊙) (SettledLow (SettledUp (SettledPair settled1 (SettledLow ())))) 
    UnProgressLow (WFPair _ _ _ _ _ _ _ wt1 wt2) (StepLow (FillLEnvLowRec (FillLEnvUpRec (FillLEnvPair1 fill1))) step (FillLEnvLowRec (FillLEnvUpRec (FillLEnvPair1 fill2)))) (SettledLow (SettledUp (SettledPair settled1 settled2))) = UnProgressLow wt1 (StepLow fill1 step fill2) settled1
    UnProgressLow (WFPair _ _ _ _ _ _ _ wt1 wt2) (StepLow (FillLEnvLowRec (FillLEnvUpRec (FillLEnvPair2 fill1))) step (FillLEnvLowRec (FillLEnvUpRec (FillLEnvPair2 fill2)))) (SettledLow (SettledUp (SettledPair settled1 settled2))) = UnProgressLow wt2 (StepLow fill1 step fill2) settled2

  UnProgressProgram : ∀ {p p'} ->  
    P⊢ p ->   
    (p P↦ p') ->   
    (p P̸↦) ->
    ⊥       
  UnProgressProgram {p = Root e .•} (WFProgram ana) (InsideStep step) (SettledProgram (SettledLow settled)) = UnProgressLow ana step (SettledLow settled)   
  
   