
open import Data.Empty 
open import Data.Sum renaming (_⊎_ to _+_; inj₁ to Inl ; inj₂ to Inr) 
open import Data.Product 
open import Relation.Nullary 
open import Relation.Binary.PropositionalEquality

open import Prelude
open import Core.Core
open import Core.Environment
open import Core.WellFormed
open import Core.Quiescent
open import Core.Lemmas
open import Core.VariableUpdate
open import Core.Update

module Core.Progress where

  mutual 

    productive-syn-syn : ∀{Γ e t n} ->
      SubsumableMid e ->
      e M̸↦ -> 
      Γ S⊢ (e ⇒ (t , n)) ->
      ∃[ t' ] (t ≡ ■ t') 
    productive-syn-syn SubsumableConst QuiescentConst (WFConst (▷Pair ▶•)) = _ , refl
    productive-syn-syn SubsumableHole QuiescentHole (WFHole (▷Pair ▶•)) = _ , refl
    productive-syn-syn SubsumableVar QuiescentVar (WFVar x x₁) = _ , refl
    productive-syn-syn SubsumableAsc (QuiescentAsc x) (WFAsc _ x₁ x₂ x₃) = _ , refl
    productive-syn-syn SubsumableAp (QuiescentAp (QuiescentLow (QuiescentUp settled)) _) (WFAp marrow consist x₄ x₅ syn ana) with productive-syn-ana settled syn | marrow | consist
    ... | _ , refl | NTArrowC (DTArrowSome x) | ▷Pair ▶• = _ , refl
    productive-syn-syn SubsumableProj (QuiescentProj (QuiescentLow (QuiescentUp settled))) (WFProj mproj consist _ wt) with productive-syn-ana settled wt | mproj | consist
    ... | _ , refl | NTProjC (DTProjSome x) | ▷Pair ▶• = _ , refl
    productive-syn-syn SubsumableTypAp (QuiescentTypAp (QuiescentLow (QuiescentUp settled))) (WFTypAp x₁ mforall x₃ sub consist syn) with productive-syn-ana settled syn | mforall | sub | consist
    ... | _ , refl | NTForallC (DTForallSome x) | NSub-pair (NSubSome x₂) | ▷Pair ▶• = _ , refl

    productive-syn-ana : ∀{Γ e t m n} ->
      e M̸↦ -> 
      Γ L⊢ ((e ⇒ (t , n)) [ m ]⇐ (□ , •)) ->
      ∃[ t' ] (t ≡ ■ t') 
    productive-syn-ana settled (WFSubsume x x₁ x₂ x₃) = productive-syn-syn x settled x₃
    productive-syn-ana (QuiescentFun (QuiescentLow (QuiescentUp settled))) (WFFun wf (NTArrowC DTArrowNone) a2 (▷Pair ▶•) a4 a5 a6 a7 a8 ana) with productive-syn-ana settled ana | a6
    ... | t , refl | ▷Pair ▶• = _ , refl
    productive-syn-ana (QuiescentPair (QuiescentLow (QuiescentUp settled1)) (QuiescentLow (QuiescentUp settled2))) (WFPair (NTProdC DTProdNone) (▷Pair ▶•) (▷Pair ▶•) ▶• con4 consist con5 wt1 wt2) with productive-syn-ana settled1 wt1 | productive-syn-ana settled2 wt2 | con4
    ... | _ , refl | _ , refl | ▷Pair ▶• = _ , refl 
    productive-syn-ana (QuiescentTypFun (QuiescentLow (QuiescentUp settled))) (WFTypFun (NTForallBindC DTForallBindNone) (▷Pair ▶•) ▶• (▷Pair con) x₅ x₆ wf) with productive-syn-ana settled wf | con
    ... | _ , refl | ▶• = _ , refl

  dirty-ana-steps-syn-inner : ∀ {Γ e m t} ->
    Γ S⊢ e ->
    ∃[ e' ] (e [ m ]⇐ (t , ★)) l↦ e' 
  dirty-ana-steps-syn-inner (WFConst (▷Pair x)) = _ , StepAna SubsumableConst (proj₂ (~D-dec _ _)) 
  dirty-ana-steps-syn-inner (WFHole x) = _ , StepAna SubsumableHole (proj₂ (~D-dec _ _)) 
  dirty-ana-steps-syn-inner (WFAp x x₁ x₂ x₃ x₄ x₅) = _ , StepAna SubsumableAp (proj₂ (~D-dec _ _)) 
  dirty-ana-steps-syn-inner (WFVar x x₁) = _ , StepAna SubsumableVar  (proj₂ (~D-dec _ _)) 
  dirty-ana-steps-syn-inner (WFAsc _ x x₁ x₂) = _ , StepAna SubsumableAsc (proj₂ (~D-dec _ _)) 
  dirty-ana-steps-syn-inner (WFProj x x₁ x₂ x₄) = _ , StepAna SubsumableProj (proj₂ (~D-dec _ _))
  dirty-ana-steps-syn-inner (WFTypAp x x₁ x₂ x₃ x₄ x₅) = _ , StepAna SubsumableTypAp (proj₂ (~D-dec _ _))

  dirty-ana-steps-syn : ∀ {Γ e m t} ->
    Γ S⊢ e ->
    ∃[ e' ] (e [ m ]⇐ (t , ★)) L↦ e' 
  dirty-ana-steps-syn syn with dirty-ana-steps-syn-inner syn 
  ... | e' , step = e' , (StepLow FillA⊙ step FillA⊙)

  dirty-ana-steps-inner : ∀ {Γ e m t} ->
    Γ L⊢ ((e [ m ]⇐ (t , ★))) ->
    ∃[ e' ] (e [ m ]⇐ (t , ★)) l↦ e' 
  dirty-ana-steps-inner (WFSubsume x x₁ x₂ syn) = dirty-ana-steps-syn-inner syn
  dirty-ana-steps-inner (WFFun _ x x₁ x₂ x₃ x₄ x₅ x₆ x₇ ana) = _ , (StepAnaFun (proj₂ (proj₂ (proj₂ (▸DTArrow-dec _)))) (■~D-pair (proj₂ (~D-dec _ _))))
  dirty-ana-steps-inner (WFPair x x₁ x₂ x₃ x₄ x₅ x₆ wt wt₁) = _ , StepAnaPair (proj₂ (proj₂ (proj₂ (▸DTProd-dec _))))
  dirty-ana-steps-inner (WFTypFun x x₁ x₂ x₃ x₄ x₅ wf) = _ , StepAnaTypFun (proj₂ (proj₂ (▸DTForallBind-dec _ _)))
  
  dirty-ana-steps : ∀ {Γ e m t} ->
    Γ L⊢ (e [ m ]⇐ (t , ★)) ->
    ∃[ e' ] (e [ m ]⇐ (t , ★)) L↦ e' 
  dirty-ana-steps ana with dirty-ana-steps-inner ana 
  ... | e' , step = e' , (StepLow FillA⊙ step FillA⊙)

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
  var-update-dec {ETypFun x x₁ (x₂ [ x₃ ]⇐ x₄) ⇒ x₅} = _ , VSTypFun (proj₂ var-update-dec)
  var-update-dec {ETypAp (x [ x₁ ]⇐ x₂) x₃ x₄ ⇒ x₅} = _ , VSTypAp (proj₂ var-update-dec)

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
      (Γ S⊢ e) ->      
      (∃[ e' ] (e U↦ e')) + (e almost-U̸↦)
    ProgressUp (WFConst consist) = Inr (AlmostQuiescentUp QuiescentConst)
    ProgressUp (WFHole consist) = Inr (AlmostQuiescentUp QuiescentHole)
    ProgressUp (WFAp marrow x₁ x₂ x₃ syn ana) with ProgressLow syn | ProgressLow ana 
    ProgressUp (WFAp marrow x₁ x₂ x₃ syn ana) | Inl (e' , step) | progress = Inl (_ , StepLowUp (FillAnaEnvSynRec (FillAnaEnvAp1 FillA⊙)) step (FillAnaEnvSynRec (FillAnaEnvAp1 FillA⊙)))
    ProgressUp (WFAp marrow x₁ x₂ x₃ syn ana) | Inr (AlmostQuiescentLow (AlmostQuiescentUp {★} settled1)) | progress = Inl (_ , StepUp FillS⊙ (StepAp (proj₂ (proj₂ (proj₂ (▸DTArrow-dec _))))) FillS⊙)
    ProgressUp (WFAp marrow x₁ x₂ x₃ syn ana) | Inr (AlmostQuiescentLow (AlmostQuiescentUp {•} settled1)) | Inl (e' , step) = Inl (_ , StepLowUp (FillAnaEnvSynRec (FillAnaEnvAp2 FillA⊙)) step (FillAnaEnvSynRec (FillAnaEnvAp2 FillA⊙)))
    ProgressUp (WFAp marrow x₁ x₂ x₃ syn ana) | Inr (AlmostQuiescentLow (AlmostQuiescentUp {•} settled1)) | Inr (AlmostQuiescentLow (AlmostQuiescentUp {n} settled2)) with productive-syn-ana settled1 syn | marrow | x₂
    ProgressUp (WFAp marrow x₁ x₂ x₃ syn ana) | Inr (AlmostQuiescentLow (AlmostQuiescentUp {.•} settled1)) | Inr (AlmostQuiescentLow (AlmostQuiescentUp {★} settled2)) | t , refl | NTArrowC (DTArrowSome x) | ▷Pair ▶• = Inl (_ , StepLow (FillAnaEnvSynRec (FillAnaEnvAp2 FillA⊙)) (StepSyn (proj₂ (~D-dec _ _))) (FillAnaEnvSynRec (FillAnaEnvAp2 FillA⊙))) 
    ProgressUp (WFAp marrow x₁ x₂ x₃ syn ana) | Inr (AlmostQuiescentLow (AlmostQuiescentUp {.•} settled1)) | Inr (AlmostQuiescentLow (AlmostQuiescentUp {•} settled2)) | t , refl | NTArrowC (DTArrowSome x) | ▷Pair ▶• = Inr (AlmostQuiescentUp (QuiescentAp (QuiescentLow (QuiescentUp settled1)) (QuiescentLow (QuiescentUp settled2)))) 
    ProgressUp (WFVar x x₁) = Inr (AlmostQuiescentUp QuiescentVar)
    ProgressUp (WFAsc {t-asc = (t-asc , ★)} wf x x₁ ana) = Inl (_ , StepUp FillS⊙ StepAsc FillS⊙) 
    ProgressUp (WFAsc {t-asc = (t-asc , •)} wf x x₁ ana) with ProgressLow ana 
    ... | Inl (e' , step) = Inl (_ , StepLowUp (FillAnaEnvSynRec (FillAnaEnvAsc FillA⊙)) step (FillAnaEnvSynRec (FillAnaEnvAsc FillA⊙))) 
    ... | Inr (AlmostQuiescentLow (AlmostQuiescentUp {★} settled)) = Inl (_ , StepLow (FillAnaEnvSynRec (FillAnaEnvAsc FillA⊙)) (StepSyn (proj₂ (~D-dec _ _))) (FillAnaEnvSynRec (FillAnaEnvAsc FillA⊙))) 
    ... | Inr (AlmostQuiescentLow (AlmostQuiescentUp {•} settled)) = Inr (AlmostQuiescentUp (QuiescentAsc (QuiescentLow (QuiescentUp settled)))) 
    ProgressUp (WFProj mproj con1 con2 wt) with ProgressLow wt 
    ... | Inl (e' , step ) = Inl (_ , StepLowUp (FillAnaEnvSynRec (FillAnaEnvProj FillA⊙)) step (FillAnaEnvSynRec (FillAnaEnvProj FillA⊙))) 
    ... | Inr (AlmostQuiescentLow (AlmostQuiescentUp {★} settled)) = Inl (_ , StepUp FillS⊙ (StepProj (proj₂ (proj₂ (▸DTProj-dec _ _)))) FillS⊙)
    ... | Inr (AlmostQuiescentLow (AlmostQuiescentUp {•} settled)) = Inr (AlmostQuiescentUp (QuiescentProj (QuiescentLow (QuiescentUp settled))))
    ProgressUp (WFTypAp {n-arg = ★} wf1 x₁ x₂ x₃ x₄ ana) = Inl (_ , StepUp FillS⊙ (StepTypApArg (proj₂ (proj₂ (proj₂ (▸DTForall-dec _)))) (proj₂ (DSub-dec _ _ _))) FillS⊙)
    ProgressUp (WFTypAp {n-arg = •} wf1 x₁ x₂ x₃ x₄ ana) with ProgressLow ana 
    ... | Inl (e' , step) = Inl (_ , StepLowUp (FillAnaEnvSynRec (FillAnaEnvTypAp FillA⊙)) step (FillAnaEnvSynRec (FillAnaEnvTypAp FillA⊙)))
    ... | Inr (AlmostQuiescentLow (AlmostQuiescentUp {★} settled)) = Inl (_ , StepUp FillS⊙ (StepTypApFun (proj₂ (proj₂ (proj₂ (▸DTForall-dec _)))) (proj₂ (DSub-dec _ _ _))) FillS⊙)
    ... | Inr (AlmostQuiescentLow (AlmostQuiescentUp {•} settled)) = Inr (AlmostQuiescentUp (QuiescentTypAp (QuiescentLow (QuiescentUp settled))))

    ProgressLow :  
      ∀ {Γ e} ->
      (Γ L⊢ e) ->      
      (∃[ e' ] (e L↦ e')) + (e almost-L̸↦)
    ProgressLow (WFSubsume subsumable consist m-consist syn) with ProgressUp syn 
    ProgressLow (WFSubsume subsumable consist m-consist syn) | Inl (e' , step) = Inl (_ , StepUpLow (FillSynEnvAnaRec FillS⊙) step (FillSynEnvAnaRec FillS⊙))
    ProgressLow (WFSubsume {ana-all = t , ★} subsumable consist m-consist syn) | Inr settled = Inl (dirty-ana-steps-syn syn)
    ProgressLow (WFSubsume {ana-all = t , •}  subsumable consist m-consist syn) | Inr settled = Inr (AlmostQuiescentLow settled)
    ProgressLow (WFFun {ana-all = t , ★} wf (NTArrowC marrow) (■~N-pair (~N-pair consist)) consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) = Inl (_ , StepLow FillA⊙ (StepAnaFun marrow (■~D-pair consist)) FillA⊙) 
    ProgressLow (WFFun {ana-all = ana-all , •} {t-asc = t-asc , ★} wf (NTArrowC marrow) (■~N-pair (~N-pair consist)) consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) = Inl (_ , StepLow FillA⊙ (StepAnnFun (proj₂ (proj₂ (proj₂ var-update?-dec-elaborate)))) FillA⊙)
    
    ProgressLow (WFFun {ana-all = ana-all , •} {ana-body = ana-body , ★} {t-asc = t-asc , •} wf marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) = Inl (_ , StepLow (FillAnaEnvAnaRec (FillAnaEnvSynRec (FillAnaEnvFun FillA⊙))) (proj₂ (dirty-ana-steps-inner ana)) (FillAnaEnvAnaRec (FillAnaEnvSynRec (FillAnaEnvFun FillA⊙))))
    ProgressLow (WFFun {ana-all = ana-all , •} {ana-body = ana-body , •} {t-asc = t-asc , •} wf marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) with ProgressLow ana  
    ProgressLow (WFFun {ana-all = ana-all , •} {ana-body = ana-body , •} {t-asc = t-asc , •} wf marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) | Inl (e' , step) = Inl (_ , StepLowLow (FillAnaEnvAnaRec (FillAnaEnvSynRec (FillAnaEnvFun FillA⊙))) step (FillAnaEnvAnaRec (FillAnaEnvSynRec (FillAnaEnvFun FillA⊙))))
    ProgressLow (WFFun {ana-all = ana-all , •} {ana-body = ana-body , •} {t-asc = t-asc , •} wf marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) | Inr (AlmostQuiescentLow (AlmostQuiescentUp {★} settled)) with ana-body 
    ProgressLow (WFFun {ana-all = ana-all , •} {ana-body = ana-body , •} {t-asc = t-asc , •} wf marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) | Inr (AlmostQuiescentLow (AlmostQuiescentUp {★} settled)) | □ = Inl (_ , StepLow FillA⊙ StepSynFun FillA⊙)
    ProgressLow (WFFun {ana-all = ana-all , •} {ana-body = ana-body , •} {t-asc = t-asc , •} wf marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) | Inr (AlmostQuiescentLow (AlmostQuiescentUp {★} settled)) | ■ _ = Inl (_ , StepLow (FillAnaEnvAnaRec (FillAnaEnvSynRec (FillAnaEnvFun FillA⊙))) (StepSyn (proj₂ (~D-dec _ _))) (FillAnaEnvAnaRec (FillAnaEnvSynRec (FillAnaEnvFun FillA⊙)))) 
    ProgressLow (WFFun {ana-all = ana-all , •} {ana-body = ana-body , •} {t-asc = t-asc , •} wf marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) | Inr (AlmostQuiescentLow (AlmostQuiescentUp {•} settled)) = Inr (AlmostQuiescentLow (AlmostQuiescentUp (QuiescentFun (QuiescentLow (QuiescentUp settled)))))
    ProgressLow (WFPair {ana-all = t , ★} mprod con1 con2 con3 con4 consist con5 wt1 wt2) = Inl (_ , StepLow FillA⊙ (StepAnaPair (proj₂ (proj₂ (proj₂ (▸DTProd-dec _))))) FillA⊙) 
    ProgressLow (WFPair {ana-all = t , •} {ana-fst = ana-fst , ★} mprod con1 con2 con3 con4 consist con5 wt1 wt2) = Inl (_ , StepLow (FillAnaEnvAnaRec (FillAnaEnvSynRec (FillAnaEnvPair1 FillA⊙))) (proj₂ (dirty-ana-steps-inner wt1)) (FillAnaEnvAnaRec (FillAnaEnvSynRec (FillAnaEnvPair1 FillA⊙))))
    ProgressLow (WFPair {ana-all = t , •} {ana-fst = ana-fst , •} {ana-snd = ana-snd , ★} mprod con1 con2 con3 con4 consist con5 wt1 wt2) = Inl (_ , StepLow (FillAnaEnvAnaRec (FillAnaEnvSynRec (FillAnaEnvPair2 FillA⊙))) (proj₂ (dirty-ana-steps-inner wt2)) (FillAnaEnvAnaRec (FillAnaEnvSynRec (FillAnaEnvPair2 FillA⊙))))
    ProgressLow (WFPair {ana-all = t , •} {ana-fst = ana-fst , •} {ana-snd = ana-snd , •} mprod con1 con2 con3 con4 consist con5 wt1 wt2) with ProgressLow wt1 | ProgressLow wt2 
    ProgressLow (WFPair {ana-all = t , •} {ana-fst = ana-fst , •} {ana-snd = ana-snd , •} mprod con1 con2 con3 con4 consist con5 wt1 wt2) | Inl (e' , step) | p2 = Inl (_ , StepLowLow (FillAnaEnvAnaRec (FillAnaEnvSynRec (FillAnaEnvPair1 FillA⊙))) step (FillAnaEnvAnaRec (FillAnaEnvSynRec (FillAnaEnvPair1 FillA⊙))))
    ProgressLow (WFPair {ana-all = t , •} {ana-fst = ana-fst , •} {ana-snd = ana-snd , •} mprod con1 con2 con3 con4 consist con5 wt1 wt2) | Inr (AlmostQuiescentLow (AlmostQuiescentUp {★} settled)) | p2 with ana-fst 
    ProgressLow (WFPair {ana-all = t , •} {ana-fst = ana-fst , •} {ana-snd = ana-snd , •} mprod con1 con2 con3 con4 consist con5 wt1 wt2) | Inr (AlmostQuiescentLow (AlmostQuiescentUp {★} settled)) | p2 | □ = Inl (_ , StepLow FillA⊙ StepSynPairFst FillA⊙) 
    ProgressLow (WFPair {ana-all = t , •} {ana-fst = ana-fst , •} {ana-snd = ana-snd , •} mprod con1 con2 con3 con4 consist con5 wt1 wt2) | Inr (AlmostQuiescentLow (AlmostQuiescentUp {★} settled)) | p2 | ■ _ = Inl (_ , StepLow (FillAnaEnvAnaRec (FillAnaEnvSynRec (FillAnaEnvPair1 FillA⊙))) (StepSyn (proj₂ (~D-dec _ _))) (FillAnaEnvAnaRec (FillAnaEnvSynRec (FillAnaEnvPair1 FillA⊙)))) 
    ProgressLow (WFPair {ana-all = t , •} {ana-fst = ana-fst , •} {ana-snd = ana-snd , •} mprod con1 con2 con3 con4 consist con5 wt1 wt2) | Inr (AlmostQuiescentLow (AlmostQuiescentUp {•} settled)) | Inl (e' , step) = Inl (_ , StepLowLow (FillAnaEnvAnaRec (FillAnaEnvSynRec (FillAnaEnvPair2 FillA⊙))) step (FillAnaEnvAnaRec (FillAnaEnvSynRec (FillAnaEnvPair2 FillA⊙))))
    ProgressLow (WFPair {ana-all = t , •} {ana-fst = ana-fst , •} {ana-snd = ana-snd , •} mprod con1 con2 con3 con4 consist con5 wt1 wt2) | Inr (AlmostQuiescentLow (AlmostQuiescentUp {•} settled1)) | Inr (AlmostQuiescentLow (AlmostQuiescentUp {★} settled2)) with ana-snd
    ProgressLow (WFPair {ana-all = t , •} {ana-fst = ana-fst , •} {ana-snd = ana-snd , •} mprod con1 con2 con3 con4 consist con5 wt1 wt2) | Inr (AlmostQuiescentLow (AlmostQuiescentUp {•} settled1)) | Inr (AlmostQuiescentLow (AlmostQuiescentUp {★} settled2)) | □ = Inl (_ , StepLow FillA⊙ StepSynPairSnd FillA⊙) 
    ProgressLow (WFPair {ana-all = t , •} {ana-fst = ana-fst , •} {ana-snd = ana-snd , •} mprod con1 con2 con3 con4 consist con5 wt1 wt2) | Inr (AlmostQuiescentLow (AlmostQuiescentUp {•} settled1)) | Inr (AlmostQuiescentLow (AlmostQuiescentUp {★} settled2)) | ■ _ = Inl (_ , StepLow (FillAnaEnvAnaRec (FillAnaEnvSynRec (FillAnaEnvPair2 FillA⊙))) (StepSyn (proj₂ (~D-dec _ _))) (FillAnaEnvAnaRec (FillAnaEnvSynRec (FillAnaEnvPair2 FillA⊙)))) 
    ProgressLow (WFPair {ana-all = t , •} {ana-fst = ana-fst , •} {ana-snd = ana-snd , •} mprod con1 con2 con3 con4 consist con5 wt1 wt2) | Inr (AlmostQuiescentLow (AlmostQuiescentUp {•} settled1)) | Inr (AlmostQuiescentLow (AlmostQuiescentUp {•} settled2)) = Inr (AlmostQuiescentLow (AlmostQuiescentUp (QuiescentPair (QuiescentLow (QuiescentUp settled1)) (QuiescentLow (QuiescentUp settled2))))) 
    ProgressLow (WFTypFun {ana-all = ana-all , ★} (NTForallBindC mforall) m1 m2 m3 con m4 wt) = Inl (_ , StepLow FillA⊙ (StepAnaTypFun mforall) FillA⊙)
    ProgressLow (WFTypFun {ana-all = ana-all , •} {ana-body = ana-body , ★} mforall m1 m2 m3 con m4 wt) = Inl (_ , StepLow (FillAnaEnvAnaRec (FillAnaEnvSynRec (FillAnaEnvTypFun FillA⊙))) (proj₂ (dirty-ana-steps-inner wt)) (FillAnaEnvAnaRec (FillAnaEnvSynRec (FillAnaEnvTypFun FillA⊙))))
    ProgressLow (WFTypFun {ana-all = ana-all , •} {ana-body = ana-body , •} mforall m1 m2 m3 con m4 wt) with ProgressLow wt
    ProgressLow (WFTypFun {ana-all = ana-all , •} {ana-body = ana-body , •} mforall m1 m2 m3 con m4 wt) | Inl (e' , step) = Inl (_ , StepLowLow (FillAnaEnvAnaRec (FillAnaEnvSynRec (FillAnaEnvTypFun FillA⊙))) step (FillAnaEnvAnaRec (FillAnaEnvSynRec (FillAnaEnvTypFun FillA⊙))))
    ProgressLow (WFTypFun {ana-all = ana-all , •} {ana-body = ana-body , •} mforall m1 m2 m3 con m4 wt) | Inr (AlmostQuiescentLow (AlmostQuiescentUp {★} settled)) with ana-body
    ProgressLow (WFTypFun {ana-all = ana-all , •} {ana-body = ana-body , •} mforall m1 m2 m3 con m4 wt) | Inr (AlmostQuiescentLow (AlmostQuiescentUp {★} settled)) | □ = Inl (_ , StepLow FillA⊙ StepSynTypFun FillA⊙)
    ProgressLow (WFTypFun {ana-all = ana-all , •} {ana-body = ana-body , •} mforall m1 m2 m3 con m4 wt) | Inr (AlmostQuiescentLow (AlmostQuiescentUp {★} settled)) | ■ _ = Inl (_ , StepLow (FillAnaEnvAnaRec (FillAnaEnvSynRec (FillAnaEnvTypFun FillA⊙))) (StepSyn (proj₂ (~D-dec _ _))) (FillAnaEnvAnaRec (FillAnaEnvSynRec (FillAnaEnvTypFun FillA⊙))))
    ProgressLow (WFTypFun {ana-all = ana-all , •} {ana-body = ana-body , •} mforall m1 m2 m3 con m4 wt) | Inr (AlmostQuiescentLow (AlmostQuiescentUp {•} settled)) = Inr (AlmostQuiescentLow (AlmostQuiescentUp (QuiescentTypFun (QuiescentLow (QuiescentUp settled)))))


  step-preserves-program : ∀ {p e} -> 
    AnaExpOfProgram p L↦ e -> 
    ∃[ p' ] (e ≡ AnaExpOfProgram p')
  step-preserves-program {p = Root e n} (StepUp (FillSynEnvAnaRec x) step (FillSynEnvAnaRec x₁)) = Root _ _ , refl
  step-preserves-program {p = Root e n} (StepLow (FillAnaEnvAnaRec x) step (FillAnaEnvAnaRec x₁)) = Root _ _ , refl
  step-preserves-program {p = Root e n} (StepLow FillA⊙ (StepAna x consist) FillA⊙) with ~DVoid-right consist 
  ... | refl = Root _ _ , refl
  step-preserves-program {p = Root e n} (StepLow FillA⊙ (StepAnaFun _ _) FillA⊙) = Root _ _ , refl
  step-preserves-program {p = Root e n} (StepLow FillA⊙ (StepAnnFun _) FillA⊙) = Root _ _ , refl
  step-preserves-program {p = Root e n} (StepLow FillA⊙ StepSynFun FillA⊙) = Root _ _ , refl
  step-preserves-program {p = Root e n} (StepLow FillA⊙ (StepAnaPair _) FillA⊙) = Root _ _ , refl
  step-preserves-program {p = Root e n} (StepLow FillA⊙ StepSynPairFst FillA⊙) = Root _ _ , refl
  step-preserves-program {p = Root e n} (StepLow FillA⊙ StepSynPairSnd FillA⊙) = Root _ _ , refl
  step-preserves-program {p = Root e n} (StepLow FillA⊙ (StepAnaTypFun x) FillA⊙) = Root _ _ , refl
  step-preserves-program {p = Root e n} (StepLow FillA⊙ StepSynTypFun FillA⊙) = Root _ _ , refl

  ProgressProgram : ∀ {p} ->
    P⊢ p ->   
    (∃[ p' ] (p P↦ p')) + (p P̸↦)   
  ProgressProgram (WFProgram ana) with ProgressLow ana   
  ProgressProgram (WFProgram ana) | Inl (e' , step) with step-preserves-program step 
  ProgressProgram (WFProgram ana) | Inl (e' , step) | p' , refl = Inl (p' , (InsideStep step)) 
  ProgressProgram {p = Root e n} (WFProgram ana) | Inr (AlmostQuiescentLow (AlmostQuiescentUp {•} settled)) = Inr (QuiescentProgram (QuiescentLow (QuiescentUp settled))) 
  ProgressProgram {p = Root e n} (WFProgram ana) | Inr (AlmostQuiescentLow (AlmostQuiescentUp {★} settled)) = Inl (_ , TopStep) 

  mutual 
    
    UnProgressUp : ∀ {Γ e e'} ->
      (Γ S⊢ e) ->  
      (e U↦ e') -> 
      (e U̸↦) ->
      ⊥ 
    UnProgressUp (WFConst x) (StepUp FillS⊙ () FillS⊙) settled
    UnProgressUp (WFHole x) (StepUp FillS⊙ () FillS⊙) settled
    UnProgressUp (WFVar x x₁) (StepUp FillS⊙ () FillS⊙) settled
    UnProgressUp (WFAp _ _ _ _ _ _) (StepUp FillS⊙ (StepAp _) FillS⊙) (QuiescentUp (QuiescentAp (QuiescentLow ()) _))
    UnProgressUp (WFAsc _ _ _ ana) (StepUp FillS⊙ StepAsc FillS⊙) (QuiescentUp ())
    UnProgressUp (WFTypAp _ _ _ _ _ wf) (StepUp FillS⊙ (StepTypApFun x x₁) FillS⊙) (QuiescentUp (QuiescentTypAp (QuiescentLow ())))
    UnProgressUp (WFTypAp _ _ _ _ _ wf) (StepUp FillS⊙ (StepTypApArg x x₁) FillS⊙) (QuiescentUp ())

    UnProgressUp (WFConst x) (StepUp (FillSynEnvSynRec ()) step (FillSynEnvSynRec x₁)) settled
    UnProgressUp (WFHole x) (StepUp (FillSynEnvSynRec ()) step (FillSynEnvSynRec x₁)) settled
    UnProgressUp (WFVar _ _) (StepUp (FillSynEnvSynRec ()) step (FillSynEnvSynRec x₁)) settled
    UnProgressUp (WFAp _ _ _ _ syn ana) (StepUp (FillSynEnvSynRec (FillSynEnvAp1 fill1)) step (FillSynEnvSynRec (FillSynEnvAp1 fill2))) (QuiescentUp (QuiescentAp settled _)) = UnProgressLow syn (StepUp fill1 step fill2) settled
    UnProgressUp (WFAp _ _ _ _ syn ana) (StepUp (FillSynEnvSynRec (FillSynEnvAp2 fill1)) step (FillSynEnvSynRec (FillSynEnvAp2 fill2))) (QuiescentUp (QuiescentAp _ settled)) = UnProgressLow ana (StepUp fill1 step fill2) settled
    UnProgressUp (WFAsc _ _ _ ana) (StepUp (FillSynEnvSynRec (FillSynEnvAsc fill1)) step (FillSynEnvSynRec (FillSynEnvAsc fill2))) (QuiescentUp (QuiescentAsc settled)) = UnProgressLow ana (StepUp fill1 step fill2) settled
    UnProgressUp (WFProj _ _ _ _) (StepUp FillS⊙ (StepProj _) FillS⊙) (QuiescentUp (QuiescentProj (QuiescentLow ())))
    UnProgressUp (WFProj _ _ _ wt) (StepUp (FillSynEnvSynRec (FillSynEnvProj fill1)) step (FillSynEnvSynRec (FillSynEnvProj fill2))) (QuiescentUp (QuiescentProj settled)) = UnProgressLow wt (StepUp fill1 step fill2) settled
    UnProgressUp (WFTypAp _ _ _ _ _ wf) (StepUp (FillSynEnvSynRec (FillSynEnvTypAp fill1)) step (FillSynEnvSynRec (FillSynEnvTypAp fill2))) (QuiescentUp (QuiescentTypAp settled)) = UnProgressLow wf (StepUp fill1 step fill2) settled
    
    UnProgressUp (WFConst x) (StepLow (FillAnaEnvSynRec ()) step (FillAnaEnvSynRec fill2)) (QuiescentUp settled)
    UnProgressUp (WFHole x) (StepLow (FillAnaEnvSynRec ()) step (FillAnaEnvSynRec fill2)) (QuiescentUp settled)
    UnProgressUp (WFVar _ _) (StepLow (FillAnaEnvSynRec ()) step (FillAnaEnvSynRec fill2)) (QuiescentUp settled)
    UnProgressUp (WFAp _ _ _ _ syn ana) (StepLow (FillAnaEnvSynRec (FillAnaEnvAp1 fill1)) step (FillAnaEnvSynRec (FillAnaEnvAp1 fill2))) (QuiescentUp (QuiescentAp settled _)) = UnProgressLow syn (StepLow fill1 step fill2) settled
    UnProgressUp (WFAp _ _ _ _ syn ana) (StepLow (FillAnaEnvSynRec (FillAnaEnvAp2 fill1)) step (FillAnaEnvSynRec (FillAnaEnvAp2 fill2))) (QuiescentUp (QuiescentAp _ settled)) = UnProgressLow ana (StepLow fill1 step fill2) settled
    UnProgressUp (WFAsc _ _ _ ana) (StepLow (FillAnaEnvSynRec (FillAnaEnvAsc fill1)) step (FillAnaEnvSynRec (FillAnaEnvAsc fill2))) (QuiescentUp (QuiescentAsc settled)) = UnProgressLow ana (StepLow fill1 step fill2) settled
    UnProgressUp (WFProj _ _ _ wt) (StepLow (FillAnaEnvSynRec (FillAnaEnvProj fill1)) step (FillAnaEnvSynRec (FillAnaEnvProj fill2))) (QuiescentUp (QuiescentProj settled)) = UnProgressLow wt (StepLow fill1 step fill2) settled 
    UnProgressUp (WFTypAp _ _ _ _ _ wf) (StepLow (FillAnaEnvSynRec (FillAnaEnvTypAp fill1)) step (FillAnaEnvSynRec (FillAnaEnvTypAp fill2))) (QuiescentUp (QuiescentTypAp settled)) = UnProgressLow wf (StepLow fill1 step fill2) settled

    UnProgressLow : ∀ {Γ e e'} ->
      (Γ L⊢ e) ->  
      (e L↦ e') -> 
      (e L̸↦) ->
      ⊥ 
    UnProgressLow (WFSubsume _ _ _ syn) (StepLow FillA⊙ (StepSyn _) FillA⊙) (QuiescentLow ())
    UnProgressLow (WFSubsume _ _ _ syn) (StepLow (FillAnaEnvAnaRec fill1) step (FillAnaEnvAnaRec fill2)) (QuiescentLow settled) = UnProgressUp syn (StepLow fill1 step fill2) settled
    UnProgressLow (WFSubsume _ _ _ syn) (StepUp (FillSynEnvAnaRec fill1) step (FillSynEnvAnaRec fill2)) (QuiescentLow settled) = UnProgressUp syn (StepUp fill1 step fill2) settled
    UnProgressLow (WFFun _ _ _ _ _ _ _ _ _ ana) (StepLow FillA⊙ StepSynFun FillA⊙) (QuiescentLow (QuiescentUp (QuiescentFun (QuiescentLow ()))))
    UnProgressLow (WFFun _ _ _ _ _ _ _ _ _ ana) (StepUp (FillSynEnvAnaRec (FillSynEnvSynRec (FillSynEnvFun fill1))) step (FillSynEnvAnaRec (FillSynEnvSynRec (FillSynEnvFun fill2)))) (QuiescentLow (QuiescentUp (QuiescentFun settled))) = UnProgressLow ana (StepUp fill1 step fill2) settled
    UnProgressLow (WFFun _ _ _ _ _ _ _ _ _ ana) (StepLow (FillAnaEnvAnaRec (FillAnaEnvSynRec (FillAnaEnvFun fill1))) step (FillAnaEnvAnaRec (FillAnaEnvSynRec (FillAnaEnvFun fill2)))) (QuiescentLow (QuiescentUp (QuiescentFun settled))) = UnProgressLow ana (StepLow fill1 step fill2) settled
    UnProgressLow (WFPair _ _ _ _ _ _ _ wt1 wt2) (StepUp (FillSynEnvAnaRec (FillSynEnvSynRec (FillSynEnvPair1 fill1))) step (FillSynEnvAnaRec (FillSynEnvSynRec (FillSynEnvPair1 fill2)))) (QuiescentLow (QuiescentUp (QuiescentPair settled1 settled2))) = UnProgressLow wt1 (StepUp fill1 step fill2) settled1
    UnProgressLow (WFPair _ _ _ _ _ _ _ wt1 wt2) (StepUp (FillSynEnvAnaRec (FillSynEnvSynRec (FillSynEnvPair2 fill1))) step (FillSynEnvAnaRec (FillSynEnvSynRec (FillSynEnvPair2 fill2)))) (QuiescentLow (QuiescentUp (QuiescentPair settled1 settled2))) = UnProgressLow wt2 (StepUp fill1 step fill2) settled2
    UnProgressLow (WFPair _ _ _ _ _ _ _ wt1 wt2) (StepLow FillA⊙ StepSynPairFst FillA⊙) (QuiescentLow (QuiescentUp (QuiescentPair (QuiescentLow ()) settled2))) 
    UnProgressLow (WFPair _ _ _ _ _ _ _ wt1 wt2) (StepLow FillA⊙ StepSynPairSnd FillA⊙) (QuiescentLow (QuiescentUp (QuiescentPair settled1 (QuiescentLow ())))) 
    UnProgressLow (WFPair _ _ _ _ _ _ _ wt1 wt2) (StepLow (FillAnaEnvAnaRec (FillAnaEnvSynRec (FillAnaEnvPair1 fill1))) step (FillAnaEnvAnaRec (FillAnaEnvSynRec (FillAnaEnvPair1 fill2)))) (QuiescentLow (QuiescentUp (QuiescentPair settled1 settled2))) = UnProgressLow wt1 (StepLow fill1 step fill2) settled1
    UnProgressLow (WFPair _ _ _ _ _ _ _ wt1 wt2) (StepLow (FillAnaEnvAnaRec (FillAnaEnvSynRec (FillAnaEnvPair2 fill1))) step (FillAnaEnvAnaRec (FillAnaEnvSynRec (FillAnaEnvPair2 fill2)))) (QuiescentLow (QuiescentUp (QuiescentPair settled1 settled2))) = UnProgressLow wt2 (StepLow fill1 step fill2) settled2
    UnProgressLow (WFTypFun _ _ _ _ _ _ wf) (StepLow FillA⊙ StepSynTypFun FillA⊙) (QuiescentLow (QuiescentUp (QuiescentTypFun (QuiescentLow ()))))
    UnProgressLow (WFTypFun _ _ _ _ _ _ wf) (StepUp (FillSynEnvAnaRec (FillSynEnvSynRec (FillSynEnvTypFun fill1))) step (FillSynEnvAnaRec (FillSynEnvSynRec (FillSynEnvTypFun fill2)))) (QuiescentLow (QuiescentUp (QuiescentTypFun settled))) = UnProgressLow wf (StepUp fill1 step fill2) settled
    UnProgressLow (WFTypFun _ _ _ _ _ _ wf) (StepLow (FillAnaEnvAnaRec (FillAnaEnvSynRec (FillAnaEnvTypFun fill1))) step (FillAnaEnvAnaRec (FillAnaEnvSynRec (FillAnaEnvTypFun fill2)))) (QuiescentLow (QuiescentUp (QuiescentTypFun settled))) = UnProgressLow wf (StepLow fill1 step fill2) settled

  UnProgressProgram : ∀ {p p'} ->  
    P⊢ p ->   
    (p P↦ p') ->   
    (p P̸↦) ->
    ⊥       
  UnProgressProgram {p = Root e .•} (WFProgram ana) (InsideStep step) (QuiescentProgram (QuiescentLow settled)) = UnProgressLow ana step (QuiescentLow settled)   
  
    