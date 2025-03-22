
open import Data.Product 
open import Relation.Binary.PropositionalEquality

open import Prelude
open import Core.Core
open import Core.WellTyped
open import Core.Lemmas
open import Core.Actions
open import Core.VarsSynthesizePreservation

module Core.ActionPreservation where

  beyond-αL↦ : ∀ {Γ α e e' m m' ana ana'} -> 
    Γ ⊢ α , (e [ m ]⇐ ana) αL↦ (e' [ m' ]⇐ ana') -> 
    ◁▷ ana ana' 
  beyond-αL↦ (ALC _) = ◁▷C

  beyond-AL↦ : ∀ {Γ A e e' m m' ana ana'} -> 
    Γ ⊢ A , (e [ m ]⇐ ana) AL↦ (e' [ m' ]⇐ ana') -> 
    ◁▷ ana ana' 
  beyond-AL↦ (ALowDone (ALC _)) = ◁▷C
  beyond-AL↦ {ana = (_ , _)} (ALowUp x) = ◁▷C

  same-mark-AL↦ : ∀ {Γ A e e' m m' ana ana'} -> 
    Γ ⊢ A , (e [ m ]⇐ ana) AL↦ (e' [ m' ]⇐ ana') -> 
    m ≡ m'
  same-mark-AL↦ (ALowDone (ALC _)) = refl
  same-mark-AL↦ {ana = (_ , _)} (ALowUp x) = refl

  beyond-αU↦ : ∀ {Γ α e e' syn syn'} -> 
    Γ ⊢ α , (e ⇒ syn) αU↦ (e' ⇒ syn') -> 
    =▷ syn syn' 
  beyond-αU↦ ActInsertConst = =▷New
  beyond-αU↦ ActWrapFun = =▷New
  beyond-αU↦ ActWrapApOne = =▷New
  beyond-αU↦ ActWrapApTwo = =▷New
  beyond-αU↦ ActWrapPairOne = =▷New
  beyond-αU↦ ActWrapPairTwo = =▷New
  beyond-αU↦ ActWrapProj = =▷New
  beyond-αU↦ (ActInsertVar _) = =▷New
  beyond-αU↦ ActWrapAsc = =▷New
  beyond-αU↦ ActDelete = =▷New
  beyond-αU↦ (ActUnwrapFun _ _) = =▷New
  beyond-αU↦ ActUnwrapApOne = =▷New
  beyond-αU↦ ActUnwrapApTwo = =▷New
  beyond-αU↦ ActUnwrapAsc = =▷New
  beyond-αU↦ ActUnwrapPairOne = =▷New
  beyond-αU↦ ActUnwrapPairTwo = =▷New
  beyond-αU↦ ActUnwrapProj = =▷New
  beyond-αU↦ ActSetAsc = =▷Refl
  beyond-αU↦ ActSetAnn = =▷Refl
  beyond-αU↦ (ActDeleteBinder _ _) = =▷Refl
  beyond-αU↦ (ActInsertBinder _) = =▷Refl

  beyond-AU↦ : ∀ {Γ A e e' syn syn'} -> 
    Γ ⊢ A , (e ⇒ syn) AU↦ (e' ⇒ syn') -> 
    =▷ syn syn' 
  beyond-AU↦ (AUpMid step) = =▷Refl

  beyond-αL↦-inner : ∀ {Γ α e e' syn syn' m m' ana ana'} -> 
    Γ ⊢ α , ((e ⇒ syn) [ m ]⇐ ana) αL↦ ((e' ⇒ syn') [ m' ]⇐ ana') -> 
    =▷ syn syn' 
  beyond-αL↦-inner (ALC step) = beyond-αU↦ step

  beyond-AL↦-inner : ∀ {Γ A e e' syn syn' m m' ana ana'} -> 
    Γ ⊢ A , ((e ⇒ syn) [ m ]⇐ ana) AL↦ ((e' ⇒ syn') [ m' ]⇐ ana') -> 
    =▷ syn syn' 
  beyond-AL↦-inner (ALowDone step) = beyond-αL↦-inner step
  beyond-AL↦-inner (ALowUp step) = beyond-AU↦ step

  subsumable-AM↦ : ∀{Γ A e e'} ->
    SubsumableMid e ->
    Γ ⊢ A , e AM↦ e' ->
    SubsumableMid e'
  subsumable-AM↦ () (AMidFun x)
  subsumable-AM↦ SubsumableAsc (AMidAsc x) = SubsumableAsc
  subsumable-AM↦ SubsumableAp (AMidApOne x) = SubsumableAp
  subsumable-AM↦ SubsumableAp (AMidApTwo x) = SubsumableAp
  subsumable-AM↦ SubsumableProj (AMidProj x) = SubsumableProj

  SynSubsume :  
    ∀ {Γ e t} ->
    Γ U⊢ (e ⇒ (t , New)) ->
    Subsumable (e ⇒ (t , New))
  SynSubsume (WTConst x) = SubsumableConst
  SynSubsume (WTHole x) = SubsumableHole
  SynSubsume (WTAp x x₁ x₂ x₃ x₄ x₅) = SubsumableAp
  SynSubsume (WTVar x x₁) = SubsumableVar
  SynSubsume (WTAsc x x₁ x₂) = SubsumableAsc
  SynSubsume (WTProj x x₁ x₂ x₃) = SubsumableProj
    
  WrapSubsume :  
    ∀ {Γ e t m ana} ->
    Γ U⊢ (e ⇒ (t , New)) ->
    Γ L⊢ ((e ⇒ (t , New)) [ m ]⇐ ana)
  WrapSubsume {t = t} {ana = ana} syn with ~N-dec (t , New) ana
  ... | _ , ~N-pair x = WTUp (SynSubsume syn) (~N-pair x) ▶New syn

  PreservationStep :  
    ∀ {Γ α e e'} ->
    (Γ L⊢ e) ->
    (Γ ⊢ α , e αL↦ e') ->   
    (Γ L⊢ e')
  PreservationStep ana (ALC ActDelete) = WrapSubsume (WTHole (▷Pair ▶Old))
  PreservationStep ana (ALC ActInsertConst) = WrapSubsume (WTConst (▷Pair ▶Old))
  PreservationStep ana (ALC (ActInsertVar in-ctx)) = WrapSubsume (WTVar in-ctx (▷Pair ▶Same))
  PreservationStep ana (ALC ActWrapAsc) = WrapSubsume (WTAsc (▷Pair ▶Same) (▷Pair ▶Same) (newify-ana ana))
  PreservationStep ana (ALC ActWrapApTwo) = WrapSubsume (WTAp (NTArrowC (DTArrowSome MArrowHole)) (▷Pair ▶Old) (▷Pair ▶Old) ▶Old (WTUp SubsumableHole (~N-pair ~DVoidR) ▶Old (WTHole (▷Pair ▶Old))) (newify-ana ana))
  -- PreservationStep ana (ALC {t = t} {n = n} (ActWrapFun {t = t'} {n = n'} vars-syn)) with ▸NTArrow-dec (t , New) | ~N-dec (t' , n') (t , New)
  -- ... | (t-in , New) , (t-out , New) , (m , New) , NTArrowC consist | m' , consist-syn with ~N-dec (■ THole , New) (t-in , New) | new-through-~N-left consist-syn
  -- ... | _ , (~N-pair consist') | _ , refl = WTFun (NTArrowC consist) (■~N-pair (~N-pair consist')) (▷Pair ▶New) ▶New ▶New NUnless-new-▷ consist-syn ▶New (newify-ana (preservation-vars-ana?-alt ana vars-syn))
  PreservationStep ana (ALC {t = t} (ActWrapFun {t = t'})) with ▸DTArrow-dec t 
  ... | t-in , _ , _ , consist with ~D-dec (■ THole) t-in | ~D-dec t' t 
  ... | _ , consist1 | _ , consist2 = WTFun (NTArrowC consist) (■~N-pair (~N-pair consist1)) (▷Pair ▶New) ▶New ▶New NUnless-new-▷ (~N-pair consist2) ▶New (newify-ana ana)
  PreservationStep ana (ALC {t = t} (ActWrapApOne {t = t'} {n = n'})) with ~N-dec (t' , n') (t , New) | ▸NTArrow-dec (t' , New) 
  ... | _ , (~N-pair consist) | (t-in , New) , (t-out , New) , (m , New) , NTArrowC consist' = WTUp SubsumableAp (~N-pair consist) ▶New (WTAp (NTArrowC consist') (▷Pair ▶New) (▷Pair ▶New) ▶New (newify-ana ana) (WTUp SubsumableHole (~N-pair ~DVoidR) ▶Old (WTHole (▷Pair ▶Old))))
  PreservationStep wt (ALC ActWrapPairOne) = WTPair (NTProdC (proj₂ (proj₂ (proj₂ (▸DTProd-dec _))))) (▷Pair ▶New) (▷Pair ▶New) ▶New NUnless-new-▷ (~N-pair (proj₂ (~D-dec _ _))) ▶New (newify-ana {m = ✔} (newify-syn-inner wt)) (WTUp SubsumableHole (~N-pair ~DVoidR) ▶New (WTHole (▷Pair ▶Old)))
  PreservationStep wt (ALC ActWrapPairTwo) = WTPair (NTProdC (proj₂ (proj₂ (proj₂ (▸DTProd-dec _))))) (▷Pair ▶New) (▷Pair ▶New) ▶New NUnless-new-▷ (~N-pair (proj₂ (~D-dec _ _))) ▶New (WTUp SubsumableHole (~N-pair ~DVoidR) ▶New (WTHole (▷Pair ▶Old))) (newify-ana wt) 
  PreservationStep wt (ALC ActWrapProj) = WTUp SubsumableProj (~N-pair (proj₂ (~D-dec _ _))) ▶New (WTProj (proj₂ (proj₂ (▸NTProj-dec _ _))) (▷Pair ▶New) ▶New (newify-ana wt))

  PreservationStep (WTUp subsumable consist-t consist-m (WTAsc consist-syn consist-ana ana)) (ALC ActUnwrapAsc) = newify-ana ana
  PreservationStep (WTUp subsumable consist-t consist-m (WTAp marrow consist-syn consist-ana consist-mark syn ana)) (ALC ActUnwrapApOne) = newify-ana syn
  PreservationStep (WTUp subsumable consist-t consist-m (WTAp marrow consist-syn consist-ana consist-mark syn ana)) (ALC ActUnwrapApTwo) = newify-ana ana
  PreservationStep (WTUp subsumable consist-t consist-m (WTProj x x₁ x₂ wt)) (ALC ActUnwrapProj) = newify-ana wt
  PreservationStep (WTFun marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) (ALC (ActUnwrapFun in-ctx vars-syn)) = newify-ana (preservation-vars-unwrap in-ctx ana vars-syn)
  PreservationStep (WTUp SubsumableAsc (~N-pair consist-t) consist-m (WTAsc {syn-all = syn-all} {n-syn = n-syn} consist-syn consist-ana ana)) (ALC {t = t} ActSetAsc) = WTUp SubsumableAsc (~N-pair consist-t) ▶New-max-r (WTAsc (▷Pair ▶New) (▷Pair ▶New) ana)
  PreservationStep (WTFun {x = x} marrow consist consist-ana consist-asc consist-body consist-syn (~N-pair consist-all) consist-m-all ana) (ALC {t = t} (ActSetAnn {t = t'})) with ▸NTArrow-dec (t , New)
  ... | (t-in , New) , (t-out , New) , (m , New) , NTArrowC consist with ~D-dec (■ t') t-in 
  ... | m' , consist' = WTFun (NTArrowC consist) (■~N-pair (~N-pair consist')) (▷Pair ▶New) ▶New ▶New NUnless-new-▷ (~N-pair consist-all) ▶New-max-r (newify-ctx {x = x} ana)
  PreservationStep (WTFun (NTArrowC marrow) (■~N-pair (~N-pair consist)) consist-ana consist-asc consist-body consist-syn (~N-pair consist-all) consist-m-all ana) (ALC (ActDeleteBinder in-ctx vars-syn)) 
    = WTFun (NTArrowC marrow) (■~N-pair (~N-pair consist)) (▷Pair ▶New) ▶New ▶New-max-r NUnless-new-▷ (~N-pair (proj₂ (~D-dec _ _))) ▶New-max-r (newify-syn-inner (preservation-vars-unwrap in-ctx ana vars-syn))
  PreservationStep (WTFun (NTArrowC marrow) (■~N-pair (~N-pair consist)) consist-ana consist-asc consist-body consist-syn (~N-pair consist-all) consist-m-all ana) (ALC (ActInsertBinder vars-syn)) 
    = WTFun (NTArrowC marrow) (■~N-pair (~N-pair consist)) (▷Pair ▶New) ▶New ▶New-max-r NUnless-new-▷ (~N-pair (proj₂ (~D-dec _ _))) ▶New-max-r (newify-syn-inner (preservation-vars-ana? ana vars-syn))
  PreservationStep (WTPair x x₁ x₂ x₃ x₄ x₅ x₆ wt wt₁) (ALC ActUnwrapPairOne) = newify-ana wt
  PreservationStep (WTPair x x₁ x₂ x₃ x₄ x₅ x₆ wt wt₁) (ALC ActUnwrapPairTwo) = newify-ana wt₁



  mutual 

    PreservationSyn :  
      ∀ {Γ A e e'} ->
      (Γ U⊢ e) ->
      (Γ ⊢ A , e AU↦ e') ->   
      (Γ U⊢ e')
    PreservationSyn (WTAsc a1 (▷Pair a2) ana) (AUpMid (AMidAsc {e' = e' [ _ ]⇐ _} step)) with beyond-AL↦ step 
    ... | ◁▷C = WTAsc a1 (▷Pair a2) (PreservationAna ana step) 
    PreservationSyn (WTAp marrow consist-syn consist-ana consist-mark syn ana) (AUpMid (AMidApOne {e1' = (e-fun' ⇒ syn-fun') [ _ ]⇐ _} step)) with ▸NTArrow-dec syn-fun' 
    ... | t-in-fun' , t-out-fun' , m-fun' , marrow' with beyond-▸NTArrow (beyond-AL↦-inner step) marrow marrow' | same-mark-AL↦ step | beyond-AL↦ step
    ... | t-in-beyond , t-out-beyond , m-beyond | refl | ◁▷C = WTAp marrow' (beyond-▷ t-out-beyond consist-syn) (beyond-▷ t-in-beyond consist-ana) (beyond-▶ m-beyond consist-mark) (PreservationAna syn step) ana
    PreservationSyn (WTAp marrow consist-syn consist-ana consist-mark syn ana) (AUpMid (AMidApTwo {e2' = (e-arg' ⇒ syn-arg') [ _ ]⇐ _} step)) 
      = WTAp marrow consist-syn (beyond-▷-contra (beyond-AL↦ step) consist-ana) consist-mark syn (PreservationAna ana step)
    PreservationSyn (WTProj {s = s} x x₁ x₂ x₃) (AUpMid (AMidProj {e' = (e' ⇒ syn') [ _ ]⇐ _} step)) with ▸NTProj-dec s syn' 
    ... | _ , _ , mprod' with beyond-▸NTProj (beyond-AL↦-inner step) x mprod' | same-mark-AL↦ step | beyond-AL↦ step
    ... | t-beyond , m-beyond | refl | ◁▷C  = WTProj mprod' (beyond-▷ t-beyond x₁) (beyond-▶ m-beyond x₂) (PreservationAna x₃ step)

    PreservationAna :  
      ∀ {Γ A e e'} ->
      (Γ L⊢ e) ->
      (Γ ⊢ A , e AL↦ e') ->   
      (Γ L⊢ e')
    PreservationAna ana (ALowDone step) = PreservationStep ana step 
    PreservationAna (WTUp subsumable consist-t consist-m syn) (ALowUp {e' = e' ⇒ syn'} (AUpMid step)) = WTUp (subsumable-AM↦ subsumable step) consist-t consist-m (PreservationSyn syn (AUpMid step))
    PreservationAna (WTFun {t-asc = t-asc} marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) (ALowUp (AUpMid (AMidFun {e' = (e' ⇒ _) [ _ ]⇐ _} step))) 
      = WTFun marrow consist (beyond-▷-contra (beyond-AL↦ step) consist-ana) consist-asc consist-body  (preservation-lambda-lemma {t = t-asc} (beyond-AL↦-inner step) consist-syn) consist-all consist-m-all (PreservationAna ana step)
    PreservationAna (WTPair x x₁ x₂ x₃ x₄ x₅ x₆ wt wt₁) (ALowUp (AUpMid (AMidPairOne {e1' = (e1' ⇒ _) [ _ ]⇐ _} step))) = WTPair x (beyond-▷-contra (beyond-AL↦ step) x₁) x₂ x₃ (preservation-pair-lemma (beyond-AL↦-inner step) =▷Refl x₄) x₅ x₆ (PreservationAna wt step) wt₁
    PreservationAna (WTPair x x₁ x₂ x₃ x₄ x₅ x₆ wt wt₁) (ALowUp (AUpMid (AMidPairTwo {e2' = (e2' ⇒ _) [ _ ]⇐ _} step))) = WTPair x x₁ (beyond-▷-contra (beyond-AL↦ step) x₂) x₃ (preservation-pair-lemma =▷Refl (beyond-AL↦-inner step) x₄) x₅ x₆ wt (PreservationAna wt₁ step)
    
  PreservationProgram :    
    ∀ {A p p'} ->  
    (P⊢ p) ->   
    (A , p AP↦ p') ->        
    (P⊢ p')              
  PreservationProgram (WTProgram ana) (AStepProgram step) = WTProgram (PreservationAna ana step)    