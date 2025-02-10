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
open import Core.Actions
open import Core.Lemmas-Preservation

module Core.ActionPreservation where

  beyond-AL↦ : ∀ {Γ α e e' m m' ana ana'} -> 
    Γ ⊢ α , (e [ m ]⇐ ana) AL↦ (e' [ m' ]⇐ ana') -> 
    ◁▷ ana ana' 
  beyond-AL↦ (ALC _) = ◁▷C

  beyond-ALow↦ : ∀ {Γ α e e' m m' ana ana'} -> 
    Γ ⊢ α , (e [ m ]⇐ ana) ALow↦ (e' [ m' ]⇐ ana') -> 
    ◁▷ ana ana' 
  beyond-ALow↦ (ALowDone (ALC _)) = ◁▷C
  beyond-ALow↦ {ana = (_ , _)} (ALowUp x) = ◁▷C

  same-mark-ALow↦ : ∀ {Γ α e e' m m' ana ana'} -> 
    Γ ⊢ α , (e [ m ]⇐ ana) ALow↦ (e' [ m' ]⇐ ana') -> 
    m ≡ m'
  same-mark-ALow↦ (ALowDone (ALC _)) = refl
  same-mark-ALow↦ {ana = (_ , _)} (ALowUp x) = refl

  -- beyond-AL↦-env : ∀ {Γ α ε e e' e-in e-in' m m' ana ana'} -> 
  --   Γ ⊢ α , e AL↦ e' -> 
  --   ε L⟦ e ⟧Low== (e-in [ m ]⇐ ana) ->
  --   ε L⟦ e' ⟧Low== (e-in' [ m' ]⇐ ana') ->
  --   ◁▷ ana ana' 
  -- beyond-AL↦-env step FillL⊙ FillL⊙ = beyond-AL↦ step
  -- beyond-AL↦-env step (FillLEnvLowRec _) (FillLEnvLowRec _) = ◁▷C

  beyond-A↦ : ∀ {Γ α e e' syn syn'} -> 
    Γ ⊢ α , (e ⇒ syn) A↦ (e' ⇒ syn') -> 
    =▷ syn syn' 
  beyond-A↦ ActInsertConst = =▷New
  beyond-A↦ (ActWrapFun _) = =▷Refl
  beyond-A↦ ActWrapApOne = =▷Refl
  beyond-A↦ ActWrapApTwo = =▷New
  beyond-A↦ (ActInsertVar _) = =▷New
  beyond-A↦ ActWrapAsc = =▷New
  beyond-A↦ ActDelete = =▷New
  beyond-A↦ (ActUnwrapFun _ _) = =▷New
  beyond-A↦ ActUnwrapApOne = =▷New
  beyond-A↦ ActUnwrapApTwo = =▷New
  beyond-A↦ ActUnwrapAsc = =▷New

  beyond-AUp↦ : ∀ {Γ α e e' syn syn'} -> 
    Γ ⊢ α , (e ⇒ syn) AUp↦ (e' ⇒ syn') -> 
    =▷ syn syn' 
  beyond-AUp↦ (AUpMid step) = =▷Refl

  beyond-AL↦-inner : ∀ {Γ α e e' syn syn' m m' ana ana'} -> 
    Γ ⊢ α , ((e ⇒ syn) [ m ]⇐ ana) AL↦ ((e' ⇒ syn') [ m' ]⇐ ana') -> 
    =▷ syn syn' 
  beyond-AL↦-inner (ALC step) = beyond-A↦ step

  beyond-ALow↦-inner : ∀ {Γ α e e' syn syn' m m' ana ana'} -> 
    Γ ⊢ α , ((e ⇒ syn) [ m ]⇐ ana) ALow↦ ((e' ⇒ syn') [ m' ]⇐ ana') -> 
    =▷ syn syn' 
  beyond-ALow↦-inner (ALowDone step) = beyond-AL↦-inner step
  beyond-ALow↦-inner (ALowUp step) = beyond-AUp↦ step


  subsumable-AMid↦ : ∀{Γ α e e'} ->
    SubsumableMid e ->
    Γ ⊢ α , e AMid↦ e' ->
    SubsumableMid e'
  subsumable-AMid↦ () (AMidFun x)
  subsumable-AMid↦ SubsumableAsc (AMidAsc x) = SubsumableAsc
  subsumable-AMid↦ SubsumableAp (AMidApOne x) = SubsumableAp
  subsumable-AMid↦ SubsumableAp (AMidApTwo x) = SubsumableAp

  -- PreservationStepAna :  
  --   ∀ {Γ α e e'} ->
  --   (Γ ⊢ e ⇐) ->
  --   (Γ ⊢ α , e AL↦ e') ->   
  --   (Γ ⊢ e' ⇐)
  -- PreservationStepAna (AnaSubsume x x₁ x₂ x₃) (ActLow ActInsertConst) = AnaSubsume SubsumableConst (proj₂ (~N-dec _ _)) ▶New (SynConst (▷Pair ▶Old))
  -- PreservationStepAna (AnaSubsume {ana-all = (ana , n)} x x₁ x₂ x₃) (ActLow (ActInsertVar {t = t} in-ctx)) with ~N-dec (■ t , New) (ana , New) 
  -- ... | m , ~N-pair consist' = AnaSubsume SubsumableVar (~N-pair consist') ▶New (SynVar in-ctx (▷Pair ▶Same))
  
  -- PreservationStepAna ana (ActLow {t = t} {n = n} (ActWrapFun {t = t'} {n = n'} vars-syn)) with ▸NTArrow-dec (t , New) | ~N-dec (t' , n') (t , New)
  -- ... | (t-in , New) , (t-out , New) , (m , New) , NTArrowC consist | m' , consist-syn with ~N-dec (■ THole , New) (t-in , New) | new-through-~N-left consist-syn
  -- ... | _ , (~N-pair consist') | _ , refl = AnaFun (NTArrowC consist) (■~N-pair (~N-pair consist')) (▷Pair ▶New) ▶New ▶New NUnless-new-▷ consist-syn ▶New (newify-ana (preservation-vars-ana?-alt ana vars-syn))
  
  -- PreservationStepAna ana (ActLow {t = t} ActDelete) with ~N-dec (■ THole , New) (t , New) 
  -- ... | _ , (~N-pair consist) = AnaSubsume SubsumableHole (~N-pair consist) ▶New (SynHole (▷Pair ▶Old))
  -- PreservationStepAna ana (ActLow {t = t} ActWrapAsc) with ~N-dec (■ THole , New) (t , New) 
  -- ... | _ , (~N-pair consist) = AnaSubsume SubsumableAsc (~N-pair consist) ▶New (SynAsc (▷Pair ▶New) (▷Pair ▶New) (newify-ana ana))
  -- PreservationStepAna ana (ActLow {t = t} (ActWrapApOne {t = t'} {n = n'})) with ~N-dec (t' , n') (t , New) | ▸NTArrow-dec (t' , New) 
  -- ... | _ , (~N-pair consist) | (t-in , New) , (t-out , New) , (m , New) , NTArrowC consist' = AnaSubsume SubsumableAp (~N-pair consist) ▶New-max-r (SynAp (NTArrowC consist') (▷Pair ▶New) (▷Pair ▶New) ▶New (newify-ana ana) (AnaSubsume SubsumableHole (~N-pair ~DVoidR) ▶Old (SynHole (▷Pair ▶Old))))
  -- PreservationStepAna ana (ActLow {t = t} (ActWrapApTwo {t = t'} {n = n'})) with ~N-dec (■ THole , New) (t , New) 
  -- ... | _ , (~N-pair consist) = AnaSubsume SubsumableAp (~N-pair consist) ▶New (SynAp (NTArrowC (DTArrowSome MArrowHole)) (▷Pair ▶Old) (▷Pair ▶Old) ▶Old (AnaSubsume SubsumableHole (~N-pair ~DVoidR) ▶Old (SynHole (▷Pair ▶Old))) (newify-ana ana))
  
  -- PreservationStepAna (AnaSubsume subsumable consist-t consist-m (SynAp marrow consist-syn consist-ana consist-mark syn ana)) (ActLow ActUnwrapApOne) = newify-ana syn
  -- PreservationStepAna (AnaSubsume subsumable consist-t consist-m (SynAp marrow consist-syn consist-ana consist-mark syn ana)) (ActLow ActUnwrapApTwo) = newify-ana ana
  -- PreservationStepAna (AnaSubsume subsumable consist-t consist-m (SynAsc consist-syn consist-ana ana)) (ActLow ActUnwrapAsc) = newify-ana ana
  -- PreservationStepAna (AnaFun marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) (ActLow (ActUnwrapFun a b)) = newify-ana (preservation-vars-unwrap a ana b)

  SynSubsume :  
    ∀ {Γ e t} ->
    (Γ ⊢ (e ⇒ (t , New)) ⇒) ->
    Subsumable (e ⇒ (t , New))
  SynSubsume (SynConst x) = SubsumableConst
  SynSubsume (SynHole x) = SubsumableHole
  SynSubsume (SynAp x x₁ x₂ x₃ x₄ x₅) = SubsumableAp
  SynSubsume (SynVar x x₁) = SubsumableVar
  SynSubsume (SynAsc x x₁ x₂) = SubsumableAsc
    
  WrapSubsume :  
    ∀ {Γ e t m ana} ->
    (Γ ⊢ (e ⇒ (t , New)) ⇒) ->
    (Γ ⊢ (e ⇒ (t , New)) [ m ]⇐ ana ⇐)
  WrapSubsume {t = t} {ana = ana} syn with ~N-dec (t , New) ana
  ... | _ , ~N-pair x = AnaSubsume (SynSubsume syn) (~N-pair x) ▶New syn

  PreservationStep :  
    ∀ {Γ α e e'} ->
    (Γ ⊢ e ⇐) ->
    (Γ ⊢ α , e AL↦ e') ->   
    (Γ ⊢ e' ⇐)
  PreservationStep ana (ALC ActDelete) = WrapSubsume (SynHole (▷Pair ▶Old))
  PreservationStep ana (ALC ActInsertConst) = WrapSubsume (SynConst (▷Pair ▶Old))
  PreservationStep ana (ALC (ActInsertVar in-ctx)) = WrapSubsume (SynVar in-ctx (▷Pair ▶Same))
  PreservationStep ana (ALC ActWrapAsc) = WrapSubsume (SynAsc (▷Pair ▶New) (▷Pair ▶New) (newify-ana ana))
  PreservationStep ana (ALC ActWrapApTwo) = WrapSubsume (SynAp (NTArrowC (DTArrowSome MArrowHole)) (▷Pair ▶Old) (▷Pair ▶Old) ▶Old (AnaSubsume SubsumableHole (~N-pair ~DVoidR) ▶Old (SynHole (▷Pair ▶Old))) (newify-ana ana))
  PreservationStep ana (ALC {t = t} {n = n} (ActWrapFun {t = t'} {n = n'} vars-syn)) with ▸NTArrow-dec (t , New) | ~N-dec (t' , n') (t , New)
  ... | (t-in , New) , (t-out , New) , (m , New) , NTArrowC consist | m' , consist-syn with ~N-dec (■ THole , New) (t-in , New) | new-through-~N-left consist-syn
  ... | _ , (~N-pair consist') | _ , refl = AnaFun (NTArrowC consist) (■~N-pair (~N-pair consist')) (▷Pair ▶New) ▶New ▶New NUnless-new-▷ consist-syn ▶New (newify-ana (preservation-vars-ana?-alt ana vars-syn))
  PreservationStep ana (ALC {t = t} (ActWrapApOne {t = t'} {n = n'})) with ~N-dec (t' , n') (t , New) | ▸NTArrow-dec (t' , New) 
  ... | _ , (~N-pair consist) | (t-in , New) , (t-out , New) , (m , New) , NTArrowC consist' = AnaSubsume SubsumableAp (~N-pair consist) ▶New-max-r (SynAp (NTArrowC consist') (▷Pair ▶New) (▷Pair ▶New) ▶New (newify-ana ana) (AnaSubsume SubsumableHole (~N-pair ~DVoidR) ▶Old (SynHole (▷Pair ▶Old))))

  PreservationStep (AnaSubsume subsumable consist-t consist-m (SynAsc consist-syn consist-ana ana)) (ALC ActUnwrapAsc) = newify-ana ana
  PreservationStep (AnaSubsume subsumable consist-t consist-m (SynAp marrow consist-syn consist-ana consist-mark syn ana)) (ALC ActUnwrapApOne) = newify-ana syn
  PreservationStep (AnaSubsume subsumable consist-t consist-m (SynAp marrow consist-syn consist-ana consist-mark syn ana)) (ALC ActUnwrapApTwo) = newify-ana ana
  PreservationStep (AnaFun marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) (ALC (ActUnwrapFun in-ctx vars-syn)) = newify-ana (preservation-vars-unwrap in-ctx ana vars-syn)

  mutual 

    PreservationSyn :  
      ∀ {Γ α e e'} ->
      (Γ ⊢ e ⇒) ->
      (Γ ⊢ α , e AUp↦ e') ->   
      (Γ ⊢ e' ⇒)
    PreservationSyn (SynAsc a1 (▷Pair a2) ana) (AUpMid (AMidAsc {e' = e' [ _ ]⇐ _} step)) with beyond-ALow↦ step 
    ... | ◁▷C = SynAsc a1 (▷Pair a2) (PreservationAna ana step) 
    PreservationSyn (SynAp marrow consist-syn consist-ana consist-mark syn ana) (AUpMid (AMidApOne {e1' = (e-fun' ⇒ syn-fun') [ _ ]⇐ _} step)) with ▸NTArrow-dec syn-fun' 
    ... | t-in-fun' , t-out-fun' , m-fun' , marrow' with beyond-▸NTArrow (beyond-ALow↦-inner step) marrow marrow' | same-mark-ALow↦ step | beyond-ALow↦ step
    ... | t-in-beyond , t-out-beyond , m-beyond | refl | ◁▷C = SynAp marrow' (beyond-▷ t-out-beyond consist-syn) (beyond-▷ t-in-beyond consist-ana) (beyond-▶ m-beyond consist-mark) (PreservationAna syn step) ana
    PreservationSyn (SynAp marrow consist-syn consist-ana consist-mark syn ana) (AUpMid (AMidApTwo {e2' = (e-arg' ⇒ syn-arg') [ _ ]⇐ _} step)) 
      = SynAp marrow consist-syn (beyond-▷-contra (beyond-ALow↦ step) consist-ana) consist-mark syn (PreservationAna ana step)

    PreservationAna :  
      ∀ {Γ α e e'} ->
      (Γ ⊢ e ⇐) ->
      (Γ ⊢ α , e ALow↦ e') ->   
      (Γ ⊢ e' ⇐)
    PreservationAna ana (ALowDone step) = PreservationStep ana step 
    PreservationAna (AnaSubsume subsumable consist-t consist-m syn) (ALowUp {e' = e' ⇒ syn'} (AUpMid step)) = AnaSubsume (subsumable-AMid↦ subsumable step) consist-t consist-m (PreservationSyn syn (AUpMid step))
    PreservationAna (AnaFun {t-asc = t-asc} marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) (ALowUp (AUpMid (AMidFun {e' = (e' ⇒ _) [ _ ]⇐ _} step))) 
      = AnaFun marrow consist (beyond-▷-contra (beyond-ALow↦ step) consist-ana) consist-asc consist-body  (preservation-lambda-lemma-3 {t = t-asc} (beyond-ALow↦-inner step) consist-syn) consist-all consist-m-all (PreservationAna ana step)

  PreservationProgram :   
    ∀ {α p p'} ->  
    (WellTypedProgram p) ->  
    (α , p AP↦ p') ->      
    (WellTypedProgram p')             
  PreservationProgram (WTProg ana) (AStepProgram step) = WTProg (PreservationAna ana step)    