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
  beyond-αU↦ (ActWrapFun _) = =▷Refl
  beyond-αU↦ ActWrapApOne = =▷Refl
  beyond-αU↦ ActWrapApTwo = =▷New
  beyond-αU↦ (ActInsertVar _) = =▷New
  beyond-αU↦ ActWrapAsc = =▷New
  beyond-αU↦ ActDelete = =▷New
  beyond-αU↦ (ActUnwrapFun _ _) = =▷New
  beyond-αU↦ ActUnwrapApOne = =▷New
  beyond-αU↦ ActUnwrapApTwo = =▷New
  beyond-αU↦ ActUnwrapAsc = =▷New

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
    (Γ ⊢ α , e αL↦ e') ->   
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
      ∀ {Γ A e e'} ->
      (Γ ⊢ e ⇒) ->
      (Γ ⊢ A , e AU↦ e') ->   
      (Γ ⊢ e' ⇒)
    PreservationSyn (SynAsc a1 (▷Pair a2) ana) (AUpMid (AMidAsc {e' = e' [ _ ]⇐ _} step)) with beyond-AL↦ step 
    ... | ◁▷C = SynAsc a1 (▷Pair a2) (PreservationAna ana step) 
    PreservationSyn (SynAp marrow consist-syn consist-ana consist-mark syn ana) (AUpMid (AMidApOne {e1' = (e-fun' ⇒ syn-fun') [ _ ]⇐ _} step)) with ▸NTArrow-dec syn-fun' 
    ... | t-in-fun' , t-out-fun' , m-fun' , marrow' with beyond-▸NTArrow (beyond-AL↦-inner step) marrow marrow' | same-mark-AL↦ step | beyond-AL↦ step
    ... | t-in-beyond , t-out-beyond , m-beyond | refl | ◁▷C = SynAp marrow' (beyond-▷ t-out-beyond consist-syn) (beyond-▷ t-in-beyond consist-ana) (beyond-▶ m-beyond consist-mark) (PreservationAna syn step) ana
    PreservationSyn (SynAp marrow consist-syn consist-ana consist-mark syn ana) (AUpMid (AMidApTwo {e2' = (e-arg' ⇒ syn-arg') [ _ ]⇐ _} step)) 
      = SynAp marrow consist-syn (beyond-▷-contra (beyond-AL↦ step) consist-ana) consist-mark syn (PreservationAna ana step)

    PreservationAna :  
      ∀ {Γ A e e'} ->
      (Γ ⊢ e ⇐) ->
      (Γ ⊢ A , e AL↦ e') ->   
      (Γ ⊢ e' ⇐)
    PreservationAna ana (ALowDone step) = PreservationStep ana step 
    PreservationAna (AnaSubsume subsumable consist-t consist-m syn) (ALowUp {e' = e' ⇒ syn'} (AUpMid step)) = AnaSubsume (subsumable-AM↦ subsumable step) consist-t consist-m (PreservationSyn syn (AUpMid step))
    PreservationAna (AnaFun {t-asc = t-asc} marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) (ALowUp (AUpMid (AMidFun {e' = (e' ⇒ _) [ _ ]⇐ _} step))) 
      = AnaFun marrow consist (beyond-▷-contra (beyond-AL↦ step) consist-ana) consist-asc consist-body  (preservation-lambda-lemma-3 {t = t-asc} (beyond-AL↦-inner step) consist-syn) consist-all consist-m-all (PreservationAna ana step)

  PreservationProgram :   
    ∀ {A p p'} ->  
    (WellTypedProgram p) ->  
    (A , p AP↦ p') ->      
    (WellTypedProgram p')             
  PreservationProgram (WTProg ana) (AStepProgram step) = WTProg (PreservationAna ana step)    