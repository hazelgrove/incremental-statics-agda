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
  beyond-AL↦ (ActLow _) = ◁▷C

  beyond-AL↦-env : ∀ {Γ α ε e e' e-in e-in' m m' ana ana'} -> 
    Γ ⊢ α , e AL↦ e' -> 
    ε L⟦ e ⟧Low== (e-in [ m ]⇐ ana) ->
    ε L⟦ e' ⟧Low== (e-in' [ m' ]⇐ ana') ->
    ◁▷ ana ana' 
  beyond-AL↦-env step FillL⊙ FillL⊙ = beyond-AL↦ step
  beyond-AL↦-env step (FillLEnvLowRec _) (FillLEnvLowRec _) = ◁▷C

  beyond-AU↦ : ∀ {Γ α e e' syn syn'} -> 
    Γ ⊢ α , (e ⇒ syn) AU↦ (e' ⇒ syn') -> 
    =▷ syn syn' 
  beyond-AU↦ ActInsertConst = =▷New
  beyond-AU↦ (ActWrapFun _) = =▷Refl
  beyond-AU↦ ActWrapApOne = =▷Refl
  beyond-AU↦ ActWrapApTwo = =▷New
  beyond-AU↦ (ActInsertVar _) = =▷New
  beyond-AU↦ ActWrapAsc = =▷New
  beyond-AU↦ ActDelete = =▷New
  beyond-AU↦ (ActUnwrapFun _ _) = =▷New
  beyond-AU↦ ActUnwrapApOne = =▷New
  beyond-AU↦ ActUnwrapApTwo = =▷New
  beyond-AU↦ ActUnwrapAsc = =▷New
  
  PreservationStepAna :  
    ∀ {Γ α e e'} ->
    (Γ ⊢ e ⇐) ->
    (Γ ⊢ α , e AL↦ e') ->   
    (Γ ⊢ e' ⇐)
  PreservationStepAna (AnaSubsume x x₁ x₂ x₃) (ActLow ActInsertConst) = AnaSubsume SubsumableConst (proj₂ (~N-dec _ _)) ▶New (SynConst (▷Pair ▶Old))
  PreservationStepAna (AnaSubsume {ana-all = (ana , n)} x x₁ x₂ x₃) (ActLow (ActInsertVar {t = t} in-ctx)) with ~N-dec (■ t , New) (ana , New) 
  ... | m , ~N-pair consist' = AnaSubsume SubsumableVar (~N-pair consist') ▶New (SynVar in-ctx (▷Pair ▶Same))
  
  PreservationStepAna ana (ActLow {t = t} {n = n} (ActWrapFun {t = t'} {n = n'} vars-syn)) with ▸NTArrow-dec (t , New) | ~N-dec (t' , n') (t , New)
  ... | (t-in , New) , (t-out , New) , (m , New) , NTArrowC consist | m' , consist-syn with ~N-dec (■ THole , New) (t-in , New) | new-through-~N-left consist-syn
  ... | _ , (~N-pair consist') | _ , refl = AnaFun (NTArrowC consist) (■~N-pair (~N-pair consist')) (▷Pair ▶New) ▶New ▶New NUnless-new-▷ consist-syn ▶New (newify-ana (preservation-vars-ana?-alt ana vars-syn))
  
  PreservationStepAna ana (ActLow {t = t} ActDelete) with ~N-dec (■ THole , New) (t , New) 
  ... | _ , (~N-pair consist) = AnaSubsume SubsumableHole (~N-pair consist) ▶New (SynHole (▷Pair ▶Old))
  PreservationStepAna ana (ActLow {t = t} ActWrapAsc) with ~N-dec (■ THole , New) (t , New) 
  ... | _ , (~N-pair consist) = AnaSubsume SubsumableAsc (~N-pair consist) ▶New (SynAsc (▷Pair ▶New) (▷Pair ▶New) (newify-ana ana))
  PreservationStepAna ana (ActLow {t = t} (ActWrapApOne {t = t'} {n = n'})) with ~N-dec (t' , n') (t , New) | ▸NTArrow-dec (t' , New) 
  ... | _ , (~N-pair consist) | (t-in , New) , (t-out , New) , (m , New) , NTArrowC consist' = AnaSubsume SubsumableAp (~N-pair consist) ▶New-max-r (SynAp (NTArrowC consist') (▷Pair ▶New) (▷Pair ▶New) ▶New (newify-ana ana) (AnaSubsume SubsumableHole (~N-pair ~DVoidR) ▶Old (SynHole (▷Pair ▶Old))))
  PreservationStepAna ana (ActLow {t = t} (ActWrapApTwo {t = t'} {n = n'})) with ~N-dec (■ THole , New) (t , New) 
  ... | _ , (~N-pair consist) = AnaSubsume SubsumableAp (~N-pair consist) ▶New (SynAp (NTArrowC (DTArrowSome MArrowHole)) (▷Pair ▶Old) (▷Pair ▶Old) ▶Old (AnaSubsume SubsumableHole (~N-pair ~DVoidR) ▶Old (SynHole (▷Pair ▶Old))) (newify-ana ana))
  
  PreservationStepAna (AnaSubsume subsumable consist-t consist-m (SynAp marrow consist-syn consist-ana consist-mark syn ana)) (ActLow ActUnwrapApOne) = newify-ana syn
  PreservationStepAna (AnaSubsume subsumable consist-t consist-m (SynAp marrow consist-syn consist-ana consist-mark syn ana)) (ActLow ActUnwrapApTwo) = newify-ana ana
  PreservationStepAna (AnaSubsume subsumable consist-t consist-m (SynAsc consist-syn consist-ana ana)) (ActLow ActUnwrapAsc) = newify-ana ana
  PreservationStepAna (AnaFun marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) (ActLow (ActUnwrapFun a b)) = newify-ana (preservation-vars-unwrap a ana b)

  mutual 

    PreservationSyn :  
      ∀ {Γ α e e'} ->
      (Γ ⊢ e ⇒) ->
      (Γ ⊢ α , e AUp↦ e') ->   
      (Γ ⊢ e' ⇒)
    PreservationSyn (SynConst _) (AStepUp (FillLEnvUpRec ()) _ (FillLEnvUpRec _))
    PreservationSyn (SynHole _) (AStepUp (FillLEnvUpRec ()) _ (FillLEnvUpRec _))    
    PreservationSyn (SynVar _ _) (AStepUp (FillLEnvUpRec ()) _ (FillLEnvUpRec _))
    PreservationSyn (SynAsc consist-syn consist-ana ana) (AStepUp (FillLEnvUpRec (FillLEnvAsc fill1)) step (FillLEnvUpRec (FillLEnvAsc {e' = e' [ m' ]⇐ ana'} fill2))) with beyond-AL↦-env step fill1 fill2 
    ... | ◁▷C = SynAsc consist-syn (beyond-▷-contra ◁▷C consist-ana) (PreservationAna ana (AStepLow fill1 step fill2))
    PreservationSyn (SynAp marrow consist-syn consist-ana consist-mark syn ana) (AStepUp (FillLEnvUpRec (FillLEnvAp1 FillL⊙)) (ActLow step) (FillLEnvUpRec (FillLEnvAp1 {e' = (e-fun' ⇒ syn-fun') [ ✔ ]⇐ (□ , New)} FillL⊙))) with ▸NTArrow-dec syn-fun' 
    ... | t-in-fun' , t-out-fun' , m-fun' , marrow' with beyond-▸NTArrow (beyond-AU↦ step) marrow marrow' 
    ... | t-in-beyond , t-out-beyond , m-beyond = SynAp marrow' (beyond-▷ t-out-beyond consist-syn) (beyond-▷ t-in-beyond consist-ana) (beyond-▶ m-beyond consist-mark) (PreservationAna syn (AStepLow FillL⊙ (ActLow step) FillL⊙)) ana
    PreservationSyn (SynAp marrow consist-syn consist-ana consist-mark syn ana) (AStepUp (FillLEnvUpRec (FillLEnvAp1 (FillLEnvLowRec (FillLEnvUpRec fill1)))) (ActLow step) (FillLEnvUpRec (FillLEnvAp1 {e' = (e-fun' ⇒ syn-fun') [ ✔ ]⇐ (□ , n)} (FillLEnvLowRec (FillLEnvUpRec fill2))))) with ▸NTArrow-dec syn-fun' 
    ... | t-in-fun' , t-out-fun' , m-fun' , marrow' with beyond-▸NTArrow =▷Refl marrow marrow' 
    ... | t-in-beyond , t-out-beyond , m-beyond = SynAp marrow' (beyond-▷ t-out-beyond consist-syn) (beyond-▷ t-in-beyond consist-ana) (beyond-▶ m-beyond consist-mark) (PreservationAna syn (AStepLow (FillLEnvLowRec (FillLEnvUpRec fill1)) (ActLow step) (FillLEnvLowRec (FillLEnvUpRec fill2)))) ana
    PreservationSyn (SynAp marrow consist-syn consist-ana consist-mark syn ana) (AStepUp (FillLEnvUpRec (FillLEnvAp2 fill1)) step (FillLEnvUpRec (FillLEnvAp2 {e' = e-arg' [ m-arg' ]⇐ ana-arg'} fill2))) = SynAp marrow consist-syn (beyond-▷-contra (beyond-AL↦-env step fill1 fill2) consist-ana) consist-mark syn (PreservationAna ana (AStepLow fill1 step fill2))

    PreservationAna :  
      ∀ {Γ α e e'} ->
      (Γ ⊢ e ⇐) ->
      (Γ ⊢ α , e ALow↦ e') ->   
      (Γ ⊢ e' ⇐)
    PreservationAna ana (AStepLow FillL⊙ step FillL⊙) = PreservationStepAna ana step
    PreservationAna (AnaSubsume subsumable consist-t consist-m syn) (AStepLow (FillLEnvLowRec (FillLEnvUpRec fill1)) (ActLow step) (FillLEnvLowRec (FillLEnvUpRec fill2))) = AnaSubsume (l-env-subsumable fill1 fill2 subsumable) consist-t consist-m (PreservationSyn syn (AStepUp (FillLEnvUpRec fill1) (ActLow step) (FillLEnvUpRec fill2)))
    PreservationAna (AnaFun {t-asc = t-asc} marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) (AStepLow (FillLEnvLowRec (FillLEnvUpRec (FillLEnvFun FillL⊙))) (ActLow step) (FillLEnvLowRec (FillLEnvUpRec (FillLEnvFun {e' = (e-body' ⇒ syn-body') [ m-body' ]⇐ .(_ , New)} FillL⊙)))) = AnaFun marrow consist (beyond-▷-contra ◁▷C consist-ana) consist-asc consist-body (preservation-lambda-lemma-3 {t = t-asc} (beyond-AU↦ step) consist-syn) consist-all consist-m-all (newify-ana (PreservationAna ana (AStepLow FillL⊙ (ActLow step) FillL⊙)))
    PreservationAna (AnaFun {t-asc = t-asc} marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) (AStepLow (FillLEnvLowRec (FillLEnvUpRec (FillLEnvFun (FillLEnvLowRec (FillLEnvUpRec fill1))))) step (FillLEnvLowRec (FillLEnvUpRec (FillLEnvFun {e' = (e-body' ⇒ syn-body') [ m-body' ]⇐ ana-body'} (FillLEnvLowRec (FillLEnvUpRec fill2)))))) 
      = AnaFun marrow consist consist-ana consist-asc consist-body (preservation-lambda-lemma-3 {t = t-asc} =▷Refl consist-syn) consist-all consist-m-all (PreservationAna ana (AStepLow (FillLEnvLowRec (FillLEnvUpRec fill1)) step (FillLEnvLowRec (FillLEnvUpRec fill2))))

  PreservationProgram :   
    ∀ {α p p'} ->
    (WellTypedProgram p) -> 
    (α , p AP↦ p') ->   
    (WellTypedProgram p')      
  PreservationProgram (WTProg ana) (AStepProgram step) = WTProg (PreservationAna ana step)  