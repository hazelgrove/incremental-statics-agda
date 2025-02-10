open import Data.Nat hiding (_+_)
open import Data.Unit 
open import Data.Empty 
open import Data.List 
open import Data.Bool hiding (_<_; _≟_)
open import Data.Sum renaming (_⊎_ to _+_; inj₁ to Inl ; inj₂ to Inr) hiding (map)
open import Data.Product hiding (map)
open import Induction.WellFounded 
open import Relation.Nullary 
open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Prelude

open import Core.Core
open import Core.Update
open import Core.WellTyped
open import Core.Validity
open import Core.Actions
open import Core.UpdatePreservation renaming (PreservationProgram to UpdatePreservationProgram)
open import Core.ActionPreservation renaming (PreservationProgram to ActionPreservationProgram)
open import Core.Progress
open import Core.Marking
open import Core.Termination

module Core.Main where

  data _,_AP↦*_ : (List LocalizedAction) -> Program -> Program -> Set where 
    AP*StepAct : ∀{α αs p p' p''} ->
      α , p AP↦ p' -> 
      αs , p' AP↦* p'' ->
      (α ∷ αs) , p AP↦* p'' 
    AP*StepUpdate : ∀{αs p p' p''} ->
      p P↦ p' -> 
      αs , p' AP↦* p'' ->
      αs , p AP↦* p'' 
    AP*StepDone : ∀{p} ->
      ¬ (∃[ p' ] p P↦ p') -> 
      [] , p AP↦* p

  data _,_AB↦*_ : (List LocalizedAction) -> BareExp -> BareExp -> Set where 
    AB*StepAct : ∀{α αs e e' e''} ->
      α , e AB↦ e' -> 
      αs , e' AB↦* e'' ->
      (α ∷ αs) , e AB↦* e'' 
    AB*StepDone : ∀{e} ->
      [] , e AB↦* e

  main-theorem-valid : ∀ {p p' αs} ->
    WellTypedProgram p ->
    αs , p AP↦* p' ->
    (EraseProgram p') ~> p'
  main-theorem-valid wt (AP*StepAct step steps) = main-theorem-valid (ActionPreservationProgram wt step) steps
  main-theorem-valid wt (AP*StepUpdate step steps) = main-theorem-valid (UpdatePreservationProgram wt step) steps
  main-theorem-valid {p} wt (AP*StepDone nostep) with ProgressProgram wt
  ... | Inl step = ⊥-elim (nostep step)
  ... | Inr settled = validity wt settled

  mutual 
    action-erase-low : ∀ {Γ α e e'} ->
      (Γ ⊢ α , e AL↦ e') ->
      (α , (EraseLow e) AB↦ (EraseLow e'))
    action-erase-low step = {!   !}

  action-erase : ∀ {α p p'} ->
    (α , p AP↦ p') ->
    (α , (EraseProgram p) AB↦ (EraseProgram p'))
  action-erase (AStepProgram x) = {!   !}

  update-erase : ∀ {p p'} ->
    (p P↦ p') ->
    (EraseProgram p) ≡ (EraseProgram p')
  update-erase step = {!   !}

  
  -- action-unicity : 
  --   (α : Action) -> 
  --   (p : Program) ->
  --   ∃[ p' ] α , p AP↦ p'
  -- actions-total α p with low-actions-total α (ExpLowOfProgram p)
  -- ... | e' , step = {!   !}
  

  main-bare-step-unicity : ∀ {αs e e' e''} ->
    αs , e AB↦* e' ->
    αs , e AB↦* e'' ->
    e' ≡ e''
  main-bare-step-unicity = {!   !}

  main-step-erase : ∀ {αs p p'} ->
    (αs , p AP↦* p') ->
    (αs , (EraseProgram p) AB↦* (EraseProgram p'))
  main-step-erase (AP*StepAct step steps) = AB*StepAct (action-erase step) (main-step-erase steps)
  main-step-erase (AP*StepUpdate step steps) rewrite update-erase step = main-step-erase steps
  main-step-erase (AP*StepDone nostep) = AB*StepDone

  main-theorem-convergent : ∀ {αs p p' p''} ->
    WellTypedProgram p ->
    αs , p AP↦* p' ->
    αs , p AP↦* p'' ->
    p' ≡ p''
  main-theorem-convergent wt steps1 steps2 with main-step-erase steps1 | main-step-erase steps2
  ... | steps1' | steps2' with main-bare-step-unicity steps1' steps2' | main-theorem-valid wt steps1 | main-theorem-valid wt steps2
  ... | eq | mark1 | mark2 rewrite eq = marking-unicity mark1 mark2 

  main-theorem-termination' : 
    (p : ℕ -> Program) ->
    (Acc _↤P_ (p 0)) ->
    ((n : ℕ) -> (p n) P↦ (p (suc n))) ->
    ⊥
  main-theorem-termination' p (acc ac) steps = main-theorem-termination' (λ n -> (p (suc n))) (ac (steps 0)) λ n -> (steps (suc n))

  main-theorem-termination : 
    (p : ℕ -> Program) ->
    ((n : ℕ) -> (p n) P↦ (p (suc n))) ->
    ⊥
  main-theorem-termination p = main-theorem-termination' p (↤P-wf (p 0))
   
    