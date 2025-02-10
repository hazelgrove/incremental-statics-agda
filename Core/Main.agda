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

  data _,_AS↦*_ : (List Action) -> Program -> Program -> Set where 
    ASStepAct : ∀{α αs p p' p''} ->
      α , p AP↦ p' -> 
      αs , p' AS↦* p'' ->
      (α ∷ αs) , p AS↦* p'' 
    ASStepUpdate : ∀{αs p p' p''} ->
      p P↦ p' -> 
      αs , p' AS↦* p'' ->
      αs , p AS↦* p'' 
    ASStepDone : ∀{p} ->
      ¬ (∃[ p' ] p P↦ p') -> 
      [] , p AS↦* p

  data _,_ABS↦*_ : (List Action) -> BareExp -> BareExp -> Set where 
    ABSStepAct : ∀{α αs e e' e''} ->
      α , e AB↦ e' -> 
      αs , e' ABS↦* e'' ->
      (α ∷ αs) , e ABS↦* e'' 
    ASStepDone : ∀{e} ->
      [] , e ABS↦* e

  main-theorem-valid : ∀ {p p' αs} ->
    WellTypedProgram p ->
    αs , p AS↦* p' ->
    (EraseProgram p') ~> p'
  main-theorem-valid wt (ASStepAct step steps) = main-theorem-valid (ActionPreservationProgram wt step) steps
  main-theorem-valid wt (ASStepUpdate step steps) = main-theorem-valid (UpdatePreservationProgram wt step) steps
  main-theorem-valid {p} wt (ASStepDone nostep) with ProgressProgram wt
  ... | Inl step = ⊥-elim (nostep step)
  ... | Inr settled = validity wt settled

  mutual 
    action-erase-low : ∀ {Γ α e e'} ->
      (Γ ⊢ α , e ALow↦ e') ->
      (α , (EraseLow e) AB↦ (EraseLow e'))
    action-erase-low (AStepLow x x₁ x₂) = {!   !}

  action-erase : ∀ {α p p'} ->
    (α , p AP↦ p') ->
    (α , (EraseProgram p) AB↦ (EraseProgram p'))
  action-erase (AStepProgram x) = {!   !}

  update-erase : ∀ {p p'} ->
    (p P↦ p') ->
    (EraseProgram p) ≡ (EraseProgram p')
  update-erase step = {!   !}

  main-bare-step-unicity : ∀ {αs e e' e''} ->
    αs , e ABS↦* e' ->
    αs , e ABS↦* e'' ->
    e' ≡ e''
  main-bare-step-unicity = {!   !}

  marking-unicity : ∀ {p p' p''} ->
    p ~> p' ->
    p ~> p'' ->
    p' ≡ p''
  marking-unicity = {!   !}

  low-actions-total : ∀{Γ} ->
    (α : Action) -> 
    (e : ExpLow) ->
    ∃[ e' ] Γ ⊢ α , e ALow↦ e'
  low-actions-total = {!   !}

  actions-total : 
    (α : Action) -> 
    (p : Program) ->
    ∃[ p' ] α , p AP↦ p'
  actions-total α p with low-actions-total α (ExpLowOfProgram p)
  ... | e' , step = {!   !}
  

  main-step-erase : ∀ {αs p p'} ->
    (αs , p AS↦* p') ->
    (αs , (EraseProgram p) ABS↦* (EraseProgram p'))
  main-step-erase (ASStepAct step steps) = ABSStepAct (action-erase step) (main-step-erase steps)
  main-step-erase (ASStepUpdate step steps) rewrite update-erase step = main-step-erase steps
  main-step-erase (ASStepDone nostep) = ASStepDone

  main-theorem-convergent : ∀ {αs p p' p''} ->
    WellTypedProgram p ->
    αs , p AS↦* p' ->
    αs , p AS↦* p'' ->
    p' ≡ p''
  main-theorem-convergent wt steps1 steps2 with main-step-erase steps1 | main-step-erase steps2
  ... | steps1' | steps2' with main-bare-step-unicity steps1' steps2' | main-theorem-valid wt steps1 | main-theorem-valid wt steps2
  ... | eq | mark1 | mark2 rewrite eq = marking-unicity mark1 mark2 

  main-theorem-total-update : 
    (p : Program) ->
    WellTypedProgram p ->
    Acc _↤P_ p ->
    ∃[ p' ] [] , p AS↦* p'
  main-theorem-total-update p wt ac with ProgressProgram wt 
  main-theorem-total-update p wt (acc ac) | Inl (p' , step) with main-theorem-total-update p' (UpdatePreservationProgram wt step) (ac step)
  main-theorem-total-update p wt ac | Inl (p' , step) | p'' , steps = p'' , ASStepUpdate step steps
  main-theorem-total-update p wt ac | Inr settled = p , (ASStepDone (λ x → UnProgressProgram wt (proj₂ x) settled))

  main-theorem-total : 
    (αs : List Action) -> 
    (p : Program) ->
    WellTypedProgram p ->
    ∃[ p' ] αs , p AS↦* p'
  main-theorem-total [] p wt = main-theorem-total-update p wt (↤P-wf _)
  main-theorem-total (α ∷ αs) p wt with actions-total α p
  ... | p' , step with main-theorem-total αs p' (ActionPreservationProgram wt step)
  ... | p'' , steps = p'' , (ASStepAct step steps)

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
   
    