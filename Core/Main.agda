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
    ASStepDone : ∀{αs p} ->
      ¬ (∃[ p' ] p P↦ p') -> 
      αs , p AS↦* p

  main-theorem-valid : ∀ {p p' αs} ->
    WellTypedProgram p ->
    αs , p AS↦* p' ->
    (EraseProgram p') ~> p'
  main-theorem-valid wt (ASStepAct step steps) = main-theorem-valid (ActionPreservationProgram wt step) steps
  main-theorem-valid wt (ASStepUpdate step steps) = main-theorem-valid (UpdatePreservationProgram wt step) steps
  main-theorem-valid {p} wt (ASStepDone nostep) with ProgressProgram wt
  ... | Inl step = ⊥-elim (nostep step)
  ... | Inr settled = validity wt settled

  main-theorem-convergent : ∀ {αs p p' p''} ->
    αs , p AS↦* p' ->
    αs , p AS↦* p'' ->
    p' ≡ p''
  main-theorem-convergent = {!   !}

  main-theorem-total : 
    (αs : List Action) -> 
    (p : Program) ->
    ∃[ p' ] αs , p AS↦* p'
  main-theorem-total = {!   !}

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
 
    