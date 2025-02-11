
open import Data.Empty 
open import Data.Nat hiding (_+_)
open import Data.List 
open import Data.Sum renaming (_⊎_ to _+_; inj₁ to Inl ; inj₂ to Inr) hiding (map)
open import Data.Product
open import Relation.Nullary 
open import Relation.Binary.PropositionalEquality 
open import Induction.WellFounded 

open import Prelude
open import Core.Core
open import Core.Marking
open import Core.WellTyped
open import Core.Validity
open import Core.Update
open import Core.Actions
open import Core.UpdatePreservation renaming (PreservationProgram to UpdatePreservationProgram)
open import Core.ActionPreservation renaming (PreservationProgram to ActionPreservationProgram)
open import Core.MarkingUnicity
open import Core.ActionUnicity
open import Core.UpdateErasure
open import Core.ActionErasure
open import Core.Progress
open import Core.Termination

module Core.Main where

  data _,_AB↦*_ : (List LocalizedAction) -> BareExp -> BareExp -> Set where 
    AB*StepAct : ∀{A As e e' e''} ->
      A , e AB↦ e' -> 
      As , e' AB↦* e'' ->
      (A ∷ As) , e AB↦* e'' 
    AB*StepDone : ∀{e} ->
      [] , e AB↦* e

  data _,_AP↦*_ : (List LocalizedAction) -> Program -> Program -> Set where 
    AP*StepAct : ∀{A As p p' p''} ->
      A , p AP↦ p' -> 
      As , p' AP↦* p'' ->
      (A ∷ As) , p AP↦* p'' 
    AP*StepUpdate : ∀{As p p' p''} ->
      p P↦ p' -> 
      As , p' AP↦* p'' ->
      As , p AP↦* p'' 
    AP*StepDone : ∀{p} ->
      ¬ (∃[ p' ] p P↦ p') -> 
      [] , p AP↦* p

  AB↦*-unicity : ∀ {As e e' e''} ->
    As , e AB↦* e' ->
    As , e AB↦* e'' ->
    e' ≡ e''
  AB↦*-unicity AB*StepDone AB*StepDone = refl
  AB↦*-unicity (AB*StepAct step1 steps1) (AB*StepAct step2 steps2) 
    rewrite AB↦-unicity step1 step2 
    rewrite AB↦*-unicity steps1 steps2 = refl

  AP↦*-erase : ∀ {As p p'} ->
    (As , p AP↦* p') ->
    (As , (P◇ p) AB↦* (P◇ p'))
  AP↦*-erase (AP*StepAct step steps) = AB*StepAct (AP↦-erase step) (AP↦*-erase steps)
  AP↦*-erase (AP*StepUpdate step steps) rewrite P↦-erase step = AP↦*-erase steps
  AP↦*-erase (AP*StepDone nostep) = AB*StepDone

  main-theorem-valid : ∀ {p p' As} ->
    P⊢ p ->
    As , p AP↦* p' ->
    (P◇ p') ~> p'
  main-theorem-valid wt (AP*StepAct step steps) = main-theorem-valid (ActionPreservationProgram wt step) steps
  main-theorem-valid wt (AP*StepUpdate step steps) = main-theorem-valid (UpdatePreservationProgram wt step) steps
  main-theorem-valid {p} wt (AP*StepDone nostep) with ProgressProgram wt
  ... | Inl step = ⊥-elim (nostep step)
  ... | Inr settled = validity wt settled

  main-theorem-convergent : ∀ {As p p' p''} ->
    P⊢ p ->
    As , p AP↦* p' ->
    As , p AP↦* p'' ->
    p' ≡ p''
  main-theorem-convergent wt steps1 steps2 with AP↦*-erase steps1 | AP↦*-erase steps2
  ... | steps1' | steps2' with AB↦*-unicity steps1' steps2' | main-theorem-valid wt steps1 | main-theorem-valid wt steps2
  ... | eq | mark1 | mark2 rewrite eq = marking-unicity mark1 mark2 

  main-theorem-termination : 
    (p : ℕ -> Program) ->
    ((n : ℕ) -> (p n) P↦ (p (suc n))) ->
    ⊥
  main-theorem-termination p = helper p (↤P-wf (p 0))
    where 
    helper : 
      (p : ℕ -> Program) ->
      (Acc _↤P_ (p 0)) ->
      ((n : ℕ) -> (p n) P↦ (p (suc n))) -> ⊥
    helper p (acc ac) steps = helper (λ n -> (p (suc n))) (ac (steps 0)) λ n -> (steps (suc n))
    
  InitProgram : Program 
  InitProgram = Root (EHole ⇒ (■ THole , Old)) Old
 
  InitWellTyped : P⊢ InitProgram 
  InitWellTyped = WTProgram (WTUp SubsumableHole (~N-pair ~DVoidR) ▶Old (WTHole (▷Pair ▶Old)))

    