open import Data.Nat hiding (_+_)
open import Data.Unit 
open import Data.Empty 
open import Data.List 
open import Data.Bool hiding (_<_; _≟_)
open import Data.Sum renaming (_⊎_ to _+_; inj₁ to Inl ; inj₂ to Inr) hiding (map)
open import Data.Product hiding (map)
open import Relation.Nullary 
open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Prelude

open import Core.Core
open import Core.Update
open import Core.Actions
open import Core.Marking

module Core.Main where

  -- _Up̸↦ : ExpUp -> Set 
  -- _Up̸↦ = {!   !}

  -- data Converge : ExpUp -> (FinSet Action) -> ExpUp -> Set where 
  --   ConvergeAct : ∀ {a S S' e1 e2 e3} ->
  --     (SetDecomp a S S') -> (a , e1 A↦ e2) -> (Converge e2 S e3) -> (Converge e1 S' e3)
  --   ConvergeUpdate : ∀ {S e1 e2 e3} ->
  --     (e1 Up↦ e2) -> (Converge e2 S e3) -> (Converge e1 S e3)
  --   ConvergeDone : ∀ {S e} ->
  --     (e Up̸↦) -> (SetEmpty S) -> (Converge e S e)
  
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


  main-theorem-valid : ∀ {αs p p'} ->
    αs , p AS↦* p' ->
    (EraseProgram p') ~> p'
  main-theorem-valid = {!   !}

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

  main-theorem-termination : 
    (f : ℕ -> Program) ->
    ((n : ℕ) -> (f n) P↦ (f (suc n))) ->
    ⊥
  main-theorem-termination = {!   !}

    