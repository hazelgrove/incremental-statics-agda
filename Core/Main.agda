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
  
  data _,_AS↦_ : (List Action) -> Program -> Program -> Set where 
    ASStepAct : ∀{α αs p p' p''} ->
      α , p AP↦ p' -> 
      αs , p' AS↦ p'' ->
      (α ∷ αs) , p AS↦ p'' 
    ASStepUpdate : ∀{αs p p' p''} ->
      p P↦ p' -> 
      αs , p' AS↦ p'' ->
      αs , p AS↦ p'' 
    ASStepDone : ∀{αs p} ->
      ¬ (∃[ p' ] p P↦ p') -> 
      αs , p AS↦ p


  -- main-theorem-valid : ∀ {e1 e2 b1 b2 S} ->
  --   αs , p AS↦ p' ->
  --   ∃[ τ ] ∅ ⊢ b2 ~> e2 ⇒ τ
  -- main-theorem-valid = {!   !}

  -- main-theorem-convergent : ∀ {e e1 e2 S} ->
  --   Converge e S e1 ->
  --   Converge e S e2 ->
  --   e1 ≡ e2
  -- main-theorem-convergent = {!   !}
    