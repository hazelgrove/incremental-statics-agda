open import Data.Nat hiding (_+_)
open import Data.Unit 
open import Data.Empty 
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

  data FinSet : Set -> Set where 
  -- FinSet = {!   !} 

  -- [SetDecomp a S S'] holds when S' = S U {a}
  SetDecomp : ∀ {A} -> A -> (FinSet A) -> (FinSet A) -> Set 
  SetDecomp = {!   !}

  -- holds when empty
  SetEmpty : ∀ {A} -> (FinSet A) -> Set 
  SetEmpty = {!   !}

  _Up̸↦ : ExpUp -> Set 
  _Up̸↦ = {!   !}

  data Converge : ExpUp -> (FinSet Action) -> ExpUp -> Set where 
    ConvergeAct : ∀ {a S S' e1 e2 e3} ->
      (SetDecomp a S S') -> (a , e1 A↦ e2) -> (Converge e2 S e3) -> (Converge e1 S' e3)
    ConvergeUpdate : ∀ {S e1 e2 e3} ->
      (e1 Up↦ e2) -> (Converge e2 S e3) -> (Converge e1 S e3)
    ConvergeDone : ∀ {S e} ->
      (e Up̸↦) -> (SetEmpty S) -> (Converge e S e)

  
  ApplyActionsBare : BareExp -> (FinSet Action) -> BareExp -> Set 
  ApplyActionsBare = {!   !}


  main-theorem-valid : ∀ {e1 e2 b1 b2 S} ->
    Converge e1 S e2 ->
    BarrenExp e1 b1 ->
    ApplyActionsBare b1 S b2 -> 
    ∃[ τ ] ∅ ⊢ b2 ~> e2 ⇒ τ
  main-theorem-valid = {!   !}

  main-theorem-convergent : ∀ {e e1 e2 S} ->
    Converge e S e1 ->
    Converge e S e2 ->
    e1 ≡ e2
  main-theorem-convergent = {!   !}
    