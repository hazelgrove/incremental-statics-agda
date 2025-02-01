open import Data.Nat hiding (_+_)
open import Data.Unit 
open import Data.Bool hiding (_<_; _≟_)
open import Data.Sum renaming (_⊎_ to _+_; inj₁ to Inl ; inj₂ to Inr) hiding (map)
open import Data.Product hiding (map)
open import Relation.Nullary 
open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Prelude

open import Core.Core

module Core.Settled where


mutual 

  -- I'm not sure we actually need the context. 

  data SettledSyn : Ctx -> ExpUp -> Set where 
    SettledSynSyn : ∀ {Γ e t} ->
      SettledSynMid Γ e -> 
      SettledSyn Γ (e ⇒ (■ (t , Old)))

  data SettledSynMid : Ctx -> ExpMid -> Set where 
    SettledSynConst : ∀ {Γ} ->
      SettledSynMid Γ EConst
    SettledSynHole : ∀ {Γ} ->
      SettledSynMid Γ (EHole)
    SettledSynFun : ∀ {Γ t m1 m2 m3 e} ->
      SettledSyn ((t , Old) ∷ Γ) e ->
      SettledSynMid Γ ((EFun (t , Old) m1 m2 (e [ m3 ]⇐ □)))
    SettledSynAp : ∀ {Γ m1 m2 e1 e2} ->
      SettledSyn Γ e1 -> 
      SettledAna Γ e2 -> 
      SettledSynMid Γ ((EAp (e1 [ m1 ]⇐ □) m2 e2))
    SettledSynVar : ∀ {Γ t x m} ->
      ((x , (t , Old) ∈ Γ) + (x ̸∈ Γ)) ->
      SettledSynMid Γ ((EVar x m))
    SettledSynAsc : ∀ {Γ t e} ->
      SettledAna Γ e -> 
      SettledSynMid Γ ((EAsc (t , Old) e))

  data SettledAna : Ctx -> ExpLow -> Set where 
    SettledAnaAna : ∀ {Γ t e m} ->
      SettledAnaUp Γ e ->
      SettledAna Γ (e [ m ]⇐ (■ (t , Old)))
  
  data SettledAnaUp : Ctx -> ExpUp -> Set where 
    SettledAnaFun : ∀ {Γ t m1 m2 e} ->
      SettledAna ((t , Old) ∷ Γ) e ->
      SettledAnaUp Γ ((EFun (t , Old) m1 m2 e) ⇒ □)
    SettledAnaSubsume : ∀ {Γ e} ->
      SettledSyn Γ e ->
      SettledAnaUp Γ e

-- data SettledSynExcept : Ctx -> ExpUp -> Set where 
--   SettledSynExceptSyn : ∀ {Γ e t n} ->
--     SettledSynMid Γ e -> 
--     SettledSynExcept Γ (e ⇒ (■ (t , n)))

data SettledProgram : Program -> Set where 
  SettledRoot : ∀ {e} ->
    SettledSyn ∅ e -> 
    SettledProgram (Root e)
