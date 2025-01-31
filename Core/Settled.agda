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
      SettledAna Γ e ->
      SettledAnaUp Γ ((EFun (t , Old) m1 m2 e) ⇒ □)
    SettledAnaSubsume : ∀ {Γ e} ->
      SettledSyn Γ e ->
      SettledAnaUp Γ e


data SettledSynExcept : Ctx -> ExpUp -> Set where 
  SettledSynExceptConst : ∀ {Γ t n} ->
    SettledSynExcept Γ (EConst ⇒ (■ (t , n)))
  SettledSynExceptHole : ∀ {Γ t n} ->
    SettledSynExcept Γ (EHole ⇒ (■ (t , n)))
  SettledSynExceptFun : ∀ {Γ t1 t2 m1 m2 m3 e n} ->
    SettledSyn ((t2 , Old) ∷ Γ) e ->
    SettledSynExcept Γ ((EFun (t2 , Old) m1 m2 (e [ m3 ]⇐ □)) ⇒ (■ (t1 , n)))
  SettledSynExceptAp : ∀ {Γ t m1 m2 e1 e2 n} ->
    SettledSyn Γ e1 -> 
    SettledAna Γ e2 -> 
    SettledSynExcept Γ ((EAp (e1 [ m1 ]⇐ □) m2 e2) ⇒ (■ (t , n)))
  SettledSynExceptVar : ∀ {Γ t1 t2 x m n} ->
    ((x , (t1 , Old) ∈ Γ) + (x ̸∈ Γ)) ->
    SettledSynExcept Γ ((EVar x m) ⇒ (■ (t2 , n)))
  SettledSynExceptAsc : ∀ {Γ t1 t2 e n} ->
    SettledAna Γ e -> 
    SettledSynExcept Γ ((EAsc (t2 , Old) e) ⇒ (■ (t1 , n)))


data PSettled : Program -> Set where 
  PSettledRoot : ∀ {e} ->
    SettledSynExcept ∅ e -> 
    PSettled (PRoot e)
