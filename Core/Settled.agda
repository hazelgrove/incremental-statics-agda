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
    SettledSynConst : ∀ {Γ t} ->
      SettledSyn Γ (EConst ⇒ (■ (t , Old)))
    SettledSynHole : ∀ {Γ t} ->
      SettledSyn Γ (EHole ⇒ (■ (t , Old)))
    SettledSynFun : ∀ {Γ t1 t2 m1 m2 m3 e} ->
      SettledSyn ((t2 , Old) ∷ Γ) e ->
      SettledSyn Γ ((EFun (t2 , Old) m1 m2 (e [ m3 ]⇐ □)) ⇒ (■ (t1 , Old)))
    SettledSynAp : ∀ {Γ t m1 m2 e1 e2} ->
      SettledSyn Γ e1 -> 
      SettledAna Γ e2 -> 
      SettledSyn Γ ((EAp (e1 [ m1 ]⇐ □) m2 e2) ⇒ (■ (t , Old)))
    SettledSynVar : ∀ {Γ t1 t2 x m} ->
      ((x , (t1 , Old) ∈ Γ) + (x ̸∈ Γ)) ->
      SettledSyn Γ ((EVar x m) ⇒ (■ (t2 , Old)))
    SettledSynAsc : ∀ {Γ t1 t2 e} ->
      SettledAna Γ e -> 
      SettledSyn Γ ((EAsc (t2 , Old) e) ⇒ (■ (t1 , Old)))

  data SettledAna : Ctx -> ExpLow -> Set where 
    SettledAnaFun : ∀ {Γ t1 t2 m1 m2 m3 e} ->
      SettledAna Γ e ->
      SettledAna Γ (((EFun (t2 , Old) m2 m3 e) ⇒ □) [ m1 ]⇐ (■ (t1 , Old)))
    SettledAnaSubsume : ∀ {Γ e t m} ->
      SettledSyn Γ e ->
      SettledAna Γ (e [ m ]⇐ (■ (t , Old)))


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
