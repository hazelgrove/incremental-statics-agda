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

  data _U̸↦ : ExpUp -> Set where 
    SettledUp : ∀ {e t} ->
      e M̸↦ -> 
      (e ⇒ (t , Old)) U̸↦

  data _M̸↦ : ExpMid -> Set where 
    SettledConst :
      EConst M̸↦
    SettledHole : 
      EHole M̸↦
    SettledFun : ∀ {x t e m1 m2} ->
      e L̸↦ ->
      ((EFun x (t , Old) m1 m2 e)) M̸↦
    SettledAp : ∀ {m e1 e2} ->
      e1 L̸↦ -> 
      e2 L̸↦ -> 
      ((EAp e1 m e2)) M̸↦
    SettledVar : ∀ {x m} ->
      (EVar x m) M̸↦
    SettledAsc : ∀ {t e} ->
      e L̸↦ -> 
      (EAsc (t , Old) e) M̸↦

  data _L̸↦ : ExpLow -> Set where 
    SettledLow : ∀ {t e m} ->
      e U̸↦ ->
      (e [ m ]⇐ (t , Old)) L̸↦

data _almost-U̸↦ : ExpUp -> Set where 
  AlmostSettledUp : ∀ {n e t} ->
    e M̸↦ -> 
    (e ⇒ (t , n)) almost-U̸↦

data _almost-L̸↦ : ExpLow -> Set where 
  AlmostSettledLow : ∀ {t e m} ->
    e almost-U̸↦ ->
    (e [ m ]⇐ (t , Old)) almost-L̸↦

data _P̸↦ : Program -> Set where 
  SettledProgram : ∀ {p} ->
    (ExpLowOfProgram p) L̸↦  -> 
    p P̸↦
