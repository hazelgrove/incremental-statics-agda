
open import Data.Product 

open import Prelude
open import Core.Core

module Core.Settled where

mutual 

  data _U̸↦ : ExpUp -> Set where 
    SettledUp : ∀ {e t} ->
      e M̸↦ -> 
      (e ⇒ (t , •)) U̸↦

  data _M̸↦ : ExpMid -> Set where 
    SettledConst :
      EConst M̸↦
    SettledHole : 
      EHole M̸↦
    SettledFun : ∀ {x t e m1 m2} ->
      e L̸↦ ->
      ((EFun x (t , •) m1 m2 e)) M̸↦
    SettledAp : ∀ {m e1 e2} ->
      e1 L̸↦ -> 
      e2 L̸↦ -> 
      ((EAp e1 m e2)) M̸↦
    SettledVar : ∀ {x m} ->
      (EVar x m) M̸↦
    SettledAsc : ∀ {t e} ->
      e L̸↦ -> 
      (EAsc (t , •) e) M̸↦
    SettledPair : ∀ {m e1 e2} ->
      e1 L̸↦ -> 
      e2 L̸↦ -> 
      ((EPair e1 e2 m)) M̸↦
    SettledProj : ∀ {s e m} ->
      e L̸↦ -> 
      ((EProj s e m)) M̸↦

  data _L̸↦ : ExpLow -> Set where 
    SettledLow : ∀ {t e m} ->
      e U̸↦ ->
      (e [ m ]⇐ (t , •)) L̸↦

data _almost-U̸↦ : ExpUp -> Set where 
  AlmostSettledUp : ∀ {n e t} ->
    e M̸↦ -> 
    (e ⇒ (t , n)) almost-U̸↦

data _almost-L̸↦ : ExpLow -> Set where 
  AlmostSettledLow : ∀ {t e m} ->
    e almost-U̸↦ ->
    (e [ m ]⇐ (t , •)) almost-L̸↦

data _P̸↦ : Program -> Set where 
  SettledProgram : ∀ {p} ->
    (ExpLowOfProgram p) L̸↦  -> 
    p P̸↦
