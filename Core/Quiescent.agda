
open import Data.Product 

open import Prelude
open import Core.Core

module Core.Quiescent where

mutual 

  data _U̸↦ : SynExp -> Set where 
    QuiescentUp : ∀ {e t} ->
      e M̸↦ -> 
      (e ⇒ (t , •)) U̸↦

  data _M̸↦ : ConExp -> Set where 
    QuiescentConst :
      EConst M̸↦
    QuiescentHole : 
      EHole M̸↦
    QuiescentFun : ∀ {x t e m1 m2} ->
      e L̸↦ ->
      ((EFun x (t , •) m1 m2 e)) M̸↦
    QuiescentAp : ∀ {m e1 e2} ->
      e1 L̸↦ -> 
      e2 L̸↦ -> 
      ((EAp e1 m e2)) M̸↦
    QuiescentVar : ∀ {x m} ->
      (EVar x m) M̸↦
    QuiescentAsc : ∀ {t e} ->
      e L̸↦ -> 
      (EAsc (t , •) e) M̸↦
    QuiescentPair : ∀ {m e1 e2} ->
      e1 L̸↦ -> 
      e2 L̸↦ -> 
      ((EPair e1 e2 m)) M̸↦
    QuiescentProj : ∀ {s e m} ->
      e L̸↦ -> 
      ((EProj s e m)) M̸↦
    QuiescentTypFun : ∀ {x m e} ->
      e L̸↦ ->
      ((ETypFun x m e)) M̸↦
    QuiescentTypAp : ∀ {m e t} ->
      e L̸↦ -> 
      ((ETypAp e m (t , •))) M̸↦

  data _L̸↦ : AnaExp -> Set where 
    QuiescentLow : ∀ {t e m} ->
      e U̸↦ ->
      (e [ m ]⇐ (t , •)) L̸↦

data _almost-U̸↦ : SynExp -> Set where 
  AlmostQuiescentUp : ∀ {n e t} ->
    e M̸↦ -> 
    (e ⇒ (t , n)) almost-U̸↦

data _almost-L̸↦ : AnaExp -> Set where 
  AlmostQuiescentLow : ∀ {t e m} ->
    e almost-U̸↦ ->
    (e [ m ]⇐ (t , •)) almost-L̸↦

data _P̸↦ : Program -> Set where 
  QuiescentProgram : ∀ {p} ->
    (AnaExpOfProgram p) L̸↦  -> 
    p P̸↦
