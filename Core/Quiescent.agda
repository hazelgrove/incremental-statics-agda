
open import Data.Product 

open import Prelude
open import Core.Core

module Core.Quiescent where

mutual 

  data _S̸↦ : SynExp -> Set where 
    QuiescentUp : ∀ {e t} ->
      e C̸↦ -> 
      (e ⇒ (t , •)) S̸↦

  data _C̸↦ : ConExp -> Set where
    QuiescentConst :
      EConst C̸↦
    QuiescentHole : 
      EHole C̸↦
    QuiescentFun : ∀ {x t e m1 m2} ->
      e A̸↦ ->
      ((EFun x (t , •) m1 m2 e)) C̸↦
    QuiescentAp : ∀ {m e1 e2} ->
      e1 A̸↦ -> 
      e2 A̸↦ ->
      ((EAp e1 m e2)) C̸↦
    QuiescentVar : ∀ {x m} ->
      (EVar x m) C̸↦
    QuiescentAsc : ∀ {t e} ->
      e A̸↦ -> 
      (EAsc (t , •) e) C̸↦
    QuiescentPair : ∀ {m e1 e2} ->
      e1 A̸↦ -> 
      e2 A̸↦ -> 
      ((EPair e1 e2 m)) C̸↦
    QuiescentProj : ∀ {s e m} ->
      e A̸↦ -> 
      ((EProj s e m)) C̸↦
    QuiescentTypFun : ∀ {x m e} ->
      e A̸↦ ->
      ((ETypFun x m e)) C̸↦
    QuiescentTypAp : ∀ {m e t} ->
      e A̸↦ -> 
      ((ETypAp e m (t , •))) C̸↦

  data _A̸↦ : AnaExp -> Set where 
    QuiescentLow : ∀ {t e m} ->
      e S̸↦ ->
      (e [ m ]⇐ (t , •)) A̸↦

data _almost-S̸↦ : SynExp -> Set where 
  AlmostQuiescentUp : ∀ {n e t} ->
    e C̸↦ -> 
    (e ⇒ (t , n)) almost-S̸↦

data _almost-A̸↦ : AnaExp -> Set where 
  AlmostQuiescentLow : ∀ {t e m} ->
    e almost-S̸↦ ->
    (e [ m ]⇐ (t , •)) almost-A̸↦

data _P̸↦ : Program -> Set where 
  QuiescentProgram : ∀ {p} ->
    (AnaExpOfProgram p) A̸↦  -> 
    p P̸↦
