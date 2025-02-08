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

  data SettledUp : ExpUp -> Set where 
    SettledUpC : ∀ {e t} ->
      SettledMid e -> 
      SettledUp (e ⇒ (t , Old))

  data SettledMid : ExpMid -> Set where 
    SettledConst :
      SettledMid EConst
    SettledHole : 
      SettledMid (EHole)
    SettledFun : ∀ {x t e m1 m2} ->
      SettledLow e ->
      SettledMid ((EFun x (t , Old) m1 m2 e))
    SettledAp : ∀ {m e1 e2} ->
      SettledLow e1 -> 
      SettledLow e2 -> 
      SettledMid ((EAp e1 m e2))
    SettledVar : ∀ {x m} ->
      SettledMid (EVar x m)
    SettledAsc : ∀ {t e} ->
      SettledLow e -> 
      SettledMid (EAsc (t , Old) e)

  data SettledLow : ExpLow -> Set where 
    SettledLowC : ∀ {t e m} ->
      SettledUp e ->
      SettledLow (e [ m ]⇐ (t , Old))

data AlmostSettledUp : ExpUp -> Set where 
  AlmostSettledUpC : ∀ {n e t} ->
    SettledMid e -> 
    AlmostSettledUp (e ⇒ (t , n))

data AlmostSettledLow : ExpLow -> Set where 
  AlmostSettledLowC : ∀ {t e m} ->
    AlmostSettledUp e ->
    AlmostSettledLow (e [ m ]⇐ (t , Old))

data SettledProgram : Program -> Set where 
  SettledRoot : ∀ {p} ->
    SettledLow (ExpLowOfProgram p) -> 
    SettledProgram p
