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

-- this would probably be nicer if it weren't bidirectional

mutual 

  data SettledSyn : ExpUp -> Set where 
    SettledSynSyn : ∀ {e t} ->
      SettledSynMid e -> 
      SettledSyn (e ⇒ ((■ t , Old)))

  data SettledSynMid : ExpMid -> Set where 
    SettledSynConst :
      SettledSynMid EConst
    SettledSynHole : 
      SettledSynMid (EHole)
    SettledSynFun : ∀ {x t e} ->
      SettledSyn e ->
      SettledSynMid ((EFun x (t , Old) ✔ ✔ (e [ ✔ ]⇐ (□ , Old))))
    SettledSynAp : ∀ {m e1 e2} ->
      SettledSyn e1 -> 
      SettledAna e2 -> 
      SettledSynMid ((EAp (e1 [ ✔ ]⇐ (□ , Old)) m e2))
    SettledSynVar : ∀ {x m} ->
      SettledSynMid ((EVar x m))
    SettledSynAsc : ∀ {t e} ->
      SettledAna e -> 
      SettledSynMid ((EAsc (t , Old) e))

  data SettledAna : ExpLow -> Set where 
    SettledAnaAna : ∀ {t e m} ->
      SettledAnaUp e ->
      SettledAna (e [ m ]⇐ ((■ t , Old)))
  
  data SettledAnaUp : ExpUp -> Set where 
    SettledAnaFun : ∀ {x t m1 m2 e} ->
      SettledAna e ->
      SettledAnaUp ((EFun x (t , Old) m1 m2 e) ⇒ (□ , Old))
    SettledAnaSubsume : ∀ {e} ->
      Subsumable e ->
      SettledSyn e ->
      SettledAnaUp e

data SettledProgram : Program -> Set where 
  SettledRoot : ∀ {e} ->
    SettledSyn e -> 
    SettledProgram (Root e Old)
