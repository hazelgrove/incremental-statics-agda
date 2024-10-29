open import Data.Nat hiding (_+_)
open import Data.Unit 
open import Data.Bool hiding (_<_; _≟_)
open import Data.Sum renaming (_⊎_ to _+_; inj₁ to Inl ; inj₂ to Inr) hiding (map)
open import Data.Product hiding (map)
open import Relation.Nullary 
open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Prelude

open import Core.Core
open import Core.WellTyped

module Core.Actions where

  data Child : Set where 
    One : Child
    Two : Child
    -- Three : Child

  data Action : Set where 
    -- MoveUp : Action 
    -- MoveDown : Child -> Action
    InsertConst : Action
    WrapFun : Action
    WrapAp : Child -> Action
    InsertVar : ℕ -> Action
    WrapAsc : Action
    Delete : Action 
    Unwrap : Child -> Action

  data FreshenSyn : SynData -> SynData -> Set where
    FreshenNoneSyn : FreshenSyn ̸⇑ ̸⇑
    FreshenSomeSyn : ∀ {t n} ->
      FreshenSyn (⇑ (t , n)) (⇑ (t , New))

  new-hole-up : ExpUp 
  new-hole-up = (EUp (⇑ (THole , New)) EHole)

  data _,_A↦_ : Action -> ExpUp -> ExpUp -> Set where 
    ActInsertConst : ∀ {syn} ->
      InsertConst , (EUp syn EHole) A↦ (EUp (⇑ (TBase , New)) EConst)
    ActWrapFun : ∀ {syn syn' e} ->
      FreshenSyn syn syn' ->
      WrapFun , (EUp syn e) A↦ (EUp ̸⇑ (EFun (THole , New) Unmarked (ELow ̸⇓ Unmarked (EUp syn' e))))
    ActWrapApOne : ∀ {syn syn' e} ->
      FreshenSyn syn syn' ->
      (WrapAp One) , (EUp syn e) A↦ (EUp ̸⇑ (EAp (ELow ̸⇓ Unmarked (EUp syn' e)) Unmarked (ELow ̸⇓ Unmarked new-hole-up)))
    ActWrapApTwo : ∀ {syn syn' e} ->
      FreshenSyn syn syn' ->
      (WrapAp Two) , (EUp syn e) A↦ (EUp ̸⇑ (EAp (ELow ̸⇓ Unmarked new-hole-up) Unmarked (ELow ̸⇓ Unmarked (EUp syn' e))))
    ActInsertVar : ∀ {syn x} ->
      (InsertVar x) , (EUp syn EHole) A↦ (EUp ̸⇑ (EVar x Unmarked)) -- wrong bc bindings 
    ActWrapAsc : ∀ {syn syn' e} ->
      FreshenSyn syn syn' ->
      WrapAsc , (EUp syn e) A↦ (EUp ̸⇑ (EAsc (THole , New) (ELow ̸⇓ Unmarked (EUp syn' e))))
  ------------------------------------------------------------------------------
    ActDelete : ∀ {e} ->
      Delete , e A↦  new-hole-up -- wrong bc bindings
    ActUnwrapFun : ∀ {syn1 syn2 syn3 asc m1 m2 ana e} ->
      FreshenSyn syn2 syn3 ->
      (Unwrap One) , (EUp syn1 (EFun asc m1 (ELow ana m2 (EUp syn2 e)))) A↦ (EUp syn3 e)
    ActUnwrapApOne : ∀ {syn1 syn2 syn3 m1 m2 ana e1 e2} ->
      FreshenSyn syn2 syn3 ->
      (Unwrap One) , (EUp syn1 (EAp (ELow ana m1 (EUp syn2 e1)) m2 e2)) A↦ (EUp syn3 e1)
    ActUnwrapApTwo : ∀ {syn1 syn2 syn3 m1 m2 ana e1 e2} ->
      FreshenSyn syn2 syn3 ->
      (Unwrap Two) , (EUp syn1 (EAp e1 m1 (ELow ana m2 (EUp syn2 e2)))) A↦ (EUp syn3 e2)
    ActUnwrapAsc : ∀ {syn1 syn2 syn3 asc m ana e} ->
      FreshenSyn syn2 syn3 ->
      (Unwrap One) , (EUp syn1 (EAsc asc (ELow ana m (EUp syn2 e)))) A↦ (EUp syn3 e)
    

    
    


