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
    InsertConst : Action
    WrapFun : Action
    WrapAp : Child -> Action
    InsertVarWith : ℕ -> Type -> Mark -> Action
    WrapAsc : Action
    Delete : Action 
    Unwrap : Child -> Action

  -- still need to renew analyzed type above it
  data _,_A↦_ : Action -> ExpUp -> ExpUp -> Set where 
    ActInsertConst : ∀ {syn} ->
      InsertConst , (EHole ⇒ syn) A↦ (EConst ⇒ (■ TBase , New))
    ActWrapFun : ∀ {e t n} ->
      WrapFun , (e ⇒ (t , n)) A↦ ((EFun (THole , New) ✔ ✔ ((e ⇒ (t , New)) [ ✔ ]⇐ (□ , Old))) ⇒ (□ , Old))
    ActWrapApOne : ∀ {e t n} ->
      (WrapAp One) , (e ⇒ (t , n)) A↦ ((EAp ((e ⇒ (t , New)) [ ✔ ]⇐ (□ , Old)) ✔ ((EHole ⇒ (■ THole , Old)) [ ✔ ]⇐ (□ , Old))) ⇒ (□ , Old))
    ActWrapApTwo : ∀ {e t n} ->
      (WrapAp Two) , (e ⇒ (t , n)) A↦ ((EAp ((EHole ⇒ (■ THole , Old)) [ ✔ ]⇐ (□ , Old)) ✔ ((e ⇒ (t , Old)) [ ✔ ]⇐ (■ THole , Old))) ⇒ (■ THole , New))
    ActInsertVarWith : ∀ {syn x t m} ->
      (InsertVarWith x t m) , (EHole ⇒ syn) A↦ ((EVar x m) ⇒ (■ t , New))
    ActWrapAsc : ∀ {e syn} ->
      WrapAsc , (e ⇒ syn) A↦ ((EAsc (THole , New) ((e ⇒ syn) [ ✔ ]⇐ (■ THole , New))) ⇒ (■ THole , New))
  -- ------------------------------------------------------------------------------
    ActDelete : ∀ {e} ->
      Delete , e A↦ (EHole ⇒ (■ THole , New))
    ActUnwrapFun : ∀ {asc m-ana m-ann e t n m-body ana syn} ->
      (Unwrap One) , ((EFun asc m-ana m-ann ((e ⇒ (t , n)) [ m-body ]⇐ ana)) ⇒ syn) A↦ (e ⇒ (t , New))
    ActUnwrapApOne : ∀ {e t n m ana e-arg syn} ->
      (Unwrap One) , ((EAp ((e ⇒ (t , n)) [ m ]⇐ ana) ✔ e-arg) ⇒ syn) A↦ (e ⇒ (t , New))
    ActUnwrapApTwo : ∀ {e t n m ana e-fun syn} ->
      (Unwrap Two) , ((EAp e-fun ✔ ((e ⇒ (t , n)) [ m ]⇐ ana)) ⇒ syn) A↦ (e ⇒ (t , New))
    ActUnwrapAsc : ∀ {asc e t n m ana syn} ->
      (Unwrap One) , ((EAsc asc ((e ⇒ (t , n)) [ m ]⇐ ana)) ⇒ syn) A↦ (e ⇒ (t , New))
    

    
    


