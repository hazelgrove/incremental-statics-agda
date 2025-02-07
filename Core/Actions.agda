open import Data.Nat hiding (_+_)
open import Data.Unit 
open import Data.Bool hiding (_<_; _≟_)
open import Data.Sum renaming (_⊎_ to _+_; inj₁ to Inl ; inj₂ to Inr) hiding (map)
open import Data.Product hiding (map)
open import Relation.Nullary 
open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Prelude

open import Core.Core
open import Core.Environment

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
  data _,_AU↦_ : Action -> ExpUp -> ExpUp -> Set where 
    ActInsertConst : ∀ {syn} ->
      InsertConst , (EHole ⇒ syn) AU↦ (EConst ⇒ (■ TBase , New))
    ActWrapFun : ∀ {e t n} ->
      WrapFun , (e ⇒ (t , n)) AU↦ ((EFun (THole , New) ✔ ✔ ((e ⇒ (t , New)) [ ✔ ]⇐ (□ , Old))) ⇒ (t , n))
    ActWrapApOne : ∀ {e t n} ->
      (WrapAp One) , (e ⇒ (t , n)) AU↦ ((EAp ((e ⇒ (t , New)) [ ✔ ]⇐ (□ , Old)) ✔ ((EHole ⇒ (■ THole , Old)) [ ✔ ]⇐ (□ , Old))) ⇒ (t , n))
    ActWrapApTwo : ∀ {e t n} ->
      (WrapAp Two) , (e ⇒ (t , n)) AU↦ ((EAp ((EHole ⇒ (■ THole , Old)) [ ✔ ]⇐ (□ , Old)) ✔ ((e ⇒ (t , Old)) [ ✔ ]⇐ (■ THole , Old))) ⇒ (■ THole , New))
    ActInsertVarWith : ∀ {syn x t m} ->
      (InsertVarWith x t m) , (EHole ⇒ syn) AU↦ ((EVar x m) ⇒ (■ t , New))
    ActWrapAsc : ∀ {e syn} ->
      WrapAsc , (e ⇒ syn) AU↦ ((EAsc (THole , New) ((e ⇒ syn) [ ✔ ]⇐ (■ THole , New))) ⇒ (■ THole , New))
  -- ------------------------------------------------------------------------------
    ActDelete : ∀ {e} ->
      Delete , e AU↦ (EHole ⇒ (■ THole , New))
    ActUnwrapFun : ∀ {asc m-ana m-ann e t n m-body ana syn} ->
      (Unwrap One) , ((EFun asc m-ana m-ann ((e ⇒ (t , n)) [ m-body ]⇐ ana)) ⇒ syn) AU↦ (e ⇒ (t , New))
    ActUnwrapApOne : ∀ {e t n m ana e-arg syn} ->
      (Unwrap One) , ((EAp ((e ⇒ (t , n)) [ m ]⇐ ana) ✔ e-arg) ⇒ syn) AU↦ (e ⇒ (t , New))
    ActUnwrapApTwo : ∀ {e t n m ana e-fun syn} ->
      (Unwrap Two) , ((EAp e-fun ✔ ((e ⇒ (t , n)) [ m ]⇐ ana)) ⇒ syn) AU↦ (e ⇒ (t , New))
    ActUnwrapAsc : ∀ {asc e t n m ana syn} ->
      (Unwrap One) , ((EAsc asc ((e ⇒ (t , n)) [ m ]⇐ ana)) ⇒ syn) AU↦ (e ⇒ (t , New))


  -- for now I'm going to ignore correct types on variables, so that I can look at the proof obligation 
  -- and see how best to implement the solution. 

  -- mutual 
  --   VarTypeLEnvUp : LEnvUp -> Action -> Action 
  --   VarTypeLEnvUp (LEnvUpRec ε _) α = VarTypeLEnvMid ε α

  --   VarTypeLEnvMid : LEnvMid -> Action -> Action 
  --   VarTypeLEnvMid (LEnvAp1 ε _ _) α = VarTypeLEnvLow ε α 
  --   VarTypeLEnvMid (LEnvAp2 _ _ ε) α = VarTypeLEnvLow ε α
  --   VarTypeLEnvMid (LEnvAsc _ ε) α = VarTypeLEnvLow ε α
  --   VarTypeLEnvMid (LEnvFun x x₁ x₂ x₃) (InsertVarWith x₄ x₅ x₆) = {!   !}
  --   VarTypeLEnvMid (LEnvFun _ _ _ ε) α = VarTypeLEnvLow ε α
    
  --   VarTypeLEnvLow : LEnvLow -> Action -> Action 
  --   VarTypeLEnvLow L⊙ α = α
  --   VarTypeLEnvLow (LEnvLowRec ε _ _) α = VarTypeLEnvUp ε α

  -- mutual 
  --   VarTypeUEnvUp : UEnvUp -> Action -> Action 
  --   VarTypeUEnvUp U⊙ α = α
  --   VarTypeUEnvUp (UEnvUpRec ε _) α = VarTypeUEnvMid ε α

  --   VarTypeUEnvMid : UEnvMid -> Action -> Action 
  --   VarTypeUEnvMid (UEnvFun x x₁ x₂ x₃) α = {!   !}
  --   VarTypeUEnvMid (UEnvAp1 ε _ _) α = VarTypeUEnvLow ε α
  --   VarTypeUEnvMid (UEnvAp2 _ _ ε) α = VarTypeUEnvLow ε α
  --   VarTypeUEnvMid (UEnvAsc _ ε) α = VarTypeUEnvLow ε α

  --   VarTypeUEnvLow : UEnvLow -> Action -> Action 
  --   VarTypeUEnvLow (UEnvLowRec ε _ _) α = VarTypeUEnvUp ε α

  data _,_AL↦_ : Action -> ExpLow -> ExpLow -> Set where 
    ActLow : ∀ {α e e' m t n} ->
      α , e AU↦ e' ->
      α , (e [ m ]⇐ (t , n)) AL↦ (e' [ m ]⇐ (t , New))

  data _,_AUp↦_ : (α : Action) -> (e e' : ExpUp) -> Set where
    AStepUp : ∀{α ε e e' e-in e-in'} ->
      ε L⟦ e-in ⟧Up== e ->
      α , e-in AL↦ e-in' ->
      ε L⟦ e-in' ⟧Up== e' ->
      α , e AUp↦ e'

  data _,_ALow↦_ : (α : Action) -> (e e' : ExpLow) -> Set where
    AStepLow : ∀{α ε e e' e-in e-in'} ->
      ε L⟦ e-in ⟧Low== e ->
      α , e-in AL↦ e-in' ->
      ε L⟦ e-in' ⟧Low== e' ->
      α , e ALow↦ e'

  data _,_AP↦_ : (α : Action) -> (p p' : Program) -> Set where
    AStepProgram : ∀{α p p'} ->
      α , (ExpLowOfProgram p) ALow↦ (ExpLowOfProgram p') ->
      α , p AP↦ p'
      

      
      


