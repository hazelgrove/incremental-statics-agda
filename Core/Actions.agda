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
open import Core.VarsSynthesize
open import Core.WellTyped

module Core.Actions where

  data Child : Set where 
    One : Child
    Two : Child

  data Action : Set where 
    InsertConst : Action
    WrapFun : Binding -> Action
    WrapAp : Child -> Action
    InsertVar : Var -> Action
    WrapAsc : Action
    Delete : Action 
    Unwrap : Child -> Action

  data _⊢_,_AU↦_ : Ctx -> Action -> ExpUp -> ExpUp -> Set where 
    ActInsertConst : ∀ {Γ syn} ->
      Γ ⊢ InsertConst , (EHole ⇒ syn) AU↦ (EConst ⇒ (■ TBase , New))
    ActWrapFun : ∀ {Γ x e e' t t' n n'} ->
      VarsSynthesize? x THole ✔ (e ⇒ (t , n)) (e' ⇒ (t' , n')) ->
      Γ ⊢ WrapFun x , (e ⇒ (t , n)) AU↦ ((EFun x (THole , New) ✔ ✔ ((e' ⇒ (t' , New)) [ ✔ ]⇐ (□ , Old))) ⇒ (t , n))
    ActWrapApOne : ∀ {Γ e t n} ->
      Γ ⊢ (WrapAp One) , (e ⇒ (t , n)) AU↦ ((EAp ((e ⇒ (t , New)) [ ✔ ]⇐ (□ , New)) ✔ ((EHole ⇒ (■ THole , Old)) [ ✔ ]⇐ (□ , Old))) ⇒ (t , n))
    ActWrapApTwo : ∀ {Γ e t n} ->
      Γ ⊢ (WrapAp Two) , (e ⇒ (t , n)) AU↦ ((EAp ((EHole ⇒ (■ THole , Old)) [ ✔ ]⇐ (□ , Old)) ✔ ((e ⇒ (t , Old)) [ ✔ ]⇐ (■ THole , New))) ⇒ (■ THole , New))
    ActInsertVar : ∀ {Γ syn x n t m} ->
      x , (t , n) ∈N Γ , m ->
      Γ ⊢ (InsertVar x) , (EHole ⇒ syn) AU↦ ((EVar x m) ⇒ (■ t , New))
    ActWrapAsc : ∀ {Γ e syn} ->
      Γ ⊢ WrapAsc , (e ⇒ syn) AU↦ ((EAsc (THole , New) ((e ⇒ syn) [ ✔ ]⇐ (■ THole , New))) ⇒ (■ THole , New))
  -- ------------------------------------------------------------------------------
    ActDelete : ∀ {Γ e} ->
      Γ ⊢ Delete , e AU↦ (EHole ⇒ (■ THole , New))
    ActUnwrapFun : ∀ {Γ x asc m-ana m-ann e e' t t' n n' tx nx m m-body ana syn} ->
      x , (tx , nx) ∈N? Γ , m ->
      VarsSynthesize? x tx m (e ⇒ (t , n)) (e' ⇒ (t' , n')) ->
      Γ ⊢ (Unwrap One) , ((EFun x asc m-ana m-ann ((e ⇒ (t , n)) [ m-body ]⇐ ana)) ⇒ syn) AU↦ (e' ⇒ (t' , New))
    -- ActUnwrapFunNone : ∀ {Γ asc m-ana m-ann e t n m-body ana syn} ->
    --   Γ ⊢ (Unwrap One) , ((EFun BHole asc m-ana m-ann ((e ⇒ (t , n)) [ m-body ]⇐ ana)) ⇒ syn) AU↦ (e ⇒ (t , New))
    ActUnwrapApOne : ∀ {Γ e t n m ana e-arg syn} ->
      Γ ⊢ (Unwrap One) , ((EAp ((e ⇒ (t , n)) [ m ]⇐ ana) ✔ e-arg) ⇒ syn) AU↦ (e ⇒ (t , New))
    ActUnwrapApTwo : ∀ {Γ e t n m ana e-fun syn} ->
      Γ ⊢ (Unwrap Two) , ((EAp e-fun ✔ ((e ⇒ (t , n)) [ m ]⇐ ana)) ⇒ syn) AU↦ (e ⇒ (t , New))
    ActUnwrapAsc : ∀ {Γ asc e t n m ana syn} ->
      Γ ⊢ (Unwrap One) , ((EAsc asc ((e ⇒ (t , n)) [ m ]⇐ ana)) ⇒ syn) AU↦ (e ⇒ (t , New))

  mutual 
    CtxOfLEnvUp : LEnvUp -> Ctx -> Ctx
    CtxOfLEnvUp (LEnvUpRec ε _) Γ = CtxOfLEnvMid ε Γ 

    CtxOfLEnvMid : LEnvMid -> Ctx -> Ctx
    CtxOfLEnvMid (LEnvAp1 ε _ _) Γ = CtxOfLEnvLow ε Γ  
    CtxOfLEnvMid (LEnvAp2 _ _ ε) Γ = CtxOfLEnvLow ε Γ 
    CtxOfLEnvMid (LEnvAsc _ ε) Γ = CtxOfLEnvLow ε Γ 
    CtxOfLEnvMid (LEnvFun x t _ _ ε) Γ = CtxOfLEnvLow ε (x ∶ t ∷? Γ) 
    
    CtxOfLEnvLow : LEnvLow -> Ctx -> Ctx
    CtxOfLEnvLow L⊙ Γ = Γ
    CtxOfLEnvLow (LEnvLowRec ε _ _) Γ = CtxOfLEnvUp ε Γ 

  mutual 
    CtxOfUEnvUp : UEnvUp -> Ctx -> Ctx
    CtxOfUEnvUp U⊙ Γ = Γ
    CtxOfUEnvUp (UEnvUpRec ε _) Γ = CtxOfUEnvMid ε Γ 

    CtxOfUEnvMid : UEnvMid -> Ctx -> Ctx
    CtxOfUEnvMid (UEnvFun x t _ _ ε) Γ = CtxOfUEnvLow ε (x ∶ t ∷? Γ)
    CtxOfUEnvMid (UEnvAp1 ε _ _) Γ = CtxOfUEnvLow ε Γ 
    CtxOfUEnvMid (UEnvAp2 _ _ ε) Γ = CtxOfUEnvLow ε Γ 
    CtxOfUEnvMid (UEnvAsc _ ε) Γ = CtxOfUEnvLow ε Γ 

    CtxOfUEnvLow : UEnvLow -> Ctx -> Ctx
    CtxOfUEnvLow (UEnvLowRec ε _ _) Γ = CtxOfUEnvUp ε Γ 

  data _⊢_,_AL↦_ : Ctx -> Action -> ExpLow -> ExpLow -> Set where 
    ActLow : ∀ {Γ α e e' m t n} ->
      Γ ⊢ α , e AU↦ e' ->
      Γ ⊢ α , (e [ m ]⇐ (t , n)) AL↦ (e' [ m ]⇐ (t , New))

  data _⊢_,_AUp↦_ : Ctx -> (α : Action) -> (e e' : ExpUp) -> Set where
    AStepUp : ∀{Γ α ε e e' e-in e-in'} ->
      ε L⟦ e-in ⟧Up== e ->
      (CtxOfLEnvUp ε Γ) ⊢ α , e-in AL↦ e-in' ->
      ε L⟦ e-in' ⟧Up== e' ->
      Γ ⊢ α , e AUp↦ e'

  data _⊢_,_ALow↦_ : Ctx -> (α : Action) -> (e e' : ExpLow) -> Set where
    AStepLow : ∀{Γ α ε e e' e-in e-in'} ->
      ε L⟦ e-in ⟧Low== e ->
      (CtxOfLEnvLow ε Γ) ⊢ α , e-in AL↦ e-in' ->
      ε L⟦ e-in' ⟧Low== e' ->
      Γ ⊢ α , e ALow↦ e'

  data _,_AP↦_ : (α : Action) -> (p p' : Program) -> Set where
    AStepProgram : ∀{α p p'} ->
      ∅ ⊢ α , (ExpLowOfProgram p) ALow↦ (ExpLowOfProgram p') ->
      α , p AP↦ p'