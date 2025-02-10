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

  data _,_AB↦_ : Action -> BareExp -> BareExp -> Set where
    ActInsertConst : 
      InsertConst , BareEHole AB↦ BareEConst
    ActWrapFun : ∀ {x e} ->
      WrapFun x , e AB↦ (BareEFun x THole e)
    ActWrapApOne : ∀ {e} ->
      (WrapAp One) , e AB↦ (BareEAp e BareEHole)
    ActWrapApTwo : ∀ {e} ->
      (WrapAp Two) , e AB↦ (BareEAp BareEHole e)
    ActInsertVar : ∀ {x} ->
      (InsertVar x) , BareEHole AB↦ (BareEVar x)
    ActWrapAsc : ∀ {e} ->
      WrapAsc , e AB↦ (BareEAsc THole e)
    ActDelete : ∀ {e} ->
      Delete , e AB↦ BareEHole
    ActUnwrapFun : ∀ {x asc e} ->
      (Unwrap One) , (BareEFun x asc e) AB↦ e
    ActUnwrapApOne : ∀ {e e-arg} ->
      (Unwrap One) , (BareEAp e e-arg) AB↦ e
    ActUnwrapApTwo : ∀ {e e-fun} ->
      (Unwrap Two) , (BareEAp e-fun e) AB↦ e
    ActUnwrapAsc : ∀ {asc e} ->
      (Unwrap One) , (BareEAsc asc e) AB↦ e

  data _⊢_,_A↦_ : Ctx -> Action -> ExpUp -> ExpUp -> Set where 
    ActInsertConst : ∀ {Γ syn} ->
      Γ ⊢ InsertConst , (EHole ⇒ syn) A↦ (EConst ⇒ (■ TBase , New))
    ActWrapFun : ∀ {Γ x e e' t t' n n'} ->
      VarsSynthesize? x THole ✔ (e ⇒ (t , n)) (e' ⇒ (t' , n')) ->
      Γ ⊢ WrapFun x , (e ⇒ (t , n)) A↦ ((EFun x (THole , Old) ✔ ✔ ((e' ⇒ (t' , New)) [ ✔ ]⇐ (□ , New))) ⇒ (t , n))
    ActWrapApOne : ∀ {Γ e t n} ->
      Γ ⊢ (WrapAp One) , (e ⇒ (t , n)) A↦ ((EAp ((e ⇒ (t , New)) [ ✔ ]⇐ (□ , New)) ✔ ((EHole ⇒ (■ THole , Old)) [ ✔ ]⇐ (□ , Old))) ⇒ (t , n))
    ActWrapApTwo : ∀ {Γ e t n} ->
      Γ ⊢ (WrapAp Two) , (e ⇒ (t , n)) A↦ ((EAp ((EHole ⇒ (■ THole , Old)) [ ✔ ]⇐ (□ , Old)) ✔ ((e ⇒ (t , Old)) [ ✔ ]⇐ (■ THole , New))) ⇒ (■ THole , New))
    ActInsertVar : ∀ {Γ syn x n t m} ->
      x , (t , n) ∈N Γ , m ->
      Γ ⊢ (InsertVar x) , (EHole ⇒ syn) A↦ ((EVar x m) ⇒ (■ t , New))
    ActWrapAsc : ∀ {Γ e syn} ->
      Γ ⊢ WrapAsc , (e ⇒ syn) A↦ ((EAsc (THole , New) ((e ⇒ syn) [ ✔ ]⇐ (■ THole , New))) ⇒ (■ THole , New))
    ActDelete : ∀ {Γ e} ->
      Γ ⊢ Delete , e A↦ (EHole ⇒ (■ THole , New))
    ActUnwrapFun : ∀ {Γ x asc m-ana m-ann e e' t t' n n' tx nx m m-body ana syn} ->
      x , (tx , nx) ∈N? Γ , m ->
      VarsSynthesize? x tx m (e ⇒ (t , n)) (e' ⇒ (t' , n')) ->
      Γ ⊢ (Unwrap One) , ((EFun x asc m-ana m-ann ((e ⇒ (t , n)) [ m-body ]⇐ ana)) ⇒ syn) A↦ (e' ⇒ (t' , New))
    ActUnwrapApOne : ∀ {Γ e t n m ana e-arg syn} ->
      Γ ⊢ (Unwrap One) , ((EAp ((e ⇒ (t , n)) [ m ]⇐ ana) ✔ e-arg) ⇒ syn) A↦ (e ⇒ (t , New))
    ActUnwrapApTwo : ∀ {Γ e t n m ana e-fun syn} ->
      Γ ⊢ (Unwrap Two) , ((EAp e-fun ✔ ((e ⇒ (t , n)) [ m ]⇐ ana)) ⇒ syn) A↦ (e ⇒ (t , New))
    ActUnwrapAsc : ∀ {Γ asc e t n m ana syn} ->
      Γ ⊢ (Unwrap One) , ((EAsc asc ((e ⇒ (t , n)) [ m ]⇐ ana)) ⇒ syn) A↦ (e ⇒ (t , New))

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

  record ActionOnExpLow (e : ExpLow) : Set where 
    field
      α : Action
      ε : UEnvLow 
      e-in : ExpUp 
      fill : ε U⟦ e-in ⟧Low== e

  data _,_ALow↦_ : (e : ExpLow) -> (A : ActionOnExpLow e) -> (e' : ExpLow) -> Set where
    AStepLow : ∀{ε α e e' e-in e-in' fill} ->
      (CtxOfUEnvLow ε ∅) ⊢ α , e-in A↦ e-in' ->
      ε U⟦ e-in' ⟧Low== e' ->
      e , (record {α = α ; ε = ε ; e-in = e-in ; fill = fill}) ALow↦ e'

  record ActionOnProgram (p : Program) : Set where 
    field
      α : Action
      ε : UEnvLow 
      e-in : ExpUp 
      fill : ε U⟦ e-in ⟧Low== (ExpLowOfProgram p)

  data _,_AP↦_ : (p : Program) -> (A : ActionOnProgram p) -> (p' : Program) -> Set where
    AStepProgram : ∀{A p p'} ->
      (ExpLowOfProgram p) , ? ALow↦ (ExpLowOfProgram p') ->
      p , A AP↦ p'