open import Data.Nat hiding (_+_)
open import Data.Unit 
open import Data.List 
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

  data _⊢_,_AL↦_ : Ctx -> Action -> ExpLow -> ExpLow -> Set where 
    ALC : ∀ {Γ α e e' m t n} ->
        Γ ⊢ α , e  A↦ e' ->
        Γ ⊢ α , e [ m ]⇐ (t , n) AL↦ (e' [ m ]⇐ (t , New))

  LocalizedAction : Set
  LocalizedAction = Action × (List Child)

  mutual 

    data _⊢_,_AUp↦_ : (Γ : Ctx) -> (α : LocalizedAction) -> (e : ExpUp) -> (e' : ExpUp) -> Set where
      AUpMid : ∀ {Γ α e e' syn} ->
        Γ ⊢ α , e  AMid↦ e' ->
        Γ ⊢ α , (e ⇒ syn) AUp↦ (e' ⇒ syn) 

    data _⊢_,_AMid↦_ : (Γ : Ctx) -> (α : LocalizedAction) -> (e : ExpMid) -> (e' : ExpMid) -> Set where 
      AMidAsc : ∀ {Γ α l e e' a1} ->
        Γ ⊢ (α , l) , e ALow↦ e' ->
        Γ ⊢ (α , One ∷ l) , (EAsc a1 e) AMid↦ (EAsc a1 e')
      AMidFun : ∀ {Γ α l e e' x t m1 m2} ->
        (x ∶ t ∷? Γ) ⊢ (α , l) , e ALow↦ e' ->
        Γ ⊢ (α , One ∷ l) , (EFun x t m1 m2 e) AMid↦ (EFun x t m1 m2 e')
      AMidApOne : ∀ {Γ α l e1 e2 e1' m} ->
        Γ ⊢ (α , l) , e1 ALow↦ e1' ->
        Γ ⊢ (α , One ∷ l) , (EAp e1 m e2) AMid↦ (EAp e1' m e2)
      AMidApTwo : ∀ {Γ α l e1 e2 e2' m} ->
        Γ ⊢ (α , l) , e2 ALow↦ e2' ->
        Γ ⊢ (α , Two ∷ l) , (EAp e1 m e2) AMid↦ (EAp e1 m e2')
    
    data _⊢_,_ALow↦_ : (Γ : Ctx) -> (α : LocalizedAction) -> (e : ExpLow) -> (e' : ExpLow) -> Set where
      ALowDone : ∀ {Γ α e e'} ->
        Γ ⊢ α , e AL↦ e' ->
        Γ ⊢ (α , []) , e ALow↦ e'
      ALowUp : ∀ {Γ α e e' m ana} ->
        Γ ⊢ α , e  AUp↦ e' ->
        Γ ⊢ α , e [ m ]⇐ ana ALow↦ (e' [ m ]⇐ ana)

  data _,_AP↦_ : (α : LocalizedAction) -> (p p' : Program) -> Set where
    AStepProgram : ∀{α p p'} ->
      ∅ ⊢ α , (ExpLowOfProgram p) ALow↦ (ExpLowOfProgram p') ->
      α , p AP↦ p'