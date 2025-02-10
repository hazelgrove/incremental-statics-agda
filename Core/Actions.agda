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
    
  LocalizedAction : Set
  LocalizedAction = Action × (List Child)

  data _,_αB↦_ : Action -> BareExp -> BareExp -> Set where
    ActInsertConst : 
      InsertConst , BareEHole αB↦ BareEConst
    ActWrapFun : ∀ {x e} ->
      WrapFun x , e αB↦ (BareEFun x THole e)
    ActWrapApOne : ∀ {e} ->
      (WrapAp One) , e αB↦ (BareEAp e BareEHole)
    ActWrapApTwo : ∀ {e} ->
      (WrapAp Two) , e αB↦ (BareEAp BareEHole e)
    ActInsertVar : ∀ {x} ->
      (InsertVar x) , BareEHole αB↦ (BareEVar x)
    ActWrapAsc : ∀ {e} ->
      WrapAsc , e αB↦ (BareEAsc THole e)
    ActDelete : ∀ {e} ->
      Delete , e αB↦ BareEHole
    ActUnwrapFun : ∀ {x asc e} ->
      (Unwrap One) , (BareEFun x asc e) αB↦ e
    ActUnwrapApOne : ∀ {e e-arg} ->
      (Unwrap One) , (BareEAp e e-arg) αB↦ e
    ActUnwrapApTwo : ∀ {e e-fun} ->
      (Unwrap Two) , (BareEAp e-fun e) αB↦ e
    ActUnwrapAsc : ∀ {asc e} ->
      (Unwrap One) , (BareEAsc asc e) αB↦ e

  data _,_AB↦_ : LocalizedAction -> BareExp -> BareExp -> Set where
    ABareDone : ∀ {α e e'} ->
      α , e αB↦ e' ->
      (α , []) , e AB↦ e
    ABareAsc : ∀ {α l e e' a1} ->
      (α , l) , e AB↦ e' ->
      (α , One ∷ l) , (BareEAsc a1 e) AB↦ (BareEAsc a1 e')
    ABareFun : ∀ {α l e e' x t} ->
      (α , l) , e AB↦ e' ->
      (α , One ∷ l) , (BareEFun x t e) AB↦ (BareEFun x t e')
    ABareApOne : ∀ {α l e1 e2 e1'} ->
      (α , l) , e1 AB↦ e1' ->
      (α , One ∷ l) , (BareEAp e1 e2) AB↦ (BareEAp e1' e2)
    ABareApTwo : ∀ {α l e1 e2 e2'} ->
      (α , l) , e2 AB↦ e2' ->
      (α , Two ∷ l) , (BareEAp e1 e2) AB↦ (BareEAp e1 e2')

  data _⊢_,_αU↦_ : Ctx -> Action -> ExpUp -> ExpUp -> Set where 
    ActInsertConst : ∀ {Γ syn} ->
      Γ ⊢ InsertConst , (EHole ⇒ syn) αU↦ (EConst ⇒ (■ TBase , New))
    ActWrapFun : ∀ {Γ x e e' t t' n n'} ->
      VarsSynthesize? x THole ✔ (e ⇒ (t , n)) (e' ⇒ (t' , n')) ->
      Γ ⊢ WrapFun x , (e ⇒ (t , n)) αU↦ ((EFun x (THole , Old) ✔ ✔ ((e' ⇒ (t' , New)) [ ✔ ]⇐ (□ , New))) ⇒ (t , n))
    ActWrapApOne : ∀ {Γ e t n} ->
      Γ ⊢ (WrapAp One) , (e ⇒ (t , n)) αU↦ ((EAp ((e ⇒ (t , New)) [ ✔ ]⇐ (□ , New)) ✔ ((EHole ⇒ (■ THole , Old)) [ ✔ ]⇐ (□ , Old))) ⇒ (t , n))
    ActWrapApTwo : ∀ {Γ e t n} ->
      Γ ⊢ (WrapAp Two) , (e ⇒ (t , n)) αU↦ ((EAp ((EHole ⇒ (■ THole , Old)) [ ✔ ]⇐ (□ , Old)) ✔ ((e ⇒ (t , Old)) [ ✔ ]⇐ (■ THole , New))) ⇒ (■ THole , New))
    ActInsertVar : ∀ {Γ syn x n t m} ->
      x , (t , n) ∈N Γ , m ->
      Γ ⊢ (InsertVar x) , (EHole ⇒ syn) αU↦ ((EVar x m) ⇒ (■ t , New))
    ActWrapAsc : ∀ {Γ e syn} ->
      Γ ⊢ WrapAsc , (e ⇒ syn) αU↦ ((EAsc (THole , New) ((e ⇒ syn) [ ✔ ]⇐ (■ THole , New))) ⇒ (■ THole , New))
    ActDelete : ∀ {Γ e} ->
      Γ ⊢ Delete , e αU↦ (EHole ⇒ (■ THole , New))
    ActUnwrapFun : ∀ {Γ x asc m-ana m-ann e e' t t' n n' tx nx m m-body ana syn} ->
      x , (tx , nx) ∈N? Γ , m ->
      VarsSynthesize? x tx m (e ⇒ (t , n)) (e' ⇒ (t' , n')) ->
      Γ ⊢ (Unwrap One) , ((EFun x asc m-ana m-ann ((e ⇒ (t , n)) [ m-body ]⇐ ana)) ⇒ syn) αU↦ (e' ⇒ (t' , New))
    ActUnwrapApOne : ∀ {Γ e t n m ana e-arg syn} ->
      Γ ⊢ (Unwrap One) , ((EAp ((e ⇒ (t , n)) [ m ]⇐ ana) ✔ e-arg) ⇒ syn) αU↦ (e ⇒ (t , New))
    ActUnwrapApTwo : ∀ {Γ e t n m ana e-fun syn} ->
      Γ ⊢ (Unwrap Two) , ((EAp e-fun ✔ ((e ⇒ (t , n)) [ m ]⇐ ana)) ⇒ syn) αU↦ (e ⇒ (t , New))
    ActUnwrapAsc : ∀ {Γ asc e t n m ana syn} ->
      Γ ⊢ (Unwrap One) , ((EAsc asc ((e ⇒ (t , n)) [ m ]⇐ ana)) ⇒ syn) αU↦ (e ⇒ (t , New))

  data _⊢_,_αL↦_ : Ctx -> Action -> ExpLow -> ExpLow -> Set where 
    ALC : ∀ {Γ α e e' m t n} ->
        Γ ⊢ α , e  αU↦ e' ->
        Γ ⊢ α , e [ m ]⇐ (t , n) αL↦ (e' [ m ]⇐ (t , New))

  mutual 

    data _⊢_,_AU↦_ : (Γ : Ctx) -> (α : LocalizedAction) -> (e : ExpUp) -> (e' : ExpUp) -> Set where
      AUpMid : ∀ {Γ α e e' syn} ->
        Γ ⊢ α , e  AM↦ e' ->
        Γ ⊢ α , (e ⇒ syn) AU↦ (e' ⇒ syn) 

    data _⊢_,_AM↦_ : (Γ : Ctx) -> (α : LocalizedAction) -> (e : ExpMid) -> (e' : ExpMid) -> Set where 
      AMidAsc : ∀ {Γ α l e e' a1} ->
        Γ ⊢ (α , l) , e AL↦ e' ->
        Γ ⊢ (α , One ∷ l) , (EAsc a1 e) AM↦ (EAsc a1 e')
      AMidFun : ∀ {Γ α l e e' x t m1 m2} ->
        (x ∶ t ∷? Γ) ⊢ (α , l) , e AL↦ e' ->
        Γ ⊢ (α , One ∷ l) , (EFun x t m1 m2 e) AM↦ (EFun x t m1 m2 e')
      AMidApOne : ∀ {Γ α l e1 e2 e1' m} ->
        Γ ⊢ (α , l) , e1 AL↦ e1' ->
        Γ ⊢ (α , One ∷ l) , (EAp e1 m e2) AM↦ (EAp e1' m e2)
      AMidApTwo : ∀ {Γ α l e1 e2 e2' m} ->
        Γ ⊢ (α , l) , e2 AL↦ e2' ->
        Γ ⊢ (α , Two ∷ l) , (EAp e1 m e2) AM↦ (EAp e1 m e2')
    
    data _⊢_,_AL↦_ : (Γ : Ctx) -> (α : LocalizedAction) -> (e : ExpLow) -> (e' : ExpLow) -> Set where
      ALowDone : ∀ {Γ α e e'} ->
        Γ ⊢ α , e αL↦ e' ->
        Γ ⊢ (α , []) , e AL↦ e'
      ALowUp : ∀ {Γ α e e' m ana} ->
        Γ ⊢ α , e  AU↦ e' ->
        Γ ⊢ α , e [ m ]⇐ ana AL↦ (e' [ m ]⇐ ana)

  data _,_AP↦_ : (α : LocalizedAction) -> (p p' : Program) -> Set where
    AStepProgram : ∀{α p p'} ->
      ∅ ⊢ α , (ExpLowOfProgram p) AL↦ (ExpLowOfProgram p') ->
      α , p AP↦ p'