open import Data.Nat hiding (_+_)
open import Data.Unit 
open import Data.Bool hiding (_<_; _≟_)
open import Data.Sum renaming (_⊎_ to _+_; inj₁ to Inl ; inj₂ to Inr) hiding (map)
open import Data.Product hiding (map)
open import Relation.Nullary 
open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Prelude

open import Core.Core

module Core.Marking where

  mutual 

    EraseUp : ExpUp -> BareExp
    EraseUp (e ⇒ syn) = EraseMid e

    EraseMid : ExpMid -> BareExp 
    EraseMid EConst = BareEConst
    EraseMid EHole = BareEHole
    EraseMid (EVar x m) = (BareEVar x)
    EraseMid (EAsc (asc , n) e) = (BareEAsc asc (EraseLow e))
    EraseMid (EFun x (asc , n) m1 m2 e) = (BareEFun x asc (EraseLow e))
    EraseMid (EAp e1 m2 e2) = (BareEAp (EraseLow e1) (EraseLow e2))
    
    EraseLow : ExpLow -> BareExp
    EraseLow (e [ m ]⇐ ana) = EraseUp e

  EraseProgram : Program -> BareExp
  EraseProgram p = EraseLow (ExpLowOfProgram p) 

  EraseCtx : Ctx -> BareCtx 
  EraseCtx ∅ = ∅
  EraseCtx (x ∶ t , _ ∷ Γ) = x ∶ t ∷ EraseCtx Γ

  mutual 

    data _⊢_~>_⇒_ : (Γ : BareCtx) (b : BareExp) (e : ExpUp) (t : Type) → Set where 
      MarkConst : ∀ {Γ} →
        Γ ⊢ BareEConst ~> (EConst ⇒ ((■ TBase , Old))) ⇒ TBase
      MarkHole : ∀ {Γ} →
        Γ ⊢ BareEHole ~> (EHole ⇒ ((■ THole , Old))) ⇒ THole
      MarkSynFun : ∀ {Γ x b-body e-body t-asc t-body} ->
        (x ∶ t-asc ∷? Γ) ⊢ b-body ~> e-body ⇒ t-body ->
        Γ ⊢ (BareEFun x t-asc b-body) ~> ((EFun x (t-asc , Old) (✔) (✔) (e-body [ ✔ ]⇐ (□ , Old))) ⇒ ((■ (TArrow t-asc t-body) , Old))) ⇒ (TArrow t-asc t-body)
      MarkAp : ∀ {Γ b-fun b-arg e-fun e-arg t-fun t-in-fun t-out-fun m-fun} ->
        Γ ⊢ b-fun ~> e-fun ⇒ t-fun ->
        t-fun ▸TArrow t-in-fun , t-out-fun , m-fun ->
        Γ ⊢ b-arg ~> e-arg ⇐ t-in-fun ->
        Γ ⊢ (BareEAp b-fun b-arg) ~> ((EAp (e-fun [ ✔ ]⇐ (□ , Old)) (m-fun) e-arg) ⇒ ((■ t-out-fun , Old))) ⇒ t-out-fun
      MarkVar : ∀ {Γ x t-var m-var} ->
        x , t-var ∈ Γ , m-var ->
        Γ ⊢ (BareEVar x) ~> ((EVar x (m-var)) ⇒ ((■ t-var , Old))) ⇒ t-var
      MarkAsc : ∀ {Γ b-body e-body t-asc} ->
        Γ ⊢ b-body ~> e-body ⇐ t-asc ->
        Γ ⊢ (BareEAsc t-asc b-body) ~> ((EAsc (t-asc , Old) e-body) ⇒ ((■ t-asc , Old))) ⇒ t-asc

    data _⊢_~>_⇐_ : (Γ : BareCtx) (b : BareExp) (e : ExpLow) (t : Type) → Set where  
      MarkSubsume : ∀ {Γ b-all e-all t-syn t-ana m-all} ->
        Γ ⊢ b-all ~> e-all ⇒ t-syn ->
        BareSubsumable b-all ->
        t-syn ~ t-ana , m-all ->
        Γ ⊢ b-all ~> (e-all [ (m-all) ]⇐ ((■ t-ana , Old))) ⇐ t-ana
      MarkAnaFun : ∀ {Γ x b-body e-body t-asc t-ana t-in-ana t-out-ana m-ana m-asc} ->
        t-ana ▸TArrow t-in-ana , t-out-ana , m-ana ->
        (x ∶ t-asc ∷? Γ) ⊢ b-body ~> e-body ⇐ t-out-ana ->
        t-asc ~ t-in-ana , m-asc ->
        Γ ⊢ (BareEFun x t-asc b-body) ~> (((EFun x (t-asc , Old) (m-ana) (m-asc) e-body) ⇒ (□ , Old)) [ ✔ ]⇐ ((■ t-ana , Old))) ⇐ t-ana
    
  data _~>_ : BareExp -> Program -> Set where 
    MarkProgram : ∀ {b e t} ->
      ∅ ⊢ b ~> e ⇒ t -> 
      b ~> (Root e Old) 