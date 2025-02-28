
open import Data.Product

open import Prelude
open import Core.Core

module Core.Marking where

  mutual 

    -- U◇ : ExpUp -> BareExp
    -- U◇ (e ⇒ syn) = M◇ e

    M◇ : ExpMid -> BareExp 
    M◇ EConst = BareEConst
    M◇ EHole = BareEHole
    M◇ (EVar x m) = (BareEVar x)
    M◇ (EAsc (asc , n) e) = (BareEAsc asc (L◇ e))
    M◇ (EFun x (asc , n) m1 m2 e) = (BareEFun x asc (L◇ e))
    M◇ (EAp e1 m2 e2) = (BareEAp (L◇ e1) (L◇ e2))
    
    L◇ : ExpLow -> BareExp
    L◇ (ana ⇒ e ⇒ syn [ m ]) = M◇ e

  P◇ : Program -> BareExp
  P◇ p = L◇ (ExpLowOfProgram p) 

  Γ◇ : Ctx -> BareCtx 
  Γ◇ ∅ = ∅
  Γ◇ (x ∶ t , _ ∷ Γ) = x ∶ t ∷ Γ◇ Γ

  mutual 

    data _⊢_~>_⇒_ : (Γ : BareCtx) (b : BareExp) (e : ExpMid) (t : Type) → Set where 
      MarkConst : ∀ {Γ} →
        Γ ⊢ BareEConst ~> EConst ⇒ TBase
      MarkHole : ∀ {Γ} →
        Γ ⊢ BareEHole ~> EHole ⇒ THole
      MarkSynFun : ∀ {Γ x b-body e-body t-asc t-body} ->
        (x ∶ t-asc ∷? Γ) ⊢ b-body ~> e-body ⇒ t-body ->
        Γ ⊢ (BareEFun x t-asc b-body) ~> (EFun x (t-asc , Old) (✔) (✔) ((□ , Old) ⇒ e-body ⇒ (■ t-body , Old) [ ✔ ])) ⇒ (TArrow t-asc t-body)
      MarkAp : ∀ {Γ b-fun b-arg e-fun e-arg t-fun t-in-fun t-out-fun m-fun} ->
        Γ ⊢ b-fun ~> e-fun ⇒ t-fun ->
        t-fun ▸TArrow t-in-fun , t-out-fun , m-fun ->
        Γ ⊢ b-arg ~> e-arg ⇐ t-in-fun ->
        Γ ⊢ (BareEAp b-fun b-arg) ~> (EAp ((□ , Old) ⇒ e-fun ⇒ (■ t-fun , Old) [ ✔ ]) m-fun e-arg) ⇒ t-out-fun
      MarkVar : ∀ {Γ x t-var m-var} ->
        x , t-var ∈ Γ , m-var ->
        Γ ⊢ (BareEVar x) ~> ((EVar x (m-var))) ⇒ t-var
      MarkAsc : ∀ {Γ b-body e-body t-asc} ->
        Γ ⊢ b-body ~> e-body ⇐ t-asc ->
        Γ ⊢ (BareEAsc t-asc b-body) ~> (EAsc (t-asc , Old) e-body) ⇒ t-asc

    data _⊢_~>_⇐_ : (Γ : BareCtx) (b : BareExp) (e : ExpLow) (t : Type) → Set where  
      MarkSubsume : ∀ {Γ b-all e-all t-syn t-ana m-all} ->
        Γ ⊢ b-all ~> e-all ⇒ t-syn ->
        BareSubsumable b-all ->
        t-syn ~ t-ana , m-all ->
        Γ ⊢ b-all ~> ((■ t-ana , Old) ⇒ e-all ⇒ (■ t-syn , Old) [ m-all ]) ⇐ t-ana
      MarkAnaFun : ∀ {Γ x b-body e-body t-asc t-ana t-in-ana t-out-ana m-ana m-asc} ->
        t-ana ▸TArrow t-in-ana , t-out-ana , m-ana ->
        (x ∶ t-asc ∷? Γ) ⊢ b-body ~> e-body ⇐ t-out-ana ->
        t-asc ~ t-in-ana , m-asc ->
        Γ ⊢ (BareEFun x t-asc b-body) ~> ((■ t-ana , Old) ⇒ (EFun x (t-asc , Old) (m-ana) (m-asc) e-body) ⇒ (□ , Old) [ ✔ ]) ⇐ t-ana
    
  data _~>_ : BareExp -> Program -> Set where 
    MarkProgram : ∀ {b e t} ->
      ∅ ⊢ b ~> e ⇒ t -> 
      b ~> (Root Old e (■ t , Old)) 