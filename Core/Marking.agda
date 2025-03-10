
open import Data.Product

open import Prelude
open import Core.Core

module Core.Marking where

  mutual 

    U◇ : ExpUp -> BareExp
    U◇ (e ⇒ syn) = M◇ e

    M◇ : ExpMid -> BareExp 
    M◇ EConst = BareEConst
    M◇ EHole = BareEHole
    M◇ (EVar x m) = (BareEVar x)
    M◇ (EAsc (asc , n) e) = (BareEAsc asc (L◇ e))
    M◇ (EFun x (asc , n) m1 m2 e) = (BareEFun x asc (L◇ e))
    M◇ (EAp e1 m2 e2) = (BareEAp (L◇ e1) (L◇ e2))
    M◇ (EPair e1 e2 m) = (BareEPair (L◇ e1) (L◇ e2))
    M◇ (EProj s e m) = (BareEProj s (L◇ e))
    
    L◇ : ExpLow -> BareExp
    L◇ (e [ m ]⇐ ana) = U◇ e

  P◇ : Program -> BareExp
  P◇ p = L◇ (ExpLowOfProgram p) 

  Γ◇ : Ctx -> BareCtx 
  Γ◇ ∅ = ∅
  Γ◇ (x ∶ t , _ ∷ Γ) = x ∶ t ∷ Γ◇ Γ

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
      MarkSynPair : ∀ {Γ b1 b2 e1 e2 t1 t2} ->
        Γ ⊢ b1 ~> e1 ⇒ t1 ->
        Γ ⊢ b2 ~> e2 ⇒ t2 ->
        Γ ⊢ (BareEPair b1 b2) ~> ((EPair (e1  [ ✔ ]⇐ (□ , Old)) (e2 [ ✔ ]⇐ (□ , Old)) ✔) ⇒ ((■ (TProd t1 t2) , Old))) ⇒ (TProd t1 t2)
      MarkProj : ∀ {Γ b e t s t-side m} ->
        Γ ⊢ b ~> e ⇒ t ->
        t , s ▸TProj t-side , m ->
        Γ ⊢ (BareEProj s b) ~> ((EProj s (e [ ✔ ]⇐ (□ , Old)) m) ⇒ ((■ t-side , Old))) ⇒ t-side

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
      MarkAnaPair : ∀ {Γ b1 b2 e1 e2 t-fst t-snd t-ana m-ana} ->
        t-ana ▸TProd t-fst , t-snd , m-ana ->
        Γ ⊢ b1 ~> e1 ⇐ t-fst ->
        Γ ⊢ b2 ~> e2 ⇐ t-snd ->
        Γ ⊢ (BareEPair b1 b2) ~> (((EPair e1 e2 m-ana) ⇒ (□ , Old)) [ ✔ ]⇐ ((■ t-ana , Old))) ⇐ t-ana

  data _~>_ : BareExp -> Program -> Set where 
    MarkProgram : ∀ {b e t} ->
      ∅ ⊢ b ~> e ⇒ t -> 
      b ~> (Root e Old) 