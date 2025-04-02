
open import Data.Product

open import Prelude
open import Core.Core
open import Core.SideConditions

module Core.Marking where

  T◇ : Type -> BareType 
  T◇ TBase = BareTBase
  T◇ THole = BareTHole
  T◇ (TArrow t1 t2) = BareTArrow (T◇ t1) (T◇ t2)
  T◇ (TProd t1 t2) = BareTProd (T◇ t1) (T◇ t2)
  T◇ (TVar x m) = BareTVar x
  T◇ (TForall x t) = BareTForall x (T◇ t)

  mutual 

    U◇ : SynExp -> BareExp
    U◇ (e ⇒ syn) = M◇ e

    M◇ : ConExp -> BareExp 
    M◇ EConst = BareEConst
    M◇ EHole = BareEHole
    M◇ (EVar x m) = (BareEVar x)
    M◇ (EAsc (asc , n) e) = (BareEAsc (T◇ asc) (L◇ e))
    M◇ (EFun x (ann , n) m1 m2 e) = (BareEFun x (T◇ ann) (L◇ e))
    M◇ (EAp e1 m2 e2) = (BareEAp (L◇ e1) (L◇ e2))
    M◇ (EPair e1 e2 m) = (BareEPair (L◇ e1) (L◇ e2))
    M◇ (EProj s e m) = (BareEProj s (L◇ e))
    
    L◇ : AnaExp -> BareExp
    L◇ (e [ m ]⇐ ana) = U◇ e

  P◇ : Program -> BareExp
  P◇ p = L◇ (AnaExpOfProgram p) 

  Γ◇ : Ctx -> BareCtx 
  Γ◇ ∅ = ∅
  Γ◇ (x ∶ t , _ ∷ Γ) = x ∶ t ∷ Γ◇ Γ
  Γ◇ (x T∷ Γ) = x T∷ Γ◇ Γ

  data _⊢_T~>_ : (Γ : BareCtx) (b : BareType) (t : Type) → Set where 
    MarkBase : ∀ {Γ} -> 
      Γ ⊢ BareTBase T~> TBase
    MarkHole : ∀ {Γ} -> 
      Γ ⊢ BareTHole T~> THole
    MarkArrow : ∀ {Γ b1 b2 t1 t2} -> 
      Γ ⊢ b1 T~> t1 -> 
      Γ ⊢ b2 T~> t2 -> 
      Γ ⊢ BareTArrow b1 b2 T~> TArrow t1 t2
    MarkProd : ∀ {Γ b1 b2 t1 t2} -> 
      Γ ⊢ b1 T~> t1 -> 
      Γ ⊢ b2 T~> t2 -> 
      Γ ⊢ BareTProd b1 b2 T~> TProd t1 t2
    MarkTVar : ∀ {Γ x m} -> 
      x T∈ Γ , m ->
      Γ ⊢ BareTVar x T~> TVar x m
    MarkForall : ∀ {Γ x b t} -> 
      (x T∷? Γ) ⊢ b T~> t ->
      Γ ⊢ BareTForall x b T~> TForall x t

  -- mutual 

  --   data _⊢_~>_⇒_ : (Γ : BareCtx) (b : BareExp) (e : SynExp) (t : Type) → Set where 
  --     MarkConst : ∀ {Γ} →
  --       Γ ⊢ BareEConst ~> (EConst ⇒ ((■ TBase , •))) ⇒ TBase
  --     MarkHole : ∀ {Γ} →
  --       Γ ⊢ BareEHole ~> (EHole ⇒ ((■ THole , •))) ⇒ THole
  --     MarkSynFun : ∀ {Γ x b-body e-body t-asc t-body} ->
  --       (x ∶ t-asc ∷? Γ) ⊢ b-body ~> e-body ⇒ t-body ->
  --       Γ ⊢ (BareEFun x t-asc b-body) ~> ((EFun x (t-asc , •) (✔) (✔) (e-body [ ✔ ]⇐ (□ , •))) ⇒ ((■ (TArrow t-asc t-body) , •))) ⇒ (TArrow t-asc t-body)
  --     MarkAp : ∀ {Γ b-fun b-arg e-fun e-arg t-fun t-in-fun t-out-fun m-fun} ->
  --       Γ ⊢ b-fun ~> e-fun ⇒ t-fun ->
  --       t-fun ▸TArrow t-in-fun , t-out-fun , m-fun ->
  --       Γ ⊢ b-arg ~> e-arg ⇐ t-in-fun ->
  --       Γ ⊢ (BareEAp b-fun b-arg) ~> ((EAp (e-fun [ ✔ ]⇐ (□ , •)) (m-fun) e-arg) ⇒ ((■ t-out-fun , •))) ⇒ t-out-fun
  --     MarkVar : ∀ {Γ x t-var m-var} ->
  --       x , t-var ∈ Γ , m-var ->
  --       Γ ⊢ (BareEVar x) ~> ((EVar x (m-var)) ⇒ ((■ t-var , •))) ⇒ t-var
  --     MarkAsc : ∀ {Γ b-body e-body t-asc} ->
  --       Γ ⊢ b-body ~> e-body ⇐ t-asc ->
  --       Γ ⊢ (BareEAsc t-asc b-body) ~> ((EAsc (t-asc , •) e-body) ⇒ ((■ t-asc , •))) ⇒ t-asc
  --     MarkSynPair : ∀ {Γ b1 b2 e1 e2 t1 t2} ->
  --       Γ ⊢ b1 ~> e1 ⇒ t1 ->
  --       Γ ⊢ b2 ~> e2 ⇒ t2 ->
  --       Γ ⊢ (BareEPair b1 b2) ~> ((EPair (e1  [ ✔ ]⇐ (□ , •)) (e2 [ ✔ ]⇐ (□ , •)) ✔) ⇒ ((■ (TProd t1 t2) , •))) ⇒ (TProd t1 t2)
  --     MarkProj : ∀ {Γ b e t s t-side m} ->
  --       Γ ⊢ b ~> e ⇒ t ->
  --       t , s ▸TProj t-side , m ->
  --       Γ ⊢ (BareEProj s b) ~> ((EProj s (e [ ✔ ]⇐ (□ , •)) m) ⇒ ((■ t-side , •))) ⇒ t-side

  --   data _⊢_~>_⇐_ : (Γ : BareCtx) (b : BareExp) (e : AnaExp) (t : Type) → Set where  
  --     MarkSubsume : ∀ {Γ b-all e-all t-syn t-ana m-all} ->
  --       Γ ⊢ b-all ~> e-all ⇒ t-syn ->
  --       BareSubsumable b-all ->
  --       t-syn ~ t-ana , m-all ->
  --       Γ ⊢ b-all ~> (e-all [ (m-all) ]⇐ ((■ t-ana , •))) ⇐ t-ana
  --     MarkAnaFun : ∀ {Γ x b-body e-body t-asc t-ana t-in-ana t-out-ana m-ana m-asc} ->
  --       t-ana ▸TArrow t-in-ana , t-out-ana , m-ana ->
  --       (x ∶ t-asc ∷? Γ) ⊢ b-body ~> e-body ⇐ t-out-ana ->
  --       t-asc ~ t-in-ana , m-asc ->
  --       Γ ⊢ (BareEFun x t-asc b-body) ~> (((EFun x (t-asc , •) (m-ana) (m-asc) e-body) ⇒ (□ , •)) [ ✔ ]⇐ ((■ t-ana , •))) ⇐ t-ana
  --     MarkAnaPair : ∀ {Γ b1 b2 e1 e2 t-fst t-snd t-ana m-ana} ->
  --       t-ana ▸TProd t-fst , t-snd , m-ana ->
  --       Γ ⊢ b1 ~> e1 ⇐ t-fst ->
  --       Γ ⊢ b2 ~> e2 ⇐ t-snd ->
  --       Γ ⊢ (BareEPair b1 b2) ~> (((EPair e1 e2 m-ana) ⇒ (□ , •)) [ ✔ ]⇐ ((■ t-ana , •))) ⇐ t-ana

  -- data _~>_ : BareExp -> Program -> Set where 
  --   MarkProgram : ∀ {b e t} ->
  --     ∅ ⊢ b ~> e ⇒ t -> 
  --     b ~> (Root e •) 