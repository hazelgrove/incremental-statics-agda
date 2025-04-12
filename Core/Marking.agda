
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
    M◇ (EVar x _) = (BareEVar x)
    M◇ (EAsc (t , _) e) = (BareEAsc (T◇ t) (L◇ e))
    M◇ (EFun x (t , _) _ _ e) = (BareEFun x (T◇ t) (L◇ e))
    M◇ (EAp e1 _ e2) = (BareEAp (L◇ e1) (L◇ e2))
    M◇ (EPair e1 e2 _) = (BareEPair (L◇ e1) (L◇ e2))
    M◇ (EProj s e _) = (BareEProj s (L◇ e))
    M◇ (ETypFun x _ e) = BareETypFun x (L◇ e)
    M◇ (ETypAp e _ (t , _)) = BareETypAp (L◇ e) (T◇ t)
    
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

  mutual 

    data _⊢_~>_⇒_ : (Γ : BareCtx) (b : BareExp) (e : SynExp) (t : Type) → Set where 
      MarkConst : ∀ {Γ} →
        Γ ⊢ BareEConst ~> (EConst ⇒ ((■ TBase , •))) ⇒ TBase
      MarkHole : ∀ {Γ} →
        Γ ⊢ BareEHole ~> (EHole ⇒ ((■ THole , •))) ⇒ THole
      MarkSynFun : ∀ {Γ x b-body e-body b-ann t-ann t-body} ->
        Γ ⊢ b-ann T~> t-ann ->
        (x ∶ t-ann ∷? Γ) ⊢ b-body ~> e-body ⇒ t-body ->
        Γ ⊢ (BareEFun x b-ann b-body) ~> ((EFun x (t-ann , •) ✔ ✔ (e-body [ ✔ ]⇐ (□ , •))) ⇒ ((■ (TArrow t-ann t-body) , •))) ⇒ (TArrow t-ann t-body)
      MarkAp : ∀ {Γ b-fun b-arg e-fun e-arg t-fun t-in-fun t-out-fun m-fun} ->
        Γ ⊢ b-fun ~> e-fun ⇒ t-fun ->
        t-fun ▸TArrow t-in-fun , t-out-fun , m-fun ->
        Γ ⊢ b-arg ~> e-arg ⇐ t-in-fun ->
        Γ ⊢ (BareEAp b-fun b-arg) ~> ((EAp (e-fun [ ✔ ]⇐ (□ , •)) (m-fun) e-arg) ⇒ ((■ t-out-fun , •))) ⇒ t-out-fun
      MarkVar : ∀ {Γ x t-var m-var} ->
        x , t-var ∈ Γ , m-var ->
        Γ ⊢ (BareEVar x) ~> ((EVar x (m-var)) ⇒ ((■ t-var , •))) ⇒ t-var
      MarkAsc : ∀ {Γ b-body e-body b-asc t-asc} ->
        Γ ⊢ b-asc T~> t-asc ->
        Γ ⊢ b-body ~> e-body ⇐ t-asc ->
        Γ ⊢ (BareEAsc b-asc b-body) ~> ((EAsc (t-asc , •) e-body) ⇒ ((■ t-asc , •))) ⇒ t-asc
      MarkSynPair : ∀ {Γ b1 b2 e1 e2 t1 t2} ->
        Γ ⊢ b1 ~> e1 ⇒ t1 ->
        Γ ⊢ b2 ~> e2 ⇒ t2 ->
        Γ ⊢ (BareEPair b1 b2) ~> ((EPair (e1  [ ✔ ]⇐ (□ , •)) (e2 [ ✔ ]⇐ (□ , •)) ✔) ⇒ ((■ (TProd t1 t2) , •))) ⇒ (TProd t1 t2)
      MarkProj : ∀ {Γ b e t s t-side m} ->
        Γ ⊢ b ~> e ⇒ t ->
        t , s ▸TProj t-side , m ->
        Γ ⊢ (BareEProj s b) ~> ((EProj s (e [ ✔ ]⇐ (□ , •)) m) ⇒ ((■ t-side , •))) ⇒ t-side
      MarkSynTypFun : ∀ {Γ x b-body e-body t-body} ->
        (x T∷? Γ) ⊢ b-body ~> e-body ⇒ t-body ->
        Γ ⊢ (BareETypFun x b-body) ~> ((ETypFun x ✔ (e-body [ ✔ ]⇐ (□ , •))) ⇒ ((■ (TForall x t-body) , •))) ⇒ (TForall x t-body)
      MarkTypAp : ∀ {Γ b-fun b-arg e-fun t-arg t-fun t-fun-body m-fun x t-syn} ->
        Γ ⊢ b-fun ~> e-fun ⇒ t-fun ->
        t-fun ▸TForall x , t-fun-body , m-fun ->
        Γ ⊢ b-arg T~> t-arg ->
        Sub t-arg x t-fun-body t-syn ->
        Γ ⊢ (BareETypAp b-fun b-arg) ~> ((ETypAp (e-fun [ ✔ ]⇐ (□ , •)) m-fun (t-arg , •)) ⇒ ((■ t-syn , •))) ⇒ t-syn

    data _⊢_~>_⇐_ : (Γ : BareCtx) (b : BareExp) (e : AnaExp) (t : Type) → Set where  
      MarkSubsume : ∀ {Γ b-all e-all t-syn t-ana m-all} ->
        Γ ⊢ b-all ~> e-all ⇒ t-syn ->
        BareSubsumable b-all ->
        t-syn ~ t-ana , m-all ->
        Γ ⊢ b-all ~> (e-all [ (m-all) ]⇐ ((■ t-ana , •))) ⇐ t-ana
      MarkAnaFun : ∀ {Γ x b-body e-body b-ann t-ann t-ana t-in-ana t-out-ana m-ana m-ann} ->
        Γ ⊢ b-ann T~> t-ann ->
        t-ana ▸TArrow t-in-ana , t-out-ana , m-ana ->
        (x ∶ t-ann ∷? Γ) ⊢ b-body ~> e-body ⇐ t-out-ana ->
        t-ann ~ t-in-ana , m-ann ->
        Γ ⊢ (BareEFun x b-ann b-body) ~> (((EFun x (t-ann , •) m-ana m-ann e-body) ⇒ (□ , •)) [ ✔ ]⇐ ((■ t-ana , •))) ⇐ t-ana
      MarkAnaPair : ∀ {Γ b1 b2 e1 e2 t-fst t-snd t-ana m-ana} ->
        t-ana ▸TProd t-fst , t-snd , m-ana ->
        Γ ⊢ b1 ~> e1 ⇐ t-fst ->
        Γ ⊢ b2 ~> e2 ⇐ t-snd ->
        Γ ⊢ (BareEPair b1 b2) ~> (((EPair e1 e2 m-ana) ⇒ (□ , •)) [ ✔ ]⇐ ((■ t-ana , •))) ⇐ t-ana
      MarkAnaTypFun : ∀ {Γ x b-body e-body t-ana t-body-ana m-ana} ->
        t-ana , x ▸TForallBind t-body-ana , m-ana ->
        (x T∷? Γ) ⊢ b-body ~> e-body ⇐ t-body-ana ->
        Γ ⊢ (BareETypFun x b-body) ~> (((ETypFun x m-ana e-body) ⇒ (□ , •)) [ ✔ ]⇐ ((■ t-ana , •))) ⇐ t-ana

  data _~>_ : BareExp -> Program -> Set where 
    MarkProgram : ∀ {b e t} ->
      ∅ ⊢ b ~> e ⇒ t -> 
      b ~> (Root e •) 