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

  data BarrenExpUp : ExpUp -> BareExp -> Set where 
    BarrenUp : ∀ {e b syn} ->
      BarrenExpMid e b ->
      BarrenExpUp (e ⇒ syn) b

  data BarrenExpMid : ExpMid -> BareExp -> Set where 
    BarrenConst : 
      BarrenExpMid EConst BareEConst
    BarrenHole :
      BarrenExpMid EHole BareEHole
    BarrenFun : ∀ {asc n m1 m2 e b} -> 
      BarrenExpLow e b ->
      BarrenExpMid (EFun (asc , n) m1 m2 e) (BareEFun asc b)
    BarrenAp : ∀ {m2 e1 e2 b1 b2} -> 
      BarrenExpLow e1 b1 ->
      BarrenExpLow e2 b2 ->
      BarrenExpMid (EAp e1 m2 e2) (BareEAp b1 b2)
    BarrenVar : ∀ {x m} -> 
      BarrenExpMid (EVar x m) (BareEVar x)
    BarrenAsc : ∀ {asc n e b} -> 
      BarrenExpLow e b ->
      BarrenExpMid (EAsc (asc , n) e) (BareEAsc asc b)

  data BarrenExpLow : ExpLow -> BareExp -> Set where 
    BarrenLow : ∀ {e b ana m} ->
      BarrenExpUp e b ->
      BarrenExpLow (e [ m ]⇐ ana) b

data BarrenProgram : Program -> BareProgram -> Set where 
  BarrenP : ∀ {e b} ->
    BarrenExpUp e b -> 
    BarrenProgram (Root e) (BareRoot b)

BareCtx : Set 
BareCtx = Context Type

data _,_∈_,_ : ℕ -> Type -> BareCtx -> Mark -> Set where 
  InCtxEmpty : 
    0 , THole ∈ ∅ , ✖ 
  InCtxFound : ∀ {Γ t} -> 
    0 , t ∈ (t ∷ Γ) , ✔
  InCtxSkip : ∀ {Γ t t' x m} -> 
    (x , t ∈ Γ , m) -> 
    (suc x , t ∈ (t' ∷ Γ) , m)

-- This version of marking uses side conditions (matched arrow, consistency, or 
-- variable lookup in the context) that are total functions which also return a
-- mark bit. This allows a single rule to be used per syntactic form, rather 
-- than having multiple cases. See the variable lookup above for example.

mutual 
  data _⊢_~>_⇒_ : (Γ : BareCtx) (b : BareExp) (e : ExpUp) (t : Type) → Set where 
    MarkConst : ∀ {Γ} →
      Γ ⊢ BareEConst ~> (EConst ⇒ ((■ TBase , Old))) ⇒ TBase
    MarkHole : ∀ {Γ} →
      Γ ⊢ BareEHole ~> (EHole ⇒ ((■ THole , Old))) ⇒ THole
    MarkSynFun : ∀ {Γ b-body e-body t-asc t-body} ->
      (t-asc ∷ Γ) ⊢ b-body ~> e-body ⇒ t-body ->
      Γ ⊢ (BareEFun t-asc b-body) ~> ((EFun (t-asc , Old) (✔) (✔) (e-body [ ✔ ]⇐ (□ , Old))) ⇒ ((■ (TArrow t-asc t-body) , Old))) ⇒ (TArrow t-asc t-body)
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
    MarkAnaFun : ∀ {Γ b-body e-body t-asc t-ana t-in-ana t-out-ana m-ana m-asc} ->
      t-ana ▸TArrow t-in-ana , t-out-ana , m-ana ->
      (t-asc ∷ Γ) ⊢ b-body ~> e-body ⇐ t-out-ana ->
      t-asc ~ t-in-ana , m-asc ->
      Γ ⊢ (BareEFun t-asc b-body) ~> (((EFun (t-asc , Old) (m-ana) (m-asc) e-body) ⇒ (□ , Old)) [ ✔ ]⇐ ((■ t-ana , Old))) ⇐ t-ana
  
data _~>_⇒_ : BareProgram -> Program -> Type -> Set where 
  MarkProgram : ∀ {b e t} ->
    ∅ ⊢ b ~> e ⇒ t -> 
    (BareRoot b) ~> (Root e) ⇒ t 