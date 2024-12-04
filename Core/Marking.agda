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

  data BarrenExp : ExpUp -> BareExp -> Set where 
    BarrenConst : ∀ {syn} → 
      BarrenExp (EUp syn EConst) BareEConst
    BarrenHole : ∀ {syn} → 
      BarrenExp (EUp syn EHole) BareEHole
    BarrenFun : ∀ {syn asc n m1 e b} → 
      BarrenExpLow e b ->
      BarrenExp (EUp syn (EFun (asc , n) m1 e)) (BareEFun asc b)
    BarrenAp : ∀ {syn ana1 m1 m2 e1 e2 b1 b2} → 
      BarrenExp e1 b1 ->
      BarrenExpLow e2 b2 ->
      BarrenExp (EUp syn (EAp (ELow ana1 m1 e1) m2 e2)) (BareEAp b1 b2)
    BarrenVar : ∀ {syn x m} → 
      BarrenExp (EUp syn (EVar x m)) (BareEVar x)
    BarrenAsc : ∀ {syn asc n e b} → 
      BarrenExpLow e b ->
      BarrenExp (EUp syn (EAsc (asc , n) e)) (BareEAsc asc b)

  data BarrenExpLow : ExpLow -> BareExp -> Set where 
    BarrenLow : ∀ {e b ana m} ->
      BarrenExp e b ->
      BarrenExpLow (ELow ana m e) b

BareCtx : Set 
BareCtx = Context Type

mutual 
  data _⊢_~>_⇒_ : (Γ : BareCtx) (b : BareExp) (e : ExpUp) (t : Type) → Set where 
    MarkConst : ∀ {Γ} →
      Γ ⊢ BareEConst ~> (EUp (⇑ (TBase , Old)) EConst) ⇒ TBase
    MarkHole : ∀ {Γ} →
      Γ ⊢ BareEHole ~> (EUp (⇑ (THole , Old)) EHole) ⇒ THole
    MarkSynFun : ∀ {Γ t1 t2 b e} ->
      (t1 , Γ) ⊢ b ~> e ⇒ t2 ->
      Γ ⊢ (BareEFun t1 b) ~> (EUp (⇑ (TArrow t1 t2 , Old)) (EFun (t1 , Old) Unmarked (ELow ̸⇓ Unmarked e))) ⇒ (TArrow t1 t2)
    MarkAp : ∀ {Γ  b1 b2 e1 e2 t t1 t2} ->
      Γ ⊢ b1 ~> e1 ⇒ t ->
      t ▸TArrow t1 , t2 ->
      Γ ⊢ b2 ~> e2 ⇐ t1 ->
      Γ ⊢ (BareEAp b1 b2) ~> (EUp (⇑ (t2 , Old)) (EAp (ELow ̸⇓ Unmarked e1) Unmarked e2)) ⇒ t2
    MarkApFail : ∀ {Γ b1 b2 e1 e2 t} ->
      Γ ⊢ b1 ~> e1 ⇒ t ->
      t ̸▸TArrow ->
      Γ ⊢ b2 ~> e2 ⇐ THole ->
      Γ ⊢ (BareEAp b1 b2) ~> (EUp (⇑ (THole , Old)) (EAp (ELow ̸⇓ Unmarked e1) Marked e2)) ⇒ THole
    MarkVar : ∀ {Γ x t} ->
      x , t ∈ Γ ->
      Γ ⊢ (BareEVar x) ~> (EUp (⇑ (t , Old)) (EVar x Unmarked)) ⇒ t
    MarkVarFail : ∀ {Γ x} ->
      x ̸∈ Γ ->
      Γ ⊢ (BareEVar x) ~> (EUp (⇑ (THole , Old)) (EVar x Marked)) ⇒ THole
    MarkAsc : ∀ {Γ b t e} ->
      Γ ⊢ b ~> e ⇐ t ->
      Γ ⊢ (BareEAsc t b) ~> (EUp (⇑ (t , Old)) (EAsc (t , Old) e)) ⇒ t

  data _⊢_~>_⇐_ : (Γ : BareCtx) (b : BareExp) (e : ExpLow) (t : Type) → Set where  
    MarkSubsume : ∀ {Γ b e t1 t2} ->
      Γ ⊢ b ~> e ⇒ t1 ->
      BareSubsumable b ->
      (t1 ~ t2) ->
      Γ ⊢ b ~> (ELow (⇓ (t2 , Old)) Unmarked e) ⇐ t2
    MarkSubsumeFail : ∀ {Γ b e t1 t2} ->
      Γ ⊢ b ~> e ⇒ t1 ->
      BareSubsumable b ->
      ¬(t1 ~ t2) ->
      Γ ⊢ b ~> (ELow (⇓ (t2 , Old)) Marked e) ⇐ t2
    MarkAnaFun : ∀ {Γ t t1 t2 tasc b e} ->
      t ▸TArrow t1 , t2 ->
      (tasc , Γ) ⊢ b ~> e ⇐ t2 ->
      (tasc ~ t1) ->
      Γ ⊢ (BareEFun tasc b) ~> (ELow (⇓ (t , Old)) Unmarked (EUp ̸⇑ (EFun (tasc , Old) Unmarked e))) ⇐ t
    MarkAnaFunFail1 : ∀ {Γ t t1 t2 tasc b e} ->
      t ▸TArrow t1 , t2 ->
      (tasc , Γ) ⊢ b ~> e ⇐ t2 ->
      ¬(tasc ~ t1) ->
      Γ ⊢ (BareEFun tasc b) ~> (ELow (⇓ (t , Old)) Unmarked (EUp ̸⇑ (EFun (tasc , Old) Marked e))) ⇐ t
    -- Paper version: analyzes the body against ? if the lambda analyzed against non-arrow
    -- My version:
    MarkAnaFunFail2 : ∀ {Γ t t1 t2 b e} ->
      t ̸▸TArrow ->
      (t1 , Γ) ⊢ b ~> e ⇒ t2 ->
      Γ ⊢ (BareEFun t1 b) ~> (ELow (⇓ (t , Old)) Marked (EUp (⇑ (TArrow t1 t2 , Old)) (EFun (t1 , Old) Unmarked (ELow ̸⇓ Unmarked e)))) ⇐ t
