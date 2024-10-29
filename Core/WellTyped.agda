open import Data.Nat hiding (_+_)
open import Data.Unit 
open import Data.Bool hiding (_<_; _≟_)
open import Data.Sum renaming (_⊎_ to _+_; inj₁ to Inl ; inj₂ to Inr) hiding (map)
open import Data.Product hiding (map)
open import Relation.Nullary 
open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Prelude

open import Core.Core

module Core.WellTyped where

-- MergeInfo (t1 , n1) (t2 , n2) (t3 , n3) holds with:
-- (t1 , n1) is the stored info
-- (t2 , n2) is the calculated true info 
-- (t3 , n3) is the info that should be passed along
-- and ensures that the stored info is compatible with the real info.
-- This is the case when t1 and t2 are the same at the points where n2 is old. 
-- Where n2 is all new, the "real" info hasn't been propagated yet and doesn't 
-- need to have been stored already. It doesn't matter whether n1 is new or old. 

data MergeInfo : NewType -> NewType -> NewType -> Set where 
  MergeInfoNew : ∀ {t1 t2 n1} -> 
    MergeInfo (t1 , n1) (t2 , New) (t2 , New)
  MergeInfoOld : ∀ {t1 n1} -> 
    MergeInfo (t1 , n1) (t1 , Old) (t1 , n1)
  MergeInfoArrow : ∀ {t1 t2 t3 t4 t5 t6 n n1 n2 n3 n4 n5 n6 n7} -> 
    n ▸NArrow n1 , n2 ->
    MergeInfo (t1 , n1) (t3 , n3) (t5 , n5) ->
    MergeInfo (t2 , n2) (t4 , n4) (t6 , n6) ->
    narrow n5 n6 ≡ n7 ->
    MergeInfo (TArrow t1 t2 , n) (TArrow t3 t4 , NArrow n3 n4) (TArrow t5 t6 , n7)

data MergeSyn : SynData -> NewType -> NewType -> Set where 
  MergeSynVoid : ∀ {syn} -> 
    MergeSyn ̸⇑ syn syn
  MergeSynMerge : ∀ {syn1 syn2 syn3} -> 
    MergeInfo syn1 syn2 syn3 ->
    MergeSyn (⇑ syn1) syn2 syn3

data MergeAna : AnaData -> NewType -> NewType -> Set where 
  MergeAnaVoid : ∀ {ana} -> 
    MergeAna ̸⇓ ana ana
  MergeAnaMerge : ∀ {ana1 ana2 ana3} -> 
    MergeInfo ana1 ana2 ana3 ->
    MergeAna (⇓ ana1) ana2 ana3

mutual 
  data _⊢_⇒_ : (Γ : Ctx) (e : ExpUp) (t : NewType) → Set where 
    SynConst : ∀ {Γ info syn} ->
      MergeSyn info (TBase , Old) syn -> 
      Γ ⊢ (EUp info EConst) ⇒ syn
    SynHole : ∀ {Γ info syn} ->
      MergeSyn info (THole , Old) syn -> 
      Γ ⊢ (EUp info EHole) ⇒ syn
    SynFun : ∀ {Γ info t1 t2 n1 n2 n3 syn e} ->
      ((t1 , n1) , Γ) ⊢ e ⇒ (t2 , n2) ->
      narrow n1 n2 ≡ n3 ->
      MergeSyn info (TArrow t1 t2 , n3) syn -> 
      Γ ⊢ (EUp info (EFun (t1 , n1) Unmarked (ELow ̸⇓ Unmarked e))) ⇒ syn
    SynFunVoid : ∀ {Γ t1 t2 n1 n2 e} ->
      ((t1 , n1) , Γ) ⊢ e ⇒ (t2 , n2) ->
      Γ ⊢ (EUp ̸⇑ (EFun (t1 , n1) Unmarked (ELow ̸⇓ Unmarked e))) ⇒ (TArrow t1 t2 , New)
    SynAp : ∀ {Γ info t t1 t2 n n1 n2 e1 e2 syn} ->
      Γ ⊢ e1 ⇒ (t , n) ->
      t ▸TArrow t1 , t2 ->
      n ▸NArrow n1 , n2 ->
      Γ ⊢ e2 ⇐ (t1 , n1) ->
      MergeSyn info (t2 , n2) syn -> 
      Γ ⊢ (EUp info (EAp (ELow ̸⇓ Unmarked e1) Unmarked e2)) ⇒ syn
    SynApFail : ∀ {Γ info t n n1 n2 e1 e2 syn} ->
      Γ ⊢ e1 ⇒ (t , n) ->
      t ̸▸TArrow ->
      n ▸NArrow n1 , n2 ->
      Γ ⊢ e2 ⇐ (THole , n1) ->
      MergeSyn info (THole , n2) syn -> 
      Γ ⊢ (EUp info (EAp (ELow ̸⇓ Unmarked e1) Marked e2)) ⇒ syn
    SynVar : ∀ {Γ info x t syn} ->
      x , t ∈ Γ ->
      MergeSyn info t syn -> 
      Γ ⊢ (EUp info (EVar x Unmarked)) ⇒ syn
    SynVarFail : ∀ {Γ info x syn} ->
      x ̸∈ Γ ->
      MergeSyn info (THole , Old) syn -> 
      Γ ⊢ (EUp info (EVar x Marked)) ⇒ syn
    SynAsc : ∀ {Γ syn t e syn'} ->
      Γ ⊢ e ⇐ t ->
      MergeInfo syn t syn' -> 
      Γ ⊢ (EUp (⇑ syn) (EAsc t e)) ⇒ syn'

  data _⊢_⇐_ : (Γ : Ctx) (e : ExpLow) (t : NewType) → Set where 
    AnaSubsume : ∀ {Γ info ana t1 t2 n1 n2 e} ->
      MergeAna info ana (t2 , n2) -> 
      Γ ⊢ e ⇒ (t1 , n1) ->
      Subsumable e ->
      (t1 ~ t2) ->
      Γ ⊢ (ELow info Unmarked e) ⇐ ana
    AnaSubsumeFail : ∀ {Γ info ana t1 t2 n1 n2 e} ->
      MergeAna info ana (t2 , n2) -> 
      Γ ⊢ e ⇒ (t1 , n1) ->
      Subsumable e ->
      ¬(t1 ~ t2) ->
      Γ ⊢ (ELow info Marked e) ⇐ ana
    AnaFun : ∀ {Γ info ana t t1 t2 n n1 n2 tasc nasc e} ->
      MergeAna info ana (t , n) -> 
      t ▸TArrow t1 , t2 ->
      n ▸NArrow n1 , n2 ->
      ((tasc , nasc) , Γ) ⊢ e ⇐ (t2 , n2) ->
      (tasc ~ t1) ->
      Γ ⊢ (ELow info Unmarked (EUp ̸⇑ (EFun (tasc , nasc) Unmarked e))) ⇐ ana
    AnaFunFail1 : ∀ {Γ info ana t t1 t2 n n1 n2 tasc nasc e} ->
      MergeAna info ana (t , n) -> 
      t ▸TArrow t1 , t2 ->
      n ▸NArrow n1 , n2 ->
      ((tasc , nasc) , Γ) ⊢ e ⇐ (t2 , n2) ->
      ¬(tasc ~ t1) ->
      Γ ⊢ (ELow info Unmarked (EUp ̸⇑ (EFun (tasc , nasc) Marked e))) ⇐ ana
    AnaFunFail2 : ∀ {Γ syn-info ana-info syn-info' ana syn t tasc n nasc e} ->
      MergeInfo ana-info ana (t , n) -> 
      t ̸▸TArrow ->
      ((tasc , nasc) , Γ) ⊢ e ⇒ syn ->
      MergeInfo syn-info syn syn-info' -> 
      Γ ⊢ (ELow (⇓ ana-info) Marked (EUp (⇑ syn-info) (EFun (tasc , nasc) Unmarked (ELow ̸⇓ Unmarked e)))) ⇐ ana
