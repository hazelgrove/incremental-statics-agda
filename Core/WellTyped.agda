open import Data.Nat hiding (_+_)
open import Data.Unit 
open import Data.Bool hiding (_<_; _≟_)
open import Data.Sum renaming (_⊎_ to _+_; inj₁ to Inl ; inj₂ to Inr) hiding (map)
open import Data.Product hiding (map)
open import Relation.Nullary 
open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Prelude

open import Core.Core
open import Core.Merge

module Core.WellTyped where

data MergeSyn : NewType -> SynData -> NewType -> Set where 
  MergeSynVoid : ∀ {t n} -> 
    MergeSyn (t , n) ̸⇑ (t , n)
  MergeSynMerge : ∀ {syn1 syn2 syn3} -> 
    syn1 ▷ syn2 == syn3 ->
    MergeSyn syn1 (⇑ syn2) syn3

data MergeAna : NewType -> AnaData -> NewType -> Set where 
  MergeAnaVoid : ∀ {t n} -> 
    MergeAna (t , n) ̸⇓ (t , New)
  MergeAnaMerge : ∀ {ana1 ana2 ana3} -> 
    ana1 ▷ ana2 == ana3 ->
    MergeAna ana1 (⇓ ana2) ana3

mutual 
  data _⊢_⇒_ : (Γ : Ctx) (e : ExpUp) (t : NewType) → Set where 
    SynUp : ∀ {Γ info e t syn} ->
      Γ ⊢ e M⇒ t ->
      MergeSyn t info syn -> 
      Γ ⊢ (EUp info e) ⇒ syn

  data _⊢_M⇒_ : (Γ : Ctx) (e : ExpMid) (t : NewType) → Set where 
    SynConst : ∀ {Γ} ->
      Γ ⊢ EConst M⇒ (TBase , Old)
    SynHole : ∀ {Γ} ->
      Γ ⊢ EHole M⇒ (THole , Old)
    SynFun : ∀ {Γ t1 t2 n1 n2 n3 e} ->
      ((t1 , n1) , Γ) ⊢ e ⇒ (t2 , n2) ->
      narrow n1 n2 ≡ n3 ->
      Γ ⊢ (EFun (t1 , n1) Unmarked (ELow ̸⇓ Unmarked e)) M⇒ (TArrow t1 t2 , n3)
    SynAp : ∀ {Γ t t1 t2 n n1 n2 e1 e2} ->
      Γ ⊢ e1 ⇒ (t , n) ->
      t ▸TArrow t1 , t2 ->
      n ▸NArrow n1 , n2 ->
      Γ ⊢ e2 ⇐ (t1 , n1) ->
      Γ ⊢ (EAp (ELow ̸⇓ Unmarked e1) Unmarked e2) M⇒ (t2 , n2)
    SynApFail : ∀ {Γ t n n1 n2 e1 e2} ->
      Γ ⊢ e1 ⇒ (t , n) ->
      t ̸▸TArrow ->
      n ▸NArrow n1 , n2 ->
      Γ ⊢ e2 ⇐ (THole , n1) ->
      Γ ⊢ (EAp (ELow ̸⇓ Unmarked e1) Marked e2) M⇒ (THole , n2)
    SynVar : ∀ {Γ x t} ->
      x , t ∈ Γ ->
      Γ ⊢ (EVar x Unmarked) M⇒ t
    SynVarFail : ∀ {Γ x} ->
      x ̸∈ Γ ->
      Γ ⊢ (EVar x Marked) M⇒ (THole , Old)
    SynAsc : ∀ {Γ t e} ->
      Γ ⊢ e ⇐ t ->
      Γ ⊢ (EAsc t e) M⇒ t

  data _⊢_⇐_ : (Γ : Ctx) (e : ExpLow) (t : NewType) → Set where 
    AnaSubsume : ∀ {Γ info ana t1 t2 n1 n2 e} ->
      MergeAna ana info (t2 , n2) -> 
      Γ ⊢ e ⇒ (t1 , n1) ->
      Subsumable e ->
      (t1 ~ t2) ->
      Γ ⊢ (ELow info Unmarked e) ⇐ ana
    AnaSubsumeFail : ∀ {Γ info ana t1 t2 n1 n2 e} ->
      MergeAna ana info (t2 , n2) -> 
      Γ ⊢ e ⇒ (t1 , n1) ->
      Subsumable e ->
      ¬(t1 ~ t2) ->
      Γ ⊢ (ELow info Marked e) ⇐ ana
    AnaFun : ∀ {Γ info ana t t1 t2 n n1 n2 tasc nasc e} ->
      MergeAna ana info (t , n) -> 
      t ▸TArrow t1 , t2 ->
      n ▸NArrow n1 , n2 ->
      ((tasc , nasc) , Γ) ⊢ e ⇐ (t2 , n2) ->
      (tasc ~ t1) ->
      Γ ⊢ (ELow info Unmarked (EUp ̸⇑ (EFun (tasc , nasc) Unmarked e))) ⇐ ana
    AnaFunFail1 : ∀ {Γ info ana t t1 t2 n n1 n2 tasc nasc e} ->
      MergeAna ana info (t , n) -> 
      t ▸TArrow t1 , t2 ->
      n ▸NArrow n1 , n2 ->
      ((tasc , nasc) , Γ) ⊢ e ⇐ (t2 , n2) ->
      ¬(tasc ~ t1) ->
      Γ ⊢ (ELow info Unmarked (EUp ̸⇑ (EFun (tasc , nasc) Marked e))) ⇐ ana
    AnaFunFail2 : ∀ {Γ syn-info ana-info syn-info' ana syn t tasc n nasc e} ->
      MergeAna ana (⇓ ana-info) (t , n) -> 
      t ̸▸TArrow ->
      ((tasc , nasc) , Γ) ⊢ e ⇒ syn ->
      MergeSyn syn (⇑ syn-info) syn-info' -> 
      Γ ⊢ (ELow (⇓ ana-info) Marked (EUp (⇑ syn-info) (EFun (tasc , nasc) Unmarked (ELow ̸⇓ Unmarked e)))) ⇐ ana
