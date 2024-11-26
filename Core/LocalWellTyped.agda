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

module Core.LocalWellTyped where


-- directed newtype consistency
data _▷_ : NewType -> NewType -> Set where 
  MergeInfoNew : ∀ {t1 t2 n2} -> 
    (t1 , New) ▷ (t2 , n2)
  MergeInfoOld : ∀ {t1 n2} -> 
    (t1 , Old) ▷ (t1 , n2)
  MergeInfoArrow : ∀ {t1 t2 t3 t4 t5 t6 n n1 n2 n3 n4 n5 n6} -> 
    n ▸NArrow n3 , n4 ->
    (t1 , n1) ▷ (t3 , n3) == (t5 , n5) ->
    (t2 , n2) ▷ (t4 , n4) == (t6 , n6) ->
    (TArrow t1 t2 , NArrow n1 n2) ▷ (TArrow t3 t4 , n)

data SynConsist : NewType -> SynData -> Set where 
  SynConsistVoid : ∀ {t n} -> 
    SynConsist (t , n) ̸⇑
  SynConsistMerge : ∀ {syn1 syn2} -> 
    syn1 ▷ syn2 ->
    SynConsist syn1 (⇑ syn2)

data AnaConsist : NewType -> AnaData -> Set where 
  AnaConsistVoid : ∀ {t n} -> 
    AnaConsist (t , n) ̸⇓
  AnaConsistMerge : ∀ {ana1 ana2} -> 
    ana1 ▷ ana2 ->
    AnaConsist ana1 (⇓ ana2)

mutual 
  data _⊢_⇒ : (Γ : Ctx) (e : ExpUp)→ Set where 
    SynUp : ∀ {Γ info e t syn} ->
      Γ ⊢ e M⇒ t ->
      SynConsist t info -> 
      Γ ⊢ (EUp info e) ⇒

  data _⊢_M⇒_ : (Γ : Ctx) (e : ExpMid) (t : NewType) → Set where 
    SynConst : ∀ {Γ} ->
      Γ ⊢ EConst M⇒ (TBase , Old)
    SynHole : ∀ {Γ} ->
      Γ ⊢ EHole M⇒ (THole , Old)
    SynFun : ∀ {Γ t1 t2 n1 n2 n3 e} -> TODO
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
      AnaConsist ana info (t2 , n2) -> 
      Γ ⊢ e ⇒ (t1 , n1) ->
      Subsumable e ->
      (t1 ~ t2) ->
      Γ ⊢ (ELow info Unmarked e) ⇐ ana
    AnaSubsumeFail : ∀ {Γ info ana t1 t2 n1 n2 e} ->
      AnaConsist ana info (t2 , n2) -> 
      Γ ⊢ e ⇒ (t1 , n1) ->
      Subsumable e ->
      ¬(t1 ~ t2) ->
      Γ ⊢ (ELow info Marked e) ⇐ ana
    AnaFun : ∀ {Γ info ana t t1 t2 n n1 n2 tasc nasc e} ->
      AnaConsist ana info (t , n) -> 
      t ▸TArrow t1 , t2 ->
      n ▸NArrow n1 , n2 ->
      ((tasc , nasc) , Γ) ⊢ e ⇐ (t2 , n2) ->
      (tasc ~ t1) ->
      Γ ⊢ (ELow info Unmarked (EUp ̸⇑ (EFun (tasc , nasc) Unmarked e))) ⇐ ana
    AnaFunFail1 : ∀ {Γ info ana t t1 t2 n n1 n2 tasc nasc e} ->
      AnaConsist ana info (t , n) -> 
      t ▸TArrow t1 , t2 ->
      n ▸NArrow n1 , n2 ->
      ((tasc , nasc) , Γ) ⊢ e ⇐ (t2 , n2) ->
      ¬(tasc ~ t1) ->
      Γ ⊢ (ELow info Unmarked (EUp ̸⇑ (EFun (tasc , nasc) Marked e))) ⇐ ana
    AnaFunFail2 : ∀ {Γ syn-info ana-info syn-info' ana syn t tasc n nasc e} ->
      AnaConsist ana (⇓ ana-info) (t , n) -> 
      t ̸▸TArrow ->
      ((tasc , nasc) , Γ) ⊢ e ⇒ syn ->
      SynConsist syn (⇑ syn-info) syn-info' -> 
      Γ ⊢ (ELow (⇓ ana-info) Marked (EUp (⇑ syn-info) (EFun (tasc , nasc) Unmarked (ELow ̸⇓ Unmarked e)))) ⇐ ana
