open import Data.Nat hiding (_+_; _⊓_)
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

-- Directed Newness Consistency Judgments:
-- Tests whether the first piece of data (which has been calculated 
-- from slightly upstream in the information flow) is consistent with the 
-- second (which is found as an annotation slghtly downstream). 

data _▷NT_ : NewType -> NewType -> Set where 
  MergeInfoNew : ∀ {t1 t2 n2} -> 
    (t1 , New) ▷NT (t2 , n2)
  MergeInfoOld : ∀ {t1 t2 n2} -> 
    (t1 ≡ t2) -> (t1 , Old) ▷NT (t2 , n2)

data ▷Syn : SynData -> SynData -> Set where 
  ▷SynVoidL : ∀ {s} -> 
    ▷Syn ̸⇑ s
  ▷SynVoidR : ∀ {s} -> 
    ▷Syn s ̸⇑
  ▷SynMerge : ∀ {syn1 syn2} -> 
    syn1 ▷NT syn2 ->
    ▷Syn (⇑ syn1) (⇑ syn2)

data ▷Ana : NewType -> AnaData -> Set where 
  ▷AnaVoid : ∀ {t n} -> 
    ▷Ana (t , n) ̸⇓
  ▷AnaMerge : ∀ {ana1 ana2} -> 
    ana1 ▷NT ana2 ->
    ▷Ana ana1 (⇓ ana2)

data ▷NM : (m1 : NewMark) (m2 : MarkData) -> Set where 
  ▷NMNew : ∀ {m1 m2} ->
    ▷NM (m1 , New) m2
  ▷NMOld : ∀ {m1 m2} ->
    (m1 ≡ m2) -> ▷NM (m1 , Old) m2

-- Side conditions returning new marks. 

data _▸TArrowNM_,_,_ : NewType -> NewType -> NewType -> NewMark -> Set where 
  MNTArrowOld : ∀ {t t1 t2 m} ->
    t ▸TArrowM t1 , t2 , m ->
    (t , Old) ▸TArrowNM (t1 , Old) , (t2 , Old) , (m , Old)
  MNTArrowNew : ∀ {t t1 t2 m} ->
    t ▸TArrowM t1 , t2 , m ->
    (t , New) ▸TArrowNM (t1 , New) , (t2 , New) , (m , New)

data _▸DTArrowNM_,_,_ : SynData -> NewType -> NewType -> NewMark -> Set where 
  SynArrowNone : ̸⇑ ▸DTArrowNM (THole , New) , (THole , New) , (Unmarked , New)
  SynArrowSome : ∀ {t t1 t2 m} ->
    t ▸TArrowNM t1 , t2 , m -> 
    (⇑ t) ▸DTArrowNM t1 , t2 , m

data _,_∈NM_,_ : ℕ -> NewType -> Ctx -> NewMark -> Set where 
  MInCtxBound : ∀ {x t Γ} -> 
    x , t ∈ Γ -> x , t ∈NM Γ , (Unmarked , Old)
  MInCtxFree : ∀ {x Γ} -> 
    x ̸∈ Γ -> x , (THole , Old) ∈NM Γ , (Marked , Old)

data _~NM_,_ : NewType -> NewType -> NewMark -> Set where 
  LNewConsist : ∀ {t1 t2 n2 m} ->
    t1 ~M t2 , m -> 
    (t1 , New) ~NM (t2 , n2) , (m , New) 
  RNewConsist : ∀ {t1 t2 n1 m} ->
    t1 ~M t2 , m -> 
    (t1 , n1) ~NM (t2 , Old) , (m , New) 
  OldOldConsist : ∀ {t1 t2 m} ->
    t1 ~M t2 , m -> 
    (t1 , Old) ~NM (t2 , Old) , (Unmarked , Old) 

data _D~NM_,_ : AnaData -> SynData -> NewMark -> Set where 
  None▷Syn : ∀ {syn} ->
     ̸⇓ D~NM syn , (Unmarked , New)
  AnaNoneConsist : ∀ {ana} ->
    ana D~NM ̸⇑ , (Unmarked , New)
  Ana▷Syn : ∀ {ana syn m} ->
    ana ~NM syn , m ->
    (⇓ ana) D~NM (⇑ syn) , m  

NTArrow : NewType -> NewType -> NewType
NTArrow (t1 , n1) (t2 , n2) = ( TArrow t1 t2 , n1 ⊓ n2 )

SynArrow : NewType -> SynData -> SynData 
SynArrow t ̸⇑ = ̸⇑
SynArrow t1 (⇑ t2) = ⇑ (NTArrow t1 t2)

mutual 

  data _⊢_⇒ : (Γ : Ctx) (e : ExpUp) -> Set where 
    SynConst : ∀ {Γ syn-all} ->
      ▷Syn (⇑ (TBase , Old)) syn-all ->
      Γ ⊢ (EUp syn-all EConst) ⇒
    SynHole : ∀ {Γ syn-all} ->
      ▷Syn (⇑ (THole , Old)) syn-all ->
      Γ ⊢ (EUp syn-all EHole) ⇒
    SynFun : ∀ {Γ e-body syn-all syn-body t-asc} ->
      ▷Syn (SynArrow t-asc syn-body) syn-all ->
      (t-asc , Γ) ⊢ (EUp syn-body e-body) ⇒ ->
      Γ ⊢ (EUp syn-all (EFun t-asc Unmarked Unmarked (ELow ̸⇓ Unmarked (EUp syn-body e-body)))) ⇒
    SynAp : ∀ {Γ e-fun e-arg syn-all syn-fun ana-arg t-in-fun t-out-fun m-all m-fun m-arg} ->
      syn-fun ▸DTArrowNM t-in-fun , t-out-fun , m-fun -> 
      ▷Syn (⇑ t-out-fun) syn-all -> 
      ▷Ana t-in-fun ana-arg -> 
      ▷NM m-fun m-all -> 
      Γ ⊢ (EUp syn-fun e-fun) ⇒ ->
      Γ ⊢ (ELow ana-arg m-arg e-arg) ⇐ ->
      Γ ⊢ (EUp syn-all (EAp (ELow ̸⇓ Unmarked (EUp syn-fun e-fun)) m-all (ELow ana-arg m-arg e-arg))) ⇒
    SynVar : ∀ {Γ x syn-all t-var m-all m-var} ->
      x , t-var ∈NM Γ , m-var ->
      ▷Syn (⇑ t-var) syn-all ->
      ▷NM m-var m-all -> 
      Γ ⊢ (EUp syn-all (EVar x m-all)) ⇒
    SynAsc : ∀ {Γ e-body syn-all ana-body t-asc m-body} ->
      ▷Syn (⇑ t-asc) syn-all -> 
      ▷Ana t-asc ana-body -> 
      Γ ⊢ (ELow ana-body m-body e-body) ⇐ ->
      Γ ⊢ (EUp syn-all (EAsc t-asc (ELow ana-body m-body e-body))) ⇒

  data _⊢_⇐ : (Γ : Ctx) (e : ExpLow) -> Set where 
    AnaSubsume : ∀ {Γ e-all syn-all ana-all m-all m-consist} ->
      SubsumableMid e-all ->
      ana-all D~NM syn-all , m-consist ->
      ▷NM m-consist m-all ->
      Γ ⊢ (EUp syn-all e-all) ⇒ -> 
      Γ ⊢ (ELow ana-all m-all (EUp syn-all e-all)) ⇐ 