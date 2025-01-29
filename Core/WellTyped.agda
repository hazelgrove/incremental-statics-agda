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

-- directed newtype consistency
data _▷_ : NewType -> NewType -> Set where 
  MergeInfoNew : ∀ {t1 t2 n2} -> 
    (t1 , New) ▷ (t2 , n2)
  MergeInfoOld : ∀ {t1 t2 n2} -> 
    (t1 ≡ t2) -> (t1 , Old) ▷ (t2 , n2)

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

data MarkConsist : (m1 : NewMark) (m2 : MarkData) -> Set where 
  MarkConsistNew : ∀ {m1 m2} ->
    MarkConsist (m1 , New) m2
  MarkConsistOld : ∀ {m1 m2} ->
    (m1 ≡ m2) -> MarkConsist (m1 , Old) m2

-- takes a newtype and projects its left and right sides as well as returning 
-- whether it matches arrow. these are newtypes/constraints, so they can be checked
-- with directed consistency against the actual annotations
data _▸NTArrow_,_,_ : NewType -> NewType -> NewType -> NewMark -> Set where 
  MNTArrowOld : ∀ {t t1 t2 m} ->
    t ▸TArrowM t1 , t2 , m ->
    (t , Old) ▸NTArrow (t1 , Old) , (t2 , Old) , (m , Old)
  MNTArrowNew : ∀ {t t1 t2 m} ->
    t ▸TArrowM t1 , t2 , m ->
    (t , New) ▸NTArrow (t1 , New) , (t2 , New) , (m , New)

data _▸SynArrowM_,_,_ : SynData -> NewType -> NewType -> NewMark -> Set where 
  SynArrowNone : ̸⇑ ▸SynArrowM (THole , New) , (THole , New) , (Unmarked , New)
  SynArrowSome : ∀ {t t1 t2 m} ->
    t ▸NTArrow t1 , t2 , m -> 
    (⇑ t) ▸SynArrowM t1 , t2 , m

data _,_∈M_,_ : ℕ -> NewType -> Ctx -> NewMark -> Set where 
  MInCtxBound : ∀ {x t Γ} -> 
    x , t ∈ Γ -> x , t ∈M Γ , (Unmarked , Old)
  MInCtxFree : ∀ {x Γ} -> 
    x ̸∈ Γ -> x , (THole , Old) ∈M Γ , (Marked , Old)

data _NT~M_,_ : NewType -> NewType -> NewMark -> Set where 
  LNewConsist : ∀ {t1 t2 n2 m} ->
    t1 ~M t2 , m -> 
    (t1 , New) NT~M (t2 , n2) , (m , New) 
  RNewConsist : ∀ {t1 t2 n1 m} ->
    t1 ~M t2 , m -> 
    (t1 , n1) NT~M (t2 , Old) , (m , New) 
  OldOldConsist : ∀ {t1 t2 m} ->
    t1 ~M t2 , m -> 
    (t1 , Old) NT~M (t2 , Old) , (Unmarked , Old) 


data _AnaSyn~M_,_ : AnaData -> SynData -> NewMark -> Set where 
  NoneSynConsist : ∀ {syn} ->
     ̸⇓ AnaSyn~M syn , (Unmarked , New)
  AnaNoneConsist : ∀ {ana} ->
    ana AnaSyn~M ̸⇑ , (Unmarked , New)
  AnaSynConsist : ∀ {ana syn m} ->
    ana NT~M syn , m ->
    (⇓ ana) AnaSyn~M (⇑ syn) , m  

mutual 

  data _⊢_⇒ : (Γ : Ctx) (e : ExpUp) -> Set where 
    SynConst : ∀ {Γ syn-all} ->
      SynConsist (TBase , Old) syn-all ->
      Γ ⊢ (EUp syn-all EConst) ⇒
    SynHole : ∀ {Γ syn-all} ->
      SynConsist (THole , Old) syn-all ->
      Γ ⊢ (EUp syn-all EHole) ⇒
    -- SynFun -- TODO
    SynAp : ∀ {Γ e-fun e-arg syn-all syn-fun ana-arg t-in-fun t-out-fun m-all m-fun m-arg} ->
      syn-fun ▸SynArrowM t-in-fun , t-out-fun , m-fun -> 
      SynConsist t-out-fun syn-all -> 
      AnaConsist t-in-fun ana-arg -> 
      MarkConsist m-fun m-all -> 
      Γ ⊢ (EUp syn-fun e-fun) ⇒ ->
      Γ ⊢ (ELow ana-arg m-arg e-arg) ⇐ ->
      Γ ⊢ (EUp syn-all (EAp (ELow ̸⇓ Unmarked (EUp syn-fun e-fun)) m-all (ELow ana-arg m-arg e-arg))) ⇒
    SynVar : ∀ {Γ x syn-all t-var m-all m-var} ->
      x , t-var ∈M Γ , m-var ->
      SynConsist t-var syn-all ->
      MarkConsist m-var m-all -> 
      Γ ⊢ (EUp syn-all (EVar x m-all)) ⇒
    SynAsc : ∀ {Γ e-body syn-all ana-body t-asc m-body} ->
      SynConsist t-asc syn-all -> 
      AnaConsist t-asc ana-body -> 
      Γ ⊢ (ELow ana-body m-body e-body) ⇐ ->
      Γ ⊢ (EUp syn-all (EAsc t-asc (ELow ana-body m-body e-body))) ⇒

  data _⊢_⇐ : (Γ : Ctx) (e : ExpLow) -> Set where 
    AnaSubsume : ∀ {Γ e-all syn-all ana-all m-all m-consist} ->
      SubsumableMid e-all ->
      ana-all AnaSyn~M syn-all , m-consist ->
      MarkConsist m-consist m-all ->
      Γ ⊢ (EUp syn-all e-all) ⇒ ->
      Γ ⊢ (ELow ana-all m-all (EUp syn-all e-all)) ⇐ 