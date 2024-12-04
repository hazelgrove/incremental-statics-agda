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

data MarkConsist : (m1 : NewMark) (m2 : MarkData) -> Set where 
  MarkConsistNew : ∀ {m1 m2} ->
    MarkConsist (m1 , MarkNew) m2
  MarkConsistOld : ∀ {m} ->
    MarkConsist (m , MarkOld) m

-- takes a newtype and projects its left and right sides as well as returning 
-- whether it matches arrow. these are newtypes/constraints, so they can be checked
-- with directed consistency against the actual annotations
data _▸NTArrow_,_,_ : NewType -> NewType -> NewType -> NewMark -> Set where 
  MNTArrowOldMatch : ∀ {t t1 t2} ->
    t ▸TArrow t1 , t2 ->
    (t , Old) ▸NTArrow (t1 , Old) , (t2 , Old) , (Unmarked , MarkOld)
  MNTArrowOldNoMatch : ∀ {t} ->
    t ̸▸TArrow ->
    (t , Old) ▸NTArrow (THole , Old) , (THole , Old) , (Marked , MarkOld)
  MNTArrowNewMatch : ∀ {t t1 t2} ->
    t ▸TArrow t1 , t2 ->
    (t , New) ▸NTArrow (t1 , New) , (t2 , New) , (Unmarked , MarkNew)
  MNTArrowNewNoMatch : ∀ {t} ->
    t ̸▸TArrow ->
    (t , New) ▸NTArrow (THole , New) , (THole , New) , (Marked , MarkNew)
  MNTArrowArrow : ∀ {t1 t2 n1 n2} → 
    (TArrow t1 t2 , NArrow n1 n2) ▸NTArrow (t1 , n1) , (t2 , n2) , (Unmarked , MarkOld)

data _▸SynArrow_,_,_ : SynData -> NewType -> NewType -> NewMark -> Set where 
  SynArrowNone : ̸⇑ ▸SynArrow (THole , New) , (THole , New) , (Unmarked , MarkNew)
  SynArrowSome : ∀ {t t1 t2 m} ->
    t ▸NTArrow t1 , t2 , m -> 
    (⇑ t) ▸SynArrow t1 , t2 , m

mutual 

  data _⊢_⇒ : (Γ : Ctx) (e : ExpUp) → Set where 
    SynConst : ∀ {Γ syn} ->
      SynConsist (TBase , Old) syn ->
      Γ ⊢ (EUp syn EConst) ⇒
    SynHole : ∀ {Γ syn} ->
      SynConsist (THole , Old) syn ->
      Γ ⊢ (EUp syn EHole) ⇒
    SynAp : ∀ {Γ syn1 syn2 e1 m1 ana m2 e2 t1 t2 m} ->
      syn2 ▸SynArrow t1 , t2 , m -> 
      SynConsist t2 syn1 -> 
      AnaConsist t1 ana -> 
      MarkConsist m m1 -> 
      Γ ⊢ (EUp syn2 e1) ⇒ ->
      Γ ⊢ (ELow ana m2 e2) ⇐ ->
      Γ ⊢ (EUp syn1 (EAp (ELow ̸⇓ Unmarked (EUp syn2 e1)) m1 (ELow ana m2 e2))) ⇒
    SynAsc : ∀ {Γ syn asc ana m e} ->
      SynConsist asc syn -> 
      AnaConsist asc ana -> 
      Γ ⊢ (ELow ana m e) ⇐ ->
      Γ ⊢ (EUp syn (EAsc asc (ELow ana m e))) ⇒

  data _⊢_⇐ : (Γ : Ctx) (e : ExpLow) → Set where 
