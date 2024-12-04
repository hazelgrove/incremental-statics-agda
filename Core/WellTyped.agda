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

data MatchArrowMarkConsist : NewType -> MarkData -> Set where 
  MAMConsistNew : ∀ {t m} ->
    MatchArrowMarkConsist (t , New) m
  MAMConsistMatch : ∀ {t t1 t2 n} ->
    t ▸TArrow t1 , t2 ->
    MatchArrowMarkConsist (t , n) Unmarked
  MAMConsistNoMatch : ∀ {t n} ->
    t ̸▸TArrow ->
    MatchArrowMarkConsist (t , n) Marked

-- I think this is correct, but can be expressed better
data ValidApStuff : (syn1 : SynData) (syn2 : SynData) (m : MarkData) (ana : AnaData) -> Set where 
  ValidApStuffNone : ∀ {syn1 m ana} ->
    ValidApStuff syn1 ̸⇑ m ana
  ValidApStuffNew : ∀ {syn1 m ana t} ->
    ValidApStuff syn1 (⇑ (t , New)) m ana
  ValidApStuffNArrow : ∀ {syn1 ana t1 n1 t2 n2} ->
    SynConsist (t2 , n2) syn1 ->
    AnaConsist (t1 , n1) ana ->
    ValidApStuff syn1 (⇑ (TArrow t1 t2 , NArrow n1 n2)) Unmarked ana
  ValidApStuffOldMatch : ∀ {syn1 ana t t1 t2} ->
    t ▸TArrow t1 , t2 ->
    SynConsist (t2 , Old) syn1 -> 
    AnaConsist (t1 , Old) ana -> 
    ValidApStuff syn1 (⇑ (t , Old)) Unmarked ana
  ValidApStuffOldNoMatch : ∀ {syn1 ana t} ->
    t ̸▸TArrow ->
    SynConsist (THole , Old) syn1 -> 
    AnaConsist (THole , Old) ana -> 
    ValidApStuff syn1 (⇑ (t , Old)) Marked ana

data MarkConstraint : Set where 
  MarkNew : MarkConstraint 
  MarkOld : MarkData -> MarkConstraint

data MarkConsist : (m1 : MarkConstraint) (m2 : MarkData) -> Set where 
  MarkConsistNew : ∀ {m} ->
    MarkConsist MarkNew m
  MarkConsistOld : ∀ {m} ->
    MarkConsist (MarkOld m) m

-- takes a newtype and projects its left and right sides as well as returning 
-- whether it matches arrow. these are newtypes/constraints, so they can be check
-- with directed consistency against the actual annotations
data _▸NTArrow_,_,_ : NewType -> NewType -> NewType -> MarkConstraint -> Set where 
  MNTArrowOldMatch : ∀ {t t1 t2} ->
    t ▸TArrow t1 , t2 ->
    (t , Old) ▸NTArrow (t1 , Old) , (t2 , Old) , (MarkOld Unmarked)
  MNTArrowOldNoMatch : ∀ {t} ->
    t ̸▸TArrow ->
    (t , Old) ▸NTArrow (THole , Old) , (THole , Old) , (MarkOld Marked)
  MNTArrowNew : ∀ {t} ->
    -- the return types are dummy. since they are new, they will be 
    -- consistent with anything. there could have been a "constraint" type 
    -- analogous to the mark constraint about - the left input to directed 
    -- consistency, which is like a newness type but with no data accompanying 
    -- the New case. but this would require a function to turn types into constraints
    (t , New) ▸NTArrow (THole , New) , (THole , New) , MarkNew
  MNTArrowArrow : ∀ {t1 t2 n1 n2} → 
    (TArrow t1 t2 , NArrow n1 n2) ▸NTArrow (t1 , n1) , (t2 , n2) , (MarkOld Unmarked)

data CoolerValidApStuff : (syn1 : SynData) (syn2 : SynData) (m : MarkData) (ana : AnaData) -> Set where 
  CoolerValidApStuffNone : ∀ {syn m ana} ->
    CoolerValidApStuff syn ̸⇑ m ana
  CoolerValidApStuffSome : ∀ {syn t m ana t1 t2 m'} ->
    t ▸NTArrow t1 , t2 , m' -> 
    SynConsist t2 syn -> 
    AnaConsist t1 ana -> 
    MarkConsist m' m -> 
    CoolerValidApStuff syn (⇑ t) m ana

mutual 

  data _⊢_⇒ : (Γ : Ctx) (e : ExpUp) → Set where 
    SynConst : ∀ {Γ syn} ->
      SynConsist (TBase , Old) syn ->
      Γ ⊢ (EUp syn EConst) ⇒
    SynHole : ∀ {Γ syn} ->
      SynConsist (THole , Old) syn ->
      Γ ⊢ (EUp syn EHole) ⇒
    SynAp : ∀ {Γ syn1 syn2 e1 m1 ana m2 e2} ->
      ValidApStuff syn1 syn2 m1 ana ->
      Γ ⊢ (EUp syn1 (EAp (ELow ̸⇓ Unmarked (EUp syn2 e1)) m1 (ELow ana m2 e2))) ⇒

  -- note: the analyzed type is actually an OUTPUT of this judgment
  data _⊢_⇐_ : (Γ : Ctx) (e : ExpLow) (t : NewType) → Set where 
