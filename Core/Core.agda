open import Data.Nat hiding (_+_; _⊓_; _⊔_)
open import Data.Unit 
open import Data.Bool hiding (_<_; _≟_)
open import Data.Sum renaming (_⊎_ to _+_; inj₁ to Inl ; inj₂ to Inr) hiding (map)
open import Data.Product hiding (map)
open import Relation.Nullary 
open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Prelude

module Core.Core where

data Type : Set where 
  TBase : Type 
  THole : Type
  TArrow : Type -> Type -> Type 

data BareExp : Set where 
  BareEConst : BareExp 
  BareEHole : BareExp
  BareEFun : Type -> BareExp -> BareExp 
  BareEAp : BareExp -> BareExp -> BareExp 
  BareEVar : ℕ -> BareExp 
  BareEAsc : Type -> BareExp -> BareExp 

data BareProgram : Set where 
  BareRoot : BareExp -> BareProgram

data BareSubsumable : BareExp -> Set where 
  BareSubsumableConst : BareSubsumable BareEConst
  BareSubsumableHole : BareSubsumable BareEHole
  BareSubsumableAp : ∀ {e1 e2} -> BareSubsumable (BareEAp e1 e2) 
  BareSubsumableVar : ∀ {x} -> BareSubsumable (BareEVar x) 
  BareSubsumableAsc : ∀ {t e} -> BareSubsumable (BareEAsc t e) 

data Newness : Set where 
  Old : Newness 
  New : Newness 

_⊓_ : Newness -> Newness -> Newness 
Old ⊓ n = n
New ⊓ n = New

-- _⊔_ : Newness -> Newness -> Newness 
-- Old ⊔ n = Old
-- New ⊔ n = n
  
data Mark : Set where 
  ✖ : Mark
  ✔ : Mark
  
_⊓M_ : Mark -> Mark -> Mark 
✔ ⊓M m = m
✖ ⊓M m = ✖

data _~_,_ : Type -> Type -> Mark -> Set where 
  ConsistBase : TBase ~ TBase , ✔
  ConsistHoleL : ∀ {t} -> THole ~ t , ✔
  ConsistHoleR : ∀ {t} -> t ~ THole , ✔
  ConsistArr : ∀ {t1 t2 t3 t4 m1 m2} -> 
    t1 ~ t3 , m1 -> 
    t2 ~ t4 , m2 -> 
    ((TArrow t1 t2) ~ (TArrow t3 t4) , (m1 ⊓M m2))
  InconsistBaseArr : ∀ {t1 t2} ->
    TBase ~ (TArrow t1 t2) , ✖
  InconsistArrBase : ∀ {t1 t2} ->
    (TArrow t1 t2) ~ TBase , ✖

data _▸TArrow_,_,_ : Type -> Type -> Type -> Mark -> Set where 
  MArrowBase :
    TBase ▸TArrow THole , THole , ✖
  MArrowHole :
    THole ▸TArrow THole , THole , ✔
  MArrowArrow : ∀ {t1 t2} -> 
    (TArrow t1 t2) ▸TArrow t1 , t2 , ✔

-- data (option)
data DATA (A : Set) : Set where 
  □ : DATA A
  ■ : A -> DATA A

Data : Set 
Data = DATA Type

-- MData : Set 
-- MData = DATA Mark

NEW : (A : Set) -> Set 
NEW A = A × Newness 

NewType : Set 
NewType = NEW Type 

NewData : Set 
NewData = NEW Data

NewMark : Set 
NewMark = NEW Mark

-- NewMData : Set 
-- NewMData = NEW MData

-- data ExpPointer : Set where 
--   Here : ExpPointer 
--   PFun : ExpPointer -> ExpPointer
--   PAp1 : ExpPointer -> ExpPointer
--   PAp2 : ExpPointer -> ExpPointer
--   PAsc : ExpPointer -> ExpPointer

-- data ExpPointerSet : Set where 
--   P∅ : ExpPointerSet
--   _P,_ : ExpPointer -> ExpPointerSet -> ExpPointerSet

mutual 

  data ExpUp : Set where  
    _⇒_ : ExpMid -> NewData -> ExpUp

  data ExpMid : Set where 
    EConst : ExpMid 
    EHole : ExpMid
    EFun : NewType -> Mark -> Mark -> ExpLow -> ExpMid 
    EAp : ExpLow -> Mark -> ExpLow -> ExpMid 
    EVar : ℕ -> Mark -> ExpMid 
    EAsc : NewType -> ExpLow -> ExpMid 

  data ExpLow : Set where 
    _[_]⇐_ : ExpUp -> Mark -> NewData -> ExpLow

data Program : Set where 
  Root : ExpUp -> Newness -> Program
  
ExpLowOfProgram : Program -> ExpLow  
ExpLowOfProgram (Root e n) = (e [ ✔ ]⇐ (□ , n)) 

data SubsumableMid : ExpMid -> Set where 
  SubsumableConst : SubsumableMid EConst
  SubsumableHole : SubsumableMid EHole
  SubsumableAp : ∀ {e1 m e2} -> SubsumableMid (EAp e1 m e2) 
  SubsumableVar : ∀ {x m} -> SubsumableMid (EVar x m) 
  SubsumableAsc : ∀ {t e} -> SubsumableMid (EAsc t e) 

Subsumable : ExpUp -> Set 
Subsumable (mid ⇒ _) = SubsumableMid mid

data Context (A : Set) : Set where 
  ∅ : Context A
  _∷_ : A -> Context A -> Context A
  
Ctx : Set 
Ctx = Context NewType
