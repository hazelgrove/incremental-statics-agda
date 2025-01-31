open import Data.Nat hiding (_+_; _⊓_)
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
Old ⊓ Old = Old
Old ⊓ New = New
New ⊓ n = New
  
data MarkData : Set where 
  ✖ : MarkData
  ✔ : MarkData

data _~_ : Type -> Type -> Set where 
  ConsistBase : TBase ~ TBase
  ConsistHole1 : ∀ {t} -> t ~ THole
  ConsistHole2 : ∀ {t} -> THole ~ t
  ConsistArr : ∀ {t1 t2 t3 t4} -> t1 ~ t3 -> t2 ~ t4 -> (TArrow t1 t2) ~ (TArrow t3 t4)

data _~M_,_ : Type -> Type -> MarkData -> Set where 
  ConsistM : ∀ {t1 t2} ->
    t1 ~ t2 -> 
    t1 ~M t2 , ✔
  InconsistM : ∀ {t1 t2} ->
    ¬(t1 ~ t2) -> 
    t1 ~M t2 , ✖

data _▸TArrow_,_ : Type -> Type -> Type -> Set where 
  MArrowHole : THole ▸TArrow THole , THole
  MArrowArrow : ∀ {t1 t2} -> (TArrow t1 t2) ▸TArrow t1 , t2

data _̸▸TArrow : Type -> Set where 
  MArrowBase : TBase ̸▸TArrow

data _▸TArrowM_,_,_ : Type -> Type -> Type -> MarkData -> Set where 
  MArrowMatch : ∀ {t} ->
    t ̸▸TArrow ->
    t ▸TArrowM THole , THole , ✖
  MArrowNoMatch : ∀ {t t1 t2} ->
    t ▸TArrow t1 , t2 ->
    t ▸TArrowM t1 , t2 , ✔

NewType : Set 
NewType = (Type × Newness) 

data TypeData : Set where 
  □ : TypeData 
  ■ : NewType -> TypeData

NewMark : Set 
NewMark = MarkData × Newness

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
    _⇒_ : ExpMid -> TypeData -> ExpUp

  data ExpMid : Set where 
    EConst : ExpMid 
    EHole : ExpMid
    EFun : NewType -> MarkData -> MarkData -> ExpLow -> ExpMid 
    EAp : ExpLow -> MarkData -> ExpLow -> ExpMid 
    EVar : ℕ -> MarkData -> ExpMid 
    EAsc : NewType -> ExpLow -> ExpMid 

  data ExpLow : Set where 
    _[_]⇐_ : ExpUp -> MarkData -> TypeData -> ExpLow

data Program : Set where 
    PRoot : ExpUp -> Program

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
  
data _,_∈_ {A : Set} : ℕ -> A -> (Context A) -> Set where 
  InCtx0 : ∀ {Γ t} -> 0 , t ∈ (t ∷ Γ)
  InCtxSuc : ∀ {Γ t t' n} -> (n , t ∈ Γ) -> (suc n , t ∈ (t' ∷ Γ))

_̸∈_ : ∀ {A} -> ℕ -> (Context A) -> Set
x ̸∈ Γ = ∀ {t} -> ¬(x , t ∈ Γ)

Ctx : Set 
Ctx = Context NewType
