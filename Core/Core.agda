open import Data.Nat hiding (_+_; _⊓_; _⊔_)
open import Data.Unit 
open import Data.Bool hiding (_<_; _≟_)
open import Data.Sum renaming (_⊎_ to _+_; inj₁ to Inl ; inj₂ to Inr) hiding (map)
open import Data.Product hiding (map)
open import Relation.Nullary 
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Prelude

module Core.Core where

  data Type : Set where 
    TBase : Type 
    THole : Type
    TArrow : Type -> Type -> Type 

  postulate 
    Var : Set 
    _≡?_ : (x y : Var) -> Dec (x ≡ y) 

  data Binding : Set where 
    BHole : Binding
    BVar : Var -> Binding

  data BareExp : Set where 
    BareEConst : BareExp 
    BareEHole : BareExp
    BareEFun : Binding -> Type -> BareExp -> BareExp 
    BareEAp : BareExp -> BareExp -> BareExp 
    BareEVar : Var -> BareExp 
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

  NEW : (A : Set) -> Set 
  NEW A = A × Newness 

  NewType : Set 
  NewType = NEW Type 

  NewData : Set 
  NewData = NEW Data

  NewMark : Set 
  NewMark = NEW Mark

  mutual 

    data ExpUp : Set where  
      _⇒_ : ExpMid -> NewData -> ExpUp

    data ExpMid : Set where 
      EConst : ExpMid 
      EHole : ExpMid
      EFun : Binding -> NewType -> Mark -> Mark -> ExpLow -> ExpMid 
      EAp : ExpLow -> Mark -> ExpLow -> ExpMid 
      EVar : Var -> Mark -> ExpMid 
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
    _∶_∷_ : Var -> A -> Context A -> Context A

  _∶_∷?_ : {A : Set} -> Binding -> A -> Context A -> Context A
  BHole ∶ t ∷? Γ = Γ
  BVar x ∶ t ∷? Γ = x ∶ t ∷ Γ

  BareCtx : Set 
  BareCtx = Context Type

  data _,_∈_,_ : Var -> Type -> BareCtx -> Mark -> Set where 
    InCtxEmpty : ∀ {x} ->
      x , THole ∈ ∅ , ✖ 
    InCtxFound : ∀ {Γ x t} ->
      x , t ∈ (x ∶ t ∷ Γ) , ✔
    InCtxSkip : ∀ {Γ t t' x x' m} -> 
      ¬(x ≡ x') ->
      (x , t ∈ Γ , m) -> 
      (x , t ∈ (x' ∶ t' ∷ Γ) , m)

  _,_∈?_,_ : Binding -> Type -> BareCtx -> Mark -> Set
  BHole , t ∈? Γ , m = ⊤
  BVar x , t ∈? Γ , m = x , t ∈ Γ , m
    
  Ctx : Set 
  Ctx = Context NewType

  data BarrenCtx : Ctx -> BareCtx -> Set where 
    BarrenCtxEmpty : BarrenCtx ∅ ∅
    BarrenCtxCons : ∀ {x t n Γ Γ'} ->
      BarrenCtx Γ Γ' ->
      BarrenCtx (x ∶ (t , n) ∷ Γ) (x ∶ t ∷ Γ')

  BarrenCtxCons? : ∀ {x t n Γ Γ'} ->
    BarrenCtx Γ Γ' -> 
    BarrenCtx (x ∶ (t , n) ∷? Γ) (x ∶ t ∷? Γ')
  BarrenCtxCons? {BHole} ctx-bare = ctx-bare
  BarrenCtxCons? {BVar x} ctx-bare = BarrenCtxCons ctx-bare
