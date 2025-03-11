
open import Data.Unit 
open import Data.Product
open import Relation.Nullary 
open import Relation.Binary.PropositionalEquality

open import Prelude

module Core.Core where

  data Type : Set where 
    TBase : Type 
    THole : Type
    TArrow : Type -> Type -> Type 
    TProd : Type -> Type -> Type 

  postulate 
    Var : Set 
    _≡?_ : (x y : Var) -> Dec (x ≡ y) 

  data Binding : Set where 
    BHole : Binding
    BVar : Var -> Binding

  data ProdSide : Set where 
    Fst : ProdSide 
    Snd : ProdSide

  data BareExp : Set where 
    BareEConst : BareExp 
    BareEHole : BareExp
    BareEFun : Binding -> Type -> BareExp -> BareExp 
    BareEAp : BareExp -> BareExp -> BareExp 
    BareEVar : Var -> BareExp 
    BareEAsc : Type -> BareExp -> BareExp 
    BareEPair : BareExp -> BareExp -> BareExp 
    BareEProj : ProdSide -> BareExp -> BareExp

  data BareSubsumable : BareExp -> Set where 
    BareSubsumableConst : BareSubsumable BareEConst
    BareSubsumableHole : BareSubsumable BareEHole
    BareSubsumableAp : ∀ {e1 e2} -> BareSubsumable (BareEAp e1 e2) 
    BareSubsumableVar : ∀ {x} -> BareSubsumable (BareEVar x) 
    BareSubsumableAsc : ∀ {t e} -> BareSubsumable (BareEAsc t e) 
    BareSubsumableProj : ∀ {s e} -> BareSubsumable (BareEProj s e) 

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
  
  data _▸TArrow_,_,_ : Type -> Type -> Type -> Mark -> Set where 
    MArrowBase :
      TBase ▸TArrow THole , THole , ✖
    MArrowHole :
      THole ▸TArrow THole , THole , ✔
    MArrowArrow : ∀ {t1 t2} -> 
      (TArrow t1 t2) ▸TArrow t1 , t2 , ✔
    MArrowProd : ∀ {t1 t2} -> 
      (TProd t1 t2) ▸TArrow THole , THole , ✖
  
  data _▸TProd_,_,_ : Type -> Type -> Type -> Mark -> Set where 
    MProdBase :
      TBase ▸TProd THole , THole , ✖
    MProdHole :
      THole ▸TProd THole , THole , ✔
    MProdArrow : ∀ {t1 t2} -> 
      (TArrow t1 t2) ▸TProd THole , THole , ✖
    MProdProd : ∀ {t1 t2} -> 
      (TProd t1 t2) ▸TProd t1 , t2 , ✔

  data _,_▸TProj_,_ : Type -> ProdSide -> Type -> Mark -> Set where 
    MProdFst : ∀ {t t-fst t-snd m} -> 
      t ▸TProd t-fst , t-snd , m ->
      t , Fst ▸TProj t-fst , m 
    MProdSnd : ∀ {t t-fst t-snd m} ->
      t ▸TProd t-fst , t-snd , m ->
      t , Snd ▸TProj t-snd , m

  data _~_,_ : Type -> Type -> Mark -> Set where 
    ConsistHoleL : ∀ {t} -> THole ~ t , ✔
    ConsistHoleR : ∀ {t} -> t ~ THole , ✔
    ConsistBase : TBase ~ TBase , ✔
    ConsistArr : ∀ {t1 t2 t3 t4 m1 m2} -> 
      t1 ~ t3 , m1 -> 
      t2 ~ t4 , m2 -> 
      ((TArrow t1 t2) ~ (TArrow t3 t4) , (m1 ⊓M m2))
    ConsistProd : ∀ {t1 t2 t3 t4 m1 m2} -> 
      t1 ~ t3 , m1 -> 
      t2 ~ t4 , m2 -> 
      ((TProd t1 t2) ~ (TProd t3 t4) , (m1 ⊓M m2))
    InconsistBaseArr : ∀ {t1 t2} ->
      TBase ~ (TArrow t1 t2) , ✖
    InconsistArrBase : ∀ {t1 t2} ->
      (TArrow t1 t2) ~ TBase , ✖
    InconsistBaseProd : ∀ {t1 t2} ->
      TBase ~ (TProd t1 t2) , ✖
    InconsistProdBase : ∀ {t1 t2} ->
      (TProd t1 t2) ~ TBase , ✖
    InconsistArrProd : ∀ {t1 t2 t3 t4} ->
      (TArrow t1 t2) ~ (TProd t3 t4) , ✖
    InconsistProdArr : ∀ {t1 t2 t3 t4} ->
      (TProd t1 t2) ~ (TArrow t3 t4) , ✖

  data Data : Set where 
    □ : Data
    ■ : Type -> Data

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
      EPair : ExpLow -> ExpLow -> Mark -> ExpMid
      EProj : ProdSide -> ExpLow -> Mark -> ExpMid

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
    SubsumableProj : ∀ {s e m} -> SubsumableMid (EProj s e m) 

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