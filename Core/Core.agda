
open import Data.Unit 
open import Data.Product
open import Relation.Nullary 
open import Relation.Binary.PropositionalEquality

open import Prelude

module Core.Core where

  postulate 
    Var : Set 
    _≡?_ : (x y : Var) -> Dec (x ≡ y) 

  data Binding : Set where 
    BHole : Binding
    BVar : Var -> Binding

  data BareType : Set where 
    BareTBase : BareType 
    BareTHole : BareType
    BareTArrow : BareType -> BareType -> BareType 
    BareTProd : BareType -> BareType -> BareType 
    BareTVar : Var -> BareType
    BareTForall : Binding -> BareType -> BareType

  data ProdSide : Set where 
    Fst : ProdSide 
    Snd : ProdSide

  data BareExp : Set where 
    BareEConst : BareExp 
    BareEHole : BareExp
    BareEFun : Binding -> BareType -> BareExp -> BareExp 
    BareEAp : BareExp -> BareExp -> BareExp 
    BareEVar : Var -> BareExp 
    BareEAsc : BareType -> BareExp -> BareExp 
    BareEPair : BareExp -> BareExp -> BareExp 
    BareEProj : ProdSide -> BareExp -> BareExp

  data BareSubsumable : BareExp -> Set where 
    BareSubsumableConst : BareSubsumable BareEConst
    BareSubsumableHole : BareSubsumable BareEHole
    BareSubsumableAp : ∀ {e1 e2} -> BareSubsumable (BareEAp e1 e2) 
    BareSubsumableVar : ∀ {x} -> BareSubsumable (BareEVar x) 
    BareSubsumableAsc : ∀ {t e} -> BareSubsumable (BareEAsc t e) 
    BareSubsumableProj : ∀ {s e} -> BareSubsumable (BareEProj s e) 
    
  data Mark : Set where 
    ✖ : Mark
    ✔ : Mark
    
  _⊓M_ : Mark -> Mark -> Mark 
  ✔ ⊓M m = m
  ✖ ⊓M m = ✖

  data Type : Set where 
    TBase : Type 
    THole : Type
    TArrow : Type -> Type -> Type 
    TProd : Type -> Type -> Type 
    TVar : Var -> Mark -> Type
    TForall : Binding -> Type -> Type

  data Data : Set where 
    □ : Data
    ■ : Type -> Data

  data Dirtiness : Set where 
    • : Dirtiness 
    ★ : Dirtiness 

  _⊓_ : Dirtiness -> Dirtiness -> Dirtiness 
  • ⊓ n = n
  ★ ⊓ n = ★

  ○ : (A : Set) -> Set 
  ○ A = A × Dirtiness 

  ○Type : Set 
  ○Type = ○ Type 

  ○Data : Set 
  ○Data = ○ Data

  ○Mark : Set 
  ○Mark = ○ Mark

  mutual 

    data SynExp : Set where  
      _⇒_ : ConExp -> ○Data -> SynExp

    data ConExp : Set where 
      EConst : ConExp 
      EHole : ConExp
      EFun : Binding -> ○Type -> Mark -> Mark -> AnaExp -> ConExp 
      EAp : AnaExp -> Mark -> AnaExp -> ConExp 
      EVar : Var -> Mark -> ConExp 
      EAsc : ○Type -> AnaExp -> ConExp 
      EPair : AnaExp -> AnaExp -> Mark -> ConExp
      EProj : ProdSide -> AnaExp -> Mark -> ConExp

    data AnaExp : Set where 
      _[_]⇐_ : SynExp -> Mark -> ○Data -> AnaExp

  data Program : Set where 
    Root : SynExp -> Dirtiness -> Program
    
  AnaExpOfProgram : Program -> AnaExp  
  AnaExpOfProgram (Root e n) = (e [ ✔ ]⇐ (□ , n)) 

  data SubsumableMid : ConExp -> Set where 
    SubsumableConst : SubsumableMid EConst
    SubsumableHole : SubsumableMid EHole
    SubsumableAp : ∀ {e1 m e2} -> SubsumableMid (EAp e1 m e2) 
    SubsumableVar : ∀ {x m} -> SubsumableMid (EVar x m) 
    SubsumableAsc : ∀ {t e} -> SubsumableMid (EAsc t e) 
    SubsumableProj : ∀ {s e m} -> SubsumableMid (EProj s e m) 

  Subsumable : SynExp -> Set 
  Subsumable (mid ⇒ _) = SubsumableMid mid

  data Context (A : Set) : Set where 
    ∅ : Context A
    _∶_∷_ : Var -> A -> Context A -> Context A
    _T∷_ : Var -> Context A -> Context A

  _∶_∷?_ : {A : Set} -> Binding -> A -> Context A -> Context A
  BHole ∶ t ∷? Γ = Γ
  BVar x ∶ t ∷? Γ = x ∶ t ∷ Γ

  _T∷?_ : {A : Set} -> Binding -> Context A -> Context A
  BHole T∷? Γ = Γ
  BVar x T∷? Γ = x T∷ Γ

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
    InCtxTSkip : ∀ {Γ t x x' m} -> 
      (x , t ∈ Γ , m) -> 
      (x , t ∈ (x' T∷ Γ) , m)

  _,_∈?_,_ : Binding -> Type -> BareCtx -> Mark -> Set
  BHole , t ∈? Γ , m = ⊤
  BVar x , t ∈? Γ , m = x , t ∈ Γ , m

  data _T∈_,_ : Var -> BareCtx -> Mark -> Set where 
    InCtxEmpty : ∀ {x} ->
      x T∈ ∅ , ✖
    InCtxFound : ∀ {Γ x} ->
      x T∈ (x T∷ Γ) , ✔
    InCtxSkip : ∀ {Γ t x x' m} -> 
      (x T∈ Γ , m) -> 
      (x T∈ (x' ∶ t ∷ Γ) , m)
    InCtxTSkip : ∀ {Γ x x' m} -> 
      ¬(x ≡ x') ->
      (x T∈ Γ , m) -> 
      (x T∈ (x' T∷ Γ) , m)

  _T∈?_,_ : Binding -> BareCtx -> Mark -> Set
  BHole T∈? Γ , m = ⊤
  BVar x T∈? Γ , m = x T∈ Γ , m
    
  Ctx : Set 
  Ctx = Context ○Type