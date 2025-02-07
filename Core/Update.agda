open import Data.Nat hiding (_+_)
open import Data.Unit 
open import Data.Bool hiding (_<_; _≟_)
open import Data.Sum renaming (_⊎_ to _+_; inj₁ to Inl ; inj₂ to Inr) hiding (map)
open import Data.Product hiding (map)
open import Relation.Nullary 
open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Prelude

open import Core.Core
open import Core.WellTyped

module Core.Update where

data VarsSynthesize : ℕ -> Type -> ExpUp -> ExpUp -> Set where 
  VSConst : ∀ {x t syn} ->
    VarsSynthesize x t (EConst ⇒ syn) (EConst ⇒ syn)
  VSHole : ∀ {x t syn} ->
    VarsSynthesize x t (EHole ⇒ syn) (EHole ⇒ syn)
  VSFun : ∀ {x t asc m-ana m-asc e-body e-body' m-body syn-all ana-body} ->
    VarsSynthesize (suc x) t e-body e-body' ->
    VarsSynthesize x t ((EFun asc m-ana m-asc (e-body [ m-body ]⇐ ana-body)) ⇒ syn-all) ((EFun asc m-ana m-asc (e-body' [ m-body ]⇐ ana-body)) ⇒ syn-all)
  VSAp : ∀ {x t syn e1 e2 e1' e2' ana1 ana2 m1 m2 m3} ->
    VarsSynthesize x t e1 e1' ->
    VarsSynthesize x t e2 e2' ->
    VarsSynthesize x t ((EAp (e1 [ m1 ]⇐ ana1) m2 (e2 [ m3 ]⇐ ana2)) ⇒ syn) ((EAp (e1' [ m1 ]⇐ ana1) m2 (e2' [ m3 ]⇐ ana2)) ⇒ syn)
  VSVar : ∀ {x t syn} ->
    VarsSynthesize x t ((EVar x ✔) ⇒ syn) ((EVar x ✔) ⇒ ((■ t , New)))
  VSOtherVar : ∀ {x y t syn} ->
    ¬(x ≡ y) -> 
    VarsSynthesize y t ((EVar x ✔) ⇒ syn) ((EVar x ✔) ⇒ syn)
  VSAsc : ∀ {x t syn asc e e' ana m} ->
    VarsSynthesize x t e e' ->
    VarsSynthesize x t ((EAsc asc (e [ m ]⇐ ana)) ⇒ syn) ((EAsc asc (e' [ m ]⇐ ana)) ⇒ syn)

infix 10 _L↦_ 
infix 10 _U↦_ 

data _L↦_ : ExpLow -> ExpLow -> Set where 
  StepNewSynConsist : ∀ {e-all t-syn t-ana m-all m-all'} ->
    t-syn ~ t-ana , m-all' ->
    (e-all ⇒ ((■ t-syn , New))) [ m-all ]⇐ (■ t-ana , Old) L↦
    (e-all ⇒ ((■ t-syn , Old))) [ m-all' ]⇐ (■ t-ana , Old)
  StepNewAnaConsist : ∀ {e-all t-syn t-ana n-syn m-all m-all'} ->
    SubsumableMid e-all -> 
    t-syn ~ t-ana , m-all' ->
    (e-all ⇒ ((■ t-syn , n-syn))) [ m-all ]⇐ ((■ t-ana , New)) L↦
    (e-all ⇒ ((■ t-syn , Old))) [ m-all' ]⇐ ((■ t-ana , Old)) 
  StepAnaFun : ∀ {e-body n-asc syn-all ana-body t-ana t-asc t-in-ana t-out-ana t-body n-body m-ana m-asc m-body m-all m-ana' m-asc'} ->
    t-ana ▸DTArrow t-in-ana , t-out-ana , m-ana' ->
    t-asc ■~D t-in-ana , m-asc' ->
    ((EFun (t-asc , n-asc) m-ana m-asc ((e-body ⇒ (t-body , n-body)) [ m-body ]⇐ ana-body)) ⇒ syn-all) [ m-all ]⇐ (t-ana , New) L↦
    ((EFun (t-asc , n-asc) m-ana' m-asc' ((e-body ⇒ (t-body , n-body)) [ m-body ]⇐ (t-out-ana , New))) ⇒ ((DUnless (DArrow t-asc t-body) t-ana) , New)) [ ✔ ]⇐ (t-ana , Old)
  StepNewAnnFun : ∀ {e-body e-body' t-asc t-body n-body m-body syn-all} ->
    VarsSynthesize 0 t-asc (e-body ⇒ ((■ t-body , n-body))) e-body' ->
    (((EFun (t-asc , New) ✔ ✔ ((e-body ⇒ ((■ t-body , n-body))) [ m-body ]⇐ (□ , Old))) ⇒ syn-all) [ ✔ ]⇐ (□ , Old)) L↦
    (((EFun (t-asc , Old) ✔ ✔ (e-body' [ m-body ]⇐ (□ , Old))) ⇒ ((■ (TArrow t-asc t-body) , New))) [ ✔ ]⇐ (□ , Old))
  StepSynFun : ∀ {e-body t-asc t-body n-asc m-body syn-all} ->
    (((EFun (t-asc , n-asc) ✔ ✔ ((e-body ⇒ (t-body , New)) [ m-body ]⇐ (□ , Old))) ⇒ syn-all) [ ✔ ]⇐ (□ , Old)) L↦
    (((EFun (t-asc , n-asc) ✔ ✔ ((e-body ⇒ (t-body , Old)) [ ✔ ]⇐ (□ , Old) )) ⇒ (DArrow t-asc t-body , New)) [ ✔ ]⇐ (□ , Old))
  
  -- StepVoidSynFun : ∀ {e-body t-asc t-body n-asc n-body m-body syn-all} ->
  --   (((EFun (t-asc , n-asc) ✔ ✔ ((e-body ⇒ ((■ t-body , n-body))) [ m-body ]⇐ (□ , {!   !}))) ⇒ syn-all) [ ✔ ]⇐ (□ , {!   !})) L↦
  --   (((EFun (t-asc , n-asc) ✔ ✔ ((e-body ⇒ ((■ t-body , Old))) [ m-body ]⇐ (□ , {!   !}))) ⇒ ((■ (TArrow t-asc t-body) , New))) [ ✔ ]⇐ (□ , {!   !}))

data _U↦_ : ExpUp -> ExpUp -> Set where 
  StepAp : ∀ {e-fun e-arg t-fun t-in-fun t-out-fun m-all m-arg m-fun syn-all ana-arg} ->
    t-fun ▸TArrow t-in-fun , t-out-fun , m-fun -> 
    (EAp ((e-fun ⇒ ((■ t-fun , New))) [ ✔ ]⇐ (□ , Old)) m-all (e-arg [ m-arg ]⇐ ana-arg)) ⇒ syn-all U↦
    (EAp ((e-fun ⇒ ((■ t-fun , Old))) [ ✔ ]⇐ (□ , Old)) m-fun (e-arg [ m-arg ]⇐ ((■ t-in-fun , New)))) ⇒ ((■ t-out-fun , New))
  StepAsc : ∀ {e-body t-asc m-body syn-all ana-body} ->
    (EAsc (t-asc , New) (e-body [ m-body ]⇐ ana-body)) ⇒ syn-all  U↦
    (EAsc (t-asc , Old) (e-body [ m-body ]⇐ ((■ t-asc , New)))) ⇒ ((■ t-asc , New))

mutual 

  data LEnvUp : Set where 
    LEnvUpRec : LEnvMid -> NewData -> LEnvUp

  data LEnvMid : Set where 
    LEnvFun : NewType -> Mark -> Mark -> LEnvLow -> LEnvMid 
    LEnvAp1 : LEnvLow -> Mark -> ExpLow -> LEnvMid 
    LEnvAp2 : ExpLow -> Mark -> LEnvLow -> LEnvMid 
    LEnvAsc : NewType -> LEnvLow -> LEnvMid 

  data LEnvLow : Set where 
    L⊙ : LEnvLow
    LEnvLowRec : LEnvUp -> Mark -> NewData -> LEnvLow

mutual 

  data UEnvUp : Set where 
    U⊙ : UEnvUp
    UEnvUpRec : UEnvMid -> NewData -> UEnvUp

  data UEnvMid : Set where 
    UEnvFun : NewType -> Mark -> Mark -> UEnvLow -> UEnvMid 
    UEnvAp1 : UEnvLow -> Mark -> ExpLow -> UEnvMid 
    UEnvAp2 : ExpLow -> Mark -> UEnvLow -> UEnvMid 
    UEnvAsc : NewType -> UEnvLow -> UEnvMid 

  data UEnvLow : Set where 
    UEnvLowRec : UEnvUp -> Mark -> NewData -> UEnvLow

mutual 
  data _L⟦_⟧Up==_ : (ε : LEnvUp) (e : ExpLow) (e' : ExpUp)  -> Set where
    FillLEnvUpRec : ∀ {e ε e' syn} ->
      ε L⟦ e ⟧Mid== e' ->
      (LEnvUpRec ε syn) L⟦ e ⟧Up== (e' ⇒ syn)

  data _L⟦_⟧Mid==_ : (ε : LEnvMid) (e : ExpLow) (e' : ExpMid)  -> Set where
    FillLEnvFun : ∀ {e ε e' t m1 m2} ->
      ε L⟦ e ⟧Low== e' ->
      (LEnvFun t m1 m2 ε) L⟦ e ⟧Mid== (EFun t m1 m2 e')
    FillLEnvAp1 : ∀ {e ε e' e2 m} ->
      ε L⟦ e ⟧Low== e' ->
      (LEnvAp1 ε m e2) L⟦ e ⟧Mid== (EAp e' m e2)
    FillLEnvAp2 : ∀ {e ε e' e1 m} ->
      ε L⟦ e ⟧Low== e' ->
      (LEnvAp2 e1 m ε) L⟦ e ⟧Mid== (EAp e1 m e')
    FillLEnvAsc : ∀ {e ε e' t} ->
      ε L⟦ e ⟧Low== e' ->
      (LEnvAsc t ε) L⟦ e ⟧Mid== (EAsc t e')

  data _L⟦_⟧Low==_ : (ε : LEnvLow) (e : ExpLow) (e' : ExpLow)  -> Set where
    FillL⊙ : ∀ {e} ->
      L⊙ L⟦ e ⟧Low== e
    FillLEnvLowRec : ∀ {e e' ana m ε} ->
      ε L⟦ e ⟧Up== e' ->
      LEnvLowRec ε m ana L⟦ e ⟧Low== (e' [ m ]⇐ ana)

mutual 
  data _U⟦_⟧Up==_ : (ε : UEnvUp) (e : ExpUp) (e' : ExpUp)  -> Set where
    FillU⊙ : ∀ {e} ->
      U⊙ U⟦ e ⟧Up== e
    FillUEnvUpRec : ∀ {e ε e' syn} ->
      ε U⟦ e ⟧Mid== e' ->
      (UEnvUpRec ε syn) U⟦ e ⟧Up== (e' ⇒ syn)

  data _U⟦_⟧Mid==_ : (ε : UEnvMid) (e : ExpUp) (e' : ExpMid)  -> Set where
    FillUEnvFun : ∀ {e ε e' t m1 m2} ->
      ε U⟦ e ⟧Low== e' ->
      (UEnvFun t m1 m2 ε) U⟦ e ⟧Mid== (EFun t m1 m2 e')
    FillUEnvAp1 : ∀ {e ε e' e2 m} ->
      ε U⟦ e ⟧Low== e' ->
      (UEnvAp1 ε m e2) U⟦ e ⟧Mid== (EAp e' m e2)
    FillUEnvAp2 : ∀ {e ε e' e1 m} ->
      ε U⟦ e ⟧Low== e' ->
      (UEnvAp2 e1 m ε) U⟦ e ⟧Mid== (EAp e1 m e')
    FillUEnvAsc : ∀ {e ε e' t} ->
      ε U⟦ e ⟧Low== e' ->
      (UEnvAsc t ε) U⟦ e ⟧Mid== (EAsc t e')

  data _U⟦_⟧Low==_ : (ε : UEnvLow) (e : ExpUp) (e' : ExpLow)  -> Set where
    FillUEnvLowRec : ∀ {e e' ana m ε} ->
      ε U⟦ e ⟧Up== e' ->
      UEnvLowRec ε m ana U⟦ e ⟧Low== (e' [ m ]⇐ ana)

data _Up↦_ : (e e' : ExpUp) -> Set where
  StepUp : ∀{ε e e' e-in e-in'} ->
    ε U⟦ e-in ⟧Up== e ->
    e-in U↦ e-in' ->
    ε U⟦ e-in' ⟧Up== e' ->
    e Up↦ e'
  StepLow : ∀{ε e e' e-in e-in'} ->
    ε L⟦ e-in ⟧Up== e ->
    e-in L↦ e-in' ->
    ε L⟦ e-in' ⟧Up== e' ->
    e Up↦ e'

data _Low↦_ : (e e' : ExpLow) -> Set where
  StepUp : ∀{ε e e' e-in e-in'} ->
    ε U⟦ e-in ⟧Low== e ->
    e-in U↦ e-in' ->
    ε U⟦ e-in' ⟧Low== e' ->
    e Low↦ e'
  StepLow : ∀{ε e e' e-in e-in'} ->
    ε L⟦ e-in ⟧Low== e ->
    e-in L↦ e-in' ->
    ε L⟦ e-in' ⟧Low== e' ->
    e Low↦ e'

data _P↦_ : (e e' : Program) -> Set where
  TopStepStep : ∀{e e'} ->
    e Up↦ e' ->
    (Root e) P↦ (Root e')
  TopStepDone : ∀{t e} ->
    (Root (e ⇒ ((■ t , New)))) P↦ (Root (e ⇒ ((■ t , Old))))