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
open import Core.Merge

module Core.Update where

data VarsSynthesize : ℕ -> NewType -> ExpUp -> ExpUp -> Set where 
  VSConst : ∀ {x t syn} ->
    VarsSynthesize x t (EConst ⇒ syn) (EConst ⇒ syn)
  VSHole : ∀ {x t syn} ->
    VarsSynthesize x t (EHole ⇒ syn) (EHole ⇒ syn)
  VSFun : ∀ {x t syn asc ana m1 m2 e e'} ->
    VarsSynthesize (suc x) t e e' ->
    VarsSynthesize x t ((EFun asc m1 (ELow ana m2 e)) ⇒ syn) ((EFun asc m1 (ELow ana m2 e')) ⇒ syn)
  VSAp : ∀ {x t syn e1 e2 e1' e2' ana1 ana2 m1 m2 m3} ->
    VarsSynthesize x t e1 e1' ->
    VarsSynthesize x t e2 e2' ->
    VarsSynthesize x t ((EAp (ELow ana1 m1 e1) m2 (ELow ana2 m3 e2)) ⇒ syn) ((EAp (ELow ana1 m1 e1') m2 (ELow ana2 m3 e2')) ⇒ syn)
  VSVar : ∀ {x t syn} ->
    VarsSynthesize x t ((EVar x Unmarked) ⇒ syn) ((EVar x Unmarked) ⇒ (⇑ t))
  VSAsc : ∀ {x t syn asc e e' ana m} ->
    VarsSynthesize x t e e' ->
    VarsSynthesize x t ((EAsc asc (ELow ana m e)) ⇒ syn) ((EAsc asc (ELow ana m e')) ⇒ syn)

data _L↦_ : ExpLow -> ExpLow -> Set where 
  -- NewSyn Steps
  StepNewSynConsist : ∀ {t1 t2 m n e} ->
    IsNew n ->
    t1 ~ t2 ->
    ELow (⇓ (t1 , Old)) m (e ⇒ (⇑ (t2 , n))) L↦
    ELow (⇓ (t1 , Old)) Unmarked (e ⇒ (⇑ (t2 , Old))) 
  StepNewSynInconsist : ∀ {t1 t2 m n e} ->
    IsNew n ->
    ¬(t1 ~ t2) ->
    ELow (⇓ (t1 , Old)) m (e ⇒ (⇑ (t2 , n))) L↦
    ELow (⇓ (t1 , Old)) Marked (e ⇒ (⇑ (t2 , Old))) 
  -- NewAna Steps
  StepNewAnaConsist : ∀ {t1 t2 n1 n2 m e} ->
    IsNew n1 ->
    SubsumableMid e -> 
    t1 ~ t2 ->
    ELow (⇓ (t1 , n1)) m (e ⇒ (⇑ (t2 , n2))) L↦
    ELow (⇓ (t1 , Old)) Unmarked (e ⇒ (⇑ (t2 , Old))) 
  StepNewAnaInconsist : ∀ {t1 t2 n1 n2 m e} ->
    IsNew n1 ->
    SubsumableMid e -> 
    ¬(t1 ~ t2) ->
    ELow (⇓ (t1 , n1)) m (e ⇒ (⇑ (t2 , n2))) L↦
    ELow (⇓ (t1 , Old)) Marked (e ⇒ (⇑ (t2 , Old))) 
  -- Fun Steps
  StepAnaFun : ∀ {t t1 t2 tasc n n1 n2 nasc m1 m2 m3 syn ana e} ->
    IsNew n ->
    t ▸TArrow t1 , t2 ->
    n ▸NArrow n1 , n2 ->
    tasc ~ t1 ->
    ELow (⇓ (t , n)) m1 ((EFun (tasc , nasc) m2 (ELow ana m3 e)) ⇒ syn) L↦
    ELow (⇓ (t , Old)) Unmarked ((EFun (tasc , nasc) Unmarked (ELow (⇓ (t2 , n2)) m3 e)) ⇒ □)
  StepAnaFunFail1 : ∀ {t t1 t2 tasc n n1 n2 nasc m1 m2 m3 syn ana e} ->
    IsNew n ->
    t ▸TArrow t1 , t2 ->
    n ▸NArrow n1 , n2 ->
    ¬(tasc ~ t1) ->
    ELow (⇓ (t , n)) m1 ((EFun (tasc , nasc) m2 (ELow ana m3 e)) ⇒ syn) L↦
    ELow (⇓ (t , Old)) Unmarked ((EFun (tasc , nasc) Marked (ELow (⇓ (t2 , n2)) m3 e)) ⇒ □)
  StepAnaFunFail2 : ∀ {t asc n m1 m2 m3 ana e} ->
    IsNew n ->
    t ̸▸TArrow ->
    ELow (⇓ (t , n)) m1 ((EFun asc m2 (ELow (⇓ ana) m3 e)) ⇒ □) L↦
    ELow (⇓ (t , Old)) Unmarked ((EFun asc Unmarked (ELow ̸⇓ Unmarked e)) ⇒ □)
  StepNoAnaFun : ∀ {asc m1 m2 ana e} ->
    ELow ̸⇓ Unmarked ((EFun asc m1 (ELow (⇓ ana) m2 e)) ⇒ □) L↦
    ELow ̸⇓ Unmarked ((EFun asc m1 (ELow ̸⇓ Unmarked e)) ⇒ □)

data _U↦_ : ExpUp -> ExpUp -> Set where 
  -- Fun Steps
  StepNewAnnFun1 : ∀ {t1 n1 m t2 n2 e e'} ->
    IsNew n1 ->
    VarsSynthesize 0 (t1 , n1) (e ⇒ (⇑ (t2 , n2))) e' ->
    (EFun (t1 , n1) Unmarked (ELow ̸⇓ m (e ⇒ (⇑ (t2 , n2))))) ⇒ □ U↦
    (EFun (t1 , Old) Unmarked (ELow ̸⇓ m e')) ⇒ (⇑ (TArrow t1 t2 , New))
  StepNewAnnFun2 :  ∀ {n oldt1 oldt2 oldn1 oldn2 t1 n1 m t2 n2 e e'} ->
    IsNew n2 ->
    n ▸NArrow oldn1 , oldn2 ->
    VarsSynthesize 0 (t1 , n1) (⇒ (⇑ (t2 , n2)) e) e' ->
    ⇒ (⇑ (TArrow oldt1 oldt2 , n)) (EFun (t1 , n1) Unmarked (ELow ̸⇓ m (⇒ (⇑ (t2 , n2)) e))) U↦
    ⇒ (⇑ (TArrow t1 oldt2 , NArrow n1 oldn2)) (EFun (t1 , Old) Unmarked (ELow ̸⇓ m e'))
  StepNewSynFun : ∀ {t1 n1 m t2 n2 e syn syn'} ->
    IsNew n2 ->
    MergeSyn (TArrow t1 t2 , NArrow Old n2) syn syn' -> 
    ⇒ syn (EFun (t1 , n1) Unmarked (ELow ̸⇓ m (⇒ (⇑ (t2 , n2)) e))) U↦
    ⇒ (⇑ syn') (EFun (t1 , n1) Unmarked (ELow ̸⇓ m (⇒ (⇑ (t2 , Old)) e)))
  -- StepNewSynFun2 : ∀ {n oldt1 oldt2 oldn1 oldn2 t1 n1 m t2 n2 e} ->
  --   IsNew n2 ->
  --   n ▸NArrow oldn1 , oldn2 ->
  --   ⇒ (⇑ (TArrow oldt1 oldt2 , n)) (EFun (t1 , n1) Unmarked (ELow ̸⇓ m (⇒ (⇑ (t2 , n2)) e))) U↦
  --   ⇒ (⇑ (TArrow oldt1 t2 , NArrow oldn1 n2)) (EFun (t1 , n1) Unmarked (ELow ̸⇓ m (⇒ (⇑ (t2 , Old)) e)))
  StepVoidSynFun : ∀ {t1 n1 m t2 n2 e} ->
    ⇒ □ (EFun (t1 , n1) Unmarked (ELow ̸⇓ m (⇒ (⇑ (t2 , n2)) e))) U↦
    ⇒ (⇑ (TArrow t1 t2 , New)) (EFun (t1 , n1) Unmarked (ELow ̸⇓ m (⇒ (⇑ (t2 , Old)) e)))
  -- Ap Steps
  StepAp : ∀ {t n t1 t2 syn syn' ana ana' e1 e2 m1 m1' mn m2} ->
    IsNew n ->
    (t , n) ▸NTArrow t1 , t2 , (m1' , mn) ->
    MergeSyn t2 syn syn' -> 
    MergeAna t1 ana ana' -> 
    ⇒ syn (EAp (ELow ̸⇓ Unmarked (⇒ (⇑ (t , n)) e1)) m1 (ELow ana m2 e2)) U↦
    ⇒ (⇑ syn') (EAp (ELow ̸⇓ Unmarked (⇒ (⇑ (t , Old)) e1)) m1' (ELow (⇓ ana') m2 e2))
  -- Asc Step
  StepAsc : ∀ {syn syn' t n ana ana' m e} ->
    IsNew n ->
    MergeSyn (t , n) syn syn' -> 
    MergeAna (t , n) ana ana' -> 
    ⇒ syn (EAsc (t , n) (ELow ana m e)) U↦
    ⇒ (⇑ syn') (EAsc (t , Old) (ELow (⇓ ana') m e))

mutual 

  data LEnvUp : Set where 
    LEnvUpRec : SynData -> LEnvMid -> LEnvUp

  data LEnvMid : Set where 
    LEnvFun : NewType -> MarkData -> LEnvLow -> LEnvMid 
    LEnvAp1 : LEnvLow -> MarkData -> ExpLow -> LEnvMid 
    LEnvAp2 : ExpLow -> MarkData -> LEnvLow -> LEnvMid 
    LEnvAsc : NewType -> LEnvLow -> LEnvMid 

  data LEnvLow : Set where 
    L⊙ : LEnvLow
    LEnvLowRec : AnaData -> MarkData -> LEnvUp -> LEnvLow

mutual 

  data UEnvUp : Set where 
    U⊙ : UEnvUp
    UEnvUpRec : SynData -> UEnvMid -> UEnvUp

  data UEnvMid : Set where 
    UEnvFun : NewType -> MarkData -> UEnvLow -> UEnvMid 
    UEnvAp1 : UEnvLow -> MarkData -> ExpLow -> UEnvMid 
    UEnvAp2 : ExpLow -> MarkData -> UEnvLow -> UEnvMid 
    UEnvAsc : NewType -> UEnvLow -> UEnvMid 

  data UEnvLow : Set where 
    UEnvLowRec : AnaData -> MarkData -> UEnvUp -> UEnvLow

mutual 
  data _L⟦_⟧Up==_ : (ε : LEnvUp) (e : ExpLow) (e' : ExpUp)  -> Set where
    FillLEnvUpRec : ∀ {e ε e' syn} ->
      ε L⟦ e ⟧Mid== e' ->
      (LEnvUpRec syn ε) L⟦ e ⟧Up== (⇒ syn e')

  data _L⟦_⟧Mid==_ : (ε : LEnvMid) (e : ExpLow) (e' : ExpMid)  -> Set where
    FillLEnvFun : ∀ {e ε e' t m} ->
      ε L⟦ e ⟧Low== e' ->
      (LEnvFun t m ε) L⟦ e ⟧Mid== (EFun t m e')
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
      LEnvLowRec ana m ε L⟦ e ⟧Low== (ELow ana m e')

mutual 
  data _U⟦_⟧Up==_ : (ε : UEnvUp) (e : ExpUp) (e' : ExpUp)  -> Set where
    FillU⊙ : ∀ {e} ->
      U⊙ U⟦ e ⟧Up== e
    FillUEnvUpRec : ∀ {e ε e' syn} ->
      ε U⟦ e ⟧Mid== e' ->
      (UEnvUpRec syn ε) U⟦ e ⟧Up== (⇒ syn e')

  data _U⟦_⟧Mid==_ : (ε : UEnvMid) (e : ExpUp) (e' : ExpMid)  -> Set where
    FillUEnvFun : ∀ {e ε e' t m} ->
      ε U⟦ e ⟧Low== e' ->
      (UEnvFun t m ε) U⟦ e ⟧Mid== (EFun t m e')
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
      UEnvLowRec ana m ε U⟦ e ⟧Low== (ELow ana m e')

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
    (PRoot e) P↦ (PRoot e')
  TopStepDone : ∀{t n e} ->
    IsNew n ->
    (PRoot (⇒ (⇑ (t , n)) e)) P↦ (PRoot (⇒ (⇑ (t , Old)) e))