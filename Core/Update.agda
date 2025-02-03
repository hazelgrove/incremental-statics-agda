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
  VSFun : ∀ {x t asc m-ana m-asc e-body e-body' m-body syn-all ana-body} ->
    VarsSynthesize (suc x) t e-body e-body' ->
    VarsSynthesize x t ((EFun asc m-ana m-asc (e-body [ m-body ]⇐ ana-body)) ⇒ syn-all) ((EFun asc m-ana m-asc (e-body' [ m-body ]⇐ ana-body)) ⇒ syn-all)
  VSAp : ∀ {x t syn e1 e2 e1' e2' ana1 ana2 m1 m2 m3} ->
    VarsSynthesize x t e1 e1' ->
    VarsSynthesize x t e2 e2' ->
    VarsSynthesize x t ((EAp (e1 [ m1 ]⇐ ana1) m2 (e2 [ m3 ]⇐ ana2)) ⇒ syn) ((EAp (e1' [ m1 ]⇐ ana1) m2 (e2' [ m3 ]⇐ ana2)) ⇒ syn)
  VSVar : ∀ {x t syn} ->
    VarsSynthesize x t ((EVar x ✔) ⇒ syn) ((EVar x ✔) ⇒ (■ t))
  VSOtherVar : ∀ {x y t syn} ->
    ¬(x ≡ y) -> 
    VarsSynthesize y t ((EVar x ✔) ⇒ syn) ((EVar x ✔) ⇒ syn)
  VSAsc : ∀ {x t syn asc e e' ana m} ->
    VarsSynthesize x t e e' ->
    VarsSynthesize x t ((EAsc asc (e [ m ]⇐ ana)) ⇒ syn) ((EAsc asc (e' [ m ]⇐ ana)) ⇒ syn)

infix 10 _L↦_ 

data _L↦_ : ExpLow -> ExpLow -> Set where 
  -- NewSyn Step
  StepNewSynConsist : ∀ {t1 t2 m m' e} ->
    t1 ~M t2 , m' ->
    (e ⇒ (■ (t2 , New))) [ m ]⇐ (■ (t1 , Old)) L↦
    (e ⇒ (■ (t2 , Old))) [ m' ]⇐ (■ (t1 , Old)) 
  -- NewAna Step
  StepNewAnaConsist : ∀ {t1 t2 n m m' e} ->
    SubsumableMid e -> 
    t1 ~M t2 , m' ->
    (e ⇒ (■ (t2 , n))) [ m ]⇐ (■ (t1 , New)) L↦
    (e ⇒ (■ (t2 , Old))) [ m' ]⇐ (■ (t1 , Old)) 
  -- Fun Steps
  StepAnaFun : ∀ {e-body n-asc syn-all ana-body t-ana t-asc t-in-ana t-out-ana m-ana m-asc m-body m-all m-ana' m-asc'} ->
    t-ana ▸TArrowM t-in-ana , t-out-ana , m-ana' ->
    t-asc ~M t-in-ana , m-asc' ->
    ((EFun (t-asc , n-asc) m-ana m-asc (e-body [ m-body ]⇐ ana-body)) ⇒ syn-all) [ m-all ]⇐ (■ (t-ana , New)) L↦
    ((EFun (t-asc , n-asc) m-ana' m-asc' (e-body [ m-body ]⇐ (■ (t-out-ana , New)))) ⇒ □) [ ✔ ]⇐ (■ (t-ana , Old))
  StepNoAnaFun : ∀ {asc m-ana m-asc e-body m-body ana-body m-all} ->
    ((EFun asc m-ana m-asc (e-body [ m-body ]⇐ (■ ana-body))) ⇒ □) [ m-all ]⇐ □ L↦
    ((EFun asc m-ana m-asc (e-body [ ✔ ]⇐ □)) ⇒ □) [ ✔ ]⇐ □

-- data _U↦_ : ExpUp -> ExpUp -> Set where 
--   -- Fun Steps
--   StepNewAnnFun1 : ∀ {t1 n1 m t2 n2 e e'} ->
--     VarsSynthesize 0 (t1 , n1) (e ⇒ (■ (t2 , n2))) e' ->
--     (EFun (t1 , New) ✔ ((e ⇒ (■ (t2 , n2))) [ m ]⇐ □)) ⇒ □ U↦
--     (EFun (t1 , Old) ✔ (e' [ m ]⇐ □)) ⇒ (■ (TArrow t1 t2 , New))
--   StepNewAnnFun2 :  ∀ {n oldt1 oldt2 oldn1 oldn2 t1 n1 m t2 n2 e e'} ->
--     n ▸NArrow oldn1 , oldn2 ->
--     VarsSynthesize 0 (t1 , n1) (e ⇒ (■ (t2 , New))) e' ->
--     (EFun (t1 , n1) ✔ ((e ⇒ (■ (t2 , New))) [ m ]⇐ □)) ⇒ (■ (TArrow oldt1 oldt2 , n)) U↦
--     (EFun (t1 , Old) ✔ (e' [ m ]⇐ □)) ⇒ (■ (TArrow t1 oldt2 , NArrow n1 oldn2))
--   StepNewSynFun : ∀ {t1 n1 m t2 e syn syn'} ->
--     MergeSyn (TArrow t1 t2 , NArrow Old New) syn syn' -> 
--     (EFun (t1 , n1) ✔ ((e ⇒ (■ (t2 , New))) [ m ]⇐ □)) ⇒ syn U↦
--     (EFun (t1 , n1) ✔ ((e ⇒ (■ (t2 , Old))) [ m ]⇐ □ )) ⇒ (■ syn')
--   -- StepNewSynFun2 : ∀ {n oldt1 oldt2 oldn1 oldn2 t1 n1 m t2 n2 e} ->
--   --   n ▸NArrow oldn1 , oldn2 ->
--   --   ⇒ (■ (TArrow oldt1 oldt2 , n)) (EFun (t1 , n1) ✔ ((e ⇒ (■ (t2 , New))) [ m ]⇐ □)) U↦
--   --   ⇒ (■ (TArrow oldt1 t2 , NArrow oldn1 n2)) (EFun (t1 , n1) ✔ ((⇒ (■ (t2 , Old)) e) [ m ]⇐ □))
--   StepVoidSynFun : ∀ {t1 n1 m t2 n2 e} ->
--     (EFun (t1 , n1) ✔ ((e ⇒ (■ (t2 , n2))) [ m ]⇐ □)) ⇒ □ U↦
--     (EFun (t1 , n1) ✔ ((e ⇒ (■ (t2 , Old))) [ m ]⇐ □)) ⇒ (■ (TArrow t1 t2 , New))
--   -- Ap Steps
--   StepAp : ∀ {t t1 t2 syn syn' ana ana' e1 e2 m1 m1' mn m2} ->
--     (t , New) ▸NTArrow t1 , t2 , (m1' , mn) ->
--     MergeSyn t2 syn syn' -> 
--     MergeAna t1 ana ana' -> 
--     (EAp ((⇒ (■ (t , New)) e1) [ ✔ ]⇐ □) m1 (e2 [ m2 ]⇐ ana)) ⇒ syn U↦
--     (EAp ((⇒ (■ (t , Old)) e1) [ ✔ ]⇐ □) m1' (e2 [ m2 ]⇐ (■ ana'))) ⇒ (■ syn')
--   -- Asc Step
--   StepAsc : ∀ {syn syn' t n ana ana' m e} ->
--     IsNew n ->
--     MergeSyn (t , n) syn syn' -> 
--     MergeAna (t , n) ana ana' -> 
--     (EAsc (t , n) (e [ m ]⇐ ana)) ⇒ syn U↦
--     (EAsc (t , Old) (e [ m ]⇐ (■ ana'))) ⇒ (■ syn')

-- mutual 

--   data LEnvUp : Set where 
--     LEnvUpRec : SynData -> LEnvMid -> LEnvUp

--   data LEnvMid : Set where 
--     LEnvFun : NewType -> MarkData -> LEnvLow -> LEnvMid 
--     LEnvAp1 : LEnvLow -> MarkData -> ExpLow -> LEnvMid 
--     LEnvAp2 : ExpLow -> MarkData -> LEnvLow -> LEnvMid 
--     LEnvAsc : NewType -> LEnvLow -> LEnvMid 

--   data LEnvLow : Set where 
--     L⊙ : LEnvLow
--     LEnvLowRec : AnaData -> MarkData -> LEnvUp -> LEnvLow

-- mutual 

--   data UEnvUp : Set where 
--     U⊙ : UEnvUp
--     UEnvUpRec : SynData -> UEnvMid -> UEnvUp

--   data UEnvMid : Set where 
--     UEnvFun : NewType -> MarkData -> UEnvLow -> UEnvMid 
--     UEnvAp1 : UEnvLow -> MarkData -> ExpLow -> UEnvMid 
--     UEnvAp2 : ExpLow -> MarkData -> UEnvLow -> UEnvMid 
--     UEnvAsc : NewType -> UEnvLow -> UEnvMid 

--   data UEnvLow : Set where 
--     UEnvLowRec : AnaData -> MarkData -> UEnvUp -> UEnvLow

-- mutual 
--   data _L⟦_⟧Up==_ : (ε : LEnvUp) (e : ExpLow) (e' : ExpUp)  -> Set where
--     FillLEnvUpRec : ∀ {e ε e' syn} ->
--       ε L⟦ e ⟧Mid== e' ->
--       (LEnvUpRec syn ε) L⟦ e ⟧Up== (e ⇒ syn)

--   data _L⟦_⟧Mid==_ : (ε : LEnvMid) (e : ExpLow) (e' : ExpMid)  -> Set where
--     FillLEnvFun : ∀ {e ε e' t m} ->
--       ε L⟦ e ⟧Low== e' ->
--       (LEnvFun t m ε) L⟦ e ⟧Mid== (EFun t m e')
--     FillLEnvAp1 : ∀ {e ε e' e2 m} ->
--       ε L⟦ e ⟧Low== e' ->
--       (LEnvAp1 ε m e2) L⟦ e ⟧Mid== (EAp e' m e2)
--     FillLEnvAp2 : ∀ {e ε e' e1 m} ->
--       ε L⟦ e ⟧Low== e' ->
--       (LEnvAp2 e1 m ε) L⟦ e ⟧Mid== (EAp e1 m e')
--     FillLEnvAsc : ∀ {e ε e' t} ->
--       ε L⟦ e ⟧Low== e' ->
--       (LEnvAsc t ε) L⟦ e ⟧Mid== (EAsc t e')

--   data _L⟦_⟧Low==_ : (ε : LEnvLow) (e : ExpLow) (e' : ExpLow)  -> Set where
--     FillL⊙ : ∀ {e} ->
--       L⊙ L⟦ e ⟧Low== e
--     FillLEnvLowRec : ∀ {e e' ana m ε} ->
--       ε L⟦ e ⟧Up== e' ->
--       LEnvLowRec ana m ε L⟦ e ⟧Low== (e' [ m ]⇐ ana)

-- mutual 
--   data _U⟦_⟧Up==_ : (ε : UEnvUp) (e : ExpUp) (e' : ExpUp)  -> Set where
--     FillU⊙ : ∀ {e} ->
--       U⊙ U⟦ e ⟧Up== e
--     FillUEnvUpRec : ∀ {e ε e' syn} ->
--       ε U⟦ e ⟧Mid== e' ->
--       (UEnvUpRec syn ε) U⟦ e ⟧Up== (e' ⇒ syn)

--   data _U⟦_⟧Mid==_ : (ε : UEnvMid) (e : ExpUp) (e' : ExpMid)  -> Set where
--     FillUEnvFun : ∀ {e ε e' t m} ->
--       ε U⟦ e ⟧Low== e' ->
--       (UEnvFun t m ε) U⟦ e ⟧Mid== (EFun t m e')
--     FillUEnvAp1 : ∀ {e ε e' e2 m} ->
--       ε U⟦ e ⟧Low== e' ->
--       (UEnvAp1 ε m e2) U⟦ e ⟧Mid== (EAp e' m e2)
--     FillUEnvAp2 : ∀ {e ε e' e1 m} ->
--       ε U⟦ e ⟧Low== e' ->
--       (UEnvAp2 e1 m ε) U⟦ e ⟧Mid== (EAp e1 m e')
--     FillUEnvAsc : ∀ {e ε e' t} ->
--       ε U⟦ e ⟧Low== e' ->
--       (UEnvAsc t ε) U⟦ e ⟧Mid== (EAsc t e')

--   data _U⟦_⟧Low==_ : (ε : UEnvLow) (e : ExpUp) (e' : ExpLow)  -> Set where
--     FillUEnvLowRec : ∀ {e e' ana m ε} ->
--       ε U⟦ e ⟧Up== e' ->
--       UEnvLowRec ana m ε U⟦ e ⟧Low== (e' [ m ]⇐ ana)

-- data _Up↦_ : (e e' : ExpUp) -> Set where
--   StepUp : ∀{ε e e' e-in e-in'} ->
--     ε U⟦ e-in ⟧Up== e ->
--     e-in U↦ e-in' ->
--     ε U⟦ e-in' ⟧Up== e' ->
--     e Up↦ e'
--   StepLow : ∀{ε e e' e-in e-in'} ->
--     ε L⟦ e-in ⟧Up== e ->
--     e-in L↦ e-in' ->
--     ε L⟦ e-in' ⟧Up== e' ->
--     e Up↦ e'

-- data _Low↦_ : (e e' : ExpLow) -> Set where
--   StepUp : ∀{ε e e' e-in e-in'} ->
--     ε U⟦ e-in ⟧Low== e ->
--     e-in U↦ e-in' ->
--     ε U⟦ e-in' ⟧Low== e' ->
--     e Low↦ e'
--   StepLow : ∀{ε e e' e-in e-in'} ->
--     ε L⟦ e-in ⟧Low== e ->
--     e-in L↦ e-in' ->
--     ε L⟦ e-in' ⟧Low== e' ->
--     e Low↦ e'

-- data _P↦_ : (e e' : Program) -> Set where
--   TopStepStep : ∀{e e'} ->
--     e Up↦ e' ->
--     (PRoot e) P↦ (PRoot e')
--   TopStepDone : ∀{t n e} ->
--     IsNew n ->
--     (PRoot (e ⇒ (■ (t , n)))) P↦ (PRoot (e ⇒ (■ (t , Old))))