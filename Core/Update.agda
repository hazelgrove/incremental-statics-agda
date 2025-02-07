open import Data.Nat hiding (_+_)
open import Data.Unit 
open import Data.Bool hiding (_<_; _≟_)
open import Data.Sum renaming (_⊎_ to _+_; inj₁ to Inl ; inj₂ to Inr) hiding (map)
open import Data.Product hiding (map)
open import Relation.Nullary 
open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Prelude

open import Core.Core
open import Core.Environment
open import Core.WellTyped

module Core.Update where

data VarsSynthesize : Var -> Type -> ExpUp -> ExpUp -> Set where 
  VSConst : ∀ {x t syn} ->
    VarsSynthesize x t (EConst ⇒ syn) (EConst ⇒ syn)
  VSHole : ∀ {x t syn} ->
    VarsSynthesize x t (EHole ⇒ syn) (EHole ⇒ syn)
  VSFunEq : ∀ {x t asc m-ana m-asc e-body m-body syn-all ana-body} ->
    VarsSynthesize x t ((EFun (BVar x) asc m-ana m-asc (e-body [ m-body ]⇐ ana-body)) ⇒ syn-all) ((EFun (BVar x) asc m-ana m-asc (e-body [ m-body ]⇐ ana-body)) ⇒ syn-all)
  VSFunNeq : ∀ {x x' t asc m-ana m-asc e-body e-body' m-body syn-all ana-body} ->
    ¬((BVar x) ≡ x') ->
    VarsSynthesize x t e-body e-body' ->
    VarsSynthesize x t ((EFun x' asc m-ana m-asc (e-body [ m-body ]⇐ ana-body)) ⇒ syn-all) ((EFun x' asc m-ana m-asc (e-body' [ m-body ]⇐ ana-body)) ⇒ syn-all)
  VSAp : ∀ {x t syn e1 e2 e1' e2' ana1 ana2 m1 m2 m3} ->
    VarsSynthesize x t e1 e1' ->
    VarsSynthesize x t e2 e2' ->
    VarsSynthesize x t ((EAp (e1 [ m1 ]⇐ ana1) m2 (e2 [ m3 ]⇐ ana2)) ⇒ syn) ((EAp (e1' [ m1 ]⇐ ana1) m2 (e2' [ m3 ]⇐ ana2)) ⇒ syn)
  VSVarEq : ∀ {x m t syn} ->
    VarsSynthesize x t ((EVar x m) ⇒ syn) ((EVar x ✔) ⇒ ((■ t , New)))
  VSVarNeq : ∀ {x x' t m syn} ->
    ¬(x ≡ x') -> 
    VarsSynthesize x t ((EVar x' m) ⇒ syn) ((EVar x' m) ⇒ syn)
  VSAsc : ∀ {x t syn asc e e' ana m} ->
    VarsSynthesize x t e e' ->
    VarsSynthesize x t ((EAsc asc (e [ m ]⇐ ana)) ⇒ syn) ((EAsc asc (e' [ m ]⇐ ana)) ⇒ syn)

VarsSynthesize? : Binding -> Type -> ExpUp -> ExpUp -> Set
VarsSynthesize? BHole t e1 e2 = e1 ≡ e2
VarsSynthesize? (BVar x) t e1 e2 = VarsSynthesize x t e1 e2

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
  StepAnaFun : ∀ {x e-body n-asc syn-all ana-body t-ana t-asc t-in-ana t-out-ana t-body n-body m-ana m-asc m-body m-all m-ana' m-asc'} ->
    t-ana ▸DTArrow t-in-ana , t-out-ana , m-ana' ->
    t-asc ■~D t-in-ana , m-asc' ->
    ((EFun x (t-asc , n-asc) m-ana m-asc ((e-body ⇒ (t-body , n-body)) [ m-body ]⇐ ana-body)) ⇒ syn-all) [ m-all ]⇐ (t-ana , New) L↦
    ((EFun x (t-asc , n-asc) m-ana' m-asc' ((e-body ⇒ (t-body , n-body)) [ m-body ]⇐ (t-out-ana , New))) ⇒ ((DUnless (DArrow t-asc t-body) t-ana) , New)) [ ✔ ]⇐ (t-ana , Old)
  StepNewAnnFun : ∀ {x e-body e-body' t-asc t-body n-body m-body syn-all} ->
    VarsSynthesize? x t-asc (e-body ⇒ (■ t-body , n-body)) e-body' ->
    (((EFun x (t-asc , New) ✔ ✔ ((e-body ⇒ ((■ t-body , n-body))) [ m-body ]⇐ (□ , Old))) ⇒ syn-all) [ ✔ ]⇐ (□ , Old)) L↦
    (((EFun x (t-asc , Old) ✔ ✔ (e-body' [ m-body ]⇐ (□ , Old))) ⇒ ((■ (TArrow t-asc t-body) , New))) [ ✔ ]⇐ (□ , Old))
  StepSynFun : ∀ {x e-body t-asc t-body n-asc m-body syn-all} ->
    (((EFun x (t-asc , n-asc) ✔ ✔ ((e-body ⇒ (t-body , New)) [ m-body ]⇐ (□ , Old))) ⇒ syn-all) [ ✔ ]⇐ (□ , Old)) L↦
    (((EFun x (t-asc , n-asc) ✔ ✔ ((e-body ⇒ (t-body , Old)) [ ✔ ]⇐ (□ , Old) )) ⇒ (DArrow t-asc t-body , New)) [ ✔ ]⇐ (□ , Old))
  
data _U↦_ : ExpUp -> ExpUp -> Set where 
  StepAp : ∀ {e-fun e-arg t-fun t-in-fun t-out-fun m-all m-arg m-fun syn-all ana-arg} ->
    t-fun ▸TArrow t-in-fun , t-out-fun , m-fun -> 
    (EAp ((e-fun ⇒ ((■ t-fun , New))) [ ✔ ]⇐ (□ , Old)) m-all (e-arg [ m-arg ]⇐ ana-arg)) ⇒ syn-all U↦
    (EAp ((e-fun ⇒ ((■ t-fun , Old))) [ ✔ ]⇐ (□ , Old)) m-fun (e-arg [ m-arg ]⇐ ((■ t-in-fun , New)))) ⇒ ((■ t-out-fun , New))
  StepAsc : ∀ {e-body t-asc m-body syn-all ana-body} ->
    (EAsc (t-asc , New) (e-body [ m-body ]⇐ ana-body)) ⇒ syn-all  U↦
    (EAsc (t-asc , Old) (e-body [ m-body ]⇐ ((■ t-asc , New)))) ⇒ ((■ t-asc , New))

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

data _P↦_ : (p p' : Program) -> Set where
  TopStep : ∀{p p'} ->
    (ExpLowOfProgram p) Low↦ (ExpLowOfProgram p') ->
    p P↦ p'