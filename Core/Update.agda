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
open import Core.VarsSynthesize

module Core.Update where

  infix 10 _L↦_ 
  infix 10 _U↦_ 

  data _L↦_ : ExpLow -> ExpLow -> Set where 
    StepNewSynConsist : ∀ {e-all t-syn t-ana m-all m-all'} ->
      t-syn ~ t-ana , m-all' ->
      (e-all ⇒ ((■ t-syn , New))) [ m-all ]⇐ (■ t-ana , Old) L↦
      (e-all ⇒ ((■ t-syn , Old))) [ m-all' ]⇐ (■ t-ana , Old)
    StepNewAnaConsist : ∀ {e-all t-syn t-ana n-syn m-all m-all'} ->
      SubsumableMid e-all -> 
      t-syn ~D t-ana , m-all' ->
      (e-all ⇒ (t-syn , n-syn)) [ m-all ]⇐ (t-ana , New) L↦
      (e-all ⇒ (t-syn , n-syn)) [ m-all' ]⇐ (t-ana , Old) 
    StepAnaFun : ∀ {x e-body n-asc syn-all ana-body t-ana t-asc t-in-ana t-out-ana t-body n-body m-ana m-asc m-body m-all m-ana' m-asc'} ->
      t-ana ▸DTArrow t-in-ana , t-out-ana , m-ana' ->
      t-asc ■~D t-in-ana , m-asc' ->
      ((EFun x (t-asc , n-asc) m-ana m-asc ((e-body ⇒ (t-body , n-body)) [ m-body ]⇐ ana-body)) ⇒ syn-all) [ m-all ]⇐ (t-ana , New) L↦
      ((EFun x (t-asc , n-asc) m-ana' m-asc' ((e-body ⇒ (t-body , n-body)) [ m-body ]⇐ (t-out-ana , New))) ⇒ ((DUnless (DArrow t-asc t-body) t-ana) , New)) [ ✔ ]⇐ (t-ana , Old)
    StepNewAnnFun : ∀ {x 
      e-body e-body' 
      t-asc t-in-ana t-out-ana
      n-body n-body' n-ana 
      m-ana m-asc m-ana' m-asc' m-body m-all 
      syn-body syn-body' syn-all 
      ana-body ana-all } ->
      ana-all ▸DTArrow t-in-ana , t-out-ana , m-ana' ->
      t-asc ■~D t-in-ana , m-asc' ->
      VarsSynthesize? x t-asc ✔ (e-body ⇒ (syn-body , n-body)) (e-body' ⇒ (syn-body' , n-body')) ->
      (((EFun x (t-asc , New) m-ana m-asc ((e-body ⇒ (syn-body , n-body)) [ m-body ]⇐ ana-body)) ⇒ syn-all) [ m-all ]⇐ (ana-all , n-ana)) L↦
      (((EFun x (t-asc , Old) m-ana m-asc' ((e-body' ⇒ (syn-body' , n-body')) [ m-body ]⇐ ana-body)) ⇒ (DUnless (DArrow t-asc syn-body') ana-all , New)) [ m-all ]⇐ (ana-all , n-ana))
    StepSynFun : ∀ {x e-body t-asc t-body n-asc m-body syn-all} ->
      (((EFun x (t-asc , n-asc) ✔ ✔ ((e-body ⇒ (t-body , New)) [ m-body ]⇐ (□ , Old))) ⇒ syn-all) [ ✔ ]⇐ (□ , Old)) L↦
      (((EFun x (t-asc , n-asc) ✔ ✔ ((e-body ⇒ (t-body , Old)) [ ✔ ]⇐ (□ , Old) )) ⇒ (DArrow t-asc t-body , New)) [ ✔ ]⇐ (□ , Old))
    
  data _U↦_ : ExpUp -> ExpUp -> Set where 
    StepAp : ∀ {e-fun e-arg t-fun t-in-fun t-out-fun m-all m-arg m-fun n-fun syn-all ana-arg} ->
      t-fun ▸DTArrow t-in-fun , t-out-fun , m-fun -> 
      (EAp ((e-fun ⇒ (t-fun , New)) [ ✔ ]⇐ (□ , n-fun)) m-all (e-arg [ m-arg ]⇐ ana-arg)) ⇒ syn-all U↦
      (EAp ((e-fun ⇒ (t-fun , Old)) [ ✔ ]⇐ (□ , n-fun)) m-fun (e-arg [ m-arg ]⇐ (t-in-fun , New))) ⇒ (t-out-fun , New)
    StepAsc : ∀ {e-body t-asc m-body syn-all ana-body} ->
      (EAsc (t-asc , New) (e-body [ m-body ]⇐ ana-body)) ⇒ syn-all  U↦
      (EAsc (t-asc , Old) (e-body [ m-body ]⇐ (■ t-asc , New))) ⇒ (■ t-asc , New)

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
    InsideStep : ∀{p p'} ->
      (ExpLowOfProgram p) Low↦ (ExpLowOfProgram p') ->
      p P↦ p'
    TopStep : ∀ {e t n} ->
      (Root (e ⇒ (t , New)) n) P↦ (Root (e ⇒ (t , Old)) n)

  StepUpLow : ∀{ε e e' e-in e-in'} ->
    ε U⟦ e-in ⟧Low== e ->
    e-in Up↦ e-in' ->
    ε U⟦ e-in' ⟧Low== e' ->
    e Low↦ e'
  StepUpLow fill1 (StepUp fill2 step fill3) fill4 = StepUp (FillUUL fill2 fill1) step (FillUUL fill3 fill4)
  StepUpLow fill1 (StepLow fill2 step fill3) fill4 = StepLow (FillLUL fill2 fill1) step (FillLUL fill3 fill4)

  StepLowLow : ∀{ε e e' e-in e-in'} ->
    ε L⟦ e-in ⟧Low== e ->
    e-in Low↦ e-in' ->
    ε L⟦ e-in' ⟧Low== e' ->
    e Low↦ e'
  StepLowLow fill1 (StepUp fill2 step fill3) fill4 = StepUp (FillULL fill2 fill1) step (FillULL fill3 fill4)
  StepLowLow fill1 (StepLow fill2 step fill3) fill4 = StepLow (FillLLL fill2 fill1) step (FillLLL fill3 fill4)