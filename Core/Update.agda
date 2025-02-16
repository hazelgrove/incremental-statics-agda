
open import Data.Product

open import Prelude
open import Core.Core
open import Core.Environment
open import Core.WellTyped
open import Core.VarsSynthesize

module Core.Update where

  infix 10 _l↦_ 
  infix 10 _u↦_ 

  data _l↦_ : ExpLow -> ExpLow -> Set where 
    StepNewSynConsist : ∀ {e-all t-syn t-ana m-all m-all' n-ana} ->
      t-syn ~D (■ t-ana) , m-all' ->
      (e-all ⇒ (t-syn , New)) [ m-all ]⇐ (■ t-ana , n-ana) l↦
      (e-all ⇒ (t-syn , Old)) [ m-all' ]⇐ (■ t-ana , n-ana)
    StepNewAnaConsist : ∀ {e-all t-syn t-ana n-syn m-all m-all'} ->
      SubsumableMid e-all -> 
      t-syn ~D t-ana , m-all' ->
      (e-all ⇒ (t-syn , n-syn)) [ m-all ]⇐ (t-ana , New) l↦
      (e-all ⇒ (t-syn , n-syn)) [ m-all' ]⇐ (t-ana , Old) 
    StepAnaFun : ∀ {x e-body n-asc syn-all ana-body t-ana t-asc t-in-ana t-out-ana t-body n-body m-ana m-asc m-body m-all m-ana' m-asc'} ->
      t-ana ▸DTArrow t-in-ana , t-out-ana , m-ana' ->
      t-asc ■~D t-in-ana , m-asc' ->
      ((EFun x (t-asc , n-asc) m-ana m-asc ((e-body ⇒ (t-body , n-body)) [ m-body ]⇐ ana-body)) ⇒ syn-all) [ m-all ]⇐ (t-ana , New) l↦
      ((EFun x (t-asc , n-asc) m-ana' m-asc' ((e-body ⇒ (t-body , n-body)) [ m-body ]⇐ (t-out-ana , New))) ⇒ ((DUnless (DArrow t-asc t-body) t-ana) , New)) [ ✔ ]⇐ (t-ana , Old)
    StepNewAnnFun : ∀ {x e-body e-body' t-asc n-body n-body' n-ana m-ana m-asc m-body m-all syn-body syn-body' syn-all ana-body ana-all } ->
      VarsSynthesize? x t-asc ✔ (e-body ⇒ (syn-body , n-body)) (e-body' ⇒ (syn-body' , n-body')) ->
      (((EFun x (t-asc , New) m-ana m-asc ((e-body ⇒ (syn-body , n-body)) [ m-body ]⇐ ana-body)) ⇒ syn-all) [ m-all ]⇐ (ana-all , n-ana)) l↦
      (((EFun x (t-asc , Old) m-ana m-asc ((e-body' ⇒ (syn-body' , n-body')) [ m-body ]⇐ ana-body)) ⇒ syn-all) [ m-all ]⇐ (ana-all , New))
    StepSynFun : ∀ {x e-body t-asc t-body n-asc m-body syn-all ana-all m1 m2 m3 n-ana n-body} ->
      (((EFun x (t-asc , n-asc) m1 m2 ((e-body ⇒ (t-body , New)) [ m-body ]⇐ (□ , n-body))) ⇒ syn-all) [ m3 ]⇐ (ana-all , n-ana)) l↦
      (((EFun x (t-asc , n-asc) m1 m2 ((e-body ⇒ (t-body , Old)) [ ✔ ]⇐ (□ , n-body) )) ⇒ (DUnless (DArrow t-asc t-body) ana-all , New)) [ m3 ]⇐ (ana-all , n-ana))
    
  data _u↦_ : ExpUp -> ExpUp -> Set where 
    StepAp : ∀ {e-fun e-arg t-fun t-in-fun t-out-fun m-all m-arg m m-fun n-fun syn-all ana-fun ana-arg} ->
      t-fun ▸DTArrow t-in-fun , t-out-fun , m-fun -> 
      (EAp ((e-fun ⇒ (t-fun , New)) [ m ]⇐ (ana-fun , n-fun)) m-all (e-arg [ m-arg ]⇐ ana-arg)) ⇒ syn-all u↦
      (EAp ((e-fun ⇒ (t-fun , Old)) [ ✔ ]⇐ (ana-fun , n-fun)) m-fun (e-arg [ m-arg ]⇐ (t-in-fun , New))) ⇒ (t-out-fun , New)
    StepAsc : ∀ {e-body t-asc m-body syn-all ana-body} ->
      (EAsc (t-asc , New) (e-body [ m-body ]⇐ ana-body)) ⇒ syn-all  u↦
      (EAsc (t-asc , Old) (e-body [ m-body ]⇐ (■ t-asc , New))) ⇒ (■ t-asc , New)

  data _U↦_ : (e e' : ExpUp) -> Set where
    StepUp : ∀{ε e e' e-in e-in'} ->
      ε U⟦ e-in ⟧U≡ e ->
      e-in u↦ e-in' ->
      ε U⟦ e-in' ⟧U≡ e' ->
      e U↦ e'
    StepLow : ∀{ε e e' e-in e-in'} ->
      ε L⟦ e-in ⟧U≡ e ->
      e-in l↦ e-in' ->
      ε L⟦ e-in' ⟧U≡ e' ->
      e U↦ e'

  data _L↦_ : (e e' : ExpLow) -> Set where
    StepUp : ∀{ε e e' e-in e-in'} ->
      ε U⟦ e-in ⟧L≡ e ->
      e-in u↦ e-in' ->
      ε U⟦ e-in' ⟧L≡ e' ->
      e L↦ e'
    StepLow : ∀{ε e e' e-in e-in'} ->
      ε L⟦ e-in ⟧L≡ e ->
      e-in l↦ e-in' ->
      ε L⟦ e-in' ⟧L≡ e' ->
      e L↦ e'

  data _P↦_ : (p p' : Program) -> Set where
    InsideStep : ∀{p p'} ->
      (ExpLowOfProgram p) L↦ (ExpLowOfProgram p') ->
      p P↦ p'
    TopStep : ∀ {e t n} ->
      (Root (e ⇒ (t , New)) n) P↦ (Root (e ⇒ (t , Old)) n)
  
  _↤P_ : Program -> Program -> Set 
  p' ↤P p = p P↦ p'

  StepUpLow : ∀{ε e e' e-in e-in'} ->
    ε U⟦ e-in ⟧L≡ e ->
    e-in U↦ e-in' ->
    ε U⟦ e-in' ⟧L≡ e' ->
    e L↦ e'
  StepUpLow fill1 (StepUp fill2 step fill3) fill4 = StepUp (FillUUL fill2 fill1) step (FillUUL fill3 fill4)
  StepUpLow fill1 (StepLow fill2 step fill3) fill4 = StepLow (FillLUL fill2 fill1) step (FillLUL fill3 fill4)

  StepLowLow : ∀{ε e e' e-in e-in'} ->
    ε L⟦ e-in ⟧L≡ e ->
    e-in L↦ e-in' ->
    ε L⟦ e-in' ⟧L≡ e' ->
    e L↦ e'
  StepLowLow fill1 (StepUp fill2 step fill3) fill4 = StepUp (FillULL fill2 fill1) step (FillULL fill3 fill4)
  StepLowLow fill1 (StepLow fill2 step fill3) fill4 = StepLow (FillLLL fill2 fill1) step (FillLLL fill3 fill4)

  StepLowUp : ∀{ε e e' e-in e-in'} ->
    ε L⟦ e-in ⟧U≡ e ->
    e-in L↦ e-in' ->
    ε L⟦ e-in' ⟧U≡ e' ->
    e U↦ e'
  StepLowUp fill1 (StepUp fill2 step fill3) fill4 = StepUp (FillULU fill2 fill1) step (FillULU fill3 fill4)
  StepLowUp fill1 (StepLow fill2 step fill3) fill4 = StepLow (FillLLU fill2 fill1) step (FillLLU fill3 fill4)