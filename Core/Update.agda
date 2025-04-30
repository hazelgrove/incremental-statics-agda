
open import Data.Product

open import Prelude
open import Core.Core
open import Core.SideConditions
open import Core.Environment
open import Core.WellFormed
open import Core.VariableUpdate

module Core.Update where

  infix 10 _a↦_ 
  infix 10 _s↦_ 

  data _a↦_ : AnaExp -> AnaExp -> Set where 
    StepSyn : ∀ {e-all t-syn t-ana m-all m-all' n-ana} ->
      t-syn ~D (■ t-ana) , m-all' ->
      (e-all ⇒ (t-syn , ★)) [ m-all ]⇐ (■ t-ana , n-ana) a↦
      (e-all ⇒ (t-syn , •)) [ m-all' ]⇐ (■ t-ana , n-ana)
    StepAna : ∀ {e-all t-syn t-ana n-syn m-all m-all'} ->
      SubsumableMid e-all -> 
      t-syn ~D t-ana , m-all' ->
      (e-all ⇒ (t-syn , n-syn)) [ m-all ]⇐ (t-ana , ★) a↦
      (e-all ⇒ (t-syn , n-syn)) [ m-all' ]⇐ (t-ana , •) 
    StepAnaFun : ∀ {x e-body n-asc syn-all ana-body t-ana t-asc t-in-ana t-out-ana t-body n-body m-ana m-asc m-body m-all m-ana' m-asc'} ->
      t-ana ▸DTArrow t-in-ana , t-out-ana , m-ana' ->
      t-asc ■~D t-in-ana , m-asc' ->
      ((EFun x (t-asc , n-asc) m-ana m-asc ((e-body ⇒ (t-body , n-body)) [ m-body ]⇐ ana-body)) ⇒ syn-all) [ m-all ]⇐ (t-ana , ★) a↦
      ((EFun x (t-asc , n-asc) m-ana' m-asc' ((e-body ⇒ (t-body , n-body)) [ m-body ]⇐ (t-out-ana , ★))) ⇒ ((DUnless (DArrow t-asc t-body) t-ana) , ★)) [ ✔ ]⇐ (t-ana , •)
    StepAnnFun : ∀ {x e-body e-body' t-asc n-ana m-ana m-asc m-body m-all syn-all ana-body ana-all } ->
      VariableUpdate? x t-asc ✔ (e-body) (e-body') ->
      (((EFun x (t-asc , ★) m-ana m-asc ((e-body) [ m-body ]⇐ ana-body)) ⇒ syn-all) [ m-all ]⇐ (ana-all , n-ana)) a↦
      (((EFun x (t-asc , •) m-ana m-asc ((e-body') [ m-body ]⇐ ana-body)) ⇒ syn-all) [ m-all ]⇐ (ana-all , ★))
    StepSynFun : ∀ {x e-body t-asc t-body n-asc m-body syn-all ana-all m1 m2 m3 n-ana n-body} ->
      (((EFun x (t-asc , n-asc) m1 m2 ((e-body ⇒ (t-body , ★)) [ m-body ]⇐ (□ , n-body))) ⇒ syn-all) [ m3 ]⇐ (ana-all , n-ana)) a↦
      (((EFun x (t-asc , n-asc) m1 m2 ((e-body ⇒ (t-body , •)) [ ✔ ]⇐ (□ , n-body) )) ⇒ (DUnless (DArrow t-asc t-body) ana-all , ★)) [ m3 ]⇐ (ana-all , n-ana))
    StepAnaPair : ∀ {e-fst e-snd t-fst t-snd n-fst n-snd t-fst-ana t-snd-ana ana-fst ana-snd m-fst m-snd m-ana m-ana' m-all syn-all ana-all} ->
      ana-all ▸DTProd t-fst-ana , t-snd-ana , m-ana' ->
      (((EPair ((e-fst ⇒ (t-fst , n-fst)) [ m-fst ]⇐ ana-fst) ((e-snd ⇒ (t-snd , n-snd)) [ m-snd ]⇐ ana-snd) m-ana) ⇒ syn-all) [ m-all ]⇐ (ana-all , ★)) a↦
      (((EPair ((e-fst ⇒ (t-fst , n-fst)) [ m-fst ]⇐ (t-fst-ana , ★)) ((e-snd ⇒ (t-snd , n-snd)) [ m-snd ]⇐ (t-snd-ana , ★)) m-ana') ⇒ (DUnless (DProd t-fst t-snd) ana-all , ★)) [ m-all ]⇐ (ana-all , •))
    StepSynPairFst : ∀ {e-fst e-snd t-fst t-snd n-snd n-fst ana-snd m-fst m-snd m-ana m-all syn-all ana-all n-ana} ->
      (((EPair ((e-fst ⇒ (t-fst , ★)) [ m-fst ]⇐ (□ , n-fst)) ((e-snd ⇒ (t-snd , n-snd)) [ m-snd ]⇐ ana-snd) m-ana) ⇒ syn-all) [ m-all ]⇐ (ana-all , n-ana)) a↦
      (((EPair ((e-fst ⇒ (t-fst , •)) [ ✔ ]⇐ (□ , n-fst)) ((e-snd ⇒ (t-snd , n-snd)) [ m-snd ]⇐ ana-snd) m-ana) ⇒ (DUnless (DProd t-fst t-snd) ana-all , ★)) [ m-all ]⇐ (ana-all , n-ana))
    StepSynPairSnd : ∀ {e-fst e-snd t-fst t-snd n-fst ana-fst n-snd m-fst m-snd m-ana m-all syn-all ana-all n-ana} ->
      (((EPair ((e-fst ⇒ (t-fst , n-fst)) [ m-fst ]⇐ ana-fst) ((e-snd ⇒ (t-snd , ★)) [ m-snd ]⇐ (□ , n-snd)) m-ana) ⇒ syn-all) [ m-all ]⇐ (ana-all , n-ana)) a↦
      (((EPair ((e-fst ⇒ (t-fst , n-fst)) [ m-fst ]⇐ ana-fst) ((e-snd ⇒ (t-snd , •)) [ ✔ ]⇐ (□ , n-snd)) m-ana) ⇒ (DUnless (DProd t-fst t-snd) ana-all , ★)) [ m-all ]⇐ (ana-all , n-ana))
    StepAnaTypFun : ∀ {x e-body syn-all ana-body t-ana t-body-ana t-body n-body m-ana m-body m-all m-ana'} ->
      t-ana , x ▸DTForallBind t-body-ana , m-ana' ->
      ((ETypFun x m-ana ((e-body ⇒ (t-body , n-body)) [ m-body ]⇐ ana-body)) ⇒ syn-all) [ m-all ]⇐ (t-ana , ★) a↦
      ((ETypFun x m-ana' ((e-body ⇒ (t-body , n-body)) [ m-body ]⇐ (t-body-ana , ★))) ⇒ ((DUnless (DForall x t-body) t-ana) , ★)) [ ✔ ]⇐ (t-ana , •)
    StepSynTypFun : ∀ {x e-body t-body m-body syn-all ana-all m1 m2 n-ana n-body} ->
      (((ETypFun x m1 ((e-body ⇒ (t-body , ★)) [ m-body ]⇐ (□ , n-body))) ⇒ syn-all) [ m2 ]⇐ (ana-all , n-ana)) a↦
      (((ETypFun x m1 ((e-body ⇒ (t-body , •)) [ ✔ ]⇐ (□ , n-body) )) ⇒ (DUnless (DForall x t-body) ana-all , ★)) [ m2 ]⇐ (ana-all , n-ana))

  data _s↦_ : SynExp -> SynExp -> Set where 
    StepAp : ∀ {e-fun e-arg t-fun t-in-fun t-out-fun m-all m-arg m m-fun n-fun syn-all ana-fun ana-arg} ->
      t-fun ▸DTArrow t-in-fun , t-out-fun , m-fun -> 
      (EAp ((e-fun ⇒ (t-fun , ★)) [ m ]⇐ (ana-fun , n-fun)) m-all (e-arg [ m-arg ]⇐ ana-arg)) ⇒ syn-all s↦
      (EAp ((e-fun ⇒ (t-fun , •)) [ m ]⇐ (ana-fun , n-fun)) m-fun (e-arg [ m-arg ]⇐ (t-in-fun , ★))) ⇒ (t-out-fun , ★)
    StepAsc : ∀ {e-body t-asc m-body syn-all ana-body} ->
      (EAsc (t-asc , ★) (e-body [ m-body ]⇐ ana-body)) ⇒ syn-all  s↦
      (EAsc (t-asc , •) (e-body [ m-body ]⇐ (■ t-asc , ★))) ⇒ (■ t-asc , ★)
    StepProj : ∀ {s e-body t-body t-side-body m-all m-body m-all-body syn-all ana-body} ->
      t-body , s ▸DTProj t-side-body , m-all-body -> 
      (EProj s ((e-body ⇒ (t-body , ★)) [ m-body ]⇐ ana-body) m-all) ⇒ syn-all s↦
      (EProj s ((e-body ⇒ (t-body , •)) [ m-body ]⇐ ana-body) m-all-body) ⇒ (t-side-body , ★)
    StepTypApFun : ∀ {e-fun m ana-fun t-fun n-fun m-fun m-all x t-fun-body t-arg n-arg t-syn syn-all} ->
      t-fun ▸DTForall x , t-fun-body , m-fun ->
      DSub t-arg x t-fun-body t-syn ->
      (ETypAp ((e-fun ⇒ (t-fun , ★)) [ m ]⇐ (ana-fun , n-fun)) m-all (t-arg , n-arg)) ⇒ syn-all s↦
      (ETypAp ((e-fun ⇒ (t-fun , •)) [ m ]⇐ (ana-fun , n-fun)) m-fun (t-arg , n-arg)) ⇒ (t-syn , ★)
    StepTypApArg : ∀ {e-fun m ana-fun t-fun n-fun n-ana-fun m-fun m-all x t-fun-body t-arg t-syn syn-all} ->
      t-fun ▸DTForall x , t-fun-body , m-fun ->
      DSub t-arg x t-fun-body t-syn ->
      (ETypAp ((e-fun ⇒ (t-fun , n-fun)) [ m ]⇐ (ana-fun , n-ana-fun)) m-all (t-arg , ★)) ⇒ syn-all s↦
      (ETypAp ((e-fun ⇒ (t-fun , n-fun)) [ m ]⇐ (ana-fun , n-ana-fun)) m-fun (t-arg , •)) ⇒ (t-syn , ★)

  data _S↦_ : (e e' : SynExp) -> Set where
    StepUp : ∀{ε e e' e-in e-in'} ->
      ε S⟦ e-in ⟧S≡ e ->
      e-in s↦ e-in' ->
      ε S⟦ e-in' ⟧S≡ e' ->
      e S↦ e'
    StepLow : ∀{ε e e' e-in e-in'} ->
      ε A⟦ e-in ⟧S≡ e ->
      e-in a↦ e-in' ->
      ε A⟦ e-in' ⟧S≡ e' ->
      e S↦ e'

  data _A↦_ : (e e' : AnaExp) -> Set where
    StepUp : ∀{ε e e' e-in e-in'} ->
      ε S⟦ e-in ⟧A≡ e ->
      e-in s↦ e-in' ->
      ε S⟦ e-in' ⟧A≡ e' ->
      e A↦ e'
    StepLow : ∀{ε e e' e-in e-in'} ->
      ε A⟦ e-in ⟧A≡ e ->
      e-in a↦ e-in' ->
      ε A⟦ e-in' ⟧A≡ e' ->
      e A↦ e'

  data _P↦_ : (p p' : Program) -> Set where
    InsideStep : ∀{p p'} ->
      (AnaExpOfProgram p) A↦ (AnaExpOfProgram p') ->
      p P↦ p'
    TopStep : ∀ {e t n} ->
      (Root (e ⇒ (t , ★)) n) P↦ (Root (e ⇒ (t , •)) n)
  
  _↤P_ : Program -> Program -> Set 
  p' ↤P p = p P↦ p'

  StepUpLow : ∀{ε e e' e-in e-in'} ->
    ε S⟦ e-in ⟧A≡ e ->
    e-in S↦ e-in' ->
    ε S⟦ e-in' ⟧A≡ e' ->
    e A↦ e'
  StepUpLow fill1 (StepUp fill2 step fill3) fill4 = StepUp (FillUUL fill2 fill1) step (FillUUL fill3 fill4)
  StepUpLow fill1 (StepLow fill2 step fill3) fill4 = StepLow (FillLUL fill2 fill1) step (FillLUL fill3 fill4)

  StepLowLow : ∀{ε e e' e-in e-in'} ->
    ε A⟦ e-in ⟧A≡ e ->
    e-in A↦ e-in' ->
    ε A⟦ e-in' ⟧A≡ e' ->
    e A↦ e'
  StepLowLow fill1 (StepUp fill2 step fill3) fill4 = StepUp (FillULL fill2 fill1) step (FillULL fill3 fill4)
  StepLowLow fill1 (StepLow fill2 step fill3) fill4 = StepLow (FillLLL fill2 fill1) step (FillLLL fill3 fill4)

  StepLowUp : ∀{ε e e' e-in e-in'} ->
    ε A⟦ e-in ⟧S≡ e ->
    e-in A↦ e-in' ->
    ε A⟦ e-in' ⟧S≡ e' ->
    e S↦ e'
  StepLowUp fill1 (StepUp fill2 step fill3) fill4 = StepUp (FillULU fill2 fill1) step (FillULU fill3 fill4)
  StepLowUp fill1 (StepLow fill2 step fill3) fill4 = StepLow (FillLLU fill2 fill1) step (FillLLU fill3 fill4)