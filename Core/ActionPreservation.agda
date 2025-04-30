
open import Data.Product 
open import Relation.Binary.PropositionalEquality

open import Prelude
open import Core.Core
open import Core.SideConditions
open import Core.WellFormed
open import Core.Lemmas
open import Core.Actions
open import Core.VariableUpdatePreservation
open import Core.TypVariableUpdatePreservation

module Core.ActionPreservation where

  beyond-αA↦ : ∀ {Γ α e e' m m' ana ana'} -> 
    Γ ⊢ α , (e [ m ]⇐ ana) αA↦ (e' [ m' ]⇐ ana') -> 
    ◁▷ ana ana' 
  beyond-αA↦ (ALC _) = ◁▷C

  beyond-AA↦ : ∀ {Γ A e e' m m' ana ana'} -> 
    Γ ⊢ A , (e [ m ]⇐ ana) AA↦ (e' [ m' ]⇐ ana') -> 
    ◁▷ ana ana' 
  beyond-AA↦ (ALowDone (ALC _)) = ◁▷C
  beyond-AA↦ {ana = (_ , _)} (ALowUp x) = ◁▷C

  same-mark-AA↦ : ∀ {Γ A e e' m m' ana ana'} -> 
    Γ ⊢ A , (e [ m ]⇐ ana) AA↦ (e' [ m' ]⇐ ana') -> 
    m ≡ m'
  same-mark-AA↦ (ALowDone (ALC _)) = refl
  same-mark-AA↦ {ana = (_ , _)} (ALowUp x) = refl

  beyond-αS↦ : ∀ {Γ α e e' syn syn'} -> 
    Γ ⊢ α , (e ⇒ syn) αS↦ (e' ⇒ syn') -> 
    =▷ syn syn' 
  beyond-αS↦ ActInsertConst = =▷★
  beyond-αS↦ ActWrapFun = =▷★
  beyond-αS↦ ActWrapApOne = =▷★
  beyond-αS↦ ActWrapApTwo = =▷★
  beyond-αS↦ ActWrapPairOne = =▷★
  beyond-αS↦ ActWrapPairTwo = =▷★
  beyond-αS↦ ActWrapProj = =▷★
  beyond-αS↦ (ActInsertVar _) = =▷★
  beyond-αS↦ ActWrapAsc = =▷★
  beyond-αS↦ ActWrapTypFun = =▷★
  beyond-αS↦ ActWrapTypAp = =▷★
  beyond-αS↦ ActDelete = =▷★
  beyond-αS↦ (ActUnwrapFun _ _) = =▷★
  beyond-αS↦ ActUnwrapApOne = =▷★
  beyond-αS↦ ActUnwrapApTwo = =▷★
  beyond-αS↦ ActUnwrapAsc = =▷★
  beyond-αS↦ ActUnwrapPairOne = =▷★
  beyond-αS↦ ActUnwrapPairTwo = =▷★
  beyond-αS↦ ActUnwrapProj = =▷★
  beyond-αS↦ (ActUnwrapTypFun x x₁) = =▷★
  beyond-αS↦ ActUnwrapTypAp = =▷★
  beyond-αS↦ (ActDeleteBinder _ _) = =▷Refl
  beyond-αS↦ (ActInsertBinder _) = =▷Refl
  beyond-αS↦ (ActDeleteTypBinder x x₁) = =▷Refl
  beyond-αS↦ (ActInsertTypBinder x) = =▷Refl

  beyond-AS↦ : ∀ {Γ A e e' syn syn'} -> 
    Γ ⊢ A , (e ⇒ syn) AS↦ (e' ⇒ syn') -> 
    =▷ syn syn' 
  beyond-AS↦ (AUpMid step) = =▷Refl

  beyond-αA↦-inner : ∀ {Γ α e e' syn syn' m m' ana ana'} -> 
    Γ ⊢ α , ((e ⇒ syn) [ m ]⇐ ana) αA↦ ((e' ⇒ syn') [ m' ]⇐ ana') -> 
    =▷ syn syn' 
  beyond-αA↦-inner (ALC step) = beyond-αS↦ step

  beyond-AA↦-inner : ∀ {Γ A e e' syn syn' m m' ana ana'} -> 
    Γ ⊢ A , ((e ⇒ syn) [ m ]⇐ ana) AA↦ ((e' ⇒ syn') [ m' ]⇐ ana') -> 
    =▷ syn syn' 
  beyond-AA↦-inner (ALowDone step) = beyond-αA↦-inner step
  beyond-AA↦-inner (ALowUp step) = beyond-AS↦ step

  subsumable-AM↦ : ∀{Γ A e e'} ->
    SubsumableMid e ->
    Γ ⊢ A , e AM↦ e' ->
    SubsumableMid e'
  subsumable-AM↦ () (AMidFunOne x)
  subsumable-AM↦ () (AMidFunTwo x)
  subsumable-AM↦ SubsumableAsc (AMidAscOne x) = SubsumableAsc
  subsumable-AM↦ SubsumableAsc (AMidAscTwo x) = SubsumableAsc
  subsumable-AM↦ SubsumableAp (AMidApOne x) = SubsumableAp
  subsumable-AM↦ SubsumableAp (AMidApTwo x) = SubsumableAp
  subsumable-AM↦ SubsumableProj (AMidProj x) = SubsumableProj

  SynSubsume :  
    ∀ {Γ e t} ->
    Γ S⊢ (e ⇒ (t , ★)) ->
    Subsumable (e ⇒ (t , ★))
  SynSubsume (WFConst x) = SubsumableConst
  SynSubsume (WFHole x) = SubsumableHole
  SynSubsume (WFAp x x₁ x₂ x₃ x₄ x₅) = SubsumableAp
  SynSubsume (WFVar x x₁) = SubsumableVar
  SynSubsume (WFAsc wf x x₁ x₂) = SubsumableAsc
  SynSubsume (WFProj x x₁ x₂ x₃) = SubsumableProj
  SynSubsume (WFTypAp x x₁ x₂ x₃ x₄ x₅) = SubsumableTypAp

  WrapSubsume :  
    ∀ {Γ e t m ana} ->
    Γ S⊢ (e ⇒ (t , ★)) ->
    Γ A⊢ ((e ⇒ (t , ★)) [ m ]⇐ ana)
  WrapSubsume {t = t} {ana = ana} syn with ~N-dec (t , ★) ana
  ... | _ , ~N-pair x = WFSubsume (SynSubsume syn) (~N-pair x) ▶★ syn

  PreservationTypStep :  
    ∀ {Γ α t t'} ->
    (Γ T⊢ t) ->
    (Γ ⊢ α , t αT↦ t') ->   
    (Γ T⊢ t')
  PreservationTypStep wf ActInsertBase = WFBase
  PreservationTypStep wf ActWrapArrowOne = WFArrow wf WFHole
  PreservationTypStep wf ActWrapArrowTwo = WFArrow WFHole wf
  PreservationTypStep wf ActWrapProdOne = WFProd wf WFHole
  PreservationTypStep wf ActWrapProdTwo = WFProd WFHole wf
  PreservationTypStep wf (ActInsertTVar x) = WFTVar x
  PreservationTypStep wf ActWrapForall = WFForall wf
  PreservationTypStep wf ActDelete = WFHole
  PreservationTypStep (WFForall wf) (ActDeleteBinder x x₁) = WFForall (preservation-tvu-unwrap? wf x x₁)
  PreservationTypStep (WFForall wf) (ActInsertBinder x) = WFForall (preservation-tvu-wrap? wf x)
  PreservationTypStep (WFArrow wf _) ActUnwrapArrowOne = wf
  PreservationTypStep (WFArrow _ wf) ActUnwrapArrowTwo = wf
  PreservationTypStep (WFProd wf _) ActUnwrapProdOne = wf
  PreservationTypStep (WFProd _ wf) ActUnwrapProdTwo = wf
  PreservationTypStep (WFForall wf) ActUnwrapForall = wf

  PreservationStep :  
    ∀ {Γ α e e'} ->
    (Γ A⊢ e) ->
    (Γ ⊢ α , e αA↦ e') ->   
    (Γ A⊢ e')
  PreservationStep ana (ALC ActDelete) = WrapSubsume (WFHole (▷Pair ▶•))
  PreservationStep ana (ALC ActInsertConst) = WrapSubsume (WFConst (▷Pair ▶•))
  PreservationStep ana (ALC (ActInsertVar in-ctx)) = WrapSubsume (WFVar in-ctx (▷Pair ▶Same))
  PreservationStep ana (ALC ActWrapAsc) = WrapSubsume (WFAsc WFHole (▷Pair ▶Same) (▷Pair ▶Same) (dirty-ana ana))
  PreservationStep ana (ALC ActWrapApTwo) = WrapSubsume (WFAp (NTArrowC (DTArrowSome (proj₂ (proj₂ (proj₂ (▸TArrow-dec THole)))))) (▷Pair ▶★) (▷Pair ▶★) ▶★ (WFSubsume SubsumableHole (~N-pair ~DVoidR) ▶★ (WFHole (▷Pair ▶•))) (dirty-ana ana))
  -- PreservationStep ana (ALC {t = t} {n = n} (ActWrapFun {t = t'} {n = n'} var-update)) with ▸NTArrow-dec (t , ★) | ~N-dec (t' , n') (t , ★)
  -- ... | (t-in , ★) , (t-out , ★) , (m , ★) , NTArrowC consist | m' , consist-syn with ~N-dec (■ THole , ★) (t-in , ★) | dirty-through-~N-left consist-syn
  -- ... | _ , (~N-pair consist') | _ , refl = WFFun (NTArrowC consist) (■~N-pair (~N-pair consist')) (▷Pair ▶★) ▶★ ▶★ NUnless-dirty-▷ consist-syn ▶★ (dirty-ana (preservation-vars-ana?-alt ana var-update))
  PreservationStep ana (ALC {t = t} (ActWrapFun {t = t'})) with ▸DTArrow-dec t 
  ... | t-in , _ , _ , consist with ~D-dec (■ THole) t-in | ~D-dec t' t 
  ... | _ , consist1 | _ , consist2 = WFFun WFHole (NTArrowC consist) (■~N-pair (~N-pair consist1)) (▷Pair ▶★) ▶★ ▶★ NUnless-dirty-▷ (~N-pair ~DVoidL) ▶★ (dirty-ana ana)
  PreservationStep ana (ALC {t = t} (ActWrapApOne {t = t'} {n = n'})) with ~N-dec (t' , n') (t , ★) | ▸NTArrow-dec (t' , ★) 
  ... | _ , (~N-pair consist) | (t-in , ★) , (t-out , ★) , (m , ★) , NTArrowC consist' = WFSubsume SubsumableAp (~N-pair ~DVoidL) ▶★ (WFAp (NTArrowC consist') (▷Pair ▶★) (▷Pair ▶★) ▶★ (dirty-ana ana) (WFSubsume SubsumableHole (~N-pair ~DVoidR) ▶• (WFHole (▷Pair ▶•))))
  PreservationStep wt (ALC ActWrapPairOne) = WFPair (NTProdC (proj₂ (proj₂ (proj₂ (▸DTProd-dec _))))) (▷Pair ▶★) (▷Pair ▶★) ▶★ NUnless-dirty-▷ (~N-pair (proj₂ (~D-dec _ _))) ▶★ (dirty-ana {m = ✔} (dirty-syn-inner wt)) (WFSubsume SubsumableHole (~N-pair ~DVoidR) ▶★ (WFHole (▷Pair ▶•)))
  PreservationStep wt (ALC ActWrapPairTwo) = WFPair (NTProdC (proj₂ (proj₂ (proj₂ (▸DTProd-dec _))))) (▷Pair ▶★) (▷Pair ▶★) ▶★ NUnless-dirty-▷ (~N-pair (proj₂ (~D-dec _ _))) ▶★ (WFSubsume SubsumableHole (~N-pair ~DVoidR) ▶★ (WFHole (▷Pair ▶•))) (dirty-ana wt) 
  PreservationStep wt (ALC ActWrapProj) = WFSubsume SubsumableProj (~N-pair (proj₂ (~D-dec _ _))) ▶★ (WFProj (proj₂ (proj₂ (▸NTProj-dec _ _))) (▷Pair ▶★) ▶★ (dirty-ana wt))
  PreservationStep wf (ALC ActWrapTypFun) = WFTypFun (NTForallBindC (proj₂ (proj₂ (▸DTForallBind-dec _ _)))) (▷Pair ▶★) ▶★ NUnless-dirty-▷ (~N-pair ~DVoidL) ▶★ (dirty-ana wf)
  PreservationStep wf (ALC ActWrapTypAp) = WFSubsume SubsumableTypAp (~N-pair ~DVoidL) ▶★ (WFTypAp WFHole (NTForallC (proj₂ (proj₂ (proj₂ (▸DTForall-dec _))))) ▶★ (NSub-pair (proj₂ (DSub-dec _ _ _))) (▷Pair ▶★) (dirty-ana wf))

  PreservationStep (WFSubsume subsumable consist-t consist-m (WFAsc wf consist-syn consist-ana ana)) (ALC ActUnwrapAsc) = dirty-ana ana
  PreservationStep (WFSubsume subsumable consist-t consist-m (WFAp marrow consist-syn consist-ana consist-mark syn ana)) (ALC ActUnwrapApOne) = dirty-ana syn
  PreservationStep (WFSubsume subsumable consist-t consist-m (WFAp marrow consist-syn consist-ana consist-mark syn ana)) (ALC ActUnwrapApTwo) = dirty-ana ana
  PreservationStep (WFSubsume subsumable consist-t consist-m (WFProj x x₁ x₂ wt)) (ALC ActUnwrapProj) = dirty-ana wt
  PreservationStep (WFSubsume subsumable consist-t consist-m (WFTypAp x x₁ x₂ x₃ x₄ wf)) (ALC ActUnwrapTypAp) = dirty-ana wf
  PreservationStep (WFFun wf marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) (ALC (ActUnwrapFun in-ctx var-update)) = dirty-ana (preservation-vars-unwrap in-ctx ana var-update)
  -- PreservationStep (WFSubsume SubsumableAsc (~N-pair consist-t) consist-m (WFAsc {syn-all = syn-all} {n-syn = n-syn} consist-syn consist-ana ana)) (ALC {t = t} ActSetAsc) = WFSubsume SubsumableAsc (~N-pair consist-t) ▶★-max-r (WFAsc (▷Pair ▶★) (▷Pair ▶★) ana)
  -- PreservationStep (WFFun {x = x} marrow consist consist-ana consist-asc consist-body consist-syn (~N-pair consist-all) consist-m-all ana) (ALC {t = t} (ActSetAnn {t = t'})) with ▸NTArrow-dec (t , ★)
  -- ... | (t-in , ★) , (t-out , ★) , (m , ★) , NTArrowC consist with ~D-dec (■ t') t-in 
  -- ... | m' , consist' = WFFun (NTArrowC consist) (■~N-pair (~N-pair consist')) (▷Pair ▶★) ▶★ ▶★ NUnless-dirty-▷ (~N-pair consist-all) ▶★-max-r (dirty-ctx {x = x} ana)
  PreservationStep (WFFun wf (NTArrowC marrow) (■~N-pair (~N-pair consist)) consist-ana consist-asc consist-body consist-syn (~N-pair consist-all) consist-m-all ana) (ALC (ActDeleteBinder in-ctx var-update)) 
    = WFFun wf (NTArrowC marrow) (■~N-pair (~N-pair consist)) (▷Pair ▶★) ▶★ ▶★-max-r NUnless-dirty-▷ (~N-pair (proj₂ (~D-dec _ _))) ▶★-max-r (dirty-syn-inner (preservation-vars-unwrap in-ctx ana var-update))
  PreservationStep (WFFun wf (NTArrowC marrow) (■~N-pair (~N-pair consist)) consist-ana consist-asc consist-body consist-syn (~N-pair consist-all) consist-m-all ana) (ALC (ActInsertBinder var-update)) 
    = WFFun wf (NTArrowC marrow) (■~N-pair (~N-pair consist)) (▷Pair ▶★) ▶★ ▶★-max-r NUnless-dirty-▷ (~N-pair (proj₂ (~D-dec _ _))) ▶★-max-r (dirty-syn-inner (preservation-vars-ana? ana var-update))
  PreservationStep (WFPair x x₁ x₂ x₃ x₄ x₅ x₆ wt wt₁) (ALC ActUnwrapPairOne) = dirty-ana wt
  PreservationStep (WFPair x x₁ x₂ x₃ x₄ x₅ x₆ wt wt₁) (ALC ActUnwrapPairTwo) = dirty-ana wt₁
  
  PreservationStep (WFTypFun x x₁ x₂ x₃ x₄ x₅ wf) (ALC (ActUnwrapTypFun x₆ x₇)) = dirty-ana (preservation-etvu-unwrap-ana? wf x₆ x₇)
  PreservationStep (WFTypFun (NTForallBindC x) x₁ x₂ x₃ x₄ x₅ wf) (ALC (ActDeleteTypBinder x₆ x₇))  
    = WFTypFun (NTForallBindC (proj₂ (proj₂ (▸DTForallBind-dec _ _)))) (▷Pair ▶★) ▶★ NUnless-dirty-▷ (~N-pair (proj₂ (~D-dec _ _))) ▶★-max-r (dirty-syn-inner (preservation-etvu-unwrap-ana? wf x₆ x₇))
  PreservationStep (WFTypFun (NTForallBindC x) x₁ x₂ x₃ x₄ x₅ wf) (ALC (ActInsertTypBinder x₆)) 
    = WFTypFun (NTForallBindC (proj₂ (proj₂ (▸DTForallBind-dec _ _)))) (▷Pair ▶★) ▶★ NUnless-dirty-▷ (~N-pair (proj₂ (~D-dec _ _))) ▶★-max-r (dirty-syn-inner (preservation-etvu-wrap-ana-outer wf x₆))


  PreservationTyp :  
    ∀ {Γ A t t'} ->
    (Γ T⊢ t) ->
    (Γ ⊢ A , t AT↦ t') ->   
    (Γ T⊢ t')
  PreservationTyp wf (ATDone x) = PreservationTypStep wf x
  PreservationTyp (WFArrow wf wf₁) (AArrowOne act) = WFArrow (PreservationTyp wf act) wf₁
  PreservationTyp (WFArrow wf wf₁) (AArrowTwo act) = WFArrow wf (PreservationTyp wf₁ act)
  PreservationTyp (WFProd wf wf₁) (AProdOne act) = WFProd (PreservationTyp wf act) wf₁
  PreservationTyp (WFProd wf wf₁) (AProdTwo act) = WFProd wf (PreservationTyp wf₁ act)
  PreservationTyp (WFForall wf) (AForall act) = WFForall (PreservationTyp wf act)

  mutual 

    PreservationSyn :  
      ∀ {Γ A e e'} ->
      (Γ S⊢ e) ->
      (Γ ⊢ A , e AS↦ e') ->   
      (Γ S⊢ e')
    PreservationSyn (WFAsc wf a1 (▷Pair a2) ana) (AUpMid (AMidAscOne step)) = WFAsc (PreservationTyp wf step) (▷Pair ▶★) (▷Pair ▶★) ana
    PreservationSyn (WFAsc wf a1 (▷Pair a2) ana) (AUpMid (AMidAscTwo {e' = e' [ _ ]⇐ _} step)) with beyond-AA↦ step 
    ... | ◁▷C = WFAsc wf a1 (▷Pair a2) (PreservationAna ana step) 
    PreservationSyn (WFAp marrow consist-syn consist-ana consist-mark syn ana) (AUpMid (AMidApOne {e1' = (e-fun' ⇒ syn-fun') [ _ ]⇐ _} step)) with ▸NTArrow-dec syn-fun' 
    ... | t-in-fun' , t-out-fun' , m-fun' , marrow' with beyond-▸NTArrow (beyond-AA↦-inner step) marrow marrow' | same-mark-AA↦ step | beyond-AA↦ step
    ... | t-in-beyond , t-out-beyond , m-beyond | refl | ◁▷C = WFAp marrow' (beyond-▷ t-out-beyond consist-syn) (beyond-▷ t-in-beyond consist-ana) (beyond-▶ m-beyond consist-mark) (PreservationAna syn step) ana
    PreservationSyn (WFAp marrow consist-syn consist-ana consist-mark syn ana) (AUpMid (AMidApTwo {e2' = (e-arg' ⇒ syn-arg') [ _ ]⇐ _} step)) 
      = WFAp marrow consist-syn (beyond-▷-contra (beyond-AA↦ step) consist-ana) consist-mark syn (PreservationAna ana step)
    PreservationSyn (WFProj {s = s} x x₁ x₂ x₃) (AUpMid (AMidProj {e' = (e' ⇒ syn') [ _ ]⇐ _} step)) with ▸NTProj-dec s syn' 
    ... | _ , _ , mprod' with beyond-▸NTProj (beyond-AA↦-inner step) x mprod' | same-mark-AA↦ step | beyond-AA↦ step
    ... | t-beyond , m-beyond | refl | ◁▷C  = WFProj mprod' (beyond-▷ t-beyond x₁) (beyond-▶ m-beyond x₂) (PreservationAna x₃ step)

    PreservationAna :  
      ∀ {Γ A e e'} ->
      (Γ A⊢ e) ->
      (Γ ⊢ A , e AA↦ e') ->   
      (Γ A⊢ e')
    PreservationAna ana (ALowDone step) = PreservationStep ana step 
    PreservationAna (WFSubsume subsumable consist-t consist-m syn) (ALowUp {e' = e' ⇒ syn'} (AUpMid step)) = WFSubsume (subsumable-AM↦ subsumable step) consist-t consist-m (PreservationSyn syn (AUpMid step))
    PreservationAna (WFFun {x = x} {t-asc = t-asc} wf marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) (ALowUp (AUpMid (AMidFunOne {t' = t'} {t = t} step))) 
      = WFFun (PreservationTyp wf step) marrow (■~N-pair (~N-pair (proj₂ (~D-dec _ _)))) consist-ana consist-asc ▶★ (consist-unless-new consist-syn) consist-all consist-m-all (dirty-ctx {x = x} ana)
    
    PreservationAna (WFFun {t-asc = t-asc} wf marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) (ALowUp (AUpMid (AMidFunTwo {e' = (e' ⇒ _) [ _ ]⇐ _} step))) 
      = WFFun wf marrow consist (beyond-▷-contra (beyond-AA↦ step) consist-ana) consist-asc consist-body  (preservation-lambda-lemma {t = t-asc} (beyond-AA↦-inner step) consist-syn) consist-all consist-m-all (PreservationAna ana step)
    PreservationAna (WFPair x x₁ x₂ x₃ x₄ x₅ x₆ wt wt₁) (ALowUp (AUpMid (AMidPairOne {e1' = (e1' ⇒ _) [ _ ]⇐ _} step))) = WFPair x (beyond-▷-contra (beyond-AA↦ step) x₁) x₂ x₃ (preservation-pair-lemma (beyond-AA↦-inner step) =▷Refl x₄) x₅ x₆ (PreservationAna wt step) wt₁
    PreservationAna (WFPair x x₁ x₂ x₃ x₄ x₅ x₆ wt wt₁) (ALowUp (AUpMid (AMidPairTwo {e2' = (e2' ⇒ _) [ _ ]⇐ _} step))) = WFPair x x₁ (beyond-▷-contra (beyond-AA↦ step) x₂) x₃ (preservation-pair-lemma =▷Refl (beyond-AA↦-inner step) x₄) x₅ x₆ wt (PreservationAna wt₁ step)
    
  PreservationProgram :
    ∀ {A p p'} ->  
    (P⊢ p) ->   
    (A , p AP↦ p') ->        
    (P⊢ p')              
  PreservationProgram (WFProgram ana) (AStepProgram step) = WFProgram (PreservationAna ana step)      