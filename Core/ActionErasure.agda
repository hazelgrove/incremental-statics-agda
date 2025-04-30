
open import Relation.Binary.PropositionalEquality

open import Prelude
open import Core.Core
open import Core.Marking
open import Core.Actions
open import Core.VariableUpdateErasure
open import Core.TypVariableUpdateErasure

module Core.ActionErasure where


  αT↦-erase : ∀ {Γ α t t'} ->
    (Γ ⊢ α , t αT↦ t') ->
    (α , (T◇ t) αBT↦ (T◇ t'))
  αT↦-erase ActInsertBase = ActInsertBase
  αT↦-erase ActWrapArrowOne = ActWrapArrowOne
  αT↦-erase ActWrapArrowTwo = ActWrapArrowTwo
  αT↦-erase ActWrapProdOne = ActWrapProdOne
  αT↦-erase ActWrapProdTwo = ActWrapProdTwo
  αT↦-erase (ActInsertTVar x) = ActInsertTVar
  αT↦-erase ActWrapForall = ActWrapForall
  αT↦-erase ActUnwrapArrowOne = ActUnwrapArrowOne
  αT↦-erase ActUnwrapArrowTwo = ActUnwrapArrowTwo
  αT↦-erase ActUnwrapProdOne = ActUnwrapProdOne
  αT↦-erase ActUnwrapProdTwo = ActUnwrapProdTwo
  αT↦-erase ActUnwrapForall = ActUnwrapForall
  αT↦-erase ActDelete = ActDelete
  αT↦-erase (ActDeleteBinder in-ctx tvar-update) 
    rewrite tvar-update?-erase tvar-update = ActDeleteBinder
  αT↦-erase (ActInsertBinder tvar-update) 
    rewrite tvar-update?-erase tvar-update = ActInsertBinder
  
  AT↦-erase : ∀ {Γ A t t'} ->
    (Γ ⊢ A , t AT↦ t') ->
    (A , (T◇ t) ABT↦ (T◇ t'))
  AT↦-erase (ATDone step) = ATBareDone (αT↦-erase step)
  AT↦-erase (AArrowOne step) = ABareArrowOne (AT↦-erase step)
  AT↦-erase (AArrowTwo step) = ABareArrowTwo (AT↦-erase step)
  AT↦-erase (AProdOne step) = ABareProdOne (AT↦-erase step)
  AT↦-erase (AProdTwo step) = ABareProdTwo (AT↦-erase step)
  AT↦-erase (AForall step) = ABareForall (AT↦-erase step)
  
  αS↦-erase : ∀ {Γ α e e'} ->
    (Γ ⊢ α , e αS↦ e') ->
    (α , (S◇ e) αB↦ (S◇ e'))
  αS↦-erase ActInsertConst = ActInsertConst
  αS↦-erase ActWrapFun = ActWrapFun
  αS↦-erase ActWrapApOne = ActWrapApOne
  αS↦-erase ActWrapApTwo = ActWrapApTwo
  αS↦-erase ActWrapAsc = ActWrapAsc
  αS↦-erase ActWrapPairOne = ActWrapPairOne
  αS↦-erase ActWrapPairTwo = ActWrapPairTwo
  αS↦-erase ActWrapProj = ActWrapProj
  αS↦-erase ActWrapTypFun = ActWrapTypFun
  αS↦-erase ActWrapTypAp = ActWrapTypAp
  αS↦-erase ActDelete = ActDelete
  αS↦-erase ActUnwrapApOne = ActUnwrapApOne
  αS↦-erase ActUnwrapApTwo = ActUnwrapApTwo
  αS↦-erase ActUnwrapAsc = ActUnwrapAsc
  αS↦-erase ActUnwrapPairOne = ActUnwrapPairOne
  αS↦-erase ActUnwrapPairTwo = ActUnwrapPairTwo
  αS↦-erase ActUnwrapProj = ActUnwrapProj
  αS↦-erase (ActUnwrapTypFun in-ctx update) 
    rewrite exp-tvar-update?-erase update = ActUnwrapTypFun
  αS↦-erase ActUnwrapTypAp = ActUnwrapTypAp
  αS↦-erase (ActInsertVar in-ctx) = ActInsertVar
  αS↦-erase (ActUnwrapFun x var-update) 
    rewrite var-update?-erase var-update = ActUnwrapFun
  αS↦-erase (ActDeleteBinder in-ctx var-update) 
    rewrite var-update?-erase var-update = ActDeleteBinder
  αS↦-erase (ActInsertBinder var-update)
    rewrite var-update?-erase var-update = ActInsertBinder
  αS↦-erase (ActDeleteTypBinder in-ctx update)
    rewrite exp-tvar-update?-erase update = ActDeleteTypBinder
  αS↦-erase (ActInsertTypBinder update)
    rewrite exp-tvar-update?-erase update = ActInsertTypBinder

  αA↦-erase : ∀ {Γ α e e'} ->
    (Γ ⊢ α , e αA↦ e') ->
    (α , (A◇ e) αB↦ (A◇ e'))
  αA↦-erase (ALC x) = αS↦-erase x

  mutual 
    AS↦-erase : ∀ {Γ A e e'} ->
      (Γ ⊢ A , e AS↦ e') ->
      (A , (S◇ e) AB↦ (S◇ e'))
    AS↦-erase (AUpMid step) = AM↦-erase step

    AM↦-erase : ∀ {Γ A e e'} ->
      (Γ ⊢ A , e AM↦ e') ->
      (A , (C◇ e) AB↦ (C◇ e'))
    AM↦-erase (AMidAscOne step) = ABareAscOne (AT↦-erase step)
    AM↦-erase (AMidAscTwo step) = ABareAscTwo (AA↦-erase step)
    AM↦-erase (AMidFunOne step) = ABareFunOne (AT↦-erase step)
    AM↦-erase (AMidFunTwo step) = ABareFunTwo (AA↦-erase step)
    AM↦-erase (AMidApOne step) = ABareApOne (AA↦-erase step)
    AM↦-erase (AMidApTwo step) = ABareApTwo (AA↦-erase step)
    AM↦-erase (AMidPairOne step) = ABarePairOne (AA↦-erase step)
    AM↦-erase (AMidPairTwo step) = ABarePairTwo (AA↦-erase step)
    AM↦-erase (AMidProj step) = ABareProj (AA↦-erase step)
 
    AA↦-erase : ∀ {Γ A e e'} ->
      (Γ ⊢ A , e AA↦ e') ->
      (A , (A◇ e) AB↦ (A◇ e')) 
    AA↦-erase (ALowDone step) = ABareDone (αA↦-erase step)
    AA↦-erase (ALowUp step) = AS↦-erase step 

  AP↦-erase : ∀ {A p p'} -> 
    (A , p AP↦ p') ->
    (A , (P◇ p) AB↦ (P◇ p'))
  AP↦-erase (AStepProgram step) = AA↦-erase step