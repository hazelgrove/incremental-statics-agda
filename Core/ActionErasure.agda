
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
  
  αU↦-erase : ∀ {Γ α e e'} ->
    (Γ ⊢ α , e αU↦ e') ->
    (α , (U◇ e) αB↦ (U◇ e'))
  αU↦-erase ActInsertConst = ActInsertConst
  αU↦-erase ActWrapFun = ActWrapFun
  αU↦-erase ActWrapApOne = ActWrapApOne
  αU↦-erase ActWrapApTwo = ActWrapApTwo
  αU↦-erase ActWrapAsc = ActWrapAsc
  αU↦-erase ActWrapPairOne = ActWrapPairOne
  αU↦-erase ActWrapPairTwo = ActWrapPairTwo
  αU↦-erase ActWrapProj = ActWrapProj
  αU↦-erase ActWrapTypFun = ActWrapTypFun
  αU↦-erase ActWrapTypAp = ActWrapTypAp
  αU↦-erase ActDelete = ActDelete
  αU↦-erase ActUnwrapApOne = ActUnwrapApOne
  αU↦-erase ActUnwrapApTwo = ActUnwrapApTwo
  αU↦-erase ActUnwrapAsc = ActUnwrapAsc
  αU↦-erase ActUnwrapPairOne = ActUnwrapPairOne
  αU↦-erase ActUnwrapPairTwo = ActUnwrapPairTwo
  αU↦-erase ActUnwrapProj = ActUnwrapProj
  αU↦-erase (ActUnwrapTypFun in-ctx update) 
    rewrite exp-tvar-update?-erase update = ActUnwrapTypFun
  αU↦-erase ActUnwrapTypAp = ActUnwrapTypAp
  αU↦-erase (ActInsertVar in-ctx) = ActInsertVar
  αU↦-erase (ActUnwrapFun x var-update) 
    rewrite var-update?-erase var-update = ActUnwrapFun
  αU↦-erase (ActDeleteBinder in-ctx var-update) 
    rewrite var-update?-erase var-update = ActDeleteBinder
  αU↦-erase (ActInsertBinder var-update)
    rewrite var-update?-erase var-update = ActInsertBinder

  αL↦-erase : ∀ {Γ α e e'} ->
    (Γ ⊢ α , e αL↦ e') ->
    (α , (L◇ e) αB↦ (L◇ e'))
  αL↦-erase (ALC x) = αU↦-erase x

  mutual 
    AU↦-erase : ∀ {Γ A e e'} ->
      (Γ ⊢ A , e AU↦ e') ->
      (A , (U◇ e) AB↦ (U◇ e'))
    AU↦-erase (AUpMid step) = AM↦-erase step

    AM↦-erase : ∀ {Γ A e e'} ->
      (Γ ⊢ A , e AM↦ e') ->
      (A , (M◇ e) AB↦ (M◇ e'))
    AM↦-erase (AMidAscOne step) = ABareAscOne (AT↦-erase step)
    AM↦-erase (AMidAscTwo step) = ABareAscTwo (AL↦-erase step)
    AM↦-erase (AMidFunOne step) = ABareFunOne (AT↦-erase step)
    AM↦-erase (AMidFunTwo step) = ABareFunTwo (AL↦-erase step)
    AM↦-erase (AMidApOne step) = ABareApOne (AL↦-erase step)
    AM↦-erase (AMidApTwo step) = ABareApTwo (AL↦-erase step)
    AM↦-erase (AMidPairOne step) = ABarePairOne (AL↦-erase step)
    AM↦-erase (AMidPairTwo step) = ABarePairTwo (AL↦-erase step)
    AM↦-erase (AMidProj step) = ABareProj (AL↦-erase step)
 
    AL↦-erase : ∀ {Γ A e e'} ->
      (Γ ⊢ A , e AL↦ e') ->
      (A , (L◇ e) AB↦ (L◇ e')) 
    AL↦-erase (ALowDone step) = ABareDone (αL↦-erase step)
    AL↦-erase (ALowUp step) = AU↦-erase step 

  AP↦-erase : ∀ {A p p'} -> 
    (A , p AP↦ p') ->
    (A , (P◇ p) AB↦ (P◇ p'))
  AP↦-erase (AStepProgram step) = AL↦-erase step