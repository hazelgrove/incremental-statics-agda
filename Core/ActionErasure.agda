
open import Relation.Binary.PropositionalEquality

open import Prelude
open import Core.Core
open import Core.Marking
open import Core.Actions
open import Core.VarsSynthesizeErasure

module Core.ActionErasure where
  
  αU↦-erase : ∀ {Γ α e e'} ->
    (Γ ⊢ α , e αU↦ e') ->
    (α , (U◇ e) αB↦ (U◇ e'))
  αU↦-erase ActInsertConst = ActInsertConst
  αU↦-erase ActWrapApOne = ActWrapApOne
  αU↦-erase ActWrapApTwo = ActWrapApTwo
  αU↦-erase ActWrapAsc = ActWrapAsc
  αU↦-erase ActDelete = ActDelete
  αU↦-erase ActUnwrapApOne = ActUnwrapApOne
  αU↦-erase ActUnwrapApTwo = ActUnwrapApTwo
  αU↦-erase ActUnwrapAsc = ActUnwrapAsc
  αU↦-erase (ActInsertVar in-ctx) = ActInsertVar
  αU↦-erase ActWrapFun = ActWrapFun
  αU↦-erase (ActUnwrapFun x vars-syn) 
    rewrite vars-syn?-erase vars-syn = ActUnwrapFun
  αU↦-erase ActSetAsc = ActSetAsc
  αU↦-erase ActSetAnn = ActSetAnn
  αU↦-erase (ActDeleteBinder in-ctx vars-syn) 
    rewrite vars-syn?-erase vars-syn = ActDeleteBinder
  αU↦-erase (ActInsertBinder vars-syn)
    rewrite vars-syn?-erase vars-syn = ActInsertBinder

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
    AM↦-erase (AMidAsc step) = ABareAsc (AL↦-erase step)
    AM↦-erase (AMidFun step) = ABareFun (AL↦-erase step)
    AM↦-erase (AMidApOne step) = ABareApOne (AL↦-erase step)
    AM↦-erase (AMidApTwo step) = ABareApTwo (AL↦-erase step)
 
    AL↦-erase : ∀ {Γ A e e'} ->
      (Γ ⊢ A , e AL↦ e') ->
      (A , (L◇ e) AB↦ (L◇ e')) 
    AL↦-erase (ALowDone step) = ABareDone (αL↦-erase step)
    AL↦-erase (ALowUp step) = AU↦-erase step

  AP↦-erase : ∀ {A p p'} -> 
    (A , p AP↦ p') ->
    (A , (P◇ p) AB↦ (P◇ p'))
  AP↦-erase (AStepProgram step) = AL↦-erase step