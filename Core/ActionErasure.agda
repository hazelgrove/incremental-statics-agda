
open import Relation.Binary.PropositionalEquality

open import Prelude
open import Core.Core
open import Core.Marking
open import Core.Actions
open import Core.VariableUpdateErasure

module Core.ActionErasure where
  
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
  αU↦-erase ActDelete = ActDelete
  αU↦-erase ActUnwrapApOne = ActUnwrapApOne
  αU↦-erase ActUnwrapApTwo = ActUnwrapApTwo
  αU↦-erase ActUnwrapAsc = ActUnwrapAsc
  αU↦-erase ActUnwrapPairOne = ActUnwrapPairOne
  αU↦-erase ActUnwrapPairTwo = ActUnwrapPairTwo
  αU↦-erase ActUnwrapProj = ActUnwrapProj
  αU↦-erase (ActInsertVar in-ctx) = ActInsertVar
  αU↦-erase (ActUnwrapFun x var-update) 
    rewrite var-update?-erase var-update = ActUnwrapFun
  αU↦-erase ActSetAsc = ActSetAsc
  αU↦-erase ActSetAnn = ActSetAnn
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
    AM↦-erase (AMidAsc step) = ABareAsc (AL↦-erase step)
    AM↦-erase (AMidFun step) = ABareFun (AL↦-erase step)
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