open import Data.Nat hiding (_+_)
open import Data.Unit 
open import Data.List 
open import Data.Bool hiding (_<_; _≟_)
open import Data.Sum renaming (_⊎_ to _+_; inj₁ to Inl ; inj₂ to Inr) hiding (map)
open import Data.Product hiding (map)
open import Relation.Nullary 
open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Prelude

open import Core.Core
open import Core.Environment
open import Core.VarsSynthesize
open import Core.WellTyped
open import Core.Actions
open import Core.Marking

module Core.ActionErasure where

  vars-syn-erase : ∀{x t m e e'} ->
    VarsSynthesize x t m e e' ->
    (EraseUp e) ≡ (EraseUp e')
  vars-syn-erase VSConst = refl
  vars-syn-erase VSHole = refl
  vars-syn-erase VSFunEq = refl
  vars-syn-erase VSVarEq = refl
  vars-syn-erase (VSVarNeq x) = refl
  vars-syn-erase (VSAsc vars-syn) 
    rewrite vars-syn-erase vars-syn = refl
  vars-syn-erase (VSFunNeq x vars-syn) 
    rewrite vars-syn-erase vars-syn = refl
  vars-syn-erase (VSAp vars-syn1 vars-syn2) 
    rewrite vars-syn-erase vars-syn1 
    rewrite vars-syn-erase vars-syn2 = refl

  vars-syn?-erase : ∀{x t m e e'} ->
    VarsSynthesize? x t m e e' ->
    (EraseUp e) ≡ (EraseUp e')
  vars-syn?-erase {BHole} refl = refl
  vars-syn?-erase {BVar x} vs = vars-syn-erase vs
  
  αU↦-erase : ∀ {Γ α e e'} ->
    (Γ ⊢ α , e αU↦ e') ->
    (α , (EraseUp e) αB↦ (EraseUp e'))
  αU↦-erase ActInsertConst = ActInsertConst
  αU↦-erase ActWrapApOne = ActWrapApOne
  αU↦-erase ActWrapApTwo = ActWrapApTwo
  αU↦-erase ActWrapAsc = ActWrapAsc
  αU↦-erase ActDelete = ActDelete
  αU↦-erase ActUnwrapApOne = ActUnwrapApOne
  αU↦-erase ActUnwrapApTwo = ActUnwrapApTwo
  αU↦-erase ActUnwrapAsc = ActUnwrapAsc
  αU↦-erase (ActInsertVar in-ctx) = ActInsertVar
  αU↦-erase (ActWrapFun vars-syn) 
    rewrite vars-syn?-erase vars-syn = ActWrapFun
  αU↦-erase (ActUnwrapFun x vars-syn) 
    rewrite vars-syn?-erase vars-syn = ActUnwrapFun

  αL↦-erase : ∀ {Γ α e e'} ->
    (Γ ⊢ α , e αL↦ e') ->
    (α , (EraseLow e) αB↦ (EraseLow e'))
  αL↦-erase (ALC x) = αU↦-erase x

  mutual 
    AU↦-erase : ∀ {Γ A e e'} ->
      (Γ ⊢ A , e AU↦ e') ->
      (A , (EraseUp e) AB↦ (EraseUp e'))
    AU↦-erase (AUpMid step) = AM↦-erase step

    AM↦-erase : ∀ {Γ A e e'} ->
      (Γ ⊢ A , e AM↦ e') ->
      (A , (EraseMid e) AB↦ (EraseMid e'))
    AM↦-erase (AMidAsc step) = ABareAsc (AL↦-erase step)
    AM↦-erase (AMidFun step) = ABareFun (AL↦-erase step)
    AM↦-erase (AMidApOne step) = ABareApOne (AL↦-erase step)
    AM↦-erase (AMidApTwo step) = ABareApTwo (AL↦-erase step)
 
    AL↦-erase : ∀ {Γ A e e'} ->
      (Γ ⊢ A , e AL↦ e') ->
      (A , (EraseLow e) AB↦ (EraseLow e')) 
    AL↦-erase (ALowDone step) = ABareDone (αL↦-erase step)
    AL↦-erase (ALowUp step) = AU↦-erase step

  AP↦-erase : ∀ {A p p'} -> 
    (A , p AP↦ p') ->
    (A , (EraseProgram p) AB↦ (EraseProgram p'))
  AP↦-erase (AStepProgram step) = AL↦-erase step