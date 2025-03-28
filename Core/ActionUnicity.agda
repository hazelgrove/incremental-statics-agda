
open import Relation.Binary.PropositionalEquality

open import Prelude
open import Core.Core
open import Core.Actions

module Core.ActionUnicity where

  αB↦-unicity : ∀ {α e e' e''} ->
    α , e αB↦ e' ->
    α , e αB↦ e'' ->
    e' ≡ e''
  αB↦-unicity ActInsertConst ActInsertConst = refl
  αB↦-unicity ActWrapFun ActWrapFun = refl
  αB↦-unicity ActWrapApOne ActWrapApOne = refl
  αB↦-unicity ActWrapApTwo ActWrapApTwo = refl
  αB↦-unicity ActInsertVar ActInsertVar = refl
  αB↦-unicity ActWrapAsc ActWrapAsc = refl
  αB↦-unicity ActWrapPairOne ActWrapPairOne = refl
  αB↦-unicity ActWrapPairTwo ActWrapPairTwo = refl
  αB↦-unicity ActWrapProj ActWrapProj = refl
  αB↦-unicity ActDelete ActDelete = refl
  αB↦-unicity ActUnwrapFun ActUnwrapFun = refl
  αB↦-unicity ActUnwrapApOne ActUnwrapApOne = refl
  αB↦-unicity ActUnwrapApTwo ActUnwrapApTwo = refl
  αB↦-unicity ActUnwrapAsc ActUnwrapAsc = refl
  αB↦-unicity ActUnwrapPairOne ActUnwrapPairOne = refl
  αB↦-unicity ActUnwrapPairTwo ActUnwrapPairTwo = refl
  αB↦-unicity ActUnwrapProj ActUnwrapProj = refl
  αB↦-unicity ActSetAsc ActSetAsc = refl
  αB↦-unicity ActSetAnn ActSetAnn = refl
  αB↦-unicity ActDeleteBinder ActDeleteBinder = refl
  αB↦-unicity ActInsertBinder ActInsertBinder = refl
  
  AB↦-unicity : ∀ {A e e' e''} ->
    A , e AB↦ e' ->
    A , e AB↦ e'' -> 
    e' ≡ e''
  AB↦-unicity (ABareDone step1) (ABareDone step2) = αB↦-unicity step1 step2 
  AB↦-unicity (ABareAsc step1) (ABareAsc step2) 
    rewrite AB↦-unicity step1 step2 = refl
  AB↦-unicity (ABareFun step1) (ABareFun step2) 
    rewrite AB↦-unicity step1 step2 = refl
  AB↦-unicity (ABareApOne step1) (ABareApOne step2) 
    rewrite AB↦-unicity step1 step2 = refl
  AB↦-unicity (ABareApTwo step1) (ABareApTwo step2) 
    rewrite AB↦-unicity step1 step2 = refl
  AB↦-unicity (ABarePairOne step1) (ABarePairOne step2) 
    rewrite AB↦-unicity step1 step2 = refl
  AB↦-unicity (ABarePairTwo step1) (ABarePairTwo step2) 
    rewrite AB↦-unicity step1 step2 = refl
  AB↦-unicity (ABareProj step1) (ABareProj step2) 
    rewrite AB↦-unicity step1 step2 = refl