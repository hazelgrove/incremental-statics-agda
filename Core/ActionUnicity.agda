
open import Relation.Binary.PropositionalEquality

open import Prelude
open import Core.Core
open import Core.Actions

module Core.ActionUnicity where

  αBT↦-unicity : ∀ {α t t' t''} ->
    α , t αBT↦ t' ->
    α , t αBT↦ t'' ->
    t' ≡ t''
  αBT↦-unicity ActInsertBase ActInsertBase = refl
  αBT↦-unicity ActWrapArrowOne ActWrapArrowOne = refl
  αBT↦-unicity ActWrapArrowTwo ActWrapArrowTwo = refl
  αBT↦-unicity ActWrapProdOne ActWrapProdOne = refl
  αBT↦-unicity ActWrapProdTwo ActWrapProdTwo = refl
  αBT↦-unicity ActInsertTVar ActInsertTVar = refl
  αBT↦-unicity ActWrapForall ActWrapForall = refl
  αBT↦-unicity ActDelete ActDelete = refl
  αBT↦-unicity ActDeleteBinder ActDeleteBinder = refl
  αBT↦-unicity ActInsertBinder ActInsertBinder = refl

  ABT↦-unicity : ∀ {A t t' t''} ->
    A , t ABT↦ t' ->
    A , t ABT↦ t'' -> 
    t' ≡ t''
  ABT↦-unicity (ATBareDone step1) (ATBareDone step2)
    rewrite αBT↦-unicity step1 step2 = refl
  ABT↦-unicity (ABareArrowOne step1) (ABareArrowOne step2)
    rewrite ABT↦-unicity step1 step2 = refl
  ABT↦-unicity (ABareArrowTwo step1) (ABareArrowTwo step2)
    rewrite ABT↦-unicity step1 step2 = refl
  ABT↦-unicity (ABareProdOne step1) (ABareProdOne step2)
    rewrite ABT↦-unicity step1 step2 = refl
  ABT↦-unicity (ABareProdTwo step1) (ABareProdTwo step2)
    rewrite ABT↦-unicity step1 step2 = refl
  ABT↦-unicity (ABareForall step1) (ABareForall step2)
    rewrite ABT↦-unicity step1 step2 = refl

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
  αB↦-unicity ActDeleteBinder ActDeleteBinder = refl
  αB↦-unicity ActInsertBinder ActInsertBinder = refl
  αB↦-unicity ActWrapTypFun ActWrapTypFun = refl
  αB↦-unicity ActWrapTypAp ActWrapTypAp = refl
  αB↦-unicity ActUnwrapTypFun ActUnwrapTypFun = refl
  αB↦-unicity ActUnwrapTypAp ActUnwrapTypAp = refl
  
  AB↦-unicity : ∀ {A e e' e''} ->
    A , e AB↦ e' ->
    A , e AB↦ e'' -> 
    e' ≡ e''
  AB↦-unicity (ABareDone step1) (ABareDone step2) = αB↦-unicity step1 step2 
  AB↦-unicity (ABareAscOne step1) (ABareAscOne step2) 
    rewrite ABT↦-unicity step1 step2 = refl
  AB↦-unicity (ABareAscTwo step1) (ABareAscTwo step2) 
    rewrite AB↦-unicity step1 step2 = refl
  AB↦-unicity (ABareFunOne step1) (ABareFunOne step2) 
    rewrite ABT↦-unicity step1 step2 = refl
  AB↦-unicity (ABareFunTwo step1) (ABareFunTwo step2) 
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
  AB↦-unicity (ABareTypFun step1) (ABareTypFun step2) 
    rewrite AB↦-unicity step1 step2 = refl
  AB↦-unicity (ABareTypApOne step1) (ABareTypApOne step2) 
    rewrite AB↦-unicity step1 step2 = refl
  AB↦-unicity (ABareTypApTwo step1) (ABareTypApTwo step2) 
    rewrite ABT↦-unicity step1 step2 = refl