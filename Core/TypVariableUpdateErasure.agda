
open import Relation.Binary.PropositionalEquality

open import Prelude
open import Core.Core
open import Core.Marking
open import Core.TypVariableUpdate

module Core.TypVariableUpdateErasure where

  tvar-update-erase : ∀{x m t t'} ->
    TypVariableUpdate x m t t' ->
    (T◇ t) ≡ (T◇ t')
  tvar-update-erase TVUBase = refl
  tvar-update-erase TVUHole = refl
  tvar-update-erase (TVUArrow tvu1 tvu2) 
    rewrite tvar-update-erase tvu1  
    rewrite tvar-update-erase tvu2 = refl
  tvar-update-erase (TVUProd tvu1 tvu2) 
    rewrite tvar-update-erase tvu1  
    rewrite tvar-update-erase tvu2 = refl
  tvar-update-erase TVUVarEq = refl
  tvar-update-erase (TVUVarNeq neq) = refl
  tvar-update-erase TVUForallEq = refl
  tvar-update-erase (TVUForallNeq neq tvu)
    rewrite tvar-update-erase tvu = refl

  tvar-update?-erase : ∀{x m t t'} ->
    TypVariableUpdate? x m t t' ->
    (T◇ t) ≡ (T◇ t')
  tvar-update?-erase {BHole} refl = refl
  tvar-update?-erase {BVar x} vs = tvar-update-erase vs

  exp-tvar-update-erase : ∀{x m e e'} ->
    ExpTypVariableUpdate x m e e' ->
    (U◇ e) ≡ (U◇ e')
  exp-tvar-update-erase ETVUConst = refl
  exp-tvar-update-erase ETVUHole = refl
  exp-tvar-update-erase (ETVUFun tvu etvu)
    rewrite tvar-update-erase tvu
    rewrite exp-tvar-update-erase etvu = refl
  exp-tvar-update-erase (ETVUAp etvu1 etvu2)
    rewrite exp-tvar-update-erase etvu1
    rewrite exp-tvar-update-erase etvu2 = refl
  exp-tvar-update-erase ETVUVar = refl
  exp-tvar-update-erase (ETVUAsc tvu etvu)
    rewrite tvar-update-erase tvu
    rewrite exp-tvar-update-erase etvu = refl
  exp-tvar-update-erase (ETVUPair etvu1 etvu2)
    rewrite exp-tvar-update-erase etvu1
    rewrite exp-tvar-update-erase etvu2 = refl
  exp-tvar-update-erase (ETVUProj etvu)
    rewrite exp-tvar-update-erase etvu = refl
  exp-tvar-update-erase ETVUTypFunEq = refl
  exp-tvar-update-erase (ETVUTypFunNeq _ etvu)
    rewrite exp-tvar-update-erase etvu = refl
  exp-tvar-update-erase (ETVUTypAp etvu tvu)
    rewrite exp-tvar-update-erase etvu
    rewrite tvar-update-erase tvu = refl
    
  exp-tvar-update?-erase : ∀{x m e e'} ->
    ExpTypVariableUpdate? x m e e' ->
    (U◇ e) ≡ (U◇ e')
  exp-tvar-update?-erase {BHole} refl = refl
  exp-tvar-update?-erase {BVar x} vs = exp-tvar-update-erase vs