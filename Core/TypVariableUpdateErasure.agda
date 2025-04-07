
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