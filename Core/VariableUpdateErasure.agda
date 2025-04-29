
open import Relation.Binary.PropositionalEquality

open import Prelude
open import Core.Core
open import Core.Marking
open import Core.VariableUpdate

module Core.VariableUpdateErasure where

  var-update-erase : ∀{x t m e e'} ->
    VariableUpdate x t m e e' ->
    (U◇ e) ≡ (U◇ e')
  var-update-erase VSConst = refl
  var-update-erase VSHole = refl
  var-update-erase VSFunEq = refl
  var-update-erase VSVarEq = refl
  var-update-erase (VSVarNeq x) = refl
  var-update-erase (VSAsc var-update) 
    rewrite var-update-erase var-update = refl
  var-update-erase (VSFunNeq x var-update) 
    rewrite var-update-erase var-update = refl
  var-update-erase (VSAp var-update1 var-update2) 
    rewrite var-update-erase var-update1 
    rewrite var-update-erase var-update2 = refl
  var-update-erase (VSPair var-update1 var-update2) 
    rewrite var-update-erase var-update1 
    rewrite var-update-erase var-update2 = refl
  var-update-erase (VSProj var-update) 
    rewrite var-update-erase var-update = refl
  var-update-erase (VSTypFun var-update) 
    rewrite var-update-erase var-update = refl
  var-update-erase (VSTypAp var-update) 
    rewrite var-update-erase var-update = refl

  var-update?-erase : ∀{x t m e e'} ->
    VariableUpdate? x t m e e' ->
    (U◇ e) ≡ (U◇ e')
  var-update?-erase {BHole} refl = refl
  var-update?-erase {BVar x} vs = var-update-erase vs