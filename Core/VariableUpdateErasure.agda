
open import Relation.Binary.PropositionalEquality

open import Prelude
open import Core.Core
open import Core.Marking
open import Core.VariableUpdate

module Core.VariableUpdateErasure where

  var-update-erase : ∀{x t m e e'} ->
    VariableUpdate x t m e e' ->
    (S◇ e) ≡ (S◇ e')
  var-update-erase VUConst = refl
  var-update-erase VUHole = refl
  var-update-erase VUFunEq = refl
  var-update-erase VUVarEq = refl
  var-update-erase (VUVarNeq x) = refl
  var-update-erase (VUAsc var-update) 
    rewrite var-update-erase var-update = refl
  var-update-erase (VUFunNeq x var-update) 
    rewrite var-update-erase var-update = refl
  var-update-erase (VUAp var-update1 var-update2) 
    rewrite var-update-erase var-update1 
    rewrite var-update-erase var-update2 = refl
  var-update-erase (VUPair var-update1 var-update2) 
    rewrite var-update-erase var-update1 
    rewrite var-update-erase var-update2 = refl
  var-update-erase (VUProj var-update) 
    rewrite var-update-erase var-update = refl
  var-update-erase (VUTypFun var-update) 
    rewrite var-update-erase var-update = refl
  var-update-erase (VUTypAp var-update) 
    rewrite var-update-erase var-update = refl

  var-update?-erase : ∀{x t m e e'} ->
    VariableUpdate? x t m e e' ->
    (S◇ e) ≡ (S◇ e')
  var-update?-erase {BHole} refl = refl
  var-update?-erase {BVar x} vs = var-update-erase vs