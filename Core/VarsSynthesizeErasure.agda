
open import Relation.Binary.PropositionalEquality

open import Prelude
open import Core.Core
open import Core.Marking
open import Core.VarsSynthesize

module Core.VarsSynthesizeErasure where

  vars-syn-erase : ∀{x t m e e'} ->
    VarsSynthesize x t m e e' ->
    (U◇ e) ≡ (U◇ e')
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
    (U◇ e) ≡ (U◇ e')
  vars-syn?-erase {BHole} refl = refl
  vars-syn?-erase {BVar x} vs = vars-syn-erase vs