
open import Relation.Binary.PropositionalEquality

open import Prelude
open import Core.Core
open import Core.Marking
open import Core.Environment
open import Core.Update
open import Core.VariableUpdateErasure

module Core.UpdateErasure where

  u↦-erase : ∀ {e e'} ->
    (e u↦ e') ->
    (U◇ e) ≡ (U◇ e')
  u↦-erase (StepAp _) = refl
  u↦-erase StepAsc = refl
  u↦-erase (StepProj _) = refl

  l↦-erase : ∀ {e e'} ->
    (e l↦ e') ->
    (L◇ e) ≡ (L◇ e')
  l↦-erase (StepSyn _) = refl
  l↦-erase (StepAna _ _) = refl
  l↦-erase (StepAnaFun _ _) = refl
  l↦-erase StepSynFun = refl
  l↦-erase (StepAnaPair _) = refl
  l↦-erase StepSynPairFst = refl
  l↦-erase StepSynPairSnd = refl
  l↦-erase (StepAnnFun var-update) 
    rewrite var-update?-erase var-update = refl

  mutual 

    fill-uu-erase : ∀{ε e e' e-in e-in'} ->
      ε S⟦ e-in ⟧S≡ e ->
      ε S⟦ e-in' ⟧S≡ e' ->
      (U◇ e-in) ≡ (U◇ e-in') ->
      (U◇ e) ≡ (U◇ e')
    fill-uu-erase FillS⊙ FillS⊙ eq = eq
    fill-uu-erase (FillSynEnvSynRec fill1) (FillSynEnvSynRec fill2) eq = fill-um-erase fill1 fill2 eq

    fill-um-erase : ∀{ε e e' e-in e-in'} ->
      ε S⟦ e-in ⟧C≡ e ->
      ε S⟦ e-in' ⟧C≡ e' ->
      (U◇ e-in) ≡ (U◇ e-in') ->
      (M◇ e) ≡ (M◇ e')
    fill-um-erase (FillSynEnvFun fill1) (FillSynEnvFun fill2) eq 
      rewrite fill-ul-erase fill1 fill2 eq = refl
    fill-um-erase (FillSynEnvProj fill1) (FillSynEnvProj fill2) eq 
      rewrite fill-ul-erase fill1 fill2 eq = refl
    fill-um-erase (FillSynEnvAp1 fill1) (FillSynEnvAp1 fill2) eq 
      rewrite fill-ul-erase fill1 fill2 eq = refl
    fill-um-erase (FillSynEnvAp2 fill1) (FillSynEnvAp2 fill2) eq 
      rewrite fill-ul-erase fill1 fill2 eq = refl
    fill-um-erase (FillSynEnvAsc fill1) (FillSynEnvAsc fill2) eq 
      rewrite fill-ul-erase fill1 fill2 eq = refl
    fill-um-erase (FillSynEnvPair1 fill1) (FillSynEnvPair1 fill2) eq 
      rewrite fill-ul-erase fill1 fill2 eq = refl
    fill-um-erase (FillSynEnvPair2 fill1) (FillSynEnvPair2 fill2) eq 
      rewrite fill-ul-erase fill1 fill2 eq = refl

    fill-ul-erase : ∀{ε e e' e-in e-in'} ->
      ε S⟦ e-in ⟧A≡ e ->
      ε S⟦ e-in' ⟧A≡ e' ->
      (U◇ e-in) ≡ (U◇ e-in') ->
      (L◇ e) ≡ (L◇ e')
    fill-ul-erase (FillSynEnvAnaRec fill1) (FillSynEnvAnaRec fill2) eq = fill-uu-erase fill1 fill2 eq

  mutual 

    fill-lu-erase : ∀{ε e e' e-in e-in'} ->
      ε A⟦ e-in ⟧S≡ e ->
      ε A⟦ e-in' ⟧S≡ e' ->
      (L◇ e-in) ≡ (L◇ e-in') ->
      (U◇ e) ≡ (U◇ e')
    fill-lu-erase (FillAnaEnvSynRec fill1) (FillAnaEnvSynRec fill2) eq = fill-lm-erase fill1 fill2 eq

    fill-lm-erase : ∀{ε e e' e-in e-in'} ->
      ε A⟦ e-in ⟧C≡ e ->
      ε A⟦ e-in' ⟧C≡ e' ->
      (L◇ e-in) ≡ (L◇ e-in') ->
      (M◇ e) ≡ (M◇ e')
    fill-lm-erase (FillAnaEnvFun fill1) (FillAnaEnvFun fill2) eq 
      rewrite fill-ll-erase fill1 fill2 eq = refl
    fill-lm-erase (FillAnaEnvProj fill1) (FillAnaEnvProj fill2) eq 
      rewrite fill-ll-erase fill1 fill2 eq = refl
    fill-lm-erase (FillAnaEnvAp1 fill1) (FillAnaEnvAp1 fill2) eq 
      rewrite fill-ll-erase fill1 fill2 eq = refl
    fill-lm-erase (FillAnaEnvAp2 fill1) (FillAnaEnvAp2 fill2) eq 
      rewrite fill-ll-erase fill1 fill2 eq = refl
    fill-lm-erase (FillAnaEnvAsc fill1) (FillAnaEnvAsc fill2) eq 
      rewrite fill-ll-erase fill1 fill2 eq = refl
    fill-lm-erase (FillAnaEnvPair1 fill1) (FillAnaEnvPair1 fill2) eq 
      rewrite fill-ll-erase fill1 fill2 eq = refl
    fill-lm-erase (FillAnaEnvPair2 fill1) (FillAnaEnvPair2 fill2) eq 
      rewrite fill-ll-erase fill1 fill2 eq = refl

    fill-ll-erase : ∀{ε e e' e-in e-in'} ->
      ε A⟦ e-in ⟧A≡ e ->
      ε A⟦ e-in' ⟧A≡ e' ->
      (L◇ e-in) ≡ (L◇ e-in') ->
      (L◇ e) ≡ (L◇ e')
    fill-ll-erase FillA⊙ FillA⊙ eq = eq
    fill-ll-erase (FillAnaEnvAnaRec fill1) (FillAnaEnvAnaRec fill2) eq = fill-lu-erase fill1 fill2 eq

  U↦-erase : ∀ {e e'} ->
    (e U↦ e') ->
    (U◇ e) ≡ (U◇ e')
  U↦-erase (StepUp FillS⊙ step FillS⊙) = u↦-erase step
  U↦-erase (StepUp (FillSynEnvSynRec (FillSynEnvFun fill1)) step (FillSynEnvSynRec (FillSynEnvFun fill2))) 
    rewrite fill-ul-erase fill1 fill2 (u↦-erase step) = refl
  U↦-erase (StepUp (FillSynEnvSynRec (FillSynEnvProj fill1)) step (FillSynEnvSynRec (FillSynEnvProj fill2))) 
    rewrite fill-ul-erase fill1 fill2 (u↦-erase step) = refl
  U↦-erase (StepUp (FillSynEnvSynRec (FillSynEnvAp1 fill1)) step (FillSynEnvSynRec (FillSynEnvAp1 fill2)))
    rewrite fill-ul-erase fill1 fill2 (u↦-erase step) = refl
  U↦-erase (StepUp (FillSynEnvSynRec (FillSynEnvAp2 fill1)) step (FillSynEnvSynRec (FillSynEnvAp2 fill2))) 
    rewrite fill-ul-erase fill1 fill2 (u↦-erase step) = refl
  U↦-erase (StepUp (FillSynEnvSynRec (FillSynEnvAsc fill1)) step (FillSynEnvSynRec (FillSynEnvAsc fill2)))
    rewrite fill-ul-erase fill1 fill2 (u↦-erase step) = refl
  U↦-erase (StepUp (FillSynEnvSynRec (FillSynEnvPair1 fill1)) step (FillSynEnvSynRec (FillSynEnvPair1 fill2)))
    rewrite fill-ul-erase fill1 fill2 (u↦-erase step) = refl
  U↦-erase (StepUp (FillSynEnvSynRec (FillSynEnvPair2 fill1)) step (FillSynEnvSynRec (FillSynEnvPair2 fill2))) 
    rewrite fill-ul-erase fill1 fill2 (u↦-erase step) = refl
  U↦-erase (StepLow (FillAnaEnvSynRec (FillAnaEnvFun fill1)) step (FillAnaEnvSynRec (FillAnaEnvFun fill2))) 
    rewrite fill-ll-erase fill1 fill2 (l↦-erase step) = refl
  U↦-erase (StepLow (FillAnaEnvSynRec (FillAnaEnvProj fill1)) step (FillAnaEnvSynRec (FillAnaEnvProj fill2))) 
    rewrite fill-ll-erase fill1 fill2 (l↦-erase step) = refl
  U↦-erase (StepLow (FillAnaEnvSynRec (FillAnaEnvAp1 fill1)) step (FillAnaEnvSynRec (FillAnaEnvAp1 fill2))) 
    rewrite fill-ll-erase fill1 fill2 (l↦-erase step) = refl
  U↦-erase (StepLow (FillAnaEnvSynRec (FillAnaEnvAp2 fill1)) step (FillAnaEnvSynRec (FillAnaEnvAp2 fill2))) 
    rewrite fill-ll-erase fill1 fill2 (l↦-erase step) = refl
  U↦-erase (StepLow (FillAnaEnvSynRec (FillAnaEnvAsc fill1)) step (FillAnaEnvSynRec (FillAnaEnvAsc fill2))) 
    rewrite fill-ll-erase fill1 fill2 (l↦-erase step) = refl
  U↦-erase (StepLow (FillAnaEnvSynRec (FillAnaEnvPair1 fill1)) step (FillAnaEnvSynRec (FillAnaEnvPair1 fill2))) 
    rewrite fill-ll-erase fill1 fill2 (l↦-erase step) = refl
  U↦-erase (StepLow (FillAnaEnvSynRec (FillAnaEnvPair2 fill1)) step (FillAnaEnvSynRec (FillAnaEnvPair2 fill2))) 
    rewrite fill-ll-erase fill1 fill2 (l↦-erase step) = refl

  L↦-erase : ∀ {e e'} ->
    (e L↦ e') ->
    (L◇ e) ≡ (L◇ e')
  L↦-erase (StepLow FillA⊙ step FillA⊙) = l↦-erase step
  L↦-erase (StepLow (FillAnaEnvAnaRec fill1) step (FillAnaEnvAnaRec fill2)) = U↦-erase (StepLow fill1 step fill2)
  L↦-erase (StepUp (FillSynEnvAnaRec fill1) step (FillSynEnvAnaRec fill2)) = U↦-erase (StepUp fill1 step fill2)

  P↦-erase : ∀ {p p'} -> 
    (p P↦ p') ->   
    (P◇ p) ≡ (P◇ p')
  P↦-erase TopStep = refl      
  P↦-erase (InsideStep step) = L↦-erase step