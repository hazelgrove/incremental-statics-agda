
open import Relation.Binary.PropositionalEquality

open import Prelude
open import Core.Core
open import Core.Marking
open import Core.Environment
open import Core.Update
open import Core.VariableUpdateErasure

module Core.UpdateErasure where

  s↦-erase : ∀ {e e'} ->
    (e s↦ e') ->
    (S◇ e) ≡ (S◇ e')
  s↦-erase (StepAp _) = refl
  s↦-erase StepAsc = refl
  s↦-erase (StepProj _) = refl
  s↦-erase (StepTypApFun _ _) = refl
  s↦-erase (StepTypApArg _ _) = refl

  a↦-erase : ∀ {e e'} ->
    (e a↦ e') ->
    (A◇ e) ≡ (A◇ e')
  a↦-erase (StepSyn _) = refl
  a↦-erase (StepAna _ _) = refl
  a↦-erase (StepAnaFun _ _) = refl
  a↦-erase StepSynFun = refl
  a↦-erase (StepAnaPair _) = refl
  a↦-erase StepSynPairFst = refl
  a↦-erase StepSynPairSnd = refl
  a↦-erase (StepAnnFun var-update) 
    rewrite var-update?-erase var-update = refl
  a↦-erase (StepAnaTypFun _) = refl
  a↦-erase StepSynTypFun = refl

  mutual 

    fill-uu-erase : ∀{ε e e' e-in e-in'} ->
      ε S⟦ e-in ⟧S≡ e ->
      ε S⟦ e-in' ⟧S≡ e' ->
      (S◇ e-in) ≡ (S◇ e-in') ->
      (S◇ e) ≡ (S◇ e')
    fill-uu-erase FillS⊙ FillS⊙ eq = eq
    fill-uu-erase (FillSynEnvSynRec fill1) (FillSynEnvSynRec fill2) eq = fill-um-erase fill1 fill2 eq

    fill-um-erase : ∀{ε e e' e-in e-in'} ->
      ε S⟦ e-in ⟧C≡ e ->
      ε S⟦ e-in' ⟧C≡ e' ->
      (S◇ e-in) ≡ (S◇ e-in') ->
      (C◇ e) ≡ (C◇ e')
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
    fill-um-erase (FillSynEnvTypFun fill1) (FillSynEnvTypFun fill2) eq 
      rewrite fill-ul-erase fill1 fill2 eq = refl
    fill-um-erase (FillSynEnvTypAp fill1) (FillSynEnvTypAp fill2) eq 
      rewrite fill-ul-erase fill1 fill2 eq = refl

    fill-ul-erase : ∀{ε e e' e-in e-in'} ->
      ε S⟦ e-in ⟧A≡ e ->
      ε S⟦ e-in' ⟧A≡ e' ->
      (S◇ e-in) ≡ (S◇ e-in') ->
      (A◇ e) ≡ (A◇ e')
    fill-ul-erase (FillSynEnvAnaRec fill1) (FillSynEnvAnaRec fill2) eq = fill-uu-erase fill1 fill2 eq

  mutual 

    fill-lu-erase : ∀{ε e e' e-in e-in'} ->
      ε A⟦ e-in ⟧S≡ e ->
      ε A⟦ e-in' ⟧S≡ e' ->
      (A◇ e-in) ≡ (A◇ e-in') ->
      (S◇ e) ≡ (S◇ e')
    fill-lu-erase (FillAnaEnvSynRec fill1) (FillAnaEnvSynRec fill2) eq = fill-lm-erase fill1 fill2 eq

    fill-lm-erase : ∀{ε e e' e-in e-in'} ->
      ε A⟦ e-in ⟧C≡ e ->
      ε A⟦ e-in' ⟧C≡ e' ->
      (A◇ e-in) ≡ (A◇ e-in') ->
      (C◇ e) ≡ (C◇ e')
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
    fill-lm-erase (FillAnaEnvTypFun fill1) (FillAnaEnvTypFun fill2) eq 
      rewrite fill-ll-erase fill1 fill2 eq = refl
    fill-lm-erase (FillAnaEnvTypAp fill1) (FillAnaEnvTypAp fill2) eq 
      rewrite fill-ll-erase fill1 fill2 eq = refl

    fill-ll-erase : ∀{ε e e' e-in e-in'} ->
      ε A⟦ e-in ⟧A≡ e ->
      ε A⟦ e-in' ⟧A≡ e' ->
      (A◇ e-in) ≡ (A◇ e-in') ->
      (A◇ e) ≡ (A◇ e')
    fill-ll-erase FillA⊙ FillA⊙ eq = eq
    fill-ll-erase (FillAnaEnvAnaRec fill1) (FillAnaEnvAnaRec fill2) eq = fill-lu-erase fill1 fill2 eq

  S↦-erase : ∀ {e e'} ->
    (e S↦ e') ->
    (S◇ e) ≡ (S◇ e')
  S↦-erase (StepUp FillS⊙ step FillS⊙) = s↦-erase step
  S↦-erase (StepUp (FillSynEnvSynRec (FillSynEnvFun fill1)) step (FillSynEnvSynRec (FillSynEnvFun fill2))) 
    rewrite fill-ul-erase fill1 fill2 (s↦-erase step) = refl
  S↦-erase (StepUp (FillSynEnvSynRec (FillSynEnvProj fill1)) step (FillSynEnvSynRec (FillSynEnvProj fill2))) 
    rewrite fill-ul-erase fill1 fill2 (s↦-erase step) = refl
  S↦-erase (StepUp (FillSynEnvSynRec (FillSynEnvAp1 fill1)) step (FillSynEnvSynRec (FillSynEnvAp1 fill2)))
    rewrite fill-ul-erase fill1 fill2 (s↦-erase step) = refl
  S↦-erase (StepUp (FillSynEnvSynRec (FillSynEnvAp2 fill1)) step (FillSynEnvSynRec (FillSynEnvAp2 fill2))) 
    rewrite fill-ul-erase fill1 fill2 (s↦-erase step) = refl
  S↦-erase (StepUp (FillSynEnvSynRec (FillSynEnvAsc fill1)) step (FillSynEnvSynRec (FillSynEnvAsc fill2)))
    rewrite fill-ul-erase fill1 fill2 (s↦-erase step) = refl
  S↦-erase (StepUp (FillSynEnvSynRec (FillSynEnvPair1 fill1)) step (FillSynEnvSynRec (FillSynEnvPair1 fill2)))
    rewrite fill-ul-erase fill1 fill2 (s↦-erase step) = refl
  S↦-erase (StepUp (FillSynEnvSynRec (FillSynEnvPair2 fill1)) step (FillSynEnvSynRec (FillSynEnvPair2 fill2))) 
    rewrite fill-ul-erase fill1 fill2 (s↦-erase step) = refl
  S↦-erase (StepUp (FillSynEnvSynRec (FillSynEnvTypFun fill1)) step (FillSynEnvSynRec (FillSynEnvTypFun fill2)))
    rewrite fill-ul-erase fill1 fill2 (s↦-erase step) = refl
  S↦-erase (StepUp (FillSynEnvSynRec (FillSynEnvTypAp fill1)) step (FillSynEnvSynRec (FillSynEnvTypAp fill2)))
    rewrite fill-ul-erase fill1 fill2 (s↦-erase step) = refl
  S↦-erase (StepLow (FillAnaEnvSynRec (FillAnaEnvFun fill1)) step (FillAnaEnvSynRec (FillAnaEnvFun fill2))) 
    rewrite fill-ll-erase fill1 fill2 (a↦-erase step) = refl
  S↦-erase (StepLow (FillAnaEnvSynRec (FillAnaEnvProj fill1)) step (FillAnaEnvSynRec (FillAnaEnvProj fill2))) 
    rewrite fill-ll-erase fill1 fill2 (a↦-erase step) = refl
  S↦-erase (StepLow (FillAnaEnvSynRec (FillAnaEnvAp1 fill1)) step (FillAnaEnvSynRec (FillAnaEnvAp1 fill2))) 
    rewrite fill-ll-erase fill1 fill2 (a↦-erase step) = refl
  S↦-erase (StepLow (FillAnaEnvSynRec (FillAnaEnvAp2 fill1)) step (FillAnaEnvSynRec (FillAnaEnvAp2 fill2))) 
    rewrite fill-ll-erase fill1 fill2 (a↦-erase step) = refl
  S↦-erase (StepLow (FillAnaEnvSynRec (FillAnaEnvAsc fill1)) step (FillAnaEnvSynRec (FillAnaEnvAsc fill2))) 
    rewrite fill-ll-erase fill1 fill2 (a↦-erase step) = refl
  S↦-erase (StepLow (FillAnaEnvSynRec (FillAnaEnvPair1 fill1)) step (FillAnaEnvSynRec (FillAnaEnvPair1 fill2))) 
    rewrite fill-ll-erase fill1 fill2 (a↦-erase step) = refl
  S↦-erase (StepLow (FillAnaEnvSynRec (FillAnaEnvPair2 fill1)) step (FillAnaEnvSynRec (FillAnaEnvPair2 fill2))) 
    rewrite fill-ll-erase fill1 fill2 (a↦-erase step) = refl
  S↦-erase (StepLow (FillAnaEnvSynRec (FillAnaEnvTypFun fill1)) step (FillAnaEnvSynRec (FillAnaEnvTypFun fill2))) 
    rewrite fill-ll-erase fill1 fill2 (a↦-erase step) = refl
  S↦-erase (StepLow (FillAnaEnvSynRec (FillAnaEnvTypAp fill1)) step (FillAnaEnvSynRec (FillAnaEnvTypAp fill2)))
    rewrite fill-ll-erase fill1 fill2 (a↦-erase step) = refl

  A↦-erase : ∀ {e e'} ->
    (e A↦ e') ->
    (A◇ e) ≡ (A◇ e')
  A↦-erase (StepLow FillA⊙ step FillA⊙) = a↦-erase step
  A↦-erase (StepLow (FillAnaEnvAnaRec fill1) step (FillAnaEnvAnaRec fill2)) = S↦-erase (StepLow fill1 step fill2)
  A↦-erase (StepUp (FillSynEnvAnaRec fill1) step (FillSynEnvAnaRec fill2)) = S↦-erase (StepUp fill1 step fill2)

  P↦-erase : ∀ {p p'} -> 
    (p P↦ p') ->   
    (P◇ p) ≡ (P◇ p')
  P↦-erase TopStep = refl      
  P↦-erase (InsideStep step) = A↦-erase step