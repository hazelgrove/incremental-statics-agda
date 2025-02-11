
open import Relation.Binary.PropositionalEquality

open import Prelude
open import Core.Core
open import Core.Marking
open import Core.Environment
open import Core.Update
open import Core.VarsSynthesizeErasure

module Core.UpdateErasure where

  u↦-erase : ∀ {e e'} ->
    (e u↦ e') ->
    (U◇ e) ≡ (U◇ e')
  u↦-erase (StepAp _) = refl
  u↦-erase StepAsc = refl

  l↦-erase : ∀ {e e'} ->
    (e l↦ e') ->
    (L◇ e) ≡ (L◇ e')
  l↦-erase (StepNewSynConsist _) = refl
  l↦-erase (StepNewAnaConsist _ _) = refl
  l↦-erase (StepAnaFun _ _) = refl
  l↦-erase StepSynFun = refl
  l↦-erase (StepNewAnnFun _ _ vars-syn) 
    rewrite vars-syn?-erase vars-syn = refl

  mutual 

    fill-uu-erase : ∀{ε e e' e-in e-in'} ->
      ε U⟦ e-in ⟧U≡ e ->
      ε U⟦ e-in' ⟧U≡ e' ->
      (U◇ e-in) ≡ (U◇ e-in') ->
      (U◇ e) ≡ (U◇ e')
    fill-uu-erase FillU⊙ FillU⊙ eq = eq
    fill-uu-erase (FillUEnvUpRec fill1) (FillUEnvUpRec fill2) eq = fill-um-erase fill1 fill2 eq

    fill-um-erase : ∀{ε e e' e-in e-in'} ->
      ε U⟦ e-in ⟧M≡ e ->
      ε U⟦ e-in' ⟧M≡ e' ->
      (U◇ e-in) ≡ (U◇ e-in') ->
      (M◇ e) ≡ (M◇ e')
    fill-um-erase (FillUEnvFun fill1) (FillUEnvFun fill2) eq 
      rewrite fill-ul-erase fill1 fill2 eq = refl
    fill-um-erase (FillUEnvAp1 fill1) (FillUEnvAp1 fill2) eq 
      rewrite fill-ul-erase fill1 fill2 eq = refl
    fill-um-erase (FillUEnvAp2 fill1) (FillUEnvAp2 fill2) eq 
      rewrite fill-ul-erase fill1 fill2 eq = refl
    fill-um-erase (FillUEnvAsc fill1) (FillUEnvAsc fill2) eq 
      rewrite fill-ul-erase fill1 fill2 eq = refl

    fill-ul-erase : ∀{ε e e' e-in e-in'} ->
      ε U⟦ e-in ⟧L≡ e ->
      ε U⟦ e-in' ⟧L≡ e' ->
      (U◇ e-in) ≡ (U◇ e-in') ->
      (L◇ e) ≡ (L◇ e')
    fill-ul-erase (FillUEnvLowRec fill1) (FillUEnvLowRec fill2) eq = fill-uu-erase fill1 fill2 eq

  mutual 

    fill-lu-erase : ∀{ε e e' e-in e-in'} ->
      ε L⟦ e-in ⟧U≡ e ->
      ε L⟦ e-in' ⟧U≡ e' ->
      (L◇ e-in) ≡ (L◇ e-in') ->
      (U◇ e) ≡ (U◇ e')
    fill-lu-erase (FillLEnvUpRec fill1) (FillLEnvUpRec fill2) eq = fill-lm-erase fill1 fill2 eq

    fill-lm-erase : ∀{ε e e' e-in e-in'} ->
      ε L⟦ e-in ⟧M≡ e ->
      ε L⟦ e-in' ⟧M≡ e' ->
      (L◇ e-in) ≡ (L◇ e-in') ->
      (M◇ e) ≡ (M◇ e')
    fill-lm-erase (FillLEnvFun fill1) (FillLEnvFun fill2) eq 
      rewrite fill-ll-erase fill1 fill2 eq = refl
    fill-lm-erase (FillLEnvAp1 fill1) (FillLEnvAp1 fill2) eq 
      rewrite fill-ll-erase fill1 fill2 eq = refl
    fill-lm-erase (FillLEnvAp2 fill1) (FillLEnvAp2 fill2) eq 
      rewrite fill-ll-erase fill1 fill2 eq = refl
    fill-lm-erase (FillLEnvAsc fill1) (FillLEnvAsc fill2) eq 
      rewrite fill-ll-erase fill1 fill2 eq = refl

    fill-ll-erase : ∀{ε e e' e-in e-in'} ->
      ε L⟦ e-in ⟧L≡ e ->
      ε L⟦ e-in' ⟧L≡ e' ->
      (L◇ e-in) ≡ (L◇ e-in') ->
      (L◇ e) ≡ (L◇ e')
    fill-ll-erase FillL⊙ FillL⊙ eq = eq
    fill-ll-erase (FillLEnvLowRec fill1) (FillLEnvLowRec fill2) eq = fill-lu-erase fill1 fill2 eq

  U↦-erase : ∀ {e e'} ->
    (e U↦ e') ->
    (U◇ e) ≡ (U◇ e')
  U↦-erase (StepUp FillU⊙ step FillU⊙) = u↦-erase step
  U↦-erase (StepUp (FillUEnvUpRec (FillUEnvFun fill1)) step (FillUEnvUpRec (FillUEnvFun fill2))) 
    rewrite fill-ul-erase fill1 fill2 (u↦-erase step) = refl
  U↦-erase (StepUp (FillUEnvUpRec (FillUEnvAp1 fill1)) step (FillUEnvUpRec (FillUEnvAp1 fill2)))
    rewrite fill-ul-erase fill1 fill2 (u↦-erase step) = refl
  U↦-erase (StepUp (FillUEnvUpRec (FillUEnvAp2 fill1)) step (FillUEnvUpRec (FillUEnvAp2 fill2))) 
    rewrite fill-ul-erase fill1 fill2 (u↦-erase step) = refl
  U↦-erase (StepUp (FillUEnvUpRec (FillUEnvAsc fill1)) step (FillUEnvUpRec (FillUEnvAsc fill2)))
    rewrite fill-ul-erase fill1 fill2 (u↦-erase step) = refl
  U↦-erase (StepLow (FillLEnvUpRec (FillLEnvFun fill1)) step (FillLEnvUpRec (FillLEnvFun fill2))) 
    rewrite fill-ll-erase fill1 fill2 (l↦-erase step) = refl
  U↦-erase (StepLow (FillLEnvUpRec (FillLEnvAp1 fill1)) step (FillLEnvUpRec (FillLEnvAp1 fill2))) 
    rewrite fill-ll-erase fill1 fill2 (l↦-erase step) = refl
  U↦-erase (StepLow (FillLEnvUpRec (FillLEnvAp2 fill1)) step (FillLEnvUpRec (FillLEnvAp2 fill2))) 
    rewrite fill-ll-erase fill1 fill2 (l↦-erase step) = refl
  U↦-erase (StepLow (FillLEnvUpRec (FillLEnvAsc fill1)) step (FillLEnvUpRec (FillLEnvAsc fill2))) 
    rewrite fill-ll-erase fill1 fill2 (l↦-erase step) = refl

  L↦-erase : ∀ {e e'} ->
    (e L↦ e') ->
    (L◇ e) ≡ (L◇ e')
  L↦-erase (StepLow FillL⊙ step FillL⊙) = l↦-erase step
  L↦-erase (StepLow (FillLEnvLowRec fill1) step (FillLEnvLowRec fill2)) = U↦-erase (StepLow fill1 step fill2)
  L↦-erase (StepUp (FillUEnvLowRec fill1) step (FillUEnvLowRec fill2)) = U↦-erase (StepUp fill1 step fill2)

  P↦-erase : ∀ {p p'} -> 
    (p P↦ p') ->   
    (P◇ p) ≡ (P◇ p')
  P↦-erase TopStep = refl      
  P↦-erase (InsideStep step) = L↦-erase step