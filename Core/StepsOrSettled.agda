open import Data.Nat hiding (_+_)
open import Data.Unit 
open import Data.Empty 
open import Data.Bool hiding (_<_; _≟_)
open import Data.Sum renaming (_⊎_ to _+_; inj₁ to Inl ; inj₂ to Inr) hiding (map)
open import Data.Product hiding (map)
open import Relation.Nullary 
open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Prelude

open import Core.Core
open import Core.WellTyped
open import Core.Update
open import Core.Settled
open import Core.Lemmas-Context

module Core.StepsOrSettled where


-- StepsOrSettledLow : (e : ExpLow) ->
--   Σ[ e' ∈ ExpLow ] (e L↦ e') + (Settled e)
-- StepsOrSettledLow

syn-child : ∀ {Γ e t'} ->
  Γ ⊢ e ⇒ t' -> 
  SettledSynExcept Γ e ->
  Σ[ t ∈ NewType ] Σ[ e' ∈ ExpMid ] e ≡ EUp (⇑ t) e'
syn-child (SynConst x) s = _ , _ , refl
syn-child (SynHole x) s = _ , _ , refl
syn-child (SynFun wt x _) s = _ , _ , refl
syn-child (SynFunVoid wt) ()
syn-child (SynAp wt x x₁ x₂ x₃) s = _ , _ , refl
syn-child (SynApFail wt x x₁ x₂ x₃) s = _ , _ , refl
syn-child (SynVar x x₁) s = _ , _ , refl
syn-child (SynVarFail x x₁) s = _ , _ , refl
syn-child (SynAsc x x₁) s = _ , _ , refl

settled-syn-old : ∀ {Γ e t n} ->
  Γ ⊢ e ⇒ (t , n) ->
  SettledSyn Γ e ->
  n ≡ Old
settled-syn-old (SynConst MergeInfoOld) SettledSynConst = refl
settled-syn-old (SynHole MergeInfoOld) SettledSynHole = refl
settled-syn-old (SynFun syn refl m) (SettledSynFun s) rewrite settled-syn-old syn s with m 
... | MergeInfoOld = refl
settled-syn-old (SynFunVoid syn) ()
settled-syn-old (SynAp syn _ mn _ m) (SettledSynAp s _) rewrite settled-syn-old syn s with mn | m 
... | MNArrowOld | MergeInfoOld = refl
settled-syn-old (SynApFail syn _ mn _ m) (SettledSynAp s x₄) rewrite settled-syn-old syn s with mn | m 
... | MNArrowOld | MergeInfoOld = refl
settled-syn-old (SynVar {info = t , Old} ctx1 m) (SettledSynVar (Inl ctx2)) rewrite (ctx-unique ctx1 ctx2) with m 
... | MergeInfoOld = refl 
settled-syn-old (SynVar {info = t , Old} ctx _) (SettledSynVar (Inr notin)) = ⊥-elim (notin ctx)
settled-syn-old (SynVarFail x MergeInfoOld) (SettledSynVar inctx) = refl
settled-syn-old (SynAsc x MergeInfoOld) (SettledSynAsc x₂) = refl

syn-child2 : ∀ {Γ e t1 n1 t2 n2} ->
  Γ ⊢ EUp (⇑ (t1 , n1)) e ⇒ (t2 , n2) -> 
  SettledSynExcept Γ (EUp (⇑ (t1 , n1)) e) ->
  t1 ≡ t2
syn-child2 (SynConst MergeInfoOld) s = refl
syn-child2 (SynHole MergeInfoOld) s = refl
syn-child2 (SynFun syn eq m) (SettledSynExceptFun s) rewrite (settled-syn-old syn s) rewrite (sym eq) with m 
... | MergeInfoOld = refl
syn-child2 (SynAp syn x mn x₂ m) (SettledSynExceptAp s _) rewrite (settled-syn-old syn s) with mn | m
... | MNArrowOld | MergeInfoOld = refl
syn-child2 (SynApFail syn x mn x₂ m) (SettledSynExceptAp s _) rewrite (settled-syn-old syn s) with mn | m
... | MNArrowOld | MergeInfoOld = refl
syn-child2 (SynVar ctx1 m) (SettledSynExceptVar (Inl ctx2)) rewrite (ctx-unique ctx1 ctx2) with m 
... | MergeInfoOld = refl
syn-child2 (SynVar ctx _) (SettledSynExceptVar (Inr notin)) = ⊥-elim (notin ctx)
syn-child2 (SynVarFail x m) s with m 
... | MergeInfoOld = refl
syn-child2 (SynAsc x m) (SettledSynExceptAsc x₂) with m 
... | MergeInfoOld = refl


settle-no-except : ∀ {Γ t e} ->
  SettledSynExcept Γ (EUp (⇑ (t , Old)) e) ->
  SettledSyn Γ (EUp (⇑ (t , Old)) e) 
settle-no-except SettledSynExceptConst = SettledSynConst
settle-no-except SettledSynExceptHole = SettledSynHole
settle-no-except (SettledSynExceptFun x) = SettledSynFun x
settle-no-except (SettledSynExceptAp x x₁) = SettledSynAp x x₁
settle-no-except (SettledSynExceptVar inctx) = SettledSynVar inctx
settle-no-except (SettledSynExceptAsc x) = SettledSynAsc x

-- mutual 


--   -- generally, case on whether children can step first, then on whether you can. 
--   -- because you want types from below to be old if you want to trust your new types

--   StepsOrSettledSyn : 
--     ∀ {Γ e} ->
--     Σ[ t ∈ NewType ] (Γ ⊢ e ⇒ t) ->
--     Σ[ e' ∈ ExpUp ] (e Up↦ e') + (SettledExcept e)
--   StepsOrSettledSyn (t , SynConst m) = Inr SettledExceptConst
--   StepsOrSettledSyn (t , SynHole m) = Inr SettledExceptHole
--   StepsOrSettledSyn (t , SynFun wt m) = {!   !}
--   StepsOrSettledSyn (.(TArrow _ _ , New) , SynFunVoid wt) = {!   !}
--   StepsOrSettledSyn (t , SynAp syn mt mn ana m) with StepsOrSettledSyn (_ , syn) | StepsOrSettledAna ana 
--   StepsOrSettledSyn (t , SynAp syn mt mn ana m) | Inl (e1' , StepUp fill1 step fill2) | ssana = Inl (_ , StepUp (FillUEnvUpRec (FillUEnvAp1 (FillUEnvLowRec fill1))) step (FillUEnvUpRec (FillUEnvAp1 (FillUEnvLowRec fill2))))
--   StepsOrSettledSyn (t , SynAp syn mt mn ana m) | Inl (e1' , StepLow fill1 step fill2) | ssana = Inl (_ , StepLow (FillLEnvUpRec (FillLEnvAp1 (FillLEnvLowRec fill1))) step (FillLEnvUpRec (FillLEnvAp1 (FillLEnvLowRec fill2))))
--   StepsOrSettledSyn (t , SynAp syn mt mn ana m) | Inr s1 | Inl (e2' , StepUp fill1 step fill2) = Inl (_ , StepUp (FillUEnvUpRec (FillUEnvAp2 fill1)) step (FillUEnvUpRec (FillUEnvAp2 fill2)))
--   StepsOrSettledSyn (t , SynAp syn mt mn ana m) | Inr s1 | Inl (e2' , StepLow fill1 step fill2) = Inl (_ , StepLow (FillLEnvUpRec (FillLEnvAp2 fill1)) step (FillLEnvUpRec (FillLEnvAp2 fill2)))
--   StepsOrSettledSyn (t , SynAp syn mt mn ana m) | Inr s1 | Inr (SettledLowAna s2) = {!   !}
--   -- StepsOrSettledSyn (t , SynAp {e1 = EUp ̸⇑ _} syn mt mn ana m) = {! Inl (_ , StepUp FillU⊙ (StepAp IsNewNew mt mn) FillU⊙)  !}
--   -- StepsOrSettledSyn (t , SynAp {e1 = EUp (⇑ (_ , New)) _} {e2 = ELow _ _ _} syn mt mn ana m) = Inl (_ , StepUp FillU⊙ (StepAp IsNewNew {!   !} {!   !}) FillU⊙)
--   -- StepsOrSettledSyn (t , SynAp {e1 = EUp (⇑ (_ , NArrow _ _)) _} syn mt mn ana m) = {!   !}
--   -- StepsOrSettledSyn (t , SynAp {e1 = EUp (⇑ (_ , Old)) _} syn mt mn ana m) = {!   !}
--   StepsOrSettledSyn (t , SynVar _ m) = Inr SettledExceptVar
--   StepsOrSettledSyn (t , SynVarFail _ m) = Inr SettledExceptVar
--   StepsOrSettledSyn (_ , SynAsc {t = (_ , New)} {e = (ELow _ _ _)} wt m) = Inl (_ , StepUp FillU⊙ (StepAsc IsNewNew) FillU⊙)
--   StepsOrSettledSyn (_ , SynAsc {t = (_ , NArrow _ _)} {e = (ELow _ _ _)} wt m) = Inl (_ , StepUp FillU⊙ (StepAsc IsNewArrow) FillU⊙)
--   StepsOrSettledSyn (_ , SynAsc {t = (_ , Old)} wt m) with StepsOrSettledAna wt
--   StepsOrSettledSyn (_ , SynAsc {t = (_ , Old)} wt m) | Inl (e' , StepUp fill1 step fill2) = Inl (_ , StepUp (FillUEnvUpRec (FillUEnvAsc fill1)) step (FillUEnvUpRec (FillUEnvAsc fill2)))
--   StepsOrSettledSyn (_ , SynAsc {t = (_ , Old)} wt m) | Inl (e' , StepLow fill1 step fill2) = Inl (_ , StepLow (FillLEnvUpRec (FillLEnvAsc fill1)) step (FillLEnvUpRec (FillLEnvAsc fill2)))
--   StepsOrSettledSyn (_ , SynAsc {t = (_ , Old)} wt m) | Inr (SettledLowAna x) = Inr (SettledExceptAsc x)

  
--   StepsOrSettledAna : 
--     ∀ {Γ e t} ->
--     (Γ ⊢ e ⇐ t) ->
--     Σ[ e' ∈ ExpLow ] (e Low↦ e') + (SettledLow e)
--   StepsOrSettledAna wt = {!   !}
 
-- StepsOrSettled : (e : Program) ->
--   Σ[ e' ∈ Program ] (e P↦ e') + (PSettled e)
-- StepsOrSettled e = {!   !} 



mutual 
  
  StepsOrSettledSyn : 
    ∀ {Γ e} ->
    Σ[ t ∈ NewType ] (Γ ⊢ e ⇒ t) ->
    Σ[ e' ∈ ExpUp ] (e Up↦ e') + (SettledSynExcept Γ e)
  StepsOrSettledSyn (t , SynConst _) = Inr SettledSynExceptConst
  StepsOrSettledSyn (t , SynHole _) = Inr SettledSynExceptHole
  StepsOrSettledSyn (t , SynFun syn refl m) = {!   !}
  StepsOrSettledSyn (.(TArrow _ _ , New) , SynFunVoid syn) = {!   !}
  StepsOrSettledSyn (t , SynAp syn mt mn ana m) with StepsOrSettledSyn (_ , syn) | StepsOrSettledAna ana 
  StepsOrSettledSyn (t , SynAp syn mt mn ana m) | Inl (e1' , StepUp fill1 step fill2) | ssana = Inl (_ , StepUp (FillUEnvUpRec (FillUEnvAp1 (FillUEnvLowRec fill1))) step (FillUEnvUpRec (FillUEnvAp1 (FillUEnvLowRec fill2))))
  StepsOrSettledSyn (t , SynAp syn mt mn ana m) | Inl (e1' , StepLow fill1 step fill2) | ssana = Inl (_ , StepLow (FillLEnvUpRec (FillLEnvAp1 (FillLEnvLowRec fill1))) step (FillLEnvUpRec (FillLEnvAp1 (FillLEnvLowRec fill2))))
  StepsOrSettledSyn (t , SynAp syn mt mn ana m) | Inr s1 | Inl (e2' , StepUp fill1 step fill2) = Inl (_ , StepUp (FillUEnvUpRec (FillUEnvAp2 fill1)) step (FillUEnvUpRec (FillUEnvAp2 fill2)))
  StepsOrSettledSyn (t , SynAp syn mt mn ana m) | Inr s1 | Inl (e2' , StepLow fill1 step fill2) = Inl (_ , StepLow (FillLEnvUpRec (FillLEnvAp2 fill1)) step (FillLEnvUpRec (FillLEnvAp2 fill2)))
  StepsOrSettledSyn (t , SynAp syn mt mn ana m) | Inr s1 | Inr s2 with syn-child syn s1 
  StepsOrSettledSyn (t , SynAp {e2 = (ELow _ _ _)} syn mt mn ana m) | Inr s1 | Inr s2 | (_ , New) , _ , refl = Inl (_ , StepUp FillU⊙ (StepAp IsNewNew {!   !} {!   !}) FillU⊙)
  StepsOrSettledSyn (t , SynAp syn mt mn ana m) | Inr s1 | Inr s2 | (_ , NArrow n n₁) , _ , refl = {!   !}
  StepsOrSettledSyn (t , SynAp syn mt mn ana m) | Inr s1 | Inr s2 | (_ , Old) , _ , refl = Inr (SettledSynExceptAp (settle-no-except s1) s2)
  StepsOrSettledSyn (t , SynApFail syn mt mn ana m) = {!   !}
  StepsOrSettledSyn (t , SynVar _ _) = {!   !} -- Inr (SettledSynExceptVar ?)
  StepsOrSettledSyn (t , SynVarFail _ _) = {!   !} -- Inr (SettledSynExceptVar ?)
  StepsOrSettledSyn (t , SynAsc ana _) with StepsOrSettledAna ana
  StepsOrSettledSyn (t , SynAsc ana _) | Inl (_ , StepUp fill1 step fill2) = Inl (_ , StepUp (FillUEnvUpRec (FillUEnvAsc fill1)) step (FillUEnvUpRec (FillUEnvAsc fill2)))
  StepsOrSettledSyn (t , SynAsc ana _) | Inl (_ , StepLow fill1 step fill2) = Inl (_ , StepLow (FillLEnvUpRec (FillLEnvAsc fill1)) step (FillLEnvUpRec (FillLEnvAsc fill2)))
  StepsOrSettledSyn (t , SynAsc {t = (_ , New)} {e = (ELow _ _ _)} ana _) | Inr sana = Inl (_ , StepUp FillU⊙ (StepAsc IsNewNew) FillU⊙)
  StepsOrSettledSyn (t , SynAsc {t = (_ , NArrow _ _)} {e = (ELow _ _ _)} ana _) | Inr sana = Inl (_ , StepUp FillU⊙ (StepAsc IsNewArrow) FillU⊙)
  StepsOrSettledSyn (t , SynAsc {t = (_ , Old)} ana _) | Inr sana = Inr (SettledSynExceptAsc sana)
 
  StepsOrSettledAna :  
    ∀ {Γ e t} ->
    (Γ ⊢ e ⇐ t) ->   
    Σ[ e' ∈ ExpLow ] (e Low↦ e') + (SettledAna Γ e)
  StepsOrSettledAna ana = {!   !}     