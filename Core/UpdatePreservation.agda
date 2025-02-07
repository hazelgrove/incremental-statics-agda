open import Data.Nat hiding (_+_; _⊓_)
open import Data.Unit 
open import Data.Empty 
open import Data.Bool hiding (_<_; _≟_)
open import Data.Sum renaming (_⊎_ to _+_; inj₁ to Inl ; inj₂ to Inr) hiding (map)
open import Data.Product hiding (map)
open import Relation.Nullary 
open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Prelude

open import Core.Core
open import Core.Environment
open import Core.WellTyped
open import Core.Update
open import Core.Lemmas-Preservation

module Core.UpdatePreservation where

  vars-syn-subsumable : ∀ {x t e e' syn syn'} ->
    VarsSynthesize x t (e ⇒ syn) (e' ⇒ syn') -> 
    SubsumableMid e ->
    SubsumableMid e'
  vars-syn-subsumable VSConst SubsumableConst = SubsumableConst
  vars-syn-subsumable VSHole SubsumableHole = SubsumableHole
  vars-syn-subsumable (VSFun vars-syn) ()
  vars-syn-subsumable (VSAp vars-syn1 vars-syn2) SubsumableAp = SubsumableAp
  vars-syn-subsumable VSVar SubsumableVar = SubsumableVar
  vars-syn-subsumable (VSOtherVar _) SubsumableVar = SubsumableVar
  vars-syn-subsumable (VSAsc vars-syn) SubsumableAsc = SubsumableAsc

  vars-syn-beyond : ∀ {x t e syn e' syn'} ->
    VarsSynthesize x t (e ⇒ syn) (e' ⇒ syn') -> 
    =▷ syn syn' 
  vars-syn-beyond VSConst = =▷Refl
  vars-syn-beyond VSHole = =▷Refl
  vars-syn-beyond (VSFun syn) = =▷Refl
  vars-syn-beyond (VSAp syn syn₁) = =▷Refl
  vars-syn-beyond VSVar = =▷New
  vars-syn-beyond (VSOtherVar x) = =▷Refl
  vars-syn-beyond (VSAsc syn) = =▷Refl

  -- -- this is imprecise : the =▷D relation is bigger than required. oh well. 
  beyond-U↦ : ∀ {e e' syn syn'} -> 
    (e ⇒ syn) U↦ (e' ⇒ syn') -> 
    =▷ syn syn' 
  beyond-U↦ (StepAp _) = =▷New
  beyond-U↦ StepAsc = =▷New

  beyond-U↦-env : ∀ {ε e e' e-in e-in' syn syn'} -> 
    e-in U↦ e-in' -> 
    ε U⟦ e-in ⟧Up== (e ⇒ syn) ->
    ε U⟦ e-in' ⟧Up== (e' ⇒ syn') ->
    =▷ syn syn' 
  beyond-U↦-env step FillU⊙ FillU⊙ = beyond-U↦ step
  beyond-U↦-env step (FillUEnvUpRec _) (FillUEnvUpRec _) = =▷Refl

  beyond-L↦ : ∀ {e e' m m' ana ana'} -> 
    (e [ m ]⇐ ana) L↦ (e' [ m' ]⇐ ana') -> 
    ◁▷ ana ana' 
  beyond-L↦ (StepNewSynConsist _) = ◁▷C
  beyond-L↦ (StepNewAnaConsist _ _) = ◁▷C
  beyond-L↦ (StepAnaFun _ _) = ◁▷C
  beyond-L↦ (StepSynFun) = ◁▷C
  beyond-L↦ (StepNewAnnFun _) = ◁▷C

  cooler-beyond-L↦-inner : ∀ {e e' syn syn' m m' n-ana ana'} -> 
    ((e ⇒ syn) [ m ]⇐ (□ , n-ana)) L↦ ((e' ⇒ syn') [ m' ]⇐ ana') -> 
    =▷ syn syn' 
  -- cooler-beyond-L↦-inner (StepNewSynConsist x) = {!  =▷New !}
  -- cooler-beyond-L↦-inner (StepNewAnaConsist x x₁) = {!   !}
  cooler-beyond-L↦-inner (StepAnaFun x x₁) = =▷New
  cooler-beyond-L↦-inner (StepNewAnnFun x) = =▷New
  cooler-beyond-L↦-inner StepSynFun = =▷New

  beyond-L↦-inner : ∀ {e e' syn syn' n n'} -> 
    ((e ⇒ syn) [ ✔ ]⇐ (□ , n)) L↦ ((e' ⇒ syn') [ ✔ ]⇐ (□ , n')) -> 
    =▷ syn syn' 
  beyond-L↦-inner (StepAnaFun a b) = =▷New
  beyond-L↦-inner (StepNewAnnFun _) = =▷New
  beyond-L↦-inner StepSynFun = =▷New

  cooler-beyond-L↦-env-inner : ∀ {ε e e' e-in e-in' syn syn' m m' n-ana ana'} -> 
    e-in L↦ e-in' -> 
    ε L⟦ e-in ⟧Low== ((e ⇒ syn) [ m ]⇐ (□ , n-ana)) ->
    ε L⟦ e-in' ⟧Low== ((e' ⇒ syn') [ m' ]⇐ ana') ->
    =▷ syn syn' 
  cooler-beyond-L↦-env-inner step FillL⊙ FillL⊙ = cooler-beyond-L↦-inner step
  cooler-beyond-L↦-env-inner step (FillLEnvLowRec (FillLEnvUpRec _)) (FillLEnvLowRec (FillLEnvUpRec _)) = =▷Refl

  beyond-L↦-env : ∀ {ε e e' e-in e-in' m m' ana ana'} -> 
    e L↦ e' -> 
    ε L⟦ e ⟧Low== (e-in [ m ]⇐ ana) ->
    ε L⟦ e' ⟧Low== (e-in' [ m' ]⇐ ana') ->
    ◁▷ ana ana' 
  beyond-L↦-env step FillL⊙ FillL⊙ = beyond-L↦ step
  beyond-L↦-env step (FillLEnvLowRec _) (FillLEnvLowRec _) = ◁▷C

  step-subsumable : ∀ {e e' syn syn'} -> 
    (e ⇒ syn) U↦ (e' ⇒ syn') ->
    SubsumableMid e -> 
    SubsumableMid e'
  step-subsumable (StepAp _) SubsumableAp = SubsumableAp
  step-subsumable StepAsc SubsumableAsc = SubsumableAsc

  oldify-ctx : Ctx -> ℕ -> Ctx 
  oldify-ctx ∅ x = ∅
  oldify-ctx ((t , n) ∷ Γ) zero = ((t , Old) ∷ Γ)
  oldify-ctx ((t , n) ∷ Γ) (suc x) = ((t , n) ∷ (oldify-ctx Γ x))

  oldify-access : ∀ {x t n Γ m} ->
    x , (t , n) ∈N Γ , m ->
    x , (t , Old) ∈N oldify-ctx Γ x , m
  oldify-access InCtxEmpty = InCtxEmpty
  oldify-access InCtxFound = InCtxFound
  oldify-access (InCtxSkip in-ctx) = InCtxSkip (oldify-access in-ctx)

  oldify-access-neq : ∀ {x y t Γ m} ->
    y , t ∈N Γ , m ->
    ¬(y ≡ x) ->
    y , t ∈N oldify-ctx Γ x , m
  oldify-access-neq InCtxEmpty neq = InCtxEmpty
  oldify-access-neq {x = zero} InCtxFound neq = ⊥-elim (neq refl)
  oldify-access-neq {x = suc x} InCtxFound neq = InCtxFound
  oldify-access-neq {x = zero} (InCtxSkip in-ctx) neq = InCtxSkip in-ctx
  oldify-access-neq {x = suc x} (InCtxSkip in-ctx) neq = InCtxSkip (oldify-access-neq in-ctx λ eq → neq (cong suc eq))
  
  mutual 

    preservation-vars-ana :
      ∀ {Γ Γ' x t e e' m ana} ->
      (Γ ⊢ (e [ m ]⇐ ana) ⇐) ->
      VarsSynthesize x t e e' ->
      x , (t , New) ∈N Γ , ✔ ->
      oldify-ctx Γ x ≡ Γ' ->
      (Γ' ⊢ (e' [ m ]⇐ ana) ⇐)
    preservation-vars-ana {e' = e-all' ⇒ syn-all'} {ana = ana} (AnaSubsume subsumable consist-t consist-m syn) vars-syn in-ctx refl with ~N-dec syn-all' ana 
    ... | m-consist' , consist-t' = AnaSubsume (vars-syn-subsumable vars-syn subsumable) consist-t' (beyond-▶ (beyond-through-~N (vars-syn-beyond vars-syn) consist-t consist-t') consist-m) (preservation-vars-syn syn vars-syn in-ctx refl)
    preservation-vars-ana (AnaFun {t-asc = t-asc} marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) (VSFun {e-body' = e-body' ⇒ syn-body'} vars-syn) in-ctx refl 
      = AnaFun marrow consist consist-ana consist-asc consist-body (preservation-lambda-lemma-3 {t = t-asc} (vars-syn-beyond vars-syn) consist-syn) consist-all consist-m-all (preservation-vars-ana ana vars-syn (InCtxSkip in-ctx) refl)      

    preservation-vars-syn :
      ∀ {Γ Γ' x t e e'} ->
      (Γ ⊢ e ⇒) ->
      VarsSynthesize x t e e' ->
      x , (t , New) ∈N Γ , ✔ ->
      oldify-ctx Γ x ≡ Γ' ->
      (Γ' ⊢ e' ⇒)
    preservation-vars-syn (SynConst consist) VSConst in-ctx refl = SynConst consist
    preservation-vars-syn (SynHole consist) VSHole in-ctx refl = SynHole consist
    -- preservation-vars-syn (SynFun consist syn) (VSFun {e-body' = e-body' ⇒ syn-body'} vars-syn) in-ctx refl = SynFun (preservation-lambda-lemma (vars-syn-beyond vars-syn) consist) (preservation-vars-syn syn vars-syn (InCtxSkip in-ctx) refl)
    preservation-vars-syn (SynAp marrow consist-syn consist-ana consist-mark syn ana) (VSAp {e1' = e-fun' ⇒ syn-fun'} vars-syn-fun vars-syn-arg) in-ctx refl with ▸NTArrow-dec syn-fun' 
    ... | t-in-fun' , t-out-fun' , m-fun' , marrow' with beyond-▸NTArrow (vars-syn-beyond vars-syn-fun) marrow marrow' 
    ... | t-in-beyond , t-out-beyond , m-beyond = SynAp marrow' (beyond-▷ t-out-beyond consist-syn) (beyond-▷ t-in-beyond consist-ana) (beyond-▶ m-beyond consist-mark) (preservation-vars-ana syn vars-syn-fun in-ctx refl) (preservation-vars-ana ana vars-syn-arg in-ctx refl)
    preservation-vars-syn {t = t} (SynVar in-ctx consist) VSVar in-ctx' refl with ∈N-unicity in-ctx in-ctx' 
    ... | refl , refl = SynVar (oldify-access in-ctx) (▷■Pair (▷Pair ▶Old)) 
    preservation-vars-syn (SynVar in-ctx consist) (VSOtherVar neq) in-ctx' refl = SynVar (oldify-access-neq in-ctx neq) consist
    preservation-vars-syn (SynAsc consist-syn consist-ana ana) (VSAsc vars-syn) in-ctx refl = SynAsc consist-syn consist-ana (preservation-vars-ana ana vars-syn in-ctx refl)

  -- preservation-vars-indirect-syn :
  --   ∀ {Γ Γ' x t e e' m} ->
  --   (Γ ⊢ (e [ m ]⇐ (□ , Old)) ⇐) ->
  --   VarsSynthesize x t e e' ->
  --   x , (t , New) ∈N Γ , ✔ ->
  --   oldify-ctx Γ x ≡ Γ' ->
  --   (Γ' ⊢ (e' [ m ]⇐ (□ , Old)) ⇐)
  -- preservation-vars-indirect-syn (AnaSubsume subsumable (~N-pair consist-t) consist-m syn) vars-syn in-ctx refl = {!   !}
  -- preservation-vars-indirect-syn (AnaFun marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) (VSFun vars-syn) in-ctx refl = {!   !} 

  PreservationStepSyn :  
    ∀ {Γ e e'} ->
    (Γ ⊢ e ⇒) ->
    (e U↦ e') ->   
    (Γ ⊢ e' ⇒)
  PreservationStepSyn (SynConst _) ()
  PreservationStepSyn (SynHole _) ()
  PreservationStepSyn (SynAp marrow consist-syn consist-ana consist-mark syn ana) (StepAp marrow') = SynAp (NTArrowC (DTArrowSome marrow')) (▷Pair ▶Old) (▷Pair ▶Old) ▶Old (oldify-syn-inner syn) (newify-ana ana)
  PreservationStepSyn (SynVar _ _) ()
  PreservationStepSyn (SynAsc consist-syn consist-ana ana) StepAsc = SynAsc (▷■Pair (▷Pair ▶Old)) (▷■Pair (▷Pair ▶Old)) (newify-ana ana)
  
  PreservationStepAna :  
    ∀ {Γ e e'} ->
    (Γ ⊢ e ⇐) ->
    (e L↦ e') ->   
    (Γ ⊢ e' ⇐)
  PreservationStepAna (AnaSubsume subsumable (~N-pair consist-t) consist-m syn) (StepNewSynConsist consist) with consist-t 
  ... | ~DSome consist-t rewrite ~-unicity consist consist-t = AnaSubsume subsumable (~N-pair (~DSome consist-t)) ▶Old (oldify-syn syn)
  PreservationStepAna (AnaSubsume subsumable (~N-pair (~DSome consist-t)) consist-m syn) (StepNewAnaConsist subsumable' consist) rewrite ~-unicity consist consist-t = AnaSubsume subsumable' (~N-pair (~DSome consist-t)) ▶Old (oldify-syn syn)
  PreservationStepAna (AnaFun marrow consist consist-ana consist-asc consist-body consist-syn (~N-pair (~DSome consist-all)) consist-m-all ana) (StepNewSynConsist consist') rewrite ~-unicity consist' consist-all  = AnaFun marrow consist consist-ana consist-asc consist-body (beyond-▷-contra ◁▷C consist-syn) (~N-pair (~DSome consist-all)) ▶Old ana
  PreservationStepAna (AnaFun {t-asc = t-asc , n-asc} (NTArrowC x) consist (▷Pair ▶New) ▶New consist-body consist-syn consist-all consist-m-all ana) (StepAnaFun marrow' (■~D-pair consist')) = AnaFun (NTArrowC marrow') (■~N-pair (~N-pair consist')) (▷Pair ▶Old) ▶Old ▶Same (consist-unless-lemma {n1 = n-asc}) (~N-pair ~D-unless) ▶Same (newify-ana ana)
  PreservationStepAna (AnaFun {e-body = e-body} marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) (StepNewAnnFun {e-body' = e-body' ⇒ (syn-body' , n-syn-body')} {t-asc} {t-body} {n-body} vars-syn) = AnaFun (NTArrowC DTArrowNone) (■~N-pair (~N-pair ~DVoidR)) (▷Pair ▶Old) ▶Old ▶Old (preservation-lambda-lemma-2 (vars-syn-beyond vars-syn')) (~N-pair ~DVoidR) ▶New (preservation-vars-ana ana vars-syn InCtxFound refl)
    where 
    vars-syn' : VarsSynthesize 0 t-asc (e-body ⇒ (■ t-body , n-body)) (e-body' ⇒ (syn-body' , n-syn-body' ⊓ Old))
    vars-syn' rewrite max-old n-syn-body' = vars-syn
  PreservationStepAna (AnaFun marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) StepSynFun = AnaFun (NTArrowC DTArrowNone) (■~N-pair (~N-pair ~DVoidR)) (▷Pair ▶Old) ▶Old ▶Same (▷Pair ▶Same) (~N-pair ~DVoidR) ▶New (oldify-syn-inner ana)
  
  -- PreservationStepSyn (SynFun consist syn) (StepNewAnnFun {e-body' = e-body' ⇒ syn-body'} vars-syn) = SynFun (preservation-lambda-lemma-2 (vars-syn-beyond vars-syn)) (preservation-vars-syn syn vars-syn InCtxFound refl)
  -- PreservationStepSyn (SynFun consist syn) (StepNewSynFun {t-asc = t-asc} {t-body} {n-asc}) = SynFun (direct-arrow-consist-lemma t-asc t-body n-asc Old) (oldify-syn syn)


  mutual 

    PreservationSyn :  
      ∀ {Γ e e'} ->
      (Γ ⊢ e ⇒) ->
      (e Up↦ e') ->   
      (Γ ⊢ e' ⇒)
    PreservationSyn syn (StepUp FillU⊙ step FillU⊙) = PreservationStepSyn syn step
    PreservationSyn (SynConst _) (StepUp (FillUEnvUpRec ()) step (FillUEnvUpRec fill2))
    PreservationSyn (SynConst _) (StepLow (FillLEnvUpRec ()) _ (FillLEnvUpRec _))
    PreservationSyn (SynHole _) (StepUp (FillUEnvUpRec ()) step (FillUEnvUpRec fill2))
    PreservationSyn (SynHole _) (StepLow (FillLEnvUpRec ()) _ (FillLEnvUpRec _))    
    PreservationSyn (SynVar _ _) (StepUp (FillUEnvUpRec ()) step (FillUEnvUpRec fill2))
    PreservationSyn (SynVar _ _) (StepLow (FillLEnvUpRec ()) _ (FillLEnvUpRec _))
    PreservationSyn (SynAp marrow consist-syn consist-ana consist-mark syn ana) (StepUp {e-in' = e-fun' ⇒ syn-fun'} (FillUEnvUpRec (FillUEnvAp1 (FillUEnvLowRec (FillUEnvUpRec fill1)))) step (FillUEnvUpRec (FillUEnvAp1 (FillUEnvLowRec (FillUEnvUpRec fill2))))) = SynAp marrow consist-syn consist-ana consist-mark (PreservationAna syn (StepUp (FillUEnvLowRec (FillUEnvUpRec fill1)) step (FillUEnvLowRec (FillUEnvUpRec fill2)))) ana 
    PreservationSyn (SynAp marrow consist-syn consist-ana consist-mark syn ana) (StepUp {e-in' = e-fun' ⇒ syn-fun'} (FillUEnvUpRec (FillUEnvAp1 (FillUEnvLowRec FillU⊙))) step (FillUEnvUpRec (FillUEnvAp1 (FillUEnvLowRec FillU⊙)))) with ▸NTArrow-dec syn-fun' 
    ... | t-in-fun' , t-out-fun' , m-fun' , marrow' with beyond-▸NTArrow (beyond-U↦ step) marrow marrow' 
    ... | t-in-beyond , t-out-beyond , m-beyond = SynAp marrow' (beyond-▷ t-out-beyond consist-syn) (beyond-▷ t-in-beyond consist-ana) (beyond-▶ m-beyond consist-mark) (PreservationAna syn (StepUp (FillUEnvLowRec FillU⊙) step (FillUEnvLowRec FillU⊙))) ana 
    PreservationSyn (SynAp marrow consist-syn consist-ana consist-mark syn ana) (StepLow (FillLEnvUpRec (FillLEnvAp1 (FillLEnvLowRec (FillLEnvUpRec fill1)))) step (FillLEnvUpRec (FillLEnvAp1 (FillLEnvLowRec (FillLEnvUpRec fill2))))) = SynAp marrow consist-syn consist-ana consist-mark (PreservationAna syn (StepLow (FillLEnvLowRec (FillLEnvUpRec fill1)) step (FillLEnvLowRec (FillLEnvUpRec fill2)))) ana 
    PreservationSyn (SynAp marrow consist-syn consist-ana consist-mark syn ana) (StepLow {e-in' = (e-fun' ⇒ syn-fun') [ ✔ ]⇐ (□ , Old)} (FillLEnvUpRec (FillLEnvAp1 FillL⊙)) step (FillLEnvUpRec (FillLEnvAp1 FillL⊙))) with ▸NTArrow-dec syn-fun' 
    ... | t-in-fun' , t-out-fun' , m-fun' , marrow' with beyond-▸NTArrow (beyond-L↦-inner step) marrow marrow' 
    ... | t-in-beyond , t-out-beyond , m-beyond = SynAp marrow' (beyond-▷ t-out-beyond consist-syn) (beyond-▷ t-in-beyond consist-ana) (beyond-▶ m-beyond consist-mark) (PreservationAna syn (StepLow FillL⊙ step FillL⊙)) ana 
    PreservationSyn (SynAp marrow consist-syn consist-ana consist-mark syn ana) (StepUp (FillUEnvUpRec (FillUEnvAp2 (FillUEnvLowRec fill1))) step (FillUEnvUpRec (FillUEnvAp2 (FillUEnvLowRec fill2)))) = SynAp marrow consist-syn consist-ana consist-mark syn (PreservationAna ana (StepUp (FillUEnvLowRec fill1) step (FillUEnvLowRec fill2)))
    PreservationSyn (SynAp marrow consist-syn consist-ana consist-mark syn ana) (StepLow {e-in' = e-in' [ m' ]⇐ ana'} (FillLEnvUpRec (FillLEnvAp2 FillL⊙)) step (FillLEnvUpRec (FillLEnvAp2 FillL⊙))) = SynAp marrow consist-syn (beyond-▷-contra (beyond-L↦-env step FillL⊙ FillL⊙) consist-ana) consist-mark syn (PreservationAna ana (StepLow FillL⊙ step FillL⊙))  
    PreservationSyn (SynAp marrow consist-syn consist-ana consist-mark syn ana) (StepLow (FillLEnvUpRec (FillLEnvAp2 (FillLEnvLowRec fill1))) step (FillLEnvUpRec (FillLEnvAp2 (FillLEnvLowRec fill2)))) = SynAp marrow consist-syn consist-ana consist-mark syn (PreservationAna ana (StepLow (FillLEnvLowRec fill1) step (FillLEnvLowRec fill2)))
    PreservationSyn (SynAsc consist-syn consist-ana ana) (StepLow (FillLEnvUpRec (FillLEnvAsc fill1)) step (FillLEnvUpRec (FillLEnvAsc {e' = e-body' [ m-body' ]⇐ ana-body'} fill2))) = SynAsc consist-syn (beyond-▷■-contra (beyond-L↦-env step fill1 fill2) consist-ana) (PreservationAna ana (StepLow fill1 step fill2))
    PreservationSyn (SynAsc consist-syn consist-ana ana) (StepUp (FillUEnvUpRec (FillUEnvAsc (FillUEnvLowRec fill1))) step (FillUEnvUpRec (FillUEnvAsc (FillUEnvLowRec fill2)))) = SynAsc consist-syn consist-ana (PreservationAna ana (StepUp (FillUEnvLowRec fill1) step (FillUEnvLowRec fill2)))

    PreservationAna :  
      ∀ {Γ e e'} -> 
      (Γ ⊢ e ⇐) ->
      (e Low↦ e') ->   
      (Γ ⊢ e' ⇐) 
    PreservationAna ana (StepLow FillL⊙ step FillL⊙) = PreservationStepAna ana step
    PreservationAna (AnaSubsume {ana-all = ana-all} subsumable consist-t consist-m syn) (StepUp {e-in' = e-all' ⇒ syn-all'} (FillUEnvLowRec FillU⊙) step (FillUEnvLowRec FillU⊙)) with ~N-dec syn-all' ana-all 
    ... | m' , consist-t' = AnaSubsume (step-subsumable step subsumable) consist-t' (beyond-▶ (beyond-through-~N (beyond-U↦ step) consist-t consist-t') consist-m) (PreservationSyn syn (StepUp FillU⊙ step FillU⊙))    
    PreservationAna (AnaSubsume subsumable consist-t consist-m syn) (StepUp (FillUEnvLowRec (FillUEnvUpRec fill1)) step (FillUEnvLowRec (FillUEnvUpRec fill2))) = AnaSubsume (u-env-subsumable fill1 fill2 subsumable) consist-t consist-m (PreservationSyn syn (StepUp (FillUEnvUpRec fill1) step (FillUEnvUpRec fill2)))
    PreservationAna (AnaSubsume subsumable consist-t consist-m syn) (StepLow (FillLEnvLowRec (FillLEnvUpRec fill1)) step (FillLEnvLowRec (FillLEnvUpRec fill2))) = AnaSubsume (l-env-subsumable fill1 fill2 subsumable) consist-t consist-m (PreservationSyn syn (StepLow (FillLEnvUpRec fill1) step (FillLEnvUpRec fill2))) 
    PreservationAna (AnaFun {t-asc = t-asc} marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) (StepUp (FillUEnvLowRec (FillUEnvUpRec (FillUEnvFun (FillUEnvLowRec fill1)))) step (FillUEnvLowRec (FillUEnvUpRec (FillUEnvFun (FillUEnvLowRec {e' = e' ⇒ syn'} fill2))))) = AnaFun marrow consist consist-ana consist-asc consist-body (preservation-lambda-lemma-3 {t = t-asc} (beyond-U↦-env step fill1 fill2) consist-syn) consist-all consist-m-all (PreservationAna ana (StepUp (FillUEnvLowRec fill1) step (FillUEnvLowRec fill2))) 
    -- snag : this one's subtle. -- (preservation-lambda-lemma-3 {t = t-asc} {! beyond-L↦-env  !} consist-syn)
    -- if analyzed against new, propagate new and consist
    -- if analyzed against old none, then body is analyzed against none, cannot take subsume step
    -- if analyzed against old some, then unless triggers and reuse consistency
    PreservationAna (AnaFun {ana-all = ana-all , New} {t-asc = (t-asc , n-asc)} marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) (StepLow (FillLEnvLowRec (FillLEnvUpRec (FillLEnvFun fill1))) step (FillLEnvLowRec (FillLEnvUpRec (FillLEnvFun {e' = (e' ⇒ (syn' , n-syn')) [ m' ]⇐ ana'} fill2)))) = AnaFun marrow consist (beyond-▷-contra (beyond-L↦-env step fill1 fill2) consist-ana) consist-asc consist-body NUnless-new-▶ consist-all consist-m-all (PreservationAna ana (StepLow fill1 step fill2))
    PreservationAna (AnaFun {ana-all = ■ ana-all , Old} {t-asc = (t-asc , n-asc)} marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) (StepLow (FillLEnvLowRec (FillLEnvUpRec (FillLEnvFun fill1))) step (FillLEnvLowRec (FillLEnvUpRec (FillLEnvFun {e' = (e' ⇒ (syn' , n-syn')) [ m' ]⇐ ana'} fill2)))) =  AnaFun marrow consist (beyond-▷-contra (beyond-L↦-env step fill1 fill2) consist-ana) consist-asc consist-body consist-syn consist-all consist-m-all (PreservationAna ana (StepLow fill1 step fill2))
    PreservationAna (AnaFun {syn-body = syn-body} {ana-all = □ , Old} {t-asc = t-asc , n-asc} (NTArrowC DTArrowNone) (■~N-pair (~N-pair ~DVoidR)) (▷Pair ▶Old) ▶Old consist-body consist-syn (~N-pair {d1} {n1 = n1} consist) consist-m-all ana) (StepLow (FillLEnvLowRec (FillLEnvUpRec (FillLEnvFun fill1))) step (FillLEnvLowRec (FillLEnvUpRec (FillLEnvFun {e' = (e' ⇒ (syn' , n-syn')) [ m' ]⇐ ana'} fill2)))) --= ?
      = AnaFun (NTArrowC DTArrowNone) (■~N-pair (~N-pair ~DVoidR)) (beyond-▷-contra (beyond-L↦-env step fill1 fill2) (▷Pair ▶Old)) ▶Old consist-body (preservation-lambda-lemma-3 {t = (t-asc , n-asc)} {syn1 = syn-body} {syn1' = (syn' , n-syn')} {syn2 = (d1 , n1)} {ana = □ , Old} (cooler-beyond-L↦-env-inner step fill1 fill2) consist-syn) (~N-pair consist) consist-m-all (PreservationAna ana (StepLow fill1 step fill2))

  PreservationProgram :  
    ∀ {p p'} ->
    (WellTypedProgram p) ->
    (p P↦ p') ->   
    (WellTypedProgram p')
  PreservationProgram (WTProg ana) (TopStep step) = WTProg (PreservationAna ana step)
  