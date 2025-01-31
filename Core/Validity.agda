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
open import Core.Marking
open import Core.WellTyped
open import Core.Settled

module Core.Validity where

  data BarrenCtx : Ctx -> BareCtx -> Set where 
    BarrenCtxEmpty : BarrenCtx ∅ ∅
    BarrenCtxCons : ∀ {t n Γ Γ'} ->
      BarrenCtx Γ Γ' ->
      BarrenCtx ((t , n) ∷ Γ) (t ∷ Γ')

  TArrowM-of-TArrowNM : ∀ {t t1 t2 m n m'} ->
    (t , n) ▸TArrowNM (t1 , Old) , (t2 , Old) , m ->
    -- ▷NM m m' ->
    t ▸TArrowM t1 , t2 , m'
  TArrowM-of-TArrowNM (MNTArrowOld x) = {!   !}
  -- tarrow-of-ntarrow (MNTArrowOldMatch x) MarkConsistOld = MArrowNoMatch x
  -- tarrow-of-ntarrow (MNTArrowOldNoMatch x) MarkConsistOld = MArrowMatch x
  -- tarrow-of-ntarrow MNTArrowArrow MarkConsistOld = MArrowNoMatch MArrowArrow

  mutual 
    -- if e is well typed in Γ, then erasing the annotations and marking from
    -- scratch results in e again (the type it will synthesize is the type 
    -- on the top annotation of e).
    validity-syn : ∀ {Γ Γ' e b t n e'} ->
      Γ ⊢ e ⇒ ->
      SettledSyn Γ e ->
      BarrenExpUp e b ->
      BarrenCtx Γ Γ' ->
      e ≡ (e' ⇒ (■ (t , n))) ->
      Γ' ⊢ b ~> e ⇒ t
    validity-syn (SynConst (▷DSome (MergeInfoOld refl))) (SettledSynSyn _) (BarrenUp BarrenConst) bare-ctx refl = MarkConst
    validity-syn (SynHole (▷DSome (MergeInfoOld refl))) (SettledSynSyn _) (BarrenUp BarrenHole) bare-ctx refl = MarkHole
    validity-syn (SynFun x syn) (SettledSynSyn (SettledSynFun sett)) (BarrenUp (BarrenFun x₁)) bare-ctx eq = {! x  !}
    
    validity-syn (SynAp (SynArrowSome (MNTArrowOld tarrow)) (▷DSome (MergeInfoOld refl)) (▷DSome (MergeInfoOld refl)) (▷NMOld refl) wt-syn wt-ana) (SettledSynSyn (SettledSynAp (SettledSynSyn set-syn) (SettledAnaAna set-ana))) (BarrenUp (BarrenAp (BarrenLow bare1) (BarrenLow bare2))) bare-ctx refl --= {!   !}
      = MarkAp (validity-syn wt-syn (SettledSynSyn set-syn) bare1 bare-ctx refl) tarrow (validity-ana wt-ana (SettledAnaAna set-ana) (BarrenLow bare2) bare-ctx refl)
    validity-syn (SynVar x x₁ x₂) (SettledSynSyn (SettledSynVar x₃)) (BarrenUp BarrenVar) bare-ctx eq = {!   !}
    validity-syn (SynAsc x x₁ x₂) (SettledSynSyn (SettledSynAsc x₃)) (BarrenUp (BarrenAsc x₄)) bare-ctx eq = {!   !}

    -- (SynConst (SynConsistMerge MergeInfoOld)) SettledSynConst BarrenConst bare-ctx refl = MarkConst
    -- validity-syn (SynHole (SynConsistMerge MergeInfoOld)) SettledSynHole BarrenHole bare-ctx refl = MarkHole
    -- validity-syn (SynAp (SynArrowSome {t = (t , n)} match1) (SynConsistMerge MergeInfoOld) (AnaConsistMerge MergeInfoOld) markcon wt-syn wt-ana) (SettledSynAp setsyn setana) (BarrenAp barexp1 barexp2) bare-ctx refl 
    --   = MarkAp (validity-syn wt-syn setsyn barexp1 bare-ctx refl) (tarrow-of-ntarrow match1 markcon) (validity-ana wt-ana setana barexp2 bare-ctx refl)
    -- validity-syn (SynAsc (SynConsistMerge MergeInfoOld) (AnaConsistMerge MergeInfoOld) wt-ana) (SettledSynAsc set) (BarrenAsc barexp) bare-ctx refl = MarkAsc (validity-ana wt-ana set barexp bare-ctx refl)

    validity-ana : ∀ {Γ Γ' e b t n m e'} ->
      Γ ⊢ e ⇐ ->
      SettledAna Γ e ->
      BarrenExpLow e b ->
      BarrenCtx Γ Γ' ->
      e ≡ (e' [ m ]⇐ (■ (t , n))) ->
      Γ' ⊢ b ~> e ⇐ t
    validity-ana = {!   !}

  -- validity : ∀ {e b t} ->
  --   -- e well typed  
  --   Settled e ->
  --   BarrenExp e b ->
  --   ∅ ⊢ b ~> e ⇒ t  
  -- validity = {!   !}  