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

  -- tarrow-of-ntarrow : ∀ {t t1 t2 m n m'} ->
  --   (t , n) ▸NTArrow (t1 , Old) , (t2 , Old) , m ->
  --   MarkConsist m m' ->
  --   t ▸TArrowM t1 , t2 , m'
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
      e ≡ ((■ (t , n)) ⇐ e') ->
      Γ' ⊢ b ~> e ⇒ t
    validity-syn (SynConst (▷DSome (MergeInfoOld refl))) SettledSynConst (BarrenUp BarrenConst) barctx refl = MarkConst
    validity-syn (SynHole (▷DSome (MergeInfoOld refl))) SettledSynHole (BarrenUp BarrenHole) barctx refl = MarkHole
    validity-syn (SynFun x syn) (SettledSynFun sett) (BarrenUp (BarrenFun x₁)) barctx eq = {! x  !}
    validity-syn (SynAp x x₁ x₂ x₃ syn x₄) (SettledSynAp sett x₅) (BarrenUp (BarrenAp x₆ x₇)) barctx eq = {!   !}
    validity-syn (SynVar x x₁ x₂) (SettledSynVar x₃) (BarrenUp BarrenVar) barctx eq = {!   !}
    validity-syn (SynAsc x x₁ x₂) (SettledSynAsc x₃) (BarrenUp (BarrenAsc x₄)) barctx eq = {!   !}

    -- (SynConst (SynConsistMerge MergeInfoOld)) SettledSynConst BarrenConst barctx refl = MarkConst
    -- validity-syn (SynHole (SynConsistMerge MergeInfoOld)) SettledSynHole BarrenHole barctx refl = MarkHole
    -- validity-syn (SynAp (SynArrowSome {t = (t , n)} match1) (SynConsistMerge MergeInfoOld) (AnaConsistMerge MergeInfoOld) markcon wtsyn wtana) (SettledSynAp setsyn setana) (BarrenAp barexp1 barexp2) barctx refl 
    --   = MarkAp (validity-syn wtsyn setsyn barexp1 barctx refl) (tarrow-of-ntarrow match1 markcon) (validity-ana wtana setana barexp2 barctx refl)
    -- validity-syn (SynAsc (SynConsistMerge MergeInfoOld) (AnaConsistMerge MergeInfoOld) wtana) (SettledSynAsc set) (BarrenAsc barexp) barctx refl = MarkAsc (validity-ana wtana set barexp barctx refl)

    validity-ana : ∀ {Γ Γ' e b t n m e'} ->
      Γ ⊢ e ⇐ ->
      SettledAna Γ e ->
      BarrenExpLow e b ->
      BarrenCtx Γ Γ' ->
      e ≡ ((■ (t , n)) ⇒[ m ] e') ->
      Γ' ⊢ b ~> e ⇐ t
    validity-ana = {!   !}

  -- validity : ∀ {e b t} ->
  --   -- e well typed  
  --   Settled e ->
  --   BarrenExp e b ->
  --   ∅ ⊢ b ~> e ⇒ t  
  -- validity = {!   !}  