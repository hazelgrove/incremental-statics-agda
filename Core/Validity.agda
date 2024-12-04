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
open import Core.Settled
open import Core.Marking

module Core.Validity where

  data BarrenCtx : Ctx -> BareCtx -> Set where 
    BarrenCtxEmpty : BarrenCtx ∅ ∅
    BarrenCtxCons : ∀ {t n Γ Γ'} ->
      BarrenCtx Γ Γ' ->
      BarrenCtx ((t , n) , Γ) (t , Γ')

  tarrow-of-ntarrow : ∀ {t t1 t2 m n m'} ->
    (t , n) ▸NTArrow (t1 , Old) , (t2 , Old) , m ->
    MarkConsist m m' ->
    t ▸TArrowM t1 , t2 , m'
  tarrow-of-ntarrow (MNTArrowOldMatch x) MarkConsistOld = MArrowNoMatch x
  tarrow-of-ntarrow (MNTArrowOldNoMatch x) MarkConsistOld = MArrowMatch x
  tarrow-of-ntarrow MNTArrowArrow MarkConsistOld = MArrowNoMatch MArrowArrow

  mutual 
    validity-syn : ∀ {Γ Γ' e b t n e'} ->
      Γ ⊢ e ⇒ ->
      SettledSyn Γ e ->
      BarrenExp e b ->
      BarrenCtx Γ Γ' ->
      e ≡ (EUp (⇑ (t , n)) e') ->
      Γ' ⊢ b ~> e ⇒ t
    validity-syn (SynConst (SynConsistMerge MergeInfoOld)) SettledSynConst BarrenConst barctx refl = MarkConst
    validity-syn (SynHole (SynConsistMerge MergeInfoOld)) SettledSynHole BarrenHole barctx refl = MarkHole
    validity-syn (SynAp (SynArrowSome {t = (t , n)} match1) (SynConsistMerge MergeInfoOld) (AnaConsistMerge MergeInfoOld) markcon wtsyn wtana) (SettledSynAp setsyn setana) (BarrenAp barexp1 barexp2) barctx refl 
      = MarkAp (validity-syn wtsyn setsyn barexp1 barctx refl) (tarrow-of-ntarrow match1 markcon) (validity-ana wtana setana barexp2 barctx refl)
    validity-syn (SynAsc (SynConsistMerge MergeInfoOld) (AnaConsistMerge MergeInfoOld) wtana) (SettledSynAsc set) (BarrenAsc barexp) barctx refl = MarkAsc (validity-ana wtana set barexp barctx refl)

    validity-ana : ∀ {Γ Γ' e b t n m e'} ->
      Γ ⊢ e ⇐ ->
      SettledAna Γ e ->
      BarrenExpLow e b ->
      BarrenCtx Γ Γ' ->
      e ≡ (ELow (⇓ (t , n)) m e') ->
      Γ' ⊢ b ~> e ⇐ t
    validity-ana = {!   !}

  -- validity : ∀ {e b t} ->
  --   -- e well typed  
  --   Settled e ->
  --   BarrenExp e b ->
  --   ∅ ⊢ b ~> e ⇒ t  
  -- validity = {!   !}  