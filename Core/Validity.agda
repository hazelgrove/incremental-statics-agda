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

  validity-syn : ∀ {Γ Γ' e b} ->
    Γ ⊢ e ⇒ ->
    SettledSyn Γ e ->
    BarrenExp e b ->
    BarrenCtx Γ Γ' ->
    ∃[ t ] Γ' ⊢ b ~> e ⇒ t
  validity-syn (SynConst (SynConsistMerge MergeInfoOld)) SettledSynConst BarrenConst barctx = TBase , MarkConst
  validity-syn (SynHole (SynConsistMerge MergeInfoOld)) SettledSynHole BarrenHole barctx = THole , MarkHole


  validity : ∀ {e b t} ->
    -- e well typed 
    Settled e ->
    BarrenExp e b ->
    ∅ ⊢ b ~> e ⇒ t 
  validity = {!   !}