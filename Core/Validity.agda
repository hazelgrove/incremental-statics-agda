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

  data CtxAllOld : Ctx -> Set where 
    EmptyAllOld : CtxAllOld ∅
    ConsAllOld : ∀ {t Γ} -> 
      CtxAllOld Γ -> 
      CtxAllOld ((t , Old) ∷ Γ)

  ∈-of-∈N : ∀ {x t n m Γ Γ'} ->
    x , (t , n) ∈N Γ , m -> 
    BarrenCtx Γ Γ' ->
    x , t ∈ Γ' , m
  ∈-of-∈N InCtxEmpty BarrenCtxEmpty = InCtxEmpty
  ∈-of-∈N InCtxFound (BarrenCtxCons bare-ctx) = InCtxFound
  ∈-of-∈N (InCtxSkip in-ctx) (BarrenCtxCons bare-ctx) = InCtxSkip (∈-of-∈N in-ctx bare-ctx)

  all-old-lookup : ∀ {x nt nm Γ} ->
    x , nt ∈N Γ , nm ->
    CtxAllOld Γ ->
    ∃[ t ] nt ≡ (t , Old)
  all-old-lookup InCtxEmpty ctx-old = THole , refl
  all-old-lookup InCtxFound (ConsAllOld ctx-old) = _ , refl
  all-old-lookup (InCtxSkip in-ctx) (ConsAllOld ctx-old) = all-old-lookup in-ctx ctx-old

  barren-subsumable : ∀ {e b} ->
    SubsumableMid e ->
    BarrenExpMid e b ->
    BareSubsumable b
  barren-subsumable SubsumableConst BarrenConst = BareSubsumableConst
  barren-subsumable SubsumableHole BarrenHole = BareSubsumableHole
  barren-subsumable SubsumableAp (BarrenAp _ _) = BareSubsumableAp
  barren-subsumable SubsumableVar BarrenVar = BareSubsumableVar
  barren-subsumable SubsumableAsc (BarrenAsc _) = BareSubsumableAsc

  mutual 
    -- if e is well typed in Γ, then erasing the annotations and marking from
    -- scratch results in e again (the type it will synthesize is the type 
    -- on the top annotation of e).

    validity-indirect-syn : ∀ {Γ Γ' e b t n e'} ->
      Γ ⊢ (e [ ✔ ]⇐ (□ , Old)) ⇐ ->
      SettledSyn e ->
      BarrenExpUp e b ->
      BarrenCtx Γ Γ' ->
      CtxAllOld Γ -> 
      e ≡ (e' ⇒ ((■ t , n))) ->
      Γ' ⊢ b ~> e ⇒ t
    validity-indirect-syn (AnaSubsume x x₁ x₂ x₃) settled bare bare-ctx ctx-old refl = validity-syn x₃ settled bare bare-ctx ctx-old refl
    validity-indirect-syn (AnaFun (NTArrowC DTArrowNone) (■~N-pair (~N-pair ~DVoidR)) (▷Pair ▶Old) ▶Old ▶Old (▷Pair ▶Old) (~N-pair ~DVoidR) ▶Old syn) (SettledSynSyn (SettledSynFun (SettledSynSyn settled))) (BarrenUp (BarrenFun (BarrenLow (BarrenUp bare)))) bare-ctx ctx-old refl = 
      MarkSynFun (validity-indirect-syn syn (SettledSynSyn settled) (BarrenUp bare) (BarrenCtxCons bare-ctx) (ConsAllOld ctx-old) refl)

    -- Issue: maybe this should really provide the annotation rather than assume it 
    -- (the conclusion is that there exists an e' t and n such that e ≡ (e' ⇒ (■ (t , n))) and Γ' ⊢ b ~> e ⇒ t)
    -- this will make things less nice, and require tightening the invariant
    validity-syn : ∀ {Γ Γ' e b t n e'} ->
      Γ ⊢ e ⇒ ->
      SettledSyn e ->
      BarrenExpUp e b ->
      BarrenCtx Γ Γ' ->
      CtxAllOld Γ -> 
      e ≡ (e' ⇒ ((■ t , n))) ->
      Γ' ⊢ b ~> e ⇒ t
    validity-syn (SynConst (▷Pair ▶Old)) (SettledSynSyn _) (BarrenUp BarrenConst) bare-ctx ctx-old refl = MarkConst
    validity-syn (SynHole (▷Pair ▶Old)) (SettledSynSyn _) (BarrenUp BarrenHole) bare-ctx ctx-old refl = MarkHole
    validity-syn (SynAp (NTArrowC (DTArrowSome tarrow)) (▷Pair ▶Old) (▷Pair ▶Old) ▶Old syn ana) (SettledSynSyn (SettledSynAp (SettledSynSyn set-syn) (SettledAnaAna set-ana))) (BarrenUp (BarrenAp (BarrenLow bare1) (BarrenLow bare2))) bare-ctx ctx-old refl
      = MarkAp (validity-indirect-syn syn (SettledSynSyn set-syn) bare1 bare-ctx ctx-old refl) tarrow (validity-ana ana (SettledAnaAna set-ana) (BarrenLow bare2) bare-ctx ctx-old refl)
    validity-syn (SynVar in-ctx (▷■Pair (▷Pair x))) (SettledSynSyn SettledSynVar) (BarrenUp BarrenVar) bare-ctx ctx-old refl with all-old-lookup in-ctx ctx-old | x
    ... | t , refl | ▶Old = MarkVar (∈-of-∈N in-ctx bare-ctx)
    validity-syn (SynAsc (▷■Pair (▷Pair ▶Old)) (▷■Pair (▷Pair ▶Old)) ana) (SettledSynSyn (SettledSynAsc set-ana)) (BarrenUp (BarrenAsc bare)) bare-ctx ctx-old refl 
      = MarkAsc (validity-ana ana set-ana bare bare-ctx ctx-old refl)

    validity-ana : ∀ {Γ Γ' e b t n m e'} ->
      Γ ⊢ e ⇐ ->
      SettledAna e ->
      BarrenExpLow e b ->
      BarrenCtx Γ Γ' ->
      CtxAllOld Γ -> 
      e ≡ (e' [ m ]⇐ ((■ t , n))) ->
      Γ' ⊢ b ~> e ⇐ t
    validity-ana (AnaSubsume subsumable (~N-pair (~DSome consist)) ▶Old syn) (SettledAnaAna (SettledAnaSubsume settled-subsumable (SettledSynSyn settled))) (BarrenLow (BarrenUp bare)) bare-ctx ctx-old refl 
      = MarkSubsume (validity-syn syn (SettledSynSyn settled) (BarrenUp bare) bare-ctx ctx-old refl) (barren-subsumable settled-subsumable bare) consist
    validity-ana (AnaFun (NTArrowC (DTArrowSome marrow)) (■~N-pair (~N-pair (~DSome consist))) (▷Pair ▶Old) ▶Old ▶Old (▷Pair x₁) (~N-pair ~DVoidL) ▶Old ana) (SettledAnaAna (SettledAnaFun (SettledAnaAna settled))) (BarrenLow (BarrenUp (BarrenFun bare))) bare-ctx ctx-old refl 
      = MarkAnaFun marrow (validity-ana ana (SettledAnaAna settled) bare (BarrenCtxCons bare-ctx) (ConsAllOld ctx-old) refl) consist 

  validity : ∀ {p b e t n1 n2} ->
    WellTypedProgram p ->
    SettledProgram p ->
    BarrenProgram p b ->   
    p ≡ Root (e ⇒ (■ t , n1)) n2 -> 
    b ~> p ⇒ t   
  validity (WTProg (AnaSubsume _ _ _ syn)) (SettledRoot settled) (BarrenP (BarrenLow bare)) refl = MarkProgram (validity-syn syn settled bare BarrenCtxEmpty EmptyAllOld refl)
  validity (WTProg (AnaFun x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈)) (SettledRoot settled) (BarrenP (BarrenLow bare)) refl = MarkProgram (validity-indirect-syn (AnaFun x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) settled bare BarrenCtxEmpty EmptyAllOld refl)
