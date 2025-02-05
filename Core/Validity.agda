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

  barren-ctx-lookup : ∀ {x t n Γ Γ'} ->
    x , (t , n) ∈ Γ ->
    BarrenCtx Γ Γ' ->
    x , t ∈ Γ'
  barren-ctx-lookup InCtx0 (BarrenCtxCons bare-ctx) = InCtx0
  barren-ctx-lookup (InCtxSuc in-ctx) (BarrenCtxCons bare-ctx) = InCtxSuc (barren-ctx-lookup in-ctx bare-ctx)

  barren-ctx-lookup-rev : ∀ {x t Γ Γ'} ->
    BarrenCtx Γ Γ' ->
    x , t ∈ Γ' ->
    ∃[ n ] (x , (t , n) ∈ Γ)
  barren-ctx-lookup-rev BarrenCtxEmpty ()
  barren-ctx-lookup-rev (BarrenCtxCons bare-ctx) InCtx0 = _ , InCtx0
  barren-ctx-lookup-rev (BarrenCtxCons bare-ctx) (InCtxSuc in-ctx) with barren-ctx-lookup-rev bare-ctx in-ctx 
  ... | n , ih = n , (InCtxSuc ih)

  ∈M-of-∈NM : ∀ {x t n m Γ Γ'} ->
    x , (t , n) ∈NM Γ , m -> 
    BarrenCtx Γ Γ' ->
    x , t ∈M Γ' , m
  ∈M-of-∈NM InCtxEmpty BarrenCtxEmpty = InCtxEmpty
  ∈M-of-∈NM InCtxFound (BarrenCtxCons bare-ctx) = InCtxFound
  ∈M-of-∈NM (InCtxSkip in-ctx) (BarrenCtxCons bare-ctx) = InCtxSkip (∈M-of-∈NM in-ctx bare-ctx)

  all-old-lookup : ∀ {x nt nm Γ} ->
    x , nt ∈NM Γ , nm ->
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

    -- Issue: maybe this should really provide the annotation rather than assume it 
    -- (the conclusion is that there exists an e' t and n such that e ≡ (e' ⇒ (■ (t , n))) and Γ' ⊢ b ~> e ⇒ t)
    -- this will make things less nice, and require tightening the invariant
    validity-syn : ∀ {Γ Γ' e b t n e'} ->
      Γ ⊢ e ⇒ ->
      SettledSyn e ->
      BarrenExpUp e b ->
      BarrenCtx Γ Γ' ->
      CtxAllOld Γ -> 
      e ≡ (e' ⇒ (■ (t , n))) ->
      Γ' ⊢ b ~> e ⇒ t
    validity-syn (SynConst (▷DSome (MergeInfoOld refl))) (SettledSynSyn _) (BarrenUp BarrenConst) bare-ctx ctx-old refl = MarkConst
    validity-syn (SynHole (▷DSome (MergeInfoOld refl))) (SettledSynSyn _) (BarrenUp BarrenHole) bare-ctx ctx-old refl = MarkHole
    validity-syn (SynFun (▷DSome (MergeInfoOld refl)) syn) (SettledSynSyn (SettledSynFun (SettledSynSyn sett))) (BarrenUp (BarrenFun {b = b} (BarrenLow (BarrenUp bare)))) bare-ctx ctx-old refl 
      = MarkSynFun (validity-syn syn (SettledSynSyn sett) (BarrenUp bare) (BarrenCtxCons bare-ctx) (ConsAllOld ctx-old) refl)
    validity-syn (SynAp (SynArrowSome (MNTArrowOld tarrow)) (▷DSome (MergeInfoOld refl)) (▷DSome (MergeInfoOld refl)) (▷NMOld refl) wt-syn wt-ana) (SettledSynSyn (SettledSynAp (SettledSynSyn set-syn) (SettledAnaAna set-ana))) (BarrenUp (BarrenAp (BarrenLow bare1) (BarrenLow bare2))) bare-ctx ctx-old refl
      = MarkAp (validity-syn wt-syn (SettledSynSyn set-syn) bare1 bare-ctx ctx-old refl) tarrow (validity-ana wt-ana (SettledAnaAna set-ana) (BarrenLow bare2) bare-ctx ctx-old refl)
    validity-syn (SynVar in-ctx (▷DSome x)) (SettledSynSyn SettledSynVar) (BarrenUp BarrenVar) bare-ctx ctx-old refl with all-old-lookup in-ctx ctx-old | x
    ... | t , refl | MergeInfoOld refl = MarkVar (∈M-of-∈NM in-ctx bare-ctx)
    validity-syn (SynAsc (▷DSome (MergeInfoOld refl)) (▷DSome (MergeInfoOld refl)) wt-ana) (SettledSynSyn (SettledSynAsc (SettledAnaAna set-ana))) (BarrenUp (BarrenAsc bare)) bare-ctx ctx-old refl 
      = MarkAsc (validity-ana wt-ana (SettledAnaAna set-ana) bare bare-ctx ctx-old refl)

    validity-ana : ∀ {Γ Γ' e b t n m e'} ->
      Γ ⊢ e ⇐ ->
      SettledAna e ->
      BarrenExpLow e b ->
      BarrenCtx Γ Γ' ->
      CtxAllOld Γ -> 
      e ≡ (e' [ m ]⇐ (■ (t , n))) ->
      Γ' ⊢ b ~> e ⇐ t
    validity-ana (AnaSubsume subsumable (~DSome (NMConsist consist)) (▷NMOld refl) syn) (SettledAnaAna (SettledAnaSubsume settled-subsumable (SettledSynSyn settled))) (BarrenLow (BarrenUp bare)) bare-ctx ctx-old refl
      = MarkSubsume (validity-syn syn (SettledSynSyn settled) (BarrenUp bare) bare-ctx ctx-old refl) (barren-subsumable subsumable bare) consist
    validity-ana (AnaFun (SynArrowSome (MNTArrowOld tarrow)) ana (NMConsist mark-consist) (▷NMOld refl) (▷NMOld refl) (▷DSome (MergeInfoOld refl)) AnaLamOld) (SettledAnaAna (SettledAnaFun (SettledAnaAna settled))) (BarrenLow (BarrenUp (BarrenFun (BarrenLow (BarrenUp bare))))) bare-ctx ctx-old refl = MarkAnaFun tarrow (validity-ana ana (SettledAnaAna settled) (BarrenLow (BarrenUp bare)) (BarrenCtxCons bare-ctx) (ConsAllOld ctx-old) refl) mark-consist

  validity : ∀ {e e' b t n} ->
    e ⇒ ->
    SettledProgram e ->
    BarrenProgram e b ->   
    e ≡ Root (e' ⇒ (■ (t , n))) -> 
    b ~> e ⇒ t  
  validity (SynProg syn) (SettledRoot settled) (BarrenP bare) refl  
    = MarkProgram (validity-syn syn settled bare BarrenCtxEmpty EmptyAllOld refl)     