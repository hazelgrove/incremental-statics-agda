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
open import Core.Lemmas-Preservation

module Core.Validity where

  data CtxAllOld : Ctx -> Set where 
    EmptyAllOld : CtxAllOld ∅
    ConsAllOld : ∀ {x t Γ} -> 
      CtxAllOld Γ -> 
      CtxAllOld (x ∶ (t , Old) ∷ Γ)
  
  ConsAllOld? : ∀ {x t Γ} -> 
    CtxAllOld Γ -> 
    CtxAllOld (x ∶ (t , Old) ∷? Γ)
  ConsAllOld? {BHole} ctx-old = ctx-old
  ConsAllOld? {BVar x} ctx-old = ConsAllOld ctx-old

  erase-∷? : ∀{x t n Γ} ->
    EraseCtx (x ∶ t , n ∷? Γ) ≡ x ∶ t ∷? (EraseCtx Γ)
  erase-∷? {BHole} = refl
  erase-∷? {BVar x} = refl

  ∈-of-∈N : ∀ {x t n m Γ} ->
    x , (t , n) ∈N Γ , m -> 
    x , t ∈ (EraseCtx Γ) , m
  ∈-of-∈N InCtxEmpty = InCtxEmpty
  ∈-of-∈N InCtxFound = InCtxFound
  ∈-of-∈N (InCtxSkip neq in-ctx) = InCtxSkip neq (∈-of-∈N in-ctx)

  all-old-lookup : ∀ {x nt nm Γ} ->
    x , nt ∈N Γ , nm ->
    CtxAllOld Γ ->
    ∃[ t ] nt ≡ (t , Old)
  all-old-lookup InCtxEmpty ctx-old = THole , refl
  all-old-lookup InCtxFound (ConsAllOld ctx-old) = _ , refl
  all-old-lookup (InCtxSkip neq in-ctx) (ConsAllOld ctx-old) = all-old-lookup in-ctx ctx-old

  barren-subsumable : ∀ {e} ->
    SubsumableMid e ->
    BareSubsumable (EraseMid e)
  barren-subsumable SubsumableConst = BareSubsumableConst
  barren-subsumable SubsumableHole = BareSubsumableHole
  barren-subsumable SubsumableAp = BareSubsumableAp
  barren-subsumable SubsumableVar = BareSubsumableVar
  barren-subsumable SubsumableAsc = BareSubsumableAsc

  ana-edge-wt : ∀ {Γ e m t} ->
    Γ L⊢ ((e ⇒ (■ t , Old)) [ m ]⇐ (□ , Old)) -> 
    m ≡ ✔
  ana-edge-wt (AnaSubsume _ (~N-pair ~DVoidR) ▶Old _) = refl
  ana-edge-wt (AnaFun _ _ _ _ _ _ (~N-pair ~DVoidR) ▶Old _) = refl

  
  -- if e is well typed in Γ, then erasing the annotations and marking from
  -- scratch results in e again (the type it will synthesize is the type 
  -- on the top annotation of e).

  data ValidityUp : BareCtx -> BareExp -> ExpUp -> Set where 
    ValidityUpSyn : ∀ {Γ b e t} ->
      Γ ⊢ b ~> (e ⇒ (■ t , Old)) ⇒ t -> 
      ValidityUp Γ b (e ⇒ (■ t , Old))

  data ValidityLow : BareCtx -> BareExp -> ExpLow -> Set where 
    ValidityLowSyn : ∀ {Γ b e t} ->
      Γ ⊢ b ~> (e ⇒ (■ t , Old)) ⇒ t -> 
      ValidityLow Γ b ((e ⇒ (■ t , Old)) [ ✔ ]⇐ (□ , Old))
    ValidityLowAna : ∀ {Γ b e t m} ->
      Γ ⊢ b ~> (e [ m ]⇐ (■ t , Old)) ⇐ t -> 
      ValidityLow Γ b (e [ m ]⇐ (■ t , Old))

  mutual 
      
    validity-up : ∀ {Γ e} ->
      Γ U⊢ e ->
      SettledUp e ->
      CtxAllOld Γ -> 
      ValidityUp (EraseCtx Γ) (EraseUp e) e
    validity-up (SynConst (▷Pair ▶Old)) (SettledUpC SettledConst) ctx-old = ValidityUpSyn MarkConst
    validity-up (SynHole (▷Pair ▶Old)) (SettledUpC SettledHole) ctx-old = ValidityUpSyn MarkHole
    validity-up (SynAp (NTArrowC marrow) (▷Pair ▶Old) (▷Pair ▶Old) ▶Old syn ana) (SettledUpC (SettledAp (SettledLowC settled1) (SettledLowC settled2))) ctx-old with validity-low syn (SettledLowC settled1) ctx-old | validity-low ana (SettledLowC settled2) ctx-old
    ... | ValidityLowSyn syn' | ValidityLowAna ana' with marrow
    ... | DTArrowSome marrow = ValidityUpSyn (MarkAp syn' marrow ana')
    validity-up (SynVar in-ctx consist) (SettledUpC SettledVar) ctx-old with all-old-lookup in-ctx ctx-old | consist
    ... | _ , refl | ▷Pair ▶Old = ValidityUpSyn (MarkVar (∈-of-∈N in-ctx))
    validity-up (SynAsc (▷Pair ▶Old) (▷Pair ▶Old) ana) (SettledUpC (SettledAsc x₃)) ctx-old with validity-low ana x₃ ctx-old 
    ... | ValidityLowAna ana' = ValidityUpSyn (MarkAsc ana') 

    validity-low : ∀ {Γ e} ->
      Γ L⊢ e ->
      SettledLow e ->
      CtxAllOld Γ -> 
      ValidityLow (EraseCtx Γ) (EraseLow e) e
    validity-low (AnaSubsume {ana-all = □ , n} x consist m-consist x₃) (SettledLowC settled) ctx-old with validity-up x₃ settled ctx-old 
    ... | ValidityUpSyn syn with consist | m-consist
    ... | ~N-pair ~DVoidR | ▶Old = ValidityLowSyn syn
    validity-low (AnaSubsume {ana-all = ■ t , n} subsumable consist m-consist syn) (SettledLowC settled) ctx-old with validity-up syn settled ctx-old 
    ... | ValidityUpSyn syn' with consist | m-consist
    ... | (~N-pair (~DSome consist)) | ▶Old = ValidityLowAna (MarkSubsume syn' (barren-subsumable subsumable) consist)
    validity-low {Γ} (AnaFun {x = x} {ana-all = □ , .Old} (NTArrowC DTArrowNone) consist (▷Pair ▶Old) ▶Old c3 c4 (~N-pair consist') c5 ana) (SettledLowC (SettledUpC (SettledFun {t = t} settled))) ctx-old with validity-low ana settled (ConsAllOld? ctx-old)
    ... | ValidityLowSyn syn rewrite erase-∷? {x} {t} {Old} {Γ}  with consist | c3 | c4 | c5
    ... | ■~N-pair (~N-pair ~DVoidR) | ▶Old | ▷Pair ▶Old | ▶Old with ~DVoid-right consist' 
    ... | refl = ValidityLowSyn (MarkSynFun syn)
    validity-low {Γ} (AnaFun {x = x} {ana-all = ■ t , .Old} (NTArrowC (DTArrowSome marrow)) (■~N-pair (~N-pair (~DSome consist))) (▷Pair ▶Old) ▶Old ▶Old (▷Pair ▶Old) consist' c5 ana) (SettledLowC (SettledUpC (SettledFun {t = t'} settled))) ctx-old 
      with validity-low ana settled (ConsAllOld? ctx-old)
    ... | ValidityLowAna ana' rewrite erase-∷? {x} {t'} {Old} {Γ} with consist' | c5 
    ... | ~N-pair ~DVoidL | ▶Old = ValidityLowAna (MarkAnaFun marrow ana' consist)

  validity : ∀ {p} ->
    P⊢ p ->
    SettledProgram p ->
    ((EraseProgram p) ~> p)
  validity {p = Root e n} (WTProg ana) (SettledRoot settled) with validity-low ana settled EmptyAllOld 
  ... | ValidityLowSyn syn = MarkProgram syn
 